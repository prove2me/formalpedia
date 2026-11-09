-- Prove2me | Definitions.Def_AlmostLinearModComp_Composition_Builder
-- name    : AlmostLinearModComp_Composition_Builder
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T10:48:25.571626+00:00
-- url     : https://prove2.me/theorems/1b32798a-9039-4c43-9f58-8835b8f91ae1
-- title:
--   Charged arithmetic circuit construction and scalar preparation
-- statement:
--   A circuit builder appends actual addition, subtraction and multiplication gates. It splices fixed-scalar linear programs and bilinear multiplication programs into that same gate list. A multiplier family contains raw finite bilinear program syntax indexed by the polynomial size; it contains no correctness, speed, inversion, or oracle field. Theorems quantify existentially over this syntax and assert the resulting correctness and bounds in their conclusions.
--
--   The explicit arithmetic constructions are coefficient-vector Kronecker multiplication with all product coefficients retained, Newton reciprocal, monic remainder by reversal and products, quotient multiplication, binary powering, and the monic Hankel multiplication and solve. The latter use the triangular Toeplitz symbol from the reversed monic polynomial. Invalid or insufficient-fuel inputs have total finite outputs; the source statements impose positive sizes and the routines supply sufficient fuel.
--
--   For a circuit whose fixed data precede its variable data, the syntactic derivative at variable zero constructs a linear program. Every primal scalar computation is emitted into the surrounding circuit. The tangent program contains only additions, subtractions and multiplication by these recorded fixed scalars. This compiler asserts no linearity or correctness; the coordinate-change theorem must establish that its result is the desired linear map. Simplification inspects only integer-zero/one wire syntax, never a ring coefficient.
-- source:
--   yang zhou, Mingsheng Wang, Almost-Linear Modular Composition over Arbitrary Commutative Rings, STOC 2027 submission #450 (October 2026), §3.2, printed pp.5–6 / PDF pp.6–7; §A.1–A.2, printed p.11 / PDF p.12; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/450.pdf

import Definitions.Def_AlmostLinearModComp_Composition_Bilinear
import Definitions.Def_AlmostLinearModComp_Composition_Transposition

namespace AlmostLinearModComp.Composition

/-- A circuit builder only appends arithmetic gates. Its state is the actual gate vector. -/
abbrev Code := StateM (Array RingGate)
abbrev WVec := List Wire

def atW (x : WVec) (i : ℕ) : Wire := x[i]?.getD (.integer 0)
def wires (n : ℕ) (f : ℕ → Wire) : WVec := (List.range n).map f

def emit (g : RingGate) : Code Wire := do
  -- Structural simplifications inspect integer syntax only, never a value in R.
  match g with
  | .add (.integer 0) b | .add b (.integer 0) | .sub b (.integer 0) => return b
  | .mul (.integer 0) _ | .mul _ (.integer 0) => return .integer 0
  | .mul (.integer 1) b | .mul b (.integer 1) => return b
  | _ =>
    let gs ← get
    let i := gs.size
    set (gs.push g)
    return .gate i

def compile (p : Code WVec) : Circuit :=
  let (o, gs) := p.run #[]
  ⟨gs.toList, o⟩

def linearWireAt (x previous : WVec) : LinearWire → Wire
  | .zero => .integer 0
  | .input i => atW x i
  | .gate i => atW previous i

/-- Splice every linear operation into the surrounding division-free circuit. -/
def emitLinear (p : LinearProgram) (scalars x : WVec) : Code WVec := do
  let fixed := scalars.toArray
  let input := x.toArray
  let read := fun (previous : Array Wire) (w : LinearWire) => match w with
    | .zero => Wire.integer 0
    | .input i => input[i]?.getD (.integer 0)
    | .gate i => previous[i]?.getD (.integer 0)
  let mut previous : Array Wire := #[]
  for g in p.gates do
    let y ← match g with
      | .add a b => emit (.add (read previous a) (read previous b))
      | .sub a b => emit (.sub (read previous a) (read previous b))
      | .scale k a => emit (.mul (fixed[k]?.getD (.integer 0)) (read previous a))
    previous := previous.push y
  return p.outputs.map (read previous)

/-- Raw arithmetic implementations: no correctness, speed or oracle field. -/
abbrev Multipliers := ℕ → BilinearProgram

def emitProduct (B : Multipliers) (s : ℕ) (x y : WVec) : Code WVec := do
  let b := B s
  let scalars := b.scalars.map Wire.integer
  let u ← emitLinear b.left scalars x
  let v ← emitLinear b.right scalars y
  let u := u.toArray
  let v := v.toArray
  let w ← (List.range b.rank).mapM fun i =>
    emit (.mul (u[i]?.getD (.integer 0)) (v[i]?.getD (.integer 0)))
  emitLinear b.finish scalars w

def padW (n : ℕ) (x : WVec) : WVec := wires n (atW x)

/-- Kronecker multiplication retaining the whole X product and then q t-coefficients.
Vectors use X-coordinate-major blocks of q coefficients. -/
def productXT (B : Multipliers) (n q : ℕ) (x y : WVec) : Code WVec := do
  let width := 2 * n - 1
  let size := width * q
  let encode := fun a => wires size fun k =>
    if k % width < n then atW a ((k % width) * q + k / width) else .integer 0
  let z ← emitProduct B size (encode x) (encode y)
  return wires (width * q) fun k => atW z (k / q + width * (k % q))

/-- Newton reciprocal; fuel is an explicit recursion bound, never a ring test. -/
def reciprocalFuel (B : Multipliers) : ℕ → ℕ → WVec → Code WVec
  | 0, s, _ => pure (wires s fun _ => .integer 0)
  | fuel + 1, s, u => do
    if s ≤ 1 then return wires s fun _ => .integer 1
    let h ← reciprocalFuel B fuel ((s + 1) / 2) u
    let uh ← emitProduct B s (padW s u) (padW s h)
    let correction ← (List.range s).mapM fun i =>
      emit (.sub (.integer (if i = 0 then 2 else 0)) (atW uh i))
    let next ← emitProduct B s (padW s h) correction
    return padW s next

def reciprocal (B : Multipliers) (s : ℕ) (u : WVec) : Code WVec :=
  reciprocalFuel B s s u

/-- The monic coefficient is implicit; all lower coefficients are actual input wires. -/
def reverseMonic (n : ℕ) (f : WVec) : WVec :=
  wires (n + 1) fun i => if i = 0 then .integer 1 else atW f (n - i)

/-- Reversal, reciprocal and products implement division by a monic polynomial.
No inverse gate or remainder oracle occurs in the returned circuit. -/
def remainderW (B : Multipliers) (n : ℕ) (f h : WVec) : Code WVec := do
  let inv ← reciprocal B n (reverseMonic n f)
  let quotRev ← emitProduct B n (wires n fun i => atW h (2 * n - 1 - i)) inv
  let quot := wires n fun i => atW quotRev (n - 1 - i)
  let fq ← emitProduct B (n + 1) (f ++ [.integer 1]) (padW (n + 1) quot)
  (List.range n).mapM fun i => emit (.sub (atW h i) (atW fq i))

def quotientProduct (B : Multipliers) (n q : ℕ) (f x y : WVec) : Code WVec := do
  let z ← productXT B n q x y
  let cols ← (List.range q).mapM fun t =>
    remainderW B n f (wires (2 * n) fun i => atW z (i * q + t))
  return wires (n * q) fun k => atW (cols[k % q]?.getD []) (k / q)

def unitXT (n q : ℕ) : WVec :=
  wires (n * q) fun i => .integer (if i = 0 then 1 else 0)

/-- Binary powering of an actual quotient-ring vector; only integer exponents branch. -/
def quotientPowerFuel (B : Multipliers) (n q : ℕ) (f : WVec) :
    ℕ → ℕ → WVec → Code WVec
  | 0, _, _ => pure (unitXT n q)
  | fuel + 1, e, x => do
    if e = 0 then return unitXT n q
    let h ← quotientPowerFuel B n q f fuel (e / 2) x
    let square ← quotientProduct B n q f h h
    if e % 2 = 0 then return square
    quotientProduct B n q f square x

def quotientPower (B : Multipliers) (n q : ℕ) (f : WVec) (e : ℕ) (x : WVec) : Code WVec :=
  quotientPowerFuel B n q f (e + 1) e x

/-- H has reversed columns equal to the Toeplitz matrix with symbol 1/reverse(F).
The inverse therefore multiplies by reverse(F) and reverses the result. -/
def hankelSolve (B : Multipliers) (n q : ℕ) (f b : WVec) : Code WVec := do
  let symbol := wires (n * q) fun k =>
    if k % q = 0 then atW (reverseMonic n f) (k / q) else .integer 0
  let x ← productXT B n q symbol b
  return wires (n * q) fun k => atW x ((n - 1 - k / q) * q + k % q)

def hankelMultiply (B : Multipliers) (n q : ℕ) (f b : WVec) : Code WVec := do
  let inv ← reciprocal B n (reverseMonic n f)
  let symbol := wires (n * q) fun k =>
    if k % q = 0 then atW inv (k / q) else .integer 0
  let rev := wires (n * q) fun k => atW b ((n - 1 - k / q) * q + k % q)
  let x ← productXT B n q symbol rev
  return padW (n * q) x

/-- Data for the syntactic derivative at variable input zero. Primal gates are charged
in Code, and tangent gates are recorded as a fixed-scalar linear program. -/
structure TangentState where
  primal : WVec := []
  tangent : List LinearWire := []
  scalars : WVec := []
  gates : List LinearGate := []

def primalWire (fixed : WVec) (s : TangentState) : Wire → Wire
  | .integer z => .integer z
  | .input i => atW fixed i
  | .gate i => atW s.primal i

def tangentWire (fixedInputs : ℕ) (s : TangentState) : Wire → LinearWire
  | .integer _ => .zero
  | .input i => if i < fixedInputs then .zero else .input (i - fixedInputs)
  | .gate i => s.tangent[i]?.getD .zero

/-- This is a syntactic compiler, not a linearity assumption. Its use for the source
routines is justified by their theorem statements. Every fixed scalar has a charged
primal computation, and no new value from R is supplied to the compiler. -/
def linearize (c : Circuit) (fixedInputs : ℕ) (fixed : WVec) :
    Code (LinearProgram × WVec) := do
  let mut s : TangentState := {}
  for g in c.gates do
    let (a, b) := match g with | .add a b | .sub a b | .mul a b => (a, b)
    let va := primalWire fixed s a
    let vb := primalWire fixed s b
    let da := tangentWire fixedInputs s a
    let db := tangentWire fixedInputs s b
    let v ← match g with
      | .add _ _ => emit (.add va vb)
      | .sub _ _ => emit (.sub va vb)
      | .mul _ _ => emit (.mul va vb)
    let old := s.gates.length
    let (nextGates, nextScalars) := match g with
      | .add _ _ => ([LinearGate.add da db], s.scalars)
      | .sub _ _ => ([LinearGate.sub da db], s.scalars)
      | .mul _ _ =>
        ([LinearGate.scale s.scalars.length db,
          LinearGate.scale (s.scalars.length + 1) da,
          LinearGate.add (.gate old) (.gate (old + 1))], s.scalars ++ [va, vb])
    s := { primal := s.primal ++ [v]
           tangent := s.tangent ++ [.gate (old + nextGates.length - 1)]
           scalars := nextScalars, gates := s.gates ++ nextGates }
  return (⟨s.gates, c.outputs.map (tangentWire fixedInputs s)⟩, s.scalars)

end AlmostLinearModComp.Composition



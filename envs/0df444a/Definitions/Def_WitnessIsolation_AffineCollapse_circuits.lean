-- Prove2me | Definitions.Def_WitnessIsolation_AffineCollapse_circuits
-- name    : WitnessIsolation_AffineCollapse_circuits
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T10:31:09.289991+00:00
-- url     : https://prove2.me/theorems/c508e384-1bab-44f9-bb00-46f4ac8228bc
-- title:
--   Boolean DAG circuits and explicit descriptions
-- statement:
--   A circuit has ordered Boolean inputs and outputs and a finite list of constant, NOT, binary AND, and binary OR gates in topological order. Wires may be shared with unrestricted fan-out. Its size is its gate count. Output wires can be inputs or gates. For a well-formed description H on n declared variables, its solution set is
--
--   $$\operatorname{Sol}(H)=\{x\in\{0,1\}^n:H(x)=1\}.$$
--
--   The serialization has unary integer fields, fixed gate tags, and an explicit output wire. A scalar description contains the declared input count, gate count, gate list, and output index, followed by arbitrary ignored padding. The decoder rejects forward or out-of-range references and descriptions declaring more variables than their bit length. A padded input for length cap s consists of an s+1-bit unary actual-length header and an s-bit payload; unused header and payload positions must be zero. Every actual length from zero to s can be represented; malformed descriptions still fail decoding.
--
--   These definitions separate description bit length from declared witness count and computational gate count. They provide concrete syntax, parsing and evaluation for the pruning and SAT contracts. An n=0 input vector has one assignment; constants remain legitimate circuits. Multi-output circuits describe actual transforming computations, rather than functions carrying an asserted cost.
--
--   **Formalization Note** Binary vectors are functions on Fin n. Integer fields are unary, a fixed polynomial change from binary wire indices. Gates are counted once even if reused. No claim of efficient composition or SAT compilation is assumed by these definitions.
-- source:
--   Sebastian ben daniel, STOC 2027 submission #346 (October 2026), §2, printed pp. 6–7, PDF pp. 7–8, circuit-encoding and padded-SAT conventions; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/346.pdf; PDF SHA256 969057d4c1837a5ebf1d45c70a14c1d66f0d76610c6233f151e2402e7611f42e

import Mathlib

set_option autoImplicit false

namespace WitnessIsolation.AffineCollapse

/-- Binary words of a prescribed length; coordinates are zero based. -/
abbrev Bits (n : ℕ) := Fin n → Bool

/-- Gates read numbered wires, with inputs preceding gates. -/
inductive Gate where
  | const : Bool → Gate
  | neg : ℕ → Gate
  | conj : ℕ → ℕ → Gate
  | disj : ℕ → ℕ → Gate
  deriving DecidableEq, Inhabited

def Gate.refs : Gate → List ℕ
  | .const _ => []
  | .neg i => [i]
  | .conj i j => [i,j]
  | .disj i j => [i,j]

def Gate.value (a : List Bool) : Gate → Bool
  | .const b => b
  | .neg i => !(a.getD i false)
  | .conj i j => a.getD i false && a.getD j false
  | .disj i j => a.getD i false || a.getD j false

/-- Arbitrary fan-out and shared gates, ordered inputs, and ordered outputs. -/
structure Circuit (n m : ℕ) where
  gates : List Gate
  valid : ∀ i, ∀ g, gates[i]? = some g → ∀ j ∈ g.refs, j < n + i
  outputs : Fin m → ℕ
  outputs_valid : ∀ i, outputs i < n + gates.length

def Circuit.size {n m : ℕ} (c : Circuit n m) : ℕ := c.gates.length

def Circuit.eval {n m : ℕ} (c : Circuit n m) (x : Bits n) : Bits m :=
  let vals := c.gates.foldl (fun a g => a ++ [g.value a]) (List.ofFn x)
  fun i => vals.getD (c.outputs i) false

def Circuit.accepts {n : ℕ} (c : Circuit n 1) (x : Bits n) : Prop :=
  c.eval x 0 = true

/-- Unary fields make the chosen encoding polynomially longer than binary wire fields. -/
def natCode (n : ℕ) : List Bool := List.replicate n true ++ [false]

def readNat : List Bool → Option (ℕ × List Bool)
  | [] => none
  | false :: xs => some (0,xs)
  | true :: xs => do
    let (n,ys) ← readNat xs
    pure (n+1,ys)

def gateCode : Gate → List Bool
  | .const false => [false,false,false]
  | .const true => [false,false,true]
  | .neg i => [false,true,false] ++ natCode i
  | .conj i j => [true,false,false] ++ natCode i ++ natCode j
  | .disj i j => [true,true,false] ++ natCode i ++ natCode j

/-- Full multi-output circuit serialization, including each declared input and output. -/
def Circuit.encode {n m : ℕ} (C : Circuit n m) : List Bool :=
  natCode n ++ natCode m ++ natCode C.gates.length ++ C.gates.flatMap gateCode ++
    (List.ofFn C.outputs).flatMap natCode

def readGate : List Bool → Option (Gate × List Bool)
  | false :: false :: b :: xs => some (.const b,xs)
  | false :: true :: false :: xs => do
    let (i,ys) ← readNat xs
    pure (.neg i,ys)
  | true :: false :: false :: xs => do
    let (i,ys) ← readNat xs
    let (j,zs) ← readNat ys
    pure (.conj i j,zs)
  | true :: true :: false :: xs => do
    let (i,ys) ← readNat xs
    let (j,zs) ← readNat ys
    pure (.disj i j,zs)
  | _ => none

def readGates : ℕ → List Bool → Option (List Gate × List Bool)
  | 0,xs => some ([],xs)
  | k+1,xs => do
    let (g,ys) ← readGate xs
    let (gs,zs) ← readGates k ys
    pure (g::gs,zs)

/-- Parsed scalar circuit; the remaining description text is ignored padding. -/
structure Description where
  inputs : ℕ
  gates : List Gate
  output : ℕ
  deriving DecidableEq

def Description.Valid (d : Description) : Prop :=
  (∀ i, ∀ g, d.gates[i]? = some g → ∀ j ∈ g.refs, j < d.inputs + i) ∧
    d.output < d.inputs + d.gates.length

instance (d : Description) : Decidable d.Valid := by
  unfold Description.Valid
  exact decidable_of_iff
    ((∀ i ∈ List.range d.gates.length, ∀ g ∈ d.gates[i]?.toList,
        ∀ j ∈ g.refs, j < d.inputs+i) ∧ d.output < d.inputs+d.gates.length)
    (by simp only [List.mem_range, Option.mem_toList]; constructor
        · rintro ⟨h,ho⟩; refine ⟨?_,ho⟩
          intro i g hg j hj
          exact h i (List.getElem?_eq_some_iff.mp hg).choose g hg j hj
        · rintro ⟨h,ho⟩; exact ⟨fun i _ g hg => h i g hg,ho⟩)

def parse (w : List Bool) : Option Description := do
  let (n,rs) ← readNat w
  let (k,rs) ← readNat rs
  let (gs,rs) ← readGates k rs
  let (o,_) ← readNat rs
  pure ⟨n,gs,o⟩

def decode (w : List Bool) : Option Description := do
  let d ← parse w
  if d.Valid ∧ d.inputs ≤ w.length then some d else none

def Description.encode (d : Description) (padding : List Bool := []) : List Bool :=
  natCode d.inputs ++ natCode d.gates.length ++ d.gates.flatMap gateCode ++
    natCode d.output ++ padding

def Description.eval (d : Description) (x : Bits d.inputs) : Bool :=
  (d.gates.foldl (fun a g => a ++ [g.value a]) (List.ofFn x)).getD d.output false

def Description.sol (d : Description) : Finset (Bits d.inputs) :=
  Finset.univ.filter (fun x => d.eval x = true)

def word (x : List Bool) (n : ℕ) : Bits n := fun i => x.getD i false

def concatBits {n m : ℕ} (x : Bits n) (y : Bits m) : Bits (n+m) :=
  word (List.ofFn x ++ List.ofFn y) (n+m)

/-- Unary actual-length header of width s+1, then s payload bits; length = 2s+1. -/
def paddedWidth (s : ℕ) : ℕ := 2*s+1

def pad (s : ℕ) (w : List Bool) : Bits (paddedWidth s) :=
  word (List.replicate w.length true ++ List.replicate (s+1-w.length) false ++
    w ++ List.replicate (s-w.length) false) (paddedWidth s)

def unpad (s : ℕ) (x : Bits (paddedWidth s)) : Option (List Bool) := do
  let xs := List.ofFn x
  let (k,rest) ← readNat (xs.take (s+1))
  if k ≤ s ∧ rest.all (fun b => !b) ∧
      ((xs.drop (s+1)).drop k).all (fun b => !b) then
    some ((xs.drop (s+1)).take k)
  else none

def decodedPadded (s : ℕ) (x : Bits (paddedWidth s)) : Option Description :=
  unpad s x >>= decode

end WitnessIsolation.AffineCollapse



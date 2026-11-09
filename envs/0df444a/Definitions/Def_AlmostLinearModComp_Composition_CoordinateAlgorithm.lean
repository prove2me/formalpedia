-- Prove2me | Definitions.Def_AlmostLinearModComp_Composition_CoordinateAlgorithm
-- name    : AlmostLinearModComp_Composition_CoordinateAlgorithm
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T10:49:24.576866+00:00
-- url     : https://prove2.me/theorems/a64388d8-7c1d-4019-a6f3-59000d558949
-- title:
--   Convolution and precision-recursive coordinate-change programs
-- statement:
--   The convolution circuit reverses the supplied $M$ array in every digit, performs the full Kronecker product, and extracts the required coefficients. For an old-basis input it doubles the last exponent, implementing $p(z,y^2)$ exactly.
--
--   At precision one, the solve multiplies by the reversed monic polynomial and reverses the result. At precision $q>1$, it first solves at $h=\lfloor q/2\rfloor$, computes the full residual, shifts by $h$ coefficient places, solves the correction at $q-h$, and concatenates the two coefficient blocks. Both recursive calls retain the same modulus and stored array. The changing precision and stored precision are separate arguments.
--
--   A stored change contains concrete linear-program syntax and wires computing its fixed scalars. Scalar preparation is charged by the surrounding builder; it contains no correctness or cost certificate. Applying the transpose uses the explicit two coefficient-block reversals around the coefficient-map transpose. A change plan exposes its fixed-data preparation circuit separately from its variable-linear program.
-- source:
--   yang zhou, Mingsheng Wang, Almost-Linear Modular Composition over Arbitrary Commutative Rings, STOC 2027 submission #450 (October 2026), §3.2, equations (5)–(9) and Lemma 3.1, printed pp.5–7 / PDF pp.6–8; §A.2, printed p.11 / PDF p.12; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/450.pdf

import Definitions.Def_AlmostLinearModComp_Composition_Builder
import Definitions.Def_AlmostLinearModComp_Composition_Stages

namespace AlmostLinearModComp.Composition

/-- Restriction/extension of coordinate-major t blocks is just a wire permutation. -/
def precisionW (n old new : ℕ) (x : WVec) : WVec :=
  wires (n * new) fun i => if i % new < old then
    atW x ((i / new) * old + i % new) else .integer 0

/-- Equation (8), or equation (9) when old=true. K is reversed in every digit;
old y exponents are doubled. The multiplication retains all encoded coefficients. -/
def convolutionW (B : Multipliers) {d : Radices} (s : Stage d)
    (q : ℕ) (M x : WVec) (old : Bool) : Code WVec := do
  let K := wires (s.arraySize * q) fun i =>
    atW M ((s.arraySize - 1 - i / q) * q + i % q)
  let entries := (List.range d.size).map fun e =>
    (s.arrayIndex fun i => (if old && i = d.m then 2 else 1) *
      s.basisDigit old e i, e)
  let encoded := wires (s.arraySize * q) fun k =>
    match entries.find? (fun ie => ie.1 = k / q) with
    | none => .integer 0
    | some ie => atW x (ie.2 * q + k % q)
  let z ← productXT B s.arraySize q K encoded
  return wires (d.size * q) fun k =>
    let pos := s.arraySize - 1 - s.arrayIndex (s.basisDigit false (k / q))
    atW z (pos * q + k % q)

/-- Both recursive calls retain F and the same stored M; only t precision decreases.
The residual division is an index shift. No ring inverse is evaluated. -/
def henselFuel (B : Multipliers) {d : Radices} (s : Stage d)
    (storedPrecision : ℕ) (f M : WVec) : ℕ → ℕ → WVec → Code WVec
  | 0, q, _ => pure (wires (d.size * q) fun _ => .integer 0)
  | fuel + 1, q, b => do
    if q ≤ 1 then return ← hankelSolve B d.size q f b
    let h := q / 2
    let x₀ ← henselFuel B s storedPrecision f M fuel h (precisionW d.size q h b)
    let Gx₀ ← convolutionW B s q (precisionW s.arraySize storedPrecision q M)
      (precisionW d.size h q x₀) false
    let residual ← (List.range (d.size * (q - h))).mapM fun k =>
      let i := k / (q - h) * q + h + k % (q - h)
      emit (.sub (atW b i) (atW Gx₀ i))
    let x₁ ← henselFuel B s storedPrecision f M fuel (q - h) residual
    return wires (d.size * q) fun k =>
      if k % q < h then atW x₀ ((k / q) * h + k % q)
      else atW x₁ ((k / q) * (q - h) + k % q - h)

/-- Assemble x₀+t^h x₁. The correction must be ADDED to x₀'s extension;
x₀ has no stored coefficients at degrees h and above. -/
def coordinateW (B : Multipliers) {d : Radices} (s : Stage d)
    (L q : ℕ) (f M p : WVec) : Code WVec := do
  let b ← convolutionW B s q (precisionW s.arraySize L q M) p true
  henselFuel B s L f M q q b

def coordinateCircuit (B : Multipliers) {d : Radices} (s : Stage d)
    (L q : ℕ) : Circuit :=
  let fixed := d.size + s.arraySize * L
  compile (coordinateW B s L q (wires d.size Wire.input)
    (wires (s.arraySize * L) fun i => .input (d.size + i))
    (wires (d.size * q) fun i => .input (fixed + i)))

/-- A stored change contains concrete linear syntax and the wires computing its scalars.
It contains no correctness certificate, inverse matrix, or operation-bound field. -/
structure StoredChange where
  program : LinearProgram
  scalars : WVec

/-- Compile a change from exactly F and M. Primal scalar preparation is charged in Code. -/
def prepareChange (B : Multipliers) {d : Radices} (s : Stage d)
    (L q : ℕ) (f M : WVec) : Code StoredChange := do
  let (p, scalars) ← linearize (coordinateCircuit B s L q)
    (d.size + s.arraySize * L) (f ++ M)
  return ⟨p, scalars⟩

def applyChange (p : StoredChange) (x : WVec) : Code WVec :=
  emitLinear p.program p.scalars x

/-- The coefficient-block reversals are part of the actual transpose, not only its spec. -/
def applyChangeTranspose (p : StoredChange) (n q : ℕ) (x : WVec) : Code WVec :=
  emitLinear (transposeTruncated p.program n q) p.scalars x

/-- Fixed-data preprocessing and the resulting variable-linear program, separated for A.2. -/
def changePlan (B : Multipliers) {d : Radices} (s : Stage d) (L q : ℕ) :
    Circuit × LinearProgram :=
  let (p, gates) := (prepareChange B s L q (wires d.size Wire.input)
    (wires (s.arraySize * L) fun i => .input (d.size + i))).run #[]
  (⟨gates.toList, p.scalars⟩, p.program)

end AlmostLinearModComp.Composition



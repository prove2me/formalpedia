-- Prove2me | Definitions.Def_PolynomialPackingMM_IntegerRecursion_RecursiveCompiler
-- name    : PolynomialPackingMM_IntegerRecursion_RecursiveCompiler
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T07:04:09.960481+00:00
-- url     : https://prove2.me/theorems/9316c84b-bddc-4ff2-b119-e8fe561cdf88
-- title:
--   Finite rational identities, effective search and the recursive integer compiler
-- statement:
--   Finite identity data store a side $v$, a rank $r$ and the rational coefficient arrays for two encoders and a decoder. Their correctness is universal coefficient matching for ordered matrix multiplication, separately asserted. Bounded enumeration searches these finite arrays using a rational exponent certificate $t>0$ and the decidable inequality $r^{\operatorname{den}(t)}<v^{\operatorname{num}(t)}$.
--
--   Let $d$ be the product of the positive denominators of every coefficient in the three arrays, and put $\Delta=d^3$. Each array is multiplied by $d$. The compiler forms encoded $v\times v$ blocks, recursively computes the $r$ ordered products, decodes and divides every output entry exactly by $\Delta$. Scalars are multiplied directly. For arbitrary $n$, it pads to $N=v^{\lceil\log_v n\rceil}$ and crops.
--
--   $$a=6r+1,\qquad C_\alpha=v^\alpha\left(1+\frac{a}{1-r/v^\alpha}\right).$$
--
--   This defines one executable compiler, not an arbitrary family of programs supplied by a hypothesis. **Formalization Note** Data contain no correctness field. The bounded search, denominator clearing, padding, program construction and evaluator are computable. The displayed constant is used only under $v\ge2$, $r\ge1$, $2<\alpha$, and a strict rank certificate below $\alpha$. Padding and cropping contribute $b=0$ in this model.
-- source:
--   Rafael Pass, STOC 2027 submission #1507 (October 2026), printed p. 19 (PDF 20), Corollary 4.4 and §4.3, proof of Theorem 1.1; https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1507.pdf; SHA256 8b32ede93c8ade8e982503a0a1eec78b50621e6fcf86eba92bef2e77847b26ba

import Definitions.Def_PolynomialPackingMM_IntegerRecursion_IntegerProgram

namespace PolynomialPackingMM.IntegerRecursion

open scoped BigOperators

/-- Finite rational data only; neither correctness nor a rank bound is a structure field. -/
structure IdentityData where
  v : ℕ
  r : ℕ
  left : List ℚ
  right : List ℚ
  decode : List ℚ
  deriving DecidableEq

def IdentityData.leftCoeff (D : IdentityData) (ν a : ℕ) : ℚ :=
  D.left[ν * D.v ^ 2 + a]?.getD 0

def IdentityData.rightCoeff (D : IdentityData) (ν b : ℕ) : ℚ :=
  D.right[ν * D.v ^ 2 + b]?.getD 0

def IdentityData.outputCoeff (D : IdentityData) (o ν : ℕ) : ℚ :=
  D.decode[o * D.r + ν]?.getD 0

/-- Coefficient matching for AB, with the inner matrix index contracted in its usual order. -/
def IdentityData.Correct (D : IdentityData) : Prop :=
  D.left.length = D.r * D.v ^ 2 ∧ D.right.length = D.r * D.v ^ 2 ∧
    D.decode.length = D.v ^ 2 * D.r ∧
    ∀ (o a b : Fin (D.v ^ 2)),
      (∑ ν : Fin D.r, D.leftCoeff ν a * D.rightCoeff ν b * D.outputCoeff o ν) =
        if o.val / D.v = a.val / D.v ∧ a.val % D.v = b.val / D.v ∧
          o.val % D.v = b.val % D.v then 1 else 0

instance (D : IdentityData) : Decidable D.Correct := by
  unfold IdentityData.Correct
  infer_instance

/-- A rational, decidable strict exponent certificate, equivalent to r < v^t for v,r>0. -/
def IdentityData.StrictRank (D : IdentityData) (t : ℚ) : Prop :=
  0 < t ∧ D.r ^ t.den < D.v ^ t.num.toNat

instance (D : IdentityData) (t : ℚ) : Decidable (D.StrictRank t) := by
  unfold IdentityData.StrictRank
  infer_instance

/-- Decode the standard effective enumeration of tuples of naturals and rational lists. -/
def decodeIdentity (code : ℕ) : Option IdentityData :=
  (Encodable.decode (α := ℕ × ℕ × List ℚ × List ℚ × List ℚ) code).map
    (fun x => ⟨x.1, x.2.1, x.2.2.1, x.2.2.2.1, x.2.2.2.2⟩)

/-- Bounded computable search. The theorem supplies a successful finite bound, never an oracle. -/
def searchIdentity (t : ℚ) (bound : ℕ) : Option IdentityData :=
  ((List.range (bound + 1)).filterMap decodeIdentity).find?
    (fun D => decide (2 ≤ D.v ∧ 1 ≤ D.r ∧ D.Correct ∧ D.StrictRank t))

/-- One common positive denominator for all three maps, with repetitions harmless. -/
def IdentityData.denominator (D : IdentityData) : ℕ+ :=
  ((D.left ++ D.right ++ D.decode).map (fun q => (⟨q.den, q.den_pos⟩ : ℕ+))).prod

def IdentityData.delta (D : IdentityData) : ℕ+ := D.denominator ^ 3

def IdentityData.clearCoefficient (D : IdentityData) (q : ℚ) : ℤ :=
  q.num * ((D.denominator : ℕ) / q.den : ℕ)

/-- The one-level arithmetic allowance: 4r for encoding, 2r for decoding, 1 for division. -/
def IdentityData.levelAllowance (D : IdentityData) : ℕ := 6 * D.r + 1

/-- The block order is row-major, with scalar entries row-major inside each block. -/
def blockRegisters (regs : List ℕ) (v s row col : ℕ) : List ℕ :=
  (List.range (v ^ 2)).map (fun a =>
    regs[((a / v * s + row) * (v * s) + (a % v * s + col))]?.getD 0)

def IdentityData.encodeBlock (D : IdentityData) (left : Bool) (ν s : ℕ)
    (regs : List ℕ) : IntegerBuilder (List ℕ) :=
  (List.range (s ^ 2)).mapM (fun entry =>
    compileLinearForm
      ((List.range (D.v ^ 2)).map (fun a => D.clearCoefficient
        (if left then D.leftCoeff ν a else D.rightCoeff ν a)))
      (blockRegisters regs D.v s (entry / s) (entry % s)))

/-- Scalar base case, then r recursively computed ordered products of encoded blocks. -/
def IdentityData.compilePower (D : IdentityData) :
    ℕ → List ℕ → List ℕ → IntegerBuilder (List ℕ)
  | 0, A, B => do
      let c ← emitIntegerGate (.mul (A[0]?.getD 0) (B[0]?.getD 0))
      return [c]
  | j + 1, A, B => do
      let s := D.v ^ j
      let products ← (List.range D.r).mapM (fun ν => do
        let x ← D.encodeBlock true ν s A
        let y ← D.encodeBlock false ν s B
        D.compilePower j x y)
      (List.range ((D.v * s) ^ 2)).mapM (fun entry => do
        let row := entry / (D.v * s)
        let col := entry % (D.v * s)
        let out := row / s * D.v + col / s
        let regs := products.map (fun z => z[(row % s) * s + col % s]?.getD 0)
        let z ← compileLinearForm
          ((List.range D.r).map (fun ν => D.clearCoefficient (D.outputCoeff out ν))) regs
        emitIntegerGate (.exactDiv z D.delta))

/-- Computable next-power padding; n=1 has depth zero. -/
def IdentityData.paddingDepth (D : IdentityData) (n : ℕ) : ℕ := Nat.clog D.v (max 1 n)

def IdentityData.paddedSide (D : IdentityData) (n : ℕ) : ℕ := D.v ^ D.paddingDepth n

/-- One compiler, fixed before n and the input values; constants/input copies/cropping are free. -/
def IdentityData.compile (D : IdentityData) (n : ℕ) : IntegerProgram := Id.run do
  let N := D.paddedSide n
  let builder : IntegerBuilder (List ℕ) := do
    let A ← (List.range (N ^ 2)).mapM (fun x => emitIntegerGate (.input false (x / N) (x % N)))
    let B ← (List.range (N ^ 2)).mapM (fun x => emitIntegerGate (.input true (x / N) (x % N)))
    let C ← D.compilePower (D.paddingDepth n) A B
    return (List.range (n ^ 2)).map (fun x => C[(x / n) * N + x % n]?.getD 0)
  let (outputs, gates) := builder.run []
  return ⟨gates, outputs⟩

/-- b=0 in this unit-cost model: padding/cropping emit no arithmetic instructions. -/
noncomputable def IdentityData.boundConstant (D : IdentityData) (α : ℝ) : ℝ :=
  (D.v : ℝ) ^ α * (1 + (D.levelAllowance : ℝ) / (1 - (D.r : ℝ) / (D.v : ℝ) ^ α))

/-- For use in supporting compiler theorems, distinct from the definition of the compiler. -/
def IdentityData.RunsCorrectly (D : IdentityData) (n : ℕ) : Prop :=
  (D.compile n).WellFormed ∧
  ∀ (A B : Matrix (Fin n) (Fin n) ℤ),
    (D.compile n).execute (integerInputs A B) =
      some (serializeMatrix (A * B), (D.compile n).cost)

end PolynomialPackingMM.IntegerRecursion



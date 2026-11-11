-- Prove2me | Definitions.Def_LiuHelsenDesigns_OneD_designs
-- name    : LiuHelsenDesigns_OneD_designs
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T11:06:30.930197+00:00
-- url     : https://prove2.me/theorems/f4e69140-eec1-4cd6-8894-f855db107a10
-- title:
--   Relative CP order, Haar moments and effective finite sampling
-- statement:
--   Let $\nu$ be a probability law on the full unitary group, represented in the ambient complex matrix space, and let $H$ denote normalized Haar measure on that group. For order $k$, the twirl averages conjugation by $U^{\otimes k}$. Complete positivity is positivity at every finite ancillary amplification.
--
--   $$(1-\varepsilon)\Phi_H^{(k)}\preceq\Phi_\nu^{(k)}\preceq(1+\varepsilon)\Phi_H^{(k)},\qquad g(\nu,k)=\|M_k(\nu)-M_k(H)\|_{2\to2}.$$
--
--   A finite sampling list carries uniform index weights, including repeated circuits. A terminating partial-recursive program returns its natural-number encoding on integer size, order and precision inputs; real precision selects the ceiling of its binary logarithm. These definitions impose no design or gap certificate on the sampler.
-- source:
--   Guoding Liu, Jonas Helsen, STOC 2027 submission #221 (October 2026), pp.10–11, Definitions 2–3, Eqs.(7)–(18); pp.3–5, Theorem 1. https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/221.pdf

import Definitions.Def_LiuHelsenDesigns_OneD_circuits
import Definitions.Def_ConstGapCircuits_compactGroups

noncomputable section
open MeasureTheory
open scoped Matrix ComplexConjugate Matrix.Norms.Elementwise ComplexOrder

namespace LiuHelsenDesigns.OneD
attribute [local instance] Classical.propDecidable Classical.decEq

abbrev Unitary (n : ℕ) := Matrix.unitaryGroup (Basis n) ℂ
instance unitaryContinuousInv (n : ℕ) : ContinuousInv (Unitary n) where
  continuous_inv := continuous_induced_rng.mpr continuous_subtype_val.star
instance unitaryTopologicalGroup (n : ℕ) : IsTopologicalGroup (Unitary n) where
instance unitaryMeasurable (n : ℕ) : MeasurableSpace (Unitary n) := borel _
instance unitaryBorel (n : ℕ) : BorelSpace (Unitary n) := ⟨rfl⟩
instance unitaryCompact (n : ℕ) : CompactSpace (Unitary n) := by
  open scoped Matrix.Norms.Elementwise in
  apply isCompact_iff_compactSpace.mp
  have hc : IsClosed (Matrix.unitaryGroup (Basis n) ℂ : Set (Mat n)) := by
    change IsClosed {A : Mat n | Aᴴ * A = 1 ∧ A * Aᴴ = 1}
    exact (isClosed_eq (continuous_id.matrix_conjTranspose.matrix_mul continuous_id)
      continuous_const).inter
      (isClosed_eq (continuous_id.matrix_mul continuous_id.matrix_conjTranspose) continuous_const)
  apply (isCompact_closedBall (0 : Mat n) 1).of_isClosed_subset hc
  intro U hU
  simpa [Metric.mem_closedBall, dist_zero_right] using entrywise_sup_norm_bound_of_unitary hU

instance matrixMeasurable (n : ℕ) : MeasurableSpace (Mat n) := borel _
instance matrixBorel (n : ℕ) : BorelSpace (Mat n) := ⟨rfl⟩

def haar (n : ℕ) : Measure (Mat n) :=
  (ConstGapCircuits.haarProbability (G := Unitary n)).map Subtype.val

def IsUnitaryLaw {n : ℕ} (ν : Measure (Mat n)) : Prop :=
  IsProbabilityMeasure ν ∧ ∀ᵐ U ∂ν, U ∈ Matrix.unitaryGroup (Basis n) ℂ

abbrev Copies (n k : ℕ) := Fin k → Basis n
abbrev CopyMat (n k : ℕ) := Matrix (Copies n k) (Copies n k) ℂ

def tensorPower {I : Type} [Fintype I] (U : Matrix I I ℂ) (k : ℕ) :
    Matrix (Fin k → I) (Fin k → I) ℂ := fun x y => ∏ i, U (x i) (y i)

def twirl {n : ℕ} (ν : Measure (Mat n)) (k : ℕ) (X : CopyMat n k) : CopyMat n k :=
  ∫ U, tensorPower U k * X * (tensorPower U k)ᴴ ∂ν

def amplify {I : Type} (r : ℕ) (Φ : Matrix I I ℂ → Matrix I I ℂ)
    (X : Matrix (Fin r × I) (Fin r × I) ℂ) : Matrix (Fin r × I) (Fin r × I) ℂ :=
  fun x y => Φ (fun i j => X (x.1,i) (y.1,j)) x.2 y.2

/-- Complete positivity tests every finite-dimensional ancillary amplification. -/
def CompletelyPositive {I : Type} [Fintype I] (Φ : Matrix I I ℂ → Matrix I I ℂ) : Prop :=
  ∀ r : ℕ, ∀ X : Matrix (Fin r × I) (Fin r × I) ℂ,
    X.PosSemidef → (amplify r Φ X).PosSemidef

def RelativeDesign {n : ℕ} (ν : Measure (Mat n)) (k : ℕ) (ε : ℝ) : Prop :=
  IsUnitaryLaw ν ∧
  CompletelyPositive (fun X => twirl ν k X - ((1-ε : ℝ) : ℂ) • twirl (haar n) k X) ∧
  CompletelyPositive (fun X => ((1+ε : ℝ) : ℂ) • twirl (haar n) k X - twirl ν k X)

def circuitLaw (n : ℕ) (cs : List Circuit) : Measure (Mat n) :=
  (ENNReal.ofReal (1 / (cs.length : ℝ))) •
    (cs.map fun C => Measure.dirac (circuitMatrix n C)).sum

def moment {n : ℕ} (ν : Measure (Mat n)) (k : ℕ) :
    Matrix (Copies n k × Copies n k) (Copies n k × Copies n k) ℂ :=
  ∫ U, fun x y => tensorPower U k x.1 y.1 * conj (tensorPower U k x.2 y.2) ∂ν

def matrixNorm {I : Type} [Fintype I] [DecidableEq I] (X : Matrix I I ℂ) : ℝ :=
  ‖Matrix.toEuclideanCLM (𝕜 := ℂ) X‖

def essentialNorm {n : ℕ} (ν : Measure (Mat n)) (k : ℕ) : ℝ :=
  matrixNorm (moment ν k - moment (haar n) k)

def powerLaw {n : ℕ} (ν : Measure (Mat n)) : ℕ → Measure (Mat n)
  | 0 => Measure.dirac 1
  | r+1 => (ν.prod (powerLaw ν r)).map (fun p => p.1 * p.2)

def precision (ε : ℝ) : ℕ := ⌈Real.logb 2 (1/ε)⌉₊

/-- A program halts with a natural encoding of its finite sampling list. -/
def ProgramOutputs (code : Nat.Partrec.Code) (n k p : ℕ) (cs : List Circuit) : Prop :=
  ∃ out : ℕ, code.eval (Nat.pair n (Nat.pair k p)) = Part.some out ∧
    Encodable.decode (α := List Circuit) out = some cs

end LiuHelsenDesigns.OneD



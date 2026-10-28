-- Prove2me | Definitions.Def_OAIQ039C012
-- name    : OAIQ039C012
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-28T06:13:04.673474+00:00
-- url     : https://prove2.me/theorems/8b11895e-022e-42de-ad95-42db522b2107
-- title:
--   Definitions bundle OAIQ039C012 of the split of OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.Kadison.uniform_commutator`, carved from OpenAI's openai/math development (OpenAI, *Kadison's similarity theorem through uniform derivation estimates (result family 288)*, OpenAI Math Release, September 23, 2026, result family 288, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 25 declarations of OpenAI's Lean: 10 definitions and 15 theorems. The definitions and types are `OAI.Kadison.HilbertPadding.extend`, `OAI.Kadison.HilbertPadding.padMatrix`, `OAI.Kadison.IntertwinerCompression.transfer`, `OAI.Kadison.Kaplansky.instDecidableEqFinOfNatNat_solutions_1`, `OAI.Kadison.MatrixAlphabet.letter`, `OAI.Kadison.MatrixAlphabet.normalizedLetter`, `OAI.Kadison.MatrixAlphabet.scale`, `OAI.Kadison.MatrixExpectation.expectation`, `OAI.Kadison.ScalarUltralimit.limit`, `OAI.Kadison.SpectralPartition.splitPiece`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis/Commutator, in whole or in part: `Commutator_HermitianAlphabet`, `Commutator_HilbertPadding`, `Commutator_InfiniteReindex`, `Commutator_IntertwinerCompression`, `Commutator_KaplanskyFullRange`, `Commutator_MatrixExpectation`, `Commutator_MatrixPadding`, `Commutator_ProjectionPartition`, `Commutator_ProjectionRounding`, `Commutator_ScalarUltralimit`, `Commutator_SelfAdjointSpectral`, `Commutator_SpectralCutoff`, `Commutator_TracialSequenceTrace`, `Commutator_UltrafilterDiagonal`.
--
--   **Imports.** It imports no bundle or statement, only Mathlib.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ039C027`, `OAIQ039C028` and `OAIQ039C037`; the statements `OAI.Kadison.HilbertPadding.amplified_extension_commutator_norm`, `OAI.Kadison.HilbertPadding.matrix_padding_commutator_norm`, `OAI.Kadison.HilbertPadding.norm_extend_commutator`, `OAI.Kadison.HilbertPadding.norm_padMatrix_le`, `OAI.Kadison.IntertwinerCompression.pullback_matrix_commutator_norm_le`, `OAI.Kadison.IntertwinerCompression.seminorm_le`, `OAI.Kadison.IrreducibleTowerAveraging.expectation_tendsto`, `OAI.Kadison.LocalQuantization.exists_small_projection` and `OAI.Kadison.MatrixTower.scalar_of_commutes`; the proofs of `OAI_Kadison_Decomposable_uniform_commutator_in_factor_model`, `OAI.Kadison.HilbertPadding.norm_extend_commutator`, `OAI.Kadison.HilbertPadding.norm_padMatrix_le`, `OAI.Kadison.IntertwinerCompression.pullback_matrix_commutator_norm_le`, `OAI.Kadison.IntertwinerCompression.seminorm_le`, `OAI.Kadison.LocalQuantization.exists_centered_compression` and `OAI_Kadison_OrbitStateHull_hull_normal`.
-- source:
--   OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 288; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Kadisons-similarity-theorem-through-uniform-derivation-estimates-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis/Commutator at commit adc7f12

import Mathlib

section
-- module Solutions.OAIQ039_CM.Commutator_HermitianAlphabet
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ComplexOrder InnerProductSpace
open Complex ContinuousLinearMap UniformSpace Completion
open scoped InnerProductSpace
open scoped TensorProduct
open scoped TensorProduct InnerProductSpace Topology
open UniformSpace Completion Filter
open scoped TensorProduct
open UniformSpace Completion
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder

namespace Kadison.MatrixAlphabet

open Matrix

variable {I : Type*} [Fintype I] [DecidableEq I]

def letter (o i : I) : Matrix I I ℂ := single o i 1 + single i o 1

omit [Fintype I] in
@[simp] lemma star_letter (o i : I) : star (letter o i) = letter o i := by
  simp only [letter, star_add, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_single,
    star_one, add_comm]

noncomputable def scale : ℂ := (Real.sqrt ((Fintype.card I : ℝ) / 2) : ℂ)

omit [DecidableEq I] in
@[simp] lemma star_scale : star (scale (I := I)) = scale (I := I) := by
  simp [scale]

noncomputable def normalizedLetter (o i : I) : Matrix I I ℂ := scale (I := I) • letter o i

@[simp] lemma star_normalizedLetter (o i : I) :
    star (normalizedLetter o i) = normalizedLetter o i := by
  simp only [normalizedLetter, star_smul, star_scale, star_letter]

end Kadison.MatrixAlphabet
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_HilbertPadding
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped BigOperators InnerProductSpace

open ContinuousLinearMap

namespace Kadison.HilbertPadding

variable {H K : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

def extend (E : H →ₗᵢ[ℂ] K) (T : H →L[ℂ] H) : K →L[ℂ] K :=
  (E.toContinuousLinearMap.comp T).comp E.toContinuousLinearMap.adjoint

end Kadison.HilbertPadding

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_InfiniteReindex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped Topology InnerProductSpace ENNReal

namespace Kadison.InfiniteAmplification

variable {ι κ : Type*}

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

omit [InnerProductSpace ℂ H] [CompleteSpace H] in
lemma extend_sq (e : ι ↪ κ) (x : ι → H) (k : κ) :
    ‖Function.extend e x 0 k‖^2=Function.extend e (fun i => ‖x i‖^2) 0 k := by
  classical
  by_cases hk : k∈Set.range e
  · obtain ⟨i,rfl⟩ := hk
    simp only [e.injective.extend_apply]
  · rw [Function.extend_apply' _ _ _ hk,Function.extend_apply' _ _ _ hk]
    simp

end Kadison.InfiniteAmplification

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_IntertwinerCompression
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

attribute [-instance] NonUnitalStarSubalgebra.nonUnitalCStarAlgebra

open scoped InnerProductSpace ComplexOrder

open ContinuousLinearMap

namespace Kadison.IntertwinerCompression

variable {H G : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]

variable {A : Type*} [CStarAlgebra A]

variable (φ : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (ψ : A →⋆ₐ[ℂ] (G →L[ℂ] G))

variable (T : H →L[ℂ] G) (hT : ∀ a,T.comp (φ a)=(ψ a).comp T)

def transfer (Y : H →L[ℂ] H) : G →L[ℂ] G := T.comp (Y.comp T.adjoint)

end Kadison.IntertwinerCompression

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_KaplanskyFullRange
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped BigOperators InnerProductSpace Topology

open Filter

namespace Kadison.Kaplansky

variable {A H : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

local instance instDecidableEqFinOfNatNat_solutions_1 : DecidableEq (Fin 2) := Classical.decEq (Fin 2)

end Kadison.Kaplansky

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_MatrixExpectation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped ComplexOrder BigOperators InnerProductSpace

namespace Kadison.MatrixExpectation

open Matrix

variable {A I : Type*} [CStarAlgebra A] [Fintype I] [DecidableEq I]

variable (φ : Matrix I I ℂ →⋆ₐ[ℂ] A)

def expectation : A →ₗ[ℂ] A :=
  (Fintype.card I:ℂ)⁻¹ • ∑ i,∑ j,
    (LinearMap.mulLeft ℂ (φ (single i j 1))).comp (LinearMap.mulRight ℂ (φ (single j i 1)))

end Kadison.MatrixExpectation

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_MatrixPadding
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped BigOperators InnerProductSpace

open ContinuousLinearMap

namespace Kadison.HilbertPadding

variable {A H : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (ι κ : Type*) [Fintype ι] [Fintype κ]

local instance matrixPaddingSourceDecidableEq_rccbcf6_1 : DecidableEq ι := Classical.decEq ι
local instance matrixPaddingComplementDecidableEq_rccbcf6_1 : DecidableEq κ := Classical.decEq κ
def padMatrix : CStarMatrix ι ι A →⋆ₙₐ[ℂ] CStarMatrix (ι⊕κ) (ι⊕κ) A where
  toFun X := CStarMatrix.ofMatrix (Matrix.fromBlocks (fun i j => X i j) 0 0 0)
  map_zero' := by ext i j; cases i <;> cases j <;> simp [Matrix.fromBlocks]
  map_add' X Y := by ext i j; cases i <;> cases j <;> simp [Matrix.fromBlocks]
  map_smul' z X := by ext i j; cases i <;> cases j <;> simp [Matrix.fromBlocks]
  map_mul' X Y := by
    ext i j
    cases i <;> cases j <;>
      simp [CStarMatrix.mul_apply,Fintype.sum_sum_type,Matrix.fromBlocks]
  map_star' X := by
    ext i j
    cases i <;> cases j <;> simp [CStarMatrix.star_apply,Matrix.fromBlocks]

end Kadison.HilbertPadding

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_ProjectionPartition
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped BigOperators

namespace Kadison.SpectralPartition

variable {R : Type*} [Ring R] [StarRing R]

def splitPiece (p : R) (b : Bool) : R := if b then p else 1-p

omit [StarRing R] in
lemma splitPiece_commute {p a : R} (h : Commute a p) (b : Bool) :
    Commute a (splitPiece p b) := by
  cases b
  · exact (Commute.one_right a).sub_right h
  · exact h

omit [StarRing R] in
lemma splitPiece_sum (p : R) : (∑ b : Bool,splitPiece p b)=1 := by
  simp [splitPiece]

end Kadison.SpectralPartition

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_ScalarUltralimit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped Topology InnerProductSpace BoundedContinuousFunction

open Filter

namespace Kadison.ScalarUltralimit

variable {ι : Type*}

lemma exists_limit (ω : Ultrafilter ι) (f : ι → ℂ) (C : ℝ)
    (hf : ∀ i, ‖f i‖≤C) : ∃ z : ℂ, ‖z‖≤C ∧ Tendsto f (ω : Filter ι) (𝓝 z) := by
  obtain ⟨z,hz,hl⟩ := (isCompact_closedBall (0 : ℂ) C).ultrafilter_le_nhds
    (ω.map f) (by
      rw [Ultrafilter.coe_map,Filter.map_le_iff_le_comap,Filter.comap_principal]
      exact Filter.le_principal_iff.mpr (Filter.Eventually.of_forall (fun i => by
        simpa only [Metric.mem_closedBall,dist_zero_right] using hf i)))
  exact ⟨z,by simpa only [Metric.mem_closedBall,dist_zero_right] using hz,hl⟩

def limit (ω : Ultrafilter ι) (f : ι → ℂ) (hf : ∃ C : ℝ, ∀ i, ‖f i‖≤C) : ℂ :=
  (exists_limit ω f hf.choose hf.choose_spec).choose

lemma tendsto_limit (ω : Ultrafilter ι) (f : ι → ℂ) (hf : ∃ C : ℝ, ∀ i, ‖f i‖≤C) :
    Tendsto f (ω : Filter ι) (𝓝 (limit ω f hf)) :=
  (exists_limit ω f hf.choose hf.choose_spec).choose_spec.2

end Kadison.ScalarUltralimit

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_TracialSequenceTrace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped Topology InnerProductSpace BoundedContinuousFunction ComplexOrder

open Filter UniformSpace Completion

namespace Kadison

namespace VectorFunctional

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

omit [CompleteSpace H] in
lemma continuous_functional_wot (x : H) :
    Continuous (fun T : H →WOT[ℂ] H => inner ℂ x (T x)) :=
  ContinuousLinearMapWOT.continuous_dual_apply x (innerSL ℂ x)

end VectorFunctional

end Kadison

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_ProjectionRounding
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped ComplexOrder InnerProductSpace Topology BigOperators

namespace Kadison.ProjectionSum

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable {I : Type*} [Fintype I]

omit [PartialOrder A] [StarOrderedRing A] in
lemma projection_sum (p : I → A) (hp : ∀ i,IsStarProjection (p i))
    (ho : ∀ i j,i≠j → p i*p j=0) : IsStarProjection (∑ i,p i) := by
  classical
  constructor
  · change (∑ i,p i)*(∑ i,p i)=∑ i,p i
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.mul_sum,Finset.sum_eq_single i]
    · exact (hp i).isIdempotentElem.eq
    · intro j hj hji; exact ho i j hji.symm
    · simp
  · change star (∑ i,p i)=∑ i,p i
    simp only [star_sum]
    exact Finset.sum_congr rfl (fun i _ => (hp i).isSelfAdjoint.star_eq)

lemma subprojections_orthogonal {p q e f : A}
    (hp : IsStarProjection p) (hq : IsStarProjection q)
    (he : IsStarProjection e) (hf : IsStarProjection f)
    (hpe : p≤e) (hqf : q≤f) (hef : e*f=0) : p*q=0 := by
  have hb := (hp.le_iff_mul_eq_left he).mp hpe
  have hc := (hq.le_iff_mul_eq_right hf).mp hqf
  calc
    p*q=(p*e)*(f*q) := by rw [hb,hc]
    _=p*(e*f)*q := by simp only [mul_assoc]
    _=0 := by rw [hef,mul_zero,zero_mul]

lemma projection_sum_le (p q : I → A) (h : ∀ i,p i≤q i) : ∑ i,p i≤∑ i,q i :=
  Finset.sum_le_sum (fun i _ => h i)

end Kadison.ProjectionSum

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_SpectralCutoff
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped InnerProductSpace ComplexOrder Topology

namespace Kadison.Polar

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

lemma posPart_mem (M : VonNeumannAlgebra H) {T : H →L[ℂ] H} (hT : T∈M) : T⁺∈M := by
  change T⁺∈M.carrier
  rw [←M.centralizer_centralizer']
  intro B hB
  exact ((show Commute T B from hB T hT).cfcₙ_real (·⁺)).eq.symm

end Kadison.Polar

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_SelfAdjointSpectral
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped ComplexOrder BigOperators

namespace Kadison.Polar

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

lemma normalized_positive_general {A : Type*} [CStarAlgebra A] [PartialOrder A]
    [StarOrderedRing A] {T : A} (hT : IsSelfAdjoint T) :
    0≤(2*‖T‖+1)⁻¹ • (T+‖T‖ • (1 : A)) ∧
    (2*‖T‖+1)⁻¹ • (T+‖T‖ • (1 : A))≤1 := by
  have hn : 0<2*‖T‖+1 := by positivity
  have hlo : -(‖T‖ • (1 : A))≤T := by
    simpa only [Algebra.algebraMap_eq_smul_one] using hT.neg_algebraMap_norm_le_self
  have hhi : T≤‖T‖ • (1 : A) := by
    simpa only [Algebra.algebraMap_eq_smul_one] using hT.le_algebraMap_norm_self
  have hpos : 0≤T+‖T‖ • (1 : A) := by
    simpa only [neg_add_cancel] using _root_.add_le_add_left hlo (‖T‖ • (1 : A))
  refine ⟨smul_nonneg (inv_nonneg.mpr hn.le) hpos,?_⟩
  have hbound : T+‖T‖ • (1 : A)≤(2*‖T‖+1) • (1 : A) := by
    calc
      T+‖T‖ • (1 : A)≤‖T‖ • (1 : A)+‖T‖ • (1 : A) := _root_.add_le_add_left hhi _
      _=(2*‖T‖) • (1 : A) := by module
      _≤(2*‖T‖+1) • (1 : A) := smul_le_smul_of_nonneg_right (by linarith) zero_le_one
  have h := smul_le_smul_of_nonneg_left hbound (inv_nonneg.mpr hn.le)
  simpa only [smul_smul,inv_mul_cancel₀ hn.ne',one_smul] using h

end Kadison.Polar

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_UltrafilterDiagonal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped Topology

open Filter

namespace Kadison.UltrafilterDiagonal

theorem depth {l : Filter ℕ} (hl : l≤atTop) (p : ℕ → ℕ → Prop)
    (hp : ∀ n, ∀ᶠ i in l, p n i) :
    ∃ d : ℕ → ℕ, Tendsto d l atTop ∧ ∀ i j, j<d i → p j i := by
  classical
  let d (i : ℕ) := Nat.findGreatest (fun n => ∀ j<n, p j i) i
  have hd (i : ℕ) : ∀ j<d i, p j i :=
    Nat.findGreatest_spec (P := fun n => ∀ j<n, p j i) (Nat.zero_le i) (by intro j hj; omega)
  refine ⟨d,?_,hd⟩
  apply tendsto_atTop.2
  intro n
  have hn : ∀ᶠ i in l, ∀ j<n, p j i := by
    simpa only [Finset.mem_range] using
      (eventually_all_finset (Finset.range n)).mpr (fun j _ => hp j)
  filter_upwards [hn,hl (eventually_ge_atTop n)] with i hi hin
  exact Nat.le_findGreatest hin hi

end Kadison.UltrafilterDiagonal

end

end
end

end OAI
end



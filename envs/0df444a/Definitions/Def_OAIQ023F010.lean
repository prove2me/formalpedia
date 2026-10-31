-- Prove2me | Definitions.Def_OAIQ023F010
-- name    : OAIQ023F010
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-30T15:57:10.739778+00:00
-- url     : https://prove2.me/theorems/b0ffaa12-7b63-47cb-9be4-a80e8fe565b8
-- title:
--   Definitions bundle OAIQ023F010 of the split of OpenAI, An algebra of infinite little finitistic dimension (result family 198)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.LittleFinitistic.Main.exists_counterexample`, carved from OpenAI's openai/math development (OpenAI, *An algebra of infinite little finitistic dimension (result family 198)*, OpenAI Math Release, September 23, 2026, result family 198, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 113 declarations of OpenAI's Lean: 42 definitions and 71 theorems. The definitions and types are `OAI.DerivedBar.Multibar.Indexed.blockDifferential`, `OAI.DerivedBar.Multibar.Indexed.decomposition`, `OAI.DerivedBar.Multibar.Indexed.explicitBlockDifferential`, `OAI.DerivedBar.Multibar.Indexed.signedAssembly`, `OAI.DerivedBar.Multibar.Indexed.signedBlockComplex`, `OAI.DerivedBar.Multibar.Indexed.signedBlockIso`, `OAI.DerivedBar.Multibar.embed`, `OAI.DerivedBar.ParityBridge.barSuffix`, `OAI.DerivedBar.ParityBridge.baseEmbed`, `OAI.DerivedBar.ParityBridge.canonicalLinear`, `OAI.DerivedBar.ParityBridge.canonicalRestrict`, `OAI.DerivedBar.ParityBridge.countObject`, `OAI.DerivedBar.ParityBridge.deshiftedCount`, `OAI.DerivedBar.ParityBridge.deshiftedCountRestriction`, `OAI.DerivedBar.ParityBridge.flatEmbedding`, `OAI.DerivedBar.ParityBridge.idealEmbed`, `OAI.DerivedBar.ParityBridge.idealSuffixEmbed`, `OAI.DerivedBar.ParityBridge.indexedPatternEmbeddingScalarModule`, `OAI.DerivedBar.ParityBridge.innerEmbedding`, `OAI.DerivedBar.ParityBridge.innerTotalEmbedding`, `OAI.DerivedBar.ParityBridge.instModuleCarrier_solutions_10`, `OAI.DerivedBar.ParityBridge.instModuleCarrier_solutions_12`, `OAI.DerivedBar.ParityBridge.instModuleCarrier_solutions_13`, `OAI.DerivedBar.ParityBridge.instModuleCarrier_solutions_9`, `OAI.DerivedBar.ParityBridge.integerCountRestrictionScalarModule`, `OAI.DerivedBar.ParityBridge.integerCountScalarModule`, `OAI.DerivedBar.ParityBridge.leadingTotalEmbedding`, `OAI.DerivedBar.ParityBridge.outerBarSuffix`, `OAI.DerivedBar.ParityBridge.outerBaseEmbed`, `OAI.DerivedBar.ParityBridge.outerCast`, `OAI.DerivedBar.ParityBridge.outerSuffixEmbed`, `OAI.DerivedBar.ParityBridge.shapeAssembly`, `OAI.DerivedBar.ParityBridge.suffixEmbed`, `OAI.DerivedBar.ParityBridge.termCast`, `OAI.DerivedBar.SquareZero.multibarAugmentedDifferential`, `OAI.DerivedBar.SquareZero.multibarCountDifferential`, `OAI.DerivedBar.SquareZero.multibarTwoSidedDifferential`, `OAI.DerivedBar.SquareZero.signEquiv`, `OAI.DerivedBar.SquareZero.twoSidedWeightComplex`, `OAI.DerivedBar.twoSidedDifferential` and 2 more.
--
--   **Sources.** They come from these modules of lean/OAI/Algebra, in whole or in part: `Finitistic_Bar_BarCoordinateNaturality`, `Finitistic_Bar_DerivedCountShift`, `Finitistic_Bar_ExplicitSignedDifferential`, `Finitistic_Bar_FlatSupportedAssembly`, `Finitistic_Bar_IndexedAssemblyComparison`, `Finitistic_Bar_IndexedPatternEmbedding`, `Finitistic_Bar_InflatedParityFaces`, `Finitistic_Bar_IntegerCountObject`, `Finitistic_Bar_IntegerCountRestriction`, `Finitistic_Bar_IntegerCountShift`, `Finitistic_Bar_LeadingBarSuffix`, `Finitistic_Bar_LeadingSuffixFaces`, `Finitistic_Bar_LeadingTotalEmbedding`, `Finitistic_Bar_MultibarBlocks`, `Finitistic_Bar_MultibarDecomposition`, `Finitistic_Bar_MultibarSigns`, `Finitistic_Bar_RecursivePrefixInclusions`, `Finitistic_Bar_RecursiveSuffixCoefficient`, `Finitistic_Bar_RecursiveSuffixEmbedding`, `Finitistic_Bar_RecursiveSuffixFaces`, `Finitistic_Bar_RecursiveSuffixTotal`, `Finitistic_Bar_SignedBlockExplicit`, `Finitistic_Bar_SignedBlockModel`, `Finitistic_Bar_SuffixNaturality`, `Finitistic_Bar_SuffixParityFaces`, `Finitistic_Bar_SupportedInnerCoordinates`, `Finitistic_Bar_TwoSided`, `Finitistic_Bar_TwoSidedWeight`, `Finitistic_Bar_Weight`, `Finitistic_Encoding_ArrowBasisIso`, `Finitistic_Rectification_SourceFiltration`, `Finitistic_Rectification_TensorArrowSum`.
--
--   **Imports.** It imports the bundles `OAIQ023F005` and `OAIQ023F006` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ023F016` and `OAIQ023F017`.
-- source:
--   OpenAI, An algebra of infinite little finitistic dimension (result family 198), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 198; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/An-algebra-of-infinite-little-finitistic-dimension-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Algebra at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ023F005
import Definitions.Def_OAIQ023F006

section
-- module Solutions.OAIQ023_Fin.Finitistic_Bar_TwoSided
attribute [-instance] _root_.OAI.DerivedBar.Multibar.patternModule _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.DerivedBar.term_finite _root_.OAI.DerivedBar.term_finiteDimensional _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instAddCommGroup _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
open scoped TensorProduct
open TensorProduct CategoryTheory
noncomputable section

namespace DerivedBar

universe u
variable (k A D N : Type u) [Field k] [Ring A] [Algebra k A] [Ring D] [Algebra k D]
  [AddCommGroup N] [Module k N] [Module A N] [IsScalarTower k A N]
variable (f : A →ₐ[k] D)

/-- The two-sided absolute bar differential after changing the free coefficient A to D. -/
def twoSidedDifferential (n : ℕ) :
    D ⊗[k] term k A N (n+1) →ₗ[D] D ⊗[k] term k A N n :=
  FreeBaseChange.map f _ _ (differential k A N (n+1))

/-- The endpoint face minus the remaining absolute bar faces, with their actual signs. -/
theorem twoSidedDifferential_tmul (n : ℕ) (d : D) (z : term k A N (n+1)) :
    twoSidedDifferential k A D N f n (d ⊗ₜ[k] z) =
      d • FreeBaseChange.coefficient f (term k A N n) z -
        d ⊗ₜ[k] differential k A N n z := by
  unfold twoSidedDifferential
  rw [FreeBaseChange.map_tmul, differential_succ_tmul k A N n 1 z,
    one_smul, map_sub, FreeBaseChange.coefficient_tmul, map_one, smul_sub,
    TensorProduct.smul_tmul', smul_eq_mul, mul_one]

theorem twoSidedDifferential_sq (n : ℕ) :
    (twoSidedDifferential k A D N f n).comp
      (twoSidedDifferential k A D N f (n+1)) = 0 := by
  unfold twoSidedDifferential
  rw [← FreeBaseChange.map_comp, differential_sq, FreeBaseChange.map_zero]

end DerivedBar

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Bar_Weight
attribute [-instance] _root_.OAI.DerivedBar.Multibar.patternModule _root_.OAI.DerivedBar.Multibar.patternTower _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.DerivedBar.term_finite _root_.OAI.DerivedBar.term_finiteDimensional _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instAddCommGroup _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
open scoped TensorProduct
open TensorProduct CategoryTheory TrivSqZeroExt
noncomputable section

namespace DerivedBar
namespace SquareZero
universe u
variable (k D X N : Type u) [Field k] [Ring D] [Algebra k D]
  [AddCommGroup X] [Module k X] [Module D X] [Module Dᵐᵒᵖ X]
  [SMulCommClass D Dᵐᵒᵖ X] [IsScalarTower k D X] [IsScalarTower k Dᵐᵒᵖ X]
  [AddCommGroup N] [Module k N]

variable {k D X N}

variable [Module (TrivSqZeroExt D X) N] [IsScalarTower k (TrivSqZeroExt D X) N]

/-- Degree-zero multiplication preserves the number of ideal factors. -/
theorem base_smul_mem {n r : ℕ} (d : D) {v : term k (TrivSqZeroExt D X) N n}
    (hv : v ∈ weight k D X N n r) :
    (inl d : (TrivSqZeroExt D X)) • v ∈ weight k D X N n r := by
  apply map_span_mem k (Algebra.lsmul k k (term k (TrivSqZeroExt D X) N n) (inl d)) _ _ _ hv
  intro v h
  cases h with
  | nil v => exact Submodule.subset_span (Word.nil _)
  | base b hb =>
    simp only [Algebra.lsmul_coe, TensorProduct.smul_tmul', smul_eq_mul,
      inl_mul_inl, weight]
    exact Submodule.subset_span (Word.base (d*b) hb)
  | ideal x hx =>
    simp only [Algebra.lsmul_coe, TensorProduct.smul_tmul', smul_eq_mul,
      inl_mul_inr, weight]
    exact Submodule.subset_span (Word.ideal (d • x) hx)

/-- Degree-one multiplication raises the count, with square-zero products vanishing. -/
theorem ideal_smul_mem (hN : ∀ (x : X) (v : N), (inr x : (TrivSqZeroExt D X)) • v = 0)
    {n r : ℕ} (x : X) {v : term k (TrivSqZeroExt D X) N n}
    (hv : v ∈ weight k D X N n r) :
    (inr x : (TrivSqZeroExt D X)) • v ∈ weight k D X N n (r+1) := by
  apply map_span_mem k (Algebra.lsmul k k (term k (TrivSqZeroExt D X) N n) (inr x)) _ _ _ hv
  intro v h
  cases h with
  | nil v =>
    simp only [Algebra.lsmul_coe, hN]

    exact Submodule.zero_mem _
  | base b hb =>
    simp only [Algebra.lsmul_coe, TensorProduct.smul_tmul', smul_eq_mul,
      inr_mul_inl, weight]
    exact Submodule.subset_span (Word.ideal (MulOpposite.op b • x) hb)
  | ideal y hy =>
    simp only [Algebra.lsmul_coe, TensorProduct.smul_tmul', smul_eq_mul,
      inr_mul_inr, TensorProduct.zero_tmul]
    exact Submodule.zero_mem _

/-- Every face of the augmented algebra bar differential preserves the X-count. -/
theorem differential_mem (hN : ∀ (x : X) (v : N), (inr x : (TrivSqZeroExt D X)) • v = 0)
    (n r : ℕ) {v : term k (TrivSqZeroExt D X) N (n+1)} (hv : v ∈ weight k D X N (n+1) r) :
    differential k (TrivSqZeroExt D X) N n v ∈ weight k D X N n r := by
  induction n generalizing r with
  | zero =>
    apply map_span_mem k ((differential k (TrivSqZeroExt D X) N 0).restrictScalars k) _ _ _ hv
    intro v h
    cases h with
    | base d h =>
      cases h with
      | nil v =>
        exact Submodule.subset_span (Word.nil _)
    | ideal x h =>
      cases h with
      | nil v =>
        simp only [LinearMap.coe_restrictScalars,
          differential_zero_tmul k (TrivSqZeroExt D X) N, hN]
        exact Submodule.zero_mem _
  | succ n ih =>
    apply map_span_mem k ((differential k (TrivSqZeroExt D X) N (n+1)).restrictScalars k) _ _ _ hv
    intro v h
    cases h with
    | base d h =>
      rw [LinearMap.coe_restrictScalars, differential_succ_tmul k (TrivSqZeroExt D X) N n]
      exact Submodule.sub_mem _ (base_smul_mem d (Submodule.subset_span h))
        (base_tmul_mem d (ih _ (Submodule.subset_span h)))
    | ideal x h =>
      rw [LinearMap.coe_restrictScalars, differential_succ_tmul k (TrivSqZeroExt D X) N n]
      exact Submodule.sub_mem _ (ideal_smul_mem hN x (Submodule.subset_span h))
        (ideal_tmul_mem x (ih _ (Submodule.subset_span h)))

end SquareZero
end DerivedBar

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Bar_TwoSidedWeight
attribute [-instance] _root_.OAI.DerivedBar.Multibar.patternModule _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.DerivedBar.term_finite _root_.OAI.DerivedBar.term_finiteDimensional _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instAddCommGroup _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
open scoped TensorProduct
open TensorProduct CategoryTheory TrivSqZeroExt
noncomputable section

namespace DerivedBar.SquareZero
universe u
variable (k D X N : Type u) [Field k] [Ring D] [Algebra k D]
  [AddCommGroup X] [Module k X] [Module D X] [Module Dᵐᵒᵖ X]
  [SMulCommClass D Dᵐᵒᵖ X] [IsScalarTower k D X] [IsScalarTower k Dᵐᵒᵖ X]
  [AddCommGroup N] [Module k N]

variable {k D X N}

/-- Projection of the leading square-zero coefficient kills an ideal letter and retains a base letter. -/
theorem coefficient_weight_mem {n r : ℕ}
    {v : term k (TrivSqZeroExt D X) N (n+1)} (hv : v ∈ weight k D X N (n+1) r) :
    FreeBaseChange.coefficient (fstHom k D X) (term k (TrivSqZeroExt D X) N n) v ∈
      twoSidedWeight k D X N n r := by
  let g := FreeBaseChange.coefficient (fstHom k D X) (term k (TrivSqZeroExt D X) N n)
  have hle : weight k D X N (n+1) r ≤
      ((twoSidedWeight k D X N n r).restrictScalars k).comap g := by
    apply Submodule.span_le.mpr
    intro z hz
    cases hz with
    | base d h =>
      exact Submodule.subset_span ⟨d, _, h, rfl⟩
    | ideal x h =>
      change (0 : D) ⊗ₜ[k] _ ∈ twoSidedWeight k D X N n _
      rw [TensorProduct.zero_tmul]
      exact Submodule.zero_mem _
  exact hle hv

variable [Module (TrivSqZeroExt D X) N] [IsScalarTower k (TrivSqZeroExt D X) N]

/-- The actual D-linear two-sided differential preserves X-count; no flatness enters the proof. -/
theorem twoSidedDifferential_mem
    (hN : ∀ (x : X) (v : N), (inr x : TrivSqZeroExt D X) • v = 0)
    (n r : ℕ) {v : D ⊗[k] term k (TrivSqZeroExt D X) N (n+1)}
    (hv : v ∈ twoSidedWeight k D X N (n+1) r) :
    twoSidedDifferential k (TrivSqZeroExt D X) D N (fstHom k D X) n v ∈
      twoSidedWeight k D X N n r := by
  have hle : twoSidedWeight k D X N (n+1) r ≤
      (twoSidedWeight k D X N n r).comap
        (twoSidedDifferential k (TrivSqZeroExt D X) D N (fstHom k D X) n) := by
    apply Submodule.span_le.mpr
    rintro v ⟨d, z, hz, rfl⟩
    change twoSidedDifferential k (TrivSqZeroExt D X) D N (fstHom k D X) n
      (d ⊗ₜ[k] z) ∈ twoSidedWeight k D X N n r
    rw [twoSidedDifferential_tmul]
    exact Submodule.sub_mem _
      (Submodule.smul_mem _ d (coefficient_weight_mem (Submodule.subset_span hz)))
      (tensor_weight_mem d (differential_mem hN n r (Submodule.subset_span hz)))
  exact hle hv

variable (k D X N)

/-- A genuine D-module chain complex for each fixed number of square-zero entries. -/
def twoSidedWeightComplex
    (hN : ∀ (x : X) (v : N), (inr x : TrivSqZeroExt D X) • v = 0) (r : ℕ) :
    ChainComplex (ModuleCat D) ℕ :=
  ChainComplex.of (fun n => ModuleCat.of D (twoSidedWeight k D X N n r))
    (fun n => ModuleCat.ofHom
      ((twoSidedDifferential k (TrivSqZeroExt D X) D N (fstHom k D X) n).restrict
        (fun v hv => twoSidedDifferential_mem hN n r hv)))
    (fun n => by
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro v
      apply Subtype.ext
      exact LinearMap.congr_fun
        (twoSidedDifferential_sq k (TrivSqZeroExt D X) D N (fstHom k D X) n) v)
end DerivedBar.SquareZero

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Bar_MultibarSigns
attribute [-instance] _root_.OAI.DerivedBar.Multibar.patternModule _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.DerivedBar.term_finite _root_.OAI.DerivedBar.term_finiteDimensional _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instAddCommGroup _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
open scoped TensorProduct
open TensorProduct TrivSqZeroExt
noncomputable section

namespace DerivedBar.SquareZero
universe u

variable (k D X N : Type u) [Field k] [Ring D] [Algebra k D]
  [AddCommGroup X] [Module k X] [Module D X] [Module Dᵐᵒᵖ X]
  [SMulCommClass D Dᵐᵒᵖ X] [IsScalarTower k D X] [IsScalarTower k Dᵐᵒᵖ X]
  [AddCommGroup N] [Module k N]

variable {k D X N}

/-- The rescaling stays inside the actual count subspace. -/
theorem signedProjection_word_mem {n r : ℕ} {v : term k (TrivSqZeroExt D X) N n}
    (hv : Word k D X N n r v) :
    signedProjection k D X N n r v ∈ weight k D X N n r := by
  induction hv with
  | nil v => exact Submodule.subset_span (Word.nil v)
  | base d h ih =>
    rw [signedProjection_base]
    exact Submodule.smul_mem _ _ (base_tmul_mem d ih)
  | ideal x h ih =>
    rw [signedProjection_ideal_succ]
    exact ideal_tmul_mem x ih

/-- The sign rescaling is its own inverse on homogeneous pure tensors. -/
theorem signedProjection_sq_word {n r : ℕ} {v : term k (TrivSqZeroExt D X) N n}
    (hv : Word k D X N n r v) :
    signedProjection k D X N n r (signedProjection k D X N n r v) = v := by
  induction hv with
  | nil v => rfl
  | @base n r v d h ih =>
    rw [signedProjection_base, map_smul, signedProjection_base, ih, smul_smul,
      sign_square, one_smul]
  | @ideal n r v x h ih =>
    rw [signedProjection_ideal_succ, signedProjection_ideal_succ, ih]

variable (k D X N)

variable {k D X N}

theorem twoSidedSignedProjection_mem {n r : ℕ}
    {v : D ⊗[k] term k (TrivSqZeroExt D X) N n}
    (hv : v ∈ twoSidedWeight k D X N n r) :
    twoSidedSignedProjection k D X N n r v ∈ twoSidedWeight k D X N n r := by
  have h : twoSidedWeight k D X N n r ≤
      (twoSidedWeight k D X N n r).comap (twoSidedSignedProjection k D X N n r) := by
    apply Submodule.span_le.mpr
    rintro w ⟨d, z, hz, rfl⟩
    exact tensor_weight_mem d (signedProjection_word_mem hz)
  exact h hv

theorem twoSidedSignedProjection_sq {n r : ℕ}
    {v : D ⊗[k] term k (TrivSqZeroExt D X) N n}
    (hv : v ∈ twoSidedWeight k D X N n r) :
    twoSidedSignedProjection k D X N n r (twoSidedSignedProjection k D X N n r v) = v := by
  have h : twoSidedWeight k D X N n r ≤
      ((twoSidedSignedProjection k D X N n r).comp
        (twoSidedSignedProjection k D X N n r) - LinearMap.id).ker := by
    apply Submodule.span_le.mpr
    rintro w ⟨d, z, hz, rfl⟩
    change d ⊗ₜ[k] signedProjection k D X N n r (signedProjection k D X N n r z) -
      d ⊗ₜ[k] z = 0
    rw [signedProjection_sq_word hz, sub_self]
  exact sub_eq_zero.mp (h hv)

variable (k D X N)

/-- Actual D-linear involution giving the manuscript's component rescaling.
This alone is not the chain comparison or the derived tensor identification. -/
def signEquiv (n r : ℕ) : twoSidedWeight k D X N n r ≃ₗ[D]
    twoSidedWeight k D X N n r where
  toLinearMap := (twoSidedSignedProjection k D X N n r).restrict
    (fun _ hv => twoSidedSignedProjection_mem hv)
  invFun v := ⟨twoSidedSignedProjection k D X N n r v, twoSidedSignedProjection_mem v.property⟩
  left_inv v := Subtype.ext (twoSidedSignedProjection_sq v.property)
  right_inv v := Subtype.ext (twoSidedSignedProjection_sq v.property)
end DerivedBar.SquareZero

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Bar_MultibarBlocks
attribute [-instance] _root_.OAI.DerivedBar.Multibar.patternModule _root_.OAI.DerivedBar.Multibar.patternTower _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.DerivedBar.term_finite _root_.OAI.DerivedBar.term_finiteDimensional _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instAddCommGroup _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
open scoped TensorProduct
open TensorProduct TrivSqZeroExt
noncomputable section

namespace DerivedBar.Multibar
universe u

variable (k D X N : Type u) [Field k] [Ring D] [Algebra k D]
  [AddCommGroup X] [Module k X] [Module D X] [Module Dᵐᵒᵖ X]
  [SMulCommClass D Dᵐᵒᵖ X] [IsScalarTower k D X] [IsScalarTower k Dᵐᵒᵖ X]
  [AddCommGroup N] [Module k N]

/-- Inclusion of each D/X tensor into the actual A bar term. -/
def embed : (p : List Bool) → patternTerm k D X N p →ₗ[k]
    DerivedBar.term k (TrivSqZeroExt D X) N p.length
  | [] => LinearMap.id
  | false :: p => TensorProduct.map (inlAlgHom k D X).toLinearMap (embed p)
  | true :: p => TensorProduct.map ((inrHom D X).restrictScalars k) (embed p)

end DerivedBar.Multibar

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Bar_BarCoordinateNaturality
attribute [-instance] _root_.OAI.DerivedBar.BimoduleTensor.twoSidedBarFunctor_additive _root_.OAI.DerivedBar.barFunctor_additive _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.DerivedBar.term_finite _root_.OAI.DerivedBar.term_finiteDimensional _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instAddCommGroup _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
open CategoryTheory TensorProduct
open scoped TensorProduct
noncomputable section
namespace DerivedBar.Multibar
universe u
variable (k D X : Type u) [Field k] [Ring D] [Algebra k D]
  [AddCommGroup X] [Module k X] [Module D X] [Module Dᵐᵒᵖ X]
  [SMulCommClass D Dᵐᵒᵖ X] [IsScalarTower k D X] [IsScalarTower k Dᵐᵒᵖ X]
variable (V W : Type u) [AddCommGroup V] [Module k V] [Module D V] [IsScalarTower k D V]
  [AddCommGroup W] [Module k W] [Module D W] [IsScalarTower k D W]

/-- The categorical free-bar differential is the supplied-scalars literal one. -/
theorem freeBarObjIso_d (n : ℕ) :
    ((barFunctor k D).obj (ModuleCat.of D V)).d (n+1) n ≫
      (freeBarObjIso k D V n).hom =
    (freeBarObjIso k D V (n+1)).hom ≫
      ModuleCat.ofHom (DerivedBar.differential k D V (n+1)) := by
  have h := BimoduleTensor.scalarModule_eq k D V
  cases h
  simp only [barFunctor, complex, ChainComplex.of_d]
  rfl

/-- The X-bar differential retains the original noncommutative bimodule actions. -/
theorem twoSidedBarObjIso_d (n : ℕ) :
    ((BimoduleTensor.twoSidedBarFunctor k D X).obj (ModuleCat.of D V)).d (n+1) n ≫
      (twoSidedBarObjIso k D X V n).hom =
    (twoSidedBarObjIso k D X V (n+1)).hom ≫
      ModuleCat.ofHom (BimoduleTensor.barDifferential k D X V n) := by
  have h := BimoduleTensor.scalarModule_eq k D V
  cases h
  simp only [BimoduleTensor.twoSidedBarFunctor, BimoduleTensor.barComplex, ChainComplex.of_d]
  rfl

/-- Scalar coherence is natural for every D-linear map of input modules. -/
theorem freeBarObjIso_map (f : V →ₗ[D] W) (n : ℕ) :
    ((barFunctor k D).map (ModuleCat.ofHom f)).f n ≫ (freeBarObjIso k D W n).hom =
    (freeBarObjIso k D V n).hom ≫ ModuleCat.ofHom (termMap k D V W f (n+1)) := by
  have hv := BimoduleTensor.scalarModule_eq k D V
  have hw := BimoduleTensor.scalarModule_eq k D W
  cases hv
  cases hw
  rfl

/-- All vertical maps of the categorical X bar become literal tensor maps. -/
theorem twoSidedBarObjIso_map (f : V →ₗ[D] W) (n : ℕ) :
    ((BimoduleTensor.twoSidedBarFunctor k D X).map (ModuleCat.ofHom f)).f n ≫
      (twoSidedBarObjIso k D X W n).hom =
    (twoSidedBarObjIso k D X V n).hom ≫ ModuleCat.ofHom
      (AlgebraTensorModule.lTensor D X ((termMap k D V W f n).restrictScalars k)) := by
  have hv := BimoduleTensor.scalarModule_eq k D V
  have hw := BimoduleTensor.scalarModule_eq k D W
  cases hv
  cases hw
  rfl
end DerivedBar.Multibar

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Bar_MultibarDecomposition
attribute [-instance] _root_.OAI.DerivedBar.Multibar.Indexed.shape_finite _root_.OAI.DerivedBar.Multibar.patternModule _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.DerivedBar.term_finite _root_.OAI.DerivedBar.term_finiteDimensional _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instAddCommGroup _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
open scoped TensorProduct DirectSum
open TensorProduct TrivSqZeroExt
noncomputable section

namespace DerivedBar.Multibar.Indexed
universe u

attribute [local instance] OAI.DerivedBar.Multibar.Indexed.instDecidableEqShape
variable (k D X N : Type u) [Field k] [Ring D] [Algebra k D]
  [AddCommGroup X] [Module k X] [Module D X] [Module Dᵐᵒᵖ X]
  [SMulCommClass D Dᵐᵒᵖ X] [IsScalarTower k D X] [IsScalarTower k Dᵐᵒᵖ X]
  [AddCommGroup N] [Module k N]

/-- Distinct patterns are separated by slotwise projections, including non-flat bimodules. -/
theorem retraction_other {n r : ℕ} (p q : Shape n r) (hpq : p ≠ q)
    (v : tensor k D X N q) : retraction k D X N p (inclusion k D X N q v) = 0 := by
  induction p with
  | nil => cases q; exact (hpq rfl).elim
  | base p ih =>
    cases q with
    | base q =>
      have h : p ≠ q := fun h => hpq (congrArg Shape.base h)
      induction v using OAI.tensorInductionOn with
      | tmul d v =>
        change d ⊗ₜ[k] retraction k D X N p (inclusion k D X N q v) = 0
        rw [ih q h, TensorProduct.tmul_zero]
      | add v w hv hw => simp only [map_add, hv, hw, add_zero]
    | ideal q =>
      induction v using OAI.tensorInductionOn with
      | tmul x v => exact TensorProduct.zero_tmul _ _
      | add v w hv hw => simp only [map_add, hv, hw, add_zero]
  | ideal p ih =>
    cases q with
    | base q =>
      induction v using OAI.tensorInductionOn with
      | tmul d v => exact TensorProduct.zero_tmul _ _
      | add v w hv hw => simp only [map_add, hv, hw, add_zero]
    | ideal q =>
      have h : p ≠ q := fun h => hpq (congrArg Shape.ideal h)
      induction v using OAI.tensorInductionOn with
      | tmul x v =>
        change x ⊗ₜ[k] retraction k D X N p (inclusion k D X N q v) = 0
        rw [ih q h, TensorProduct.tmul_zero]
      | add v w hv hw => simp only [map_add, hv, hw, add_zero]

theorem outerRetraction_other {n r : ℕ} (p q : Shape n r) (hpq : p ≠ q)
    (v : outerTensor k D X N q) :
    outerRetraction k D X N p (outerInclusion k D X N q v) = 0 := by
  induction v using OAI.tensorInductionOn with
  | tmul d v =>
    change d ⊗ₜ[k] retraction k D X N p (inclusion k D X N q v) = 0
    rw [retraction_other k D X N p q hpq, TensorProduct.tmul_zero]
  | add v w hv hw => simp only [map_add, hv, hw, add_zero]

/-- Projection onto an actual block after summation recovers the direct-sum component. -/
theorem outerRetraction_assemble (n r : ℕ) (p : Shape n r)
    (z : ⨁ p : Shape n r, outerTensor k D X N p) :
    outerRetraction k D X N p (assemble k D X N n r z) = z p := by
  have h : (outerRetraction k D X N p).comp
      ((SquareZero.twoSidedWeight k D X N n r).subtype.comp (assemble k D X N n r)) =
      DirectSum.component D (Shape n r) (outerTensor k D X N) p := by
    apply DirectSum.linearMap_ext
    intro q
    apply LinearMap.ext
    intro v
    by_cases hpq : p = q
    · subst q
      simpa only [LinearMap.comp_apply, assemble, DirectSum.toModule_lof,
        LinearMap.codRestrict_apply, Submodule.subtype_apply,
        DirectSum.component.lof_self] using
          outerRetraction_inclusion k D X N p v
    · simpa only [LinearMap.comp_apply, assemble, DirectSum.toModule_lof,
        LinearMap.codRestrict_apply, Submodule.subtype_apply,
        DirectSum.component.of, Ne.symm hpq, dite_eq_right, dite_false] using
          outerRetraction_other k D X N p q hpq v
  exact LinearMap.congr_fun h z

/-- The block direct sum is linearly isomorphic to the entire actual count submodule. -/
def decomposition (n r : ℕ) : (⨁ p : Shape n r, outerTensor k D X N p) ≃ₗ[D]
    SquareZero.twoSidedWeight k D X N n r :=
  LinearEquiv.ofBijective (assemble k D X N n r)
    ⟨by
      intro z w h
      apply DFinsupp.ext
      intro p
      rw [← outerRetraction_assemble k D X N n r p z,
        ← outerRetraction_assemble k D X N n r p w, h],
     assemble_surjective k D X N n r⟩
end DerivedBar.Multibar.Indexed

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Bar_SignedBlockModel
attribute [-instance] _root_.OAI.DerivedBar.Multibar.patternModule _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.DerivedBar.term_finite _root_.OAI.DerivedBar.term_finiteDimensional _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instAddCommGroup _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
open scoped TensorProduct DirectSum
open TensorProduct TrivSqZeroExt CategoryTheory
noncomputable section

namespace DerivedBar.Multibar.Indexed
universe u

variable (k D X N : Type u) [Field k] [Ring D] [Algebra k D]
  [AddCommGroup X] [Module k X] [Module D X] [Module Dᵐᵒᵖ X]
  [SMulCommClass D Dᵐᵒᵖ X] [IsScalarTower k D X] [IsScalarTower k Dᵐᵒᵖ X]
  [AddCommGroup N] [Module k N]

/-- Summation of genuine tensor blocks followed by the source's sign rescaling. -/
def signedAssembly (n r : ℕ) : (⨁ p : Shape n r, outerTensor k D X N p) ≃ₗ[D]
    SquareZero.twoSidedWeight k D X N n r :=
  (decomposition k D X N n r).trans (SquareZero.signEquiv k D X N n r)

variable [Module (TrivSqZeroExt D X) N] [IsScalarTower k (TrivSqZeroExt D X) N]
variable (hN : ∀ (x : X) (v : N), (inr x : TrivSqZeroExt D X) • v = 0)

/-- Transport of the actual count differential to signed tensor blocks. -/
def blockDifferential (n r : ℕ) :
    (⨁ p : Shape (n+1) r, outerTensor k D X N p) →ₗ[D]
      (⨁ p : Shape n r, outerTensor k D X N p) :=
  (signedAssembly k D X N n r).symm.toLinearMap.comp
    (((SquareZero.twoSidedWeightComplex k D X N hN r).d (n+1) n).hom.comp
      (signedAssembly k D X N (n+1) r).toLinearMap)

theorem blockDifferential_sq (n r : ℕ) :
    (blockDifferential k D X N hN n r).comp (blockDifferential k D X N hN (n+1) r) = 0 := by
  apply LinearMap.ext
  intro z
  change (signedAssembly k D X N n r).symm
    (((SquareZero.twoSidedWeightComplex k D X N hN r).d (n+1) n).hom
      (signedAssembly k D X N (n+1) r
        ((signedAssembly k D X N (n+1) r).symm
          (((SquareZero.twoSidedWeightComplex k D X N hN r).d (n+1+1) (n+1)).hom
            (signedAssembly k D X N (n+1+1) r z))))) = 0
  erw [LinearEquiv.apply_symm_apply]
  have h := LinearMap.congr_fun (ModuleCat.hom_ext_iff.mp
    ((SquareZero.twoSidedWeightComplex k D X N hN r).d_comp_d (n+1+1) (n+1) n))
      (signedAssembly k D X N (n+1+1) r z)
  change ((SquareZero.twoSidedWeightComplex k D X N hN r).d (n+1) n).hom
    (((SquareZero.twoSidedWeightComplex k D X N hN r).d (n+1+1) (n+1)).hom
      (signedAssembly k D X N (n+1+1) r z)) = 0 at h
  change (signedAssembly k D X N n r).symm _ = 0
  exact (congrArg (signedAssembly k D X N n r).symm h).trans
    (map_zero (signedAssembly k D X N n r).symm)

/-- Signed block chain model, still indexed by the full homological degree r+Σiⱼ. -/
def signedBlockComplex (r : ℕ) : ChainComplex (ModuleCat D) ℕ :=
  ChainComplex.of (fun n => ModuleCat.of D (⨁ p : Shape n r, outerTensor k D X N p))
    (fun n => ModuleCat.ofHom (blockDifferential k D X N hN n r))
    (fun n => ModuleCat.hom_ext (blockDifferential_sq k D X N hN n r))

/-- Chain isomorphism between the signed block model and the preserved count subcomplex. -/
def signedBlockIso (r : ℕ) : signedBlockComplex k D X N hN r ≅
    SquareZero.twoSidedWeightComplex k D X N hN r :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n => (signedAssembly k D X N n r).toModuleIso)
    (by
      intro i j hij
      change j+1 = i at hij
      subst i
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro v
      simp only [LinearEquiv.toModuleIso_hom, signedBlockComplex, ChainComplex.of_d]
      change ((SquareZero.twoSidedWeightComplex k D X N hN r).d (j+1) j).hom
          (signedAssembly k D X N (j+1) r v) =
        signedAssembly k D X N j r (blockDifferential k D X N hN j r v)
      exact (LinearEquiv.apply_symm_apply (signedAssembly k D X N j r) _).symm)
end DerivedBar.Multibar.Indexed

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Bar_ExplicitSignedDifferential
attribute [-instance] _root_.OAI.DerivedBar.Multibar.patternModule _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.DerivedBar.term_finite _root_.OAI.DerivedBar.term_finiteDimensional _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instAddCommGroup _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instRing
attribute [-simp] _root_.OAI.DerivedBar.Balanced.collapse_tmul _root_.OAI.DerivedBar.termMap_tmul _root_.OAI.ExternalTensor.Section4.sum_hom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
open CategoryTheory TensorProduct TrivSqZeroExt
open scoped TensorProduct
noncomputable section
namespace DerivedBar.SquareZero
universe u
variable (k D X N : Type u) [Field k] [Ring D] [Algebra k D]
  [AddCommGroup X] [Module k X] [Module D X] [Module Dᵐᵒᵖ X]
  [SMulCommClass D Dᵐᵒᵖ X] [IsScalarTower k D X] [IsScalarTower k Dᵐᵒᵖ X]
  [AddCommGroup N] [Module k N]
  [Module (TrivSqZeroExt D X) N] [IsScalarTower k (TrivSqZeroExt D X) N]
local notation "A" => TrivSqZeroExt D X

/-- Explicit bar faces with a sign change on crossing a D slot and no sign
change on crossing an X slot. This is defined independently of count transport. -/
def multibarAugmentedDifferential : (n : ℕ) → term k A N (n+1) →ₗ[k] term k A N n
  | 0 => ((action k A N).restrictScalars k).comp
      (TensorProduct.map (slotParity k D X) LinearMap.id)
  | n+1 => (((action k A (term k A N (n+1))).restrictScalars k) -
      TensorProduct.map LinearMap.id (multibarAugmentedDifferential n)).comp
        (TensorProduct.map (slotParity k D X) LinearMap.id)

@[simp] theorem multibarAugmentedDifferential_zero (a : A) (v : N) :
    multibarAugmentedDifferential k D X N 0 (a ⊗ₜ[k] v) = slotParity k D X a • v := rfl

theorem multibarAugmentedDifferential_succ (n : ℕ) (a : A) (v : term k A N (n+1)) :
    multibarAugmentedDifferential k D X N (n+1) (a ⊗ₜ[k] v) =
      slotParity k D X a • v -
        slotParity k D X a ⊗ₜ[k] multibarAugmentedDifferential k D X N n v := rfl

/-- The independent two-sided differential. The first face uses D's right
A-action by projection. All remaining faces use the explicit slot parity recursion. -/
def multibarTwoSidedDifferential (n : ℕ) :
    D ⊗[k] term k A N (n+1) →ₗ[D] D ⊗[k] term k A N n :=
  (action k D (D ⊗[k] term k A N n)).comp
    (AlgebraTensorModule.lTensor D D
      (FreeBaseChange.coefficient (fstHom k D X) (term k A N n))) -
    AlgebraTensorModule.lTensor D D (multibarAugmentedDifferential k D X N n)

/-- Literal endpoint-minus-tail formula; no signed assembly occurs in the definition. -/
theorem multibarTwoSidedDifferential_tmul (n : ℕ) (d : D) (v : term k A N (n+1)) :
    multibarTwoSidedDifferential k D X N n (d ⊗ₜ[k] v) =
      d • FreeBaseChange.coefficient (fstHom k D X) (term k A N n) v -
        d ⊗ₜ[k] multibarAugmentedDifferential k D X N n v := rfl


omit [IsScalarTower k A N] in
/-- Rescaling commutes with the D-action on each word. -/
theorem signedProjection_base_action_word {n r : ℕ} {v : term k A N n}
    (hv : Word k D X N n r v) (d : D) :
    signedProjection k D X N n r ((inl d : A) • v) =
      (inl d : A) • signedProjection k D X N n r v := by
  cases hv with
  | nil v => rfl
  | @base n r v b hv =>
    rw [TensorProduct.smul_tmul', smul_eq_mul, inl_mul_inl,
      signedProjection_base, signedProjection_base]
    have ha : (inl d : A) • ((inl b : A) ⊗ₜ[k] signedProjection k D X N n r v) =
        (inl (d*b) : A) ⊗ₜ[k] signedProjection k D X N n r v := by
      change ((inl d : A) * inl b) ⊗ₜ[k] _ = _
      rw [inl_mul_inl]
    rw [smul_comm (inl d : A) ((-1 : k)^r), ha]
  | @ideal n r v x hv =>
    rw [TensorProduct.smul_tmul', smul_eq_mul, inl_mul_inr,
      signedProjection_ideal_succ, signedProjection_ideal_succ,
      TensorProduct.smul_tmul', smul_eq_mul, inl_mul_inr]

omit [IsScalarTower k A N] in
/-- Multiplying a D slot by X removes its r inversions with the remaining X slots. -/
theorem signedProjection_ideal_action_word
    (hN : ∀ (x : X) (v : N), (inr x : TrivSqZeroExt D X) • v = (0 : N)) {n r : ℕ} {v : term k A N n}
    (hv : Word k D X N n r v) (x : X) :
    signedProjection k D X N n (r+1) ((inr x : A) • v) =
      (-1 : k)^r • ((inr x : A) • signedProjection k D X N n r v) := by
  cases hv with
  | nil v => simp [signedProjection, hN]
  | @base n r v d hv =>
    rw [TensorProduct.smul_tmul', smul_eq_mul, inr_mul_inl,
      signedProjection_ideal_succ, signedProjection_base,
      smul_comm (inr x : A) ((-1 : k)^r), smul_smul, ← mul_pow]
    simp only [neg_one_mul, neg_neg, one_pow, one_smul,
      TensorProduct.smul_tmul', smul_eq_mul, inr_mul_inl]
  | @ideal n r v y hv =>
    rw [TensorProduct.smul_tmul', smul_eq_mul, inr_mul_inr, TensorProduct.zero_tmul,
      map_zero, signedProjection_ideal_succ, TensorProduct.smul_tmul', smul_eq_mul,
      inr_mul_inr, TensorProduct.zero_tmul, smul_zero]

/-- Exact sign identity between the literal augmented faces and the ordinary bar
on every homogeneous word. The differential was defined independently above. -/
theorem multibarAugmented_sign_word
    (hN : ∀ (x : X) (v : N), (inr x : TrivSqZeroExt D X) • v = (0 : N)) (n r : ℕ) (v : term k A N (n+1))
    (hv : Word k D X N (n+1) r v) :
    multibarAugmentedDifferential k D X N n (signedProjection k D X N (n+1) r v) =
      (-1 : k)^r • signedProjection k D X N n r (differential k A N n v) := by
  induction n generalizing r with
  | zero =>
    cases hv with
    | base d hv =>
      cases hv
      simp [signedProjection, multibarAugmentedDifferential,
        slotParity_base, differential]
    | ideal x hv =>
      cases hv
      simp [signedProjection, multibarAugmentedDifferential,
        slotParity_ideal, differential, hN]
  | succ n ih =>
    cases hv with
    | @base m r v d hv =>
      rw [signedProjection_base, map_smul, multibarAugmentedDifferential_succ,
        slotParity_base, ih r v hv, differential_succ_tmul, map_sub,
        signedProjection_base_action_word k D X N hv d, signedProjection_base,
        TensorProduct.tmul_smul]
    | @ideal m r v x hv =>
      rw [signedProjection_ideal_succ, multibarAugmentedDifferential_succ,
        slotParity_ideal, ih r v hv, differential_succ_tmul, map_sub,
        signedProjection_ideal_action_word k D X N hN hv x, signedProjection_ideal_succ]
      simp only [TensorProduct.neg_tmul, TensorProduct.tmul_smul, smul_sub, smul_smul]
      rw [← pow_add, show r+1+r=2*r+1 by omega, pow_add, pow_mul]
      simp [pow_succ]
      exact _root_.neg_smul (inr x : A) (signedProjection k D X N (n+1) r v)


omit [Module A N] [IsScalarTower k A N] in
/-- The leading endpoint has the same prescribed rescaling. -/
theorem coefficient_signed_word (n r : ℕ) (v : term k A N (n+1))
    (hv : Word k D X N (n+1) r v) :
    FreeBaseChange.coefficient (fstHom k D X) (term k A N n)
        (signedProjection k D X N (n+1) r v) =
      (-1 : k)^r • twoSidedSignedProjection k D X N n r
        (FreeBaseChange.coefficient (fstHom k D X) (term k A N n) v) := by
  cases hv with
  | base d hv =>
    rw [signedProjection_base, map_smul, FreeBaseChange.coefficient_tmul,
      FreeBaseChange.coefficient_tmul]
    rfl
  | ideal x hv =>
    rw [signedProjection_ideal_succ, FreeBaseChange.coefficient_tmul,
      FreeBaseChange.coefficient_tmul]
    simp

/-- Equality of the independently defined two-sided faces and the shifted signed
ordinary bar differential, on every homogeneous pure tensor. -/
theorem multibarTwoSided_sign_word
    (hN : ∀ (x : X) (v : N), (inr x : TrivSqZeroExt D X) • v = (0 : N))
    (n r : ℕ) (d : D) (v : term k A N (n+1))
    (hv : Word k D X N (n+1) r v) :
    multibarTwoSidedDifferential k D X N n
        (twoSidedSignedProjection k D X N (n+1) r (d ⊗ₜ[k] v)) =
      (-1 : k)^r • twoSidedSignedProjection k D X N n r
        (twoSidedDifferential k A D N (fstHom k D X) n (d ⊗ₜ[k] v)) := by
  change multibarTwoSidedDifferential k D X N n
      (d ⊗ₜ[k] signedProjection k D X N (n+1) r v) = _
  rw [multibarTwoSidedDifferential_tmul, coefficient_signed_word k D X N n r v hv,
    multibarAugmented_sign_word k D X N hN n r v hv, twoSidedDifferential_tmul,
    map_sub, map_smul, smul_sub, TensorProduct.tmul_smul,
    smul_comm d ((-1 : k)^r)]
  rfl

/-- The sign comparison extends to the whole count submodule by linearity. -/
theorem multibarTwoSided_sign
    (hN : ∀ (x : X) (v : N), (inr x : TrivSqZeroExt D X) • v = (0 : N))
    (n r : ℕ) {z : D ⊗[k] term k A N (n+1)}
    (hz : z ∈ twoSidedWeight k D X N (n+1) r) :
    multibarTwoSidedDifferential k D X N n (twoSidedSignedProjection k D X N (n+1) r z) =
      (-1 : k)^r • twoSidedSignedProjection k D X N n r
        (twoSidedDifferential k A D N (fstHom k D X) n z) := by
  have h : twoSidedWeight k D X N (n+1) r ≤
      ((multibarTwoSidedDifferential k D X N n).comp
          (twoSidedSignedProjection k D X N (n+1) r) -
        (-1 : k)^r • (twoSidedSignedProjection k D X N n r).comp
          (twoSidedDifferential k A D N (fstHom k D X) n)).ker := by
    apply Submodule.span_le.mpr
    rintro z ⟨d,v,hv,rfl⟩
    exact sub_eq_zero.mpr (multibarTwoSided_sign_word k D X N hN n r d v hv)
  exact sub_eq_zero.mp (h hz)
end DerivedBar.SquareZero

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Bar_InflatedParityFaces
attribute [-instance] _root_.OAI.DerivedBar.Multibar.patternModule _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.DerivedBar.term_finite _root_.OAI.DerivedBar.term_finiteDimensional _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instAddCommGroup _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instRing
attribute [-simp] _root_.OAI.DerivedBar.termMap_tmul _root_.OAI.ExternalTensor.Section4.sum_hom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
open CategoryTheory TensorProduct TrivSqZeroExt
open scoped TensorProduct
noncomputable section
namespace DerivedBar.ParityBridge
universe u
variable (k D X N : Type u) [Field k] [Ring D] [Algebra k D]
  [AddCommGroup X] [Module k X] [Module D X] [Module Dᵐᵒᵖ X]
  [SMulCommClass D Dᵐᵒᵖ X] [IsScalarTower k D X] [IsScalarTower k Dᵐᵒᵖ X]
  [AddCommGroup N] [Module k N] [Module D N] [IsScalarTower k D N]
local notation "A" => TrivSqZeroExt D X

section Compatible
variable [Module (TrivSqZeroExt D X) N] [IsScalarTower k (TrivSqZeroExt D X) N]
variable (hbase : ∀ (d : D) (v : N), (inl d : TrivSqZeroExt D X) • v = d • v)

/-- Literal insertion of D slots into square-zero-extension slots. -/
def baseEmbed : (n : ℕ) → term k D N n →ₗ[k] term k A N n
  | 0 => LinearMap.id
  | n+1 => TensorProduct.map (inlAlgHom k D X).toLinearMap (baseEmbed n)

omit [Module D N] [IsScalarTower k D N] [Module A N] [IsScalarTower k A N] in
@[simp] theorem baseEmbed_tmul (n : ℕ) (d : D) (v : term k D N n) :
    baseEmbed k D X N (n+1) (d ⊗ₜ[k] v) = (inl d : A) ⊗ₜ[k] baseEmbed k D X N n v := rfl

include hbase in
omit [IsScalarTower k D N] [IsScalarTower k A N] in
/-- D-equivariance of insertion, including the inflated module endpoint. -/
theorem baseEmbed_smul (n : ℕ) (d : D) (v : term k D N n) :
    baseEmbed k D X N n (d • v) = (inl d : A) • baseEmbed k D X N n v := by
  cases n with
  | zero => exact (hbase d v).symm
  | succ n =>
    induction v using OAI.tensorInductionOn with
    | tmul b v =>
      change (inl (d*b) : A) ⊗ₜ[k] baseEmbed k D X N n v =
        ((inl d : A)*inl b) ⊗ₜ[k] baseEmbed k D X N n v
      rw [inl_mul_inl]
    | add v w hv hw => simp only [smul_add, map_add, hv, hw]

/-- Literal insertion of a leading X and its following D block. -/
def idealEmbed (n : ℕ) : X ⊗[k] term k D N n →ₗ[k] term k A N (n+1) :=
  TensorProduct.map ((inrHom D X).restrictScalars k) (baseEmbed k D X N n)

omit [Module D N] [IsScalarTower k D N] [Module A N] [IsScalarTower k A N] in
@[simp] theorem idealEmbed_tmul (n : ℕ) (x : X) (v : term k D N n) :
    idealEmbed k D X N n (x ⊗ₜ[k] v) = (inr x : A) ⊗ₜ[k] baseEmbed k D X N n v := rfl

end Compatible

end DerivedBar.ParityBridge

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Bar_SuffixParityFaces
attribute [-instance] _root_.OAI.DerivedBar.Multibar.patternModule _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.DerivedBar.term_finite _root_.OAI.DerivedBar.term_finiteDimensional _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instAddCommGroup _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instRing
attribute [-simp] _root_.OAI.DerivedBar.termMap_tmul _root_.OAI.ExternalTensor.Section4.sum_hom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
open CategoryTheory TensorProduct TrivSqZeroExt
open scoped TensorProduct
noncomputable section
namespace DerivedBar.ParityBridge
universe u
variable (k D X N : Type u) [Field k] [Ring D] [Algebra k D]
  [AddCommGroup X] [Module k X] [Module D X] [Module Dᵐᵒᵖ X]
  [SMulCommClass D Dᵐᵒᵖ X] [IsScalarTower k D X] [IsScalarTower k Dᵐᵒᵖ X]
  [AddCommGroup N] [Module k N]
local notation "A" => TrivSqZeroExt D X

/-- Explicit degree transport; it changes no tensor factor or action. -/
def termCast {a b : ℕ} (h : a=b) : term k A N a →ₗ[k] term k A N b := by
  subst b
  exact LinearMap.id

@[simp] theorem termCast_refl (a : ℕ) (v : term k A N a) :
    termCast k D X N (rfl : a=a) v = v := rfl

variable (M : Type u) [AddCommGroup M] [Module k M] [Module D M]
  [IsScalarTower k D M]

/-- Insert any D block before an arbitrary linear suffix, preserving its tensor order. -/
def suffixEmbed (s : ℕ) (e : M →ₗ[k] term k A N s) :
    (n : ℕ) → term k D M n →ₗ[k] term k A N (s+n)
  | 0 => e
  | n+1 => TensorProduct.map (inlAlgHom k D X).toLinearMap (suffixEmbed s e n)

omit [Module D M] [IsScalarTower k D M] in
@[simp] theorem suffixEmbed_tmul (s n : ℕ) (e : M →ₗ[k] term k A N s)
    (d : D) (v : term k D M n) :
    suffixEmbed k D X N M s e (n+1) (d ⊗ₜ[k] v) =
      (inl d : A) ⊗ₜ[k] suffixEmbed k D X N M s e n v := rfl

variable [Module (TrivSqZeroExt D X) N] [IsScalarTower k (TrivSqZeroExt D X) N]


/-- Literal X coefficient followed by any D block and any recursive suffix. -/
def idealSuffixEmbed (s n : ℕ) (e : M →ₗ[k] term k A N s) :
    X ⊗[k] term k D M n →ₗ[k] term k A N ((s+n)+1) :=
  TensorProduct.map ((inrHom D X).restrictScalars k) (suffixEmbed k D X N M s e n)

omit [Module D M] [IsScalarTower k D M] [Module A N] [IsScalarTower k A N] in
@[simp] theorem idealSuffixEmbed_tmul (s n : ℕ) (e : M →ₗ[k] term k A N s)
    (x : X) (v : term k D M n) :
    idealSuffixEmbed k D X N M s n e (x ⊗ₜ[k] v) =
      (inr x : A) ⊗ₜ[k] suffixEmbed k D X N M s e n v := rfl

end DerivedBar.ParityBridge

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Bar_LeadingSuffixFaces
attribute [-instance] _root_.OAI.DerivedBar.Multibar.patternModule _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.DerivedBar.term_finite _root_.OAI.DerivedBar.term_finiteDimensional _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instAddCommGroup _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instRing
attribute [-simp] _root_.OAI.DerivedBar.termMap_tmul _root_.OAI.ExternalTensor.Section4.sum_hom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
open CategoryTheory TensorProduct TrivSqZeroExt
open scoped TensorProduct
noncomputable section
namespace DerivedBar.ParityBridge
universe u
variable (k D X N : Type u) [Field k] [Ring D] [Algebra k D]
  [AddCommGroup X] [Module k X] [Module D X] [Module Dᵐᵒᵖ X]
  [SMulCommClass D Dᵐᵒᵖ X] [IsScalarTower k D X] [IsScalarTower k Dᵐᵒᵖ X]
  [AddCommGroup N] [Module k N]
local notation "A" => TrivSqZeroExt D X

variable (M : Type u) [AddCommGroup M] [Module k M] [Module D M]
  [IsScalarTower k D M]
variable [Module (TrivSqZeroExt D X) N] [IsScalarTower k (TrivSqZeroExt D X) N]

/-- Retain the exterior D coefficient while inserting an arbitrary suffix. -/
def outerSuffixEmbed (s n : ℕ) (e : M →ₗ[k] term k A N s) :
    D ⊗[k] term k D M n →ₗ[D] D ⊗[k] term k A N (s+n) :=
  AlgebraTensorModule.lTensor D D (suffixEmbed k D X N M s e n)

omit [Module D M] [IsScalarTower k D M] [Module A N] [IsScalarTower k A N] in
@[simp] theorem outerSuffixEmbed_tmul (s n : ℕ) (e : M →ₗ[k] term k A N s)
    (d : D) (v : term k D M n) :
    outerSuffixEmbed k D X N M s n e (d ⊗ₜ[k] v) =
      d ⊗ₜ[k] suffixEmbed k D X N M s e n v := rfl

omit [Module D M] [IsScalarTower k D M] [Module A N] [IsScalarTower k A N] in
/-- The projected leading face is exactly the original D multiplication. -/
theorem coefficient_suffixEmbed (s n : ℕ) (e : M →ₗ[k] term k A N s)
    (v : term k D M (n+1)) :
    FreeBaseChange.coefficient (fstHom k D X) (term k A N (s+n))
      (suffixEmbed k D X N M s e (n+1) v) = outerSuffixEmbed k D X N M s n e v := by
  induction v using OAI.tensorInductionOn with
  | tmul d v =>
    rw [suffixEmbed_tmul, FreeBaseChange.coefficient_tmul]
    rfl
  | add v w hv hw => simp only [map_add, hv, hw]

end DerivedBar.ParityBridge

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Bar_SuffixNaturality
attribute [-instance] _root_.OAI.DerivedBar.Multibar.patternModule _root_.OAI.DerivedBar.Multibar.patternTower _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.DerivedBar.term_finite _root_.OAI.DerivedBar.term_finiteDimensional _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instAddCommGroup _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
open CategoryTheory TensorProduct TrivSqZeroExt
open scoped TensorProduct
noncomputable section
namespace DerivedBar.ParityBridge
universe u
variable (k D X N : Type u) [Field k] [Ring D] [Algebra k D]
  [AddCommGroup X] [Module k X] [Module D X] [Module Dᵐᵒᵖ X]
  [SMulCommClass D Dᵐᵒᵖ X] [IsScalarTower k D X] [IsScalarTower k Dᵐᵒᵖ X]
  [AddCommGroup N] [Module k N]
local notation "A" => TrivSqZeroExt D X

variable (M : Type u) [AddCommGroup M] [Module k M] [Module D M]
  [IsScalarTower k D M]
variable [Module (TrivSqZeroExt D X) N] [IsScalarTower k (TrivSqZeroExt D X) N]

variable (W : Type u) [AddCommGroup W] [Module k W] [Module D W] [IsScalarTower k D W]

omit [Module A N] [IsScalarTower k A N] in
/-- Inserting D slots commutes with every actual vertical map of suffix modules. -/
theorem suffixEmbed_termMap (s n : ℕ) (e : W →ₗ[k] term k A N s)
    (f : M →ₗ[D] W) (v : term k D M n) :
    suffixEmbed k D X N W s e n (termMap k D M W f n v) =
    suffixEmbed k D X N M s (e.comp (f.restrictScalars k)) n v := by
  induction n with
  | zero => rfl
  | succ n ih =>
    induction v using OAI.tensorInductionOn with
    | tmul d v =>
      rw [termMap_tmul, suffixEmbed_tmul, suffixEmbed_tmul, ih]
    | add v w hv hw => simp only [map_add, hv, hw]

omit [Module A N] [IsScalarTower k A N] in
/-- X coefficients commute with the same vertical suffix maps. -/
theorem idealSuffixEmbed_termMap (s n : ℕ) (e : W →ₗ[k] term k A N s)
    (f : M →ₗ[D] W) (v : X ⊗[k] term k D M n) :
    idealSuffixEmbed k D X N W s n e
      (AlgebraTensorModule.lTensor D X ((termMap k D M W f n).restrictScalars k) v) =
    idealSuffixEmbed k D X N M s n (e.comp (f.restrictScalars k)) v := by
  induction v using OAI.tensorInductionOn with
  | tmul x v =>
    rw [AlgebraTensorModule.lTensor_tmul, idealSuffixEmbed_tmul, idealSuffixEmbed_tmul]
    change (inr x : A) ⊗ₜ[k] suffixEmbed k D X N W s e n (termMap k D M W f n v) = _
    rw [suffixEmbed_termMap]
  | add v w hv hw => simp only [map_add, hv, hw]

omit [Module D M] [IsScalarTower k D M] [Module A N] [IsScalarTower k A N] in
/-- Scalar totalization signs pass through the unchanged tensor prefix. -/
theorem suffixEmbed_smul_map (s n : ℕ) (a : k) (e : M →ₗ[k] term k A N s)
    (v : term k D M n) :
    suffixEmbed k D X N M s (a • e) n v = a • suffixEmbed k D X N M s e n v := by
  induction n with
  | zero => rfl
  | succ n ih =>
    induction v using OAI.tensorInductionOn with
    | tmul d v =>
      rw [suffixEmbed_tmul, suffixEmbed_tmul, ih]
      exact TensorProduct.tmul_smul _ _ _
    | add v w hv hw => simp only [map_add, hv, hw, smul_add]

end DerivedBar.ParityBridge

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Bar_RecursiveSuffixEmbedding
attribute [-instance] _root_.OAI.DerivedBar.term_finite _root_.OAI.DerivedBar.term_finiteDimensional _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instAddCommGroup _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instRing
attribute [-simp] _root_.OAI.ExternalTensor.Section4.sum_hom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
open CategoryTheory CategoryTheory.Limits TensorProduct TrivSqZeroExt
open scoped TensorProduct DirectSum
noncomputable section
namespace DerivedBar.ParityBridge
universe u
variable (k D X : Type u) [Field k] [Ring D] [Algebra k D]
  [AddCommGroup X] [Module k X] [Module D X] [Module Dᵐᵒᵖ X]
  [SMulCommClass D Dᵐᵒᵖ X] [IsScalarTower k D X] [IsScalarTower k Dᵐᵒᵖ X]
variable (N : ModuleCat.{u} D)
local notation "A" => TrivSqZeroExt D X
local notation "XB" => BimoduleTensor.twoSidedBarFunctor k D X
local notation "Z" => Functor.obj (ChainComplex.single₀ (ModuleCat D)) N
local notation "B" => (fun _ : ℕ => XB)

attribute [local instance] OAI.DerivedBar.ParityBridge.instModuleCarrier_solutions
attribute [local instance] OAI.DerivedBar.ParityBridge.instIsScalarTowerCarrier_solutions
attribute [local instance] OAI.DerivedBar.ParityBridge.instDecidableEqIndex
/-- Prefix one original categorical X bar to a linear suffix map. -/
def barSuffix (V : ModuleCat.{u} D) (s i : ℕ)
    (e : V →ₗ[k] term k A N s) :
    ((XB).obj V).X i →ₗ[k] term k A N ((s+i)+1) :=
  (idealSuffixEmbed k D X N V s i e).comp
    ((Multibar.twoSidedBarObjIso k D X V i).hom.hom.restrictScalars k)

/-- The prefix keeps the original left D action. -/
theorem barSuffix_smul (V : ModuleCat.{u} D) (s i : ℕ)
    (e : V →ₗ[k] term k A N s) (d : D) (v : ((XB).obj V).X i) :
    letI : Module A N := inflatedModule D X N
    barSuffix k D X N V s i e (d • v) =
      (inl d : A) • barSuffix k D X N V s i e v := by
  let : Module A N := inflatedModule D X N
  unfold barSuffix
  simp only [LinearMap.comp_apply, LinearMap.restrictScalars_apply, map_smul]
  generalize (Multibar.twoSidedBarObjIso k D X V i).hom.hom v = w
  induction w using OAI.tensorInductionOn with
  | tmul x w =>
    change (inr (d • x) : A) ⊗ₜ[k] _ = ((inl d : A) * inr x) ⊗ₜ[k] _
    rw [inl_mul_inr]
  | add v w hv hw => simp only [map_add, smul_add, hv, hw]

theorem barSuffix_ideal_zero (V : ModuleCat.{u} D) (s i : ℕ)
    (e : V →ₗ[k] term k A N s) (x : X) (v : ((XB).obj V).X i) :
    letI : Module A N := inflatedModule D X N
    (inr x : A) • barSuffix k D X N V s i e v = 0 := by
  let : Module A N := inflatedModule D X N
  unfold barSuffix
  simp only [LinearMap.comp_apply, LinearMap.restrictScalars_apply]
  generalize (Multibar.twoSidedBarObjIso k D X V i).hom.hom v = w
  induction w using OAI.tensorInductionOn with
  | tmul y w =>
    change ((inr x : A) * inr y) ⊗ₜ[k] _ = 0
    rw [inr_mul_inr, TensorProduct.zero_tmul]
  | add v w hv hw => simp only [map_add, smul_add, hv, hw, add_zero]

/-- Naturality uses the original bar functor, including its supplied scalar coherence. -/
theorem barSuffix_map (V W : ModuleCat.{u} D) (s i : ℕ)
    (e : W →ₗ[k] term k A N s) (f : V ⟶ W) (v : ((XB).obj V).X i) :
    barSuffix k D X N W s i e ((((XB).map f).f i).hom v) =
      barSuffix k D X N V s i (e.comp (f.hom.restrictScalars k)) v := by
  have h := congrArg (fun g => g.hom v)
    (Multibar.twoSidedBarObjIso_map k D X V W f.hom i)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_ofHom] at h
  unfold barSuffix
  simp only [LinearMap.comp_apply, LinearMap.restrictScalars_apply]
  erw [h]
  let : Module A N := inflatedModule D X N
  let : IsScalarTower k A N := IsScalarTower.of_algebraMap_smul
    (fun a v => IsScalarTower.algebraMap_smul D a v)
  exact idealSuffixEmbed_termMap k D X N V W s i e f.hom _

/-- Literal recursive suffix embedding on every summand, including zero input degrees. -/
def innerEmbedding : (r n : ℕ) →
    RecursiveTotal.flat B Z r n →ₗ[k] term k A N (r+n)
  | 0, 0 => DirectSum.toModule k _ _ (fun _ => LinearMap.id)
  | 0, n+1 => 0
  | r+1, n => DirectSum.toModule k _ _ (fun t =>
      (termCast k D X N (show ((r+t.1.val.2)+t.1.val.1)+1=(r+1)+n by
        have h := t.1.property; omega)).comp
      (barSuffix k D X N (RecursiveTotal.summand B Z r t.1.val.2 t.2)
        (r+t.1.val.2) t.1.val.1
        ((innerEmbedding r t.1.val.2).comp
          ((RecursiveTotal.lof B Z r t.1.val.2 t.2).hom.restrictScalars k))))

@[simp] theorem innerEmbedding_lof_succ (r n i q : ℕ) (h : i+q=n)
    (t : RecursiveTotal.Index r q) (v : RecursiveTotal.summand B Z (r+1) n ⟨⟨⟨i,q⟩,h⟩,t⟩) :
    innerEmbedding k D X N (r+1) n
      ((RecursiveTotal.lof B Z (r+1) n ⟨⟨⟨i,q⟩,h⟩,t⟩).hom v) =
    termCast k D X N (show ((r+q)+i)+1=(r+1)+n by omega)
      (barSuffix k D X N (RecursiveTotal.summand B Z r q t) (r+q) i
        ((innerEmbedding k D X N r q).comp
          ((RecursiveTotal.lof B Z r q t).hom.restrictScalars k)) v) := by
  simp only [innerEmbedding, RecursiveTotal.lof, ModuleCat.hom_ofHom]
  erw [DirectSum.lof_eq_of, toModule_of_scalar]
  rfl

end DerivedBar.ParityBridge

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Bar_RecursiveSuffixFaces
attribute [-instance] _root_.OAI.DerivedBar.term_finite _root_.OAI.DerivedBar.term_finiteDimensional _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instAddCommGroup _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
open CategoryTheory CategoryTheory.Limits TensorProduct TrivSqZeroExt
open scoped TensorProduct DirectSum
noncomputable section
namespace DerivedBar.ParityBridge
universe u
variable (k D X : Type u) [Field k] [Ring D] [Algebra k D]
  [AddCommGroup X] [Module k X] [Module D X] [Module Dᵐᵒᵖ X]
  [SMulCommClass D Dᵐᵒᵖ X] [IsScalarTower k D X] [IsScalarTower k Dᵐᵒᵖ X]
variable (N : ModuleCat.{u} D)
local notation "A" => TrivSqZeroExt D X
local notation "XB" => BimoduleTensor.twoSidedBarFunctor k D X

attribute [local instance] OAI.DerivedBar.ParityBridge.instModuleCarrier_solutions_1
attribute [local instance] OAI.DerivedBar.ParityBridge.instIsScalarTowerCarrier_solutions_1
local instance instDecidableEqIndex_1_r539ddc_1 (r n : ℕ) : DecidableEq (RecursiveTotal.Index r n) := Classical.decEq _
attribute [local instance] OAI.DerivedBar.ParityBridge.instModuleTrivSqZeroExtCarrier_solutions
attribute [local instance] OAI.DerivedBar.ParityBridge.instIsScalarTowerTrivSqZeroExtCarrier_solutions
/-- Prefix insertion is linear in the complete suffix map. -/
theorem barSuffix_neg (V : ModuleCat.{u} D) (s i : ℕ)
    (e : V →ₗ[k] term k A N s) :
    barSuffix k D X N V s i (-e) = -barSuffix k D X N V s i e := by
  ext v
  unfold barSuffix
  simp only [LinearMap.neg_apply, LinearMap.comp_apply, LinearMap.restrictScalars_apply]
  generalize (Multibar.twoSidedBarObjIso k D X V i).hom.hom v = w
  induction w using OAI.tensorInductionOn with
  | tmul x w =>
    change (inr x : A) ⊗ₜ[k] suffixEmbed k D X N V s (-e) i w =
      -((inr x : A) ⊗ₜ[k] suffixEmbed k D X N V s e i w)
    rw [← neg_one_smul k e, suffixEmbed_smul_map, neg_one_smul, TensorProduct.tmul_neg]
  | add v w hv hw => simp only [map_add, neg_add, hv, hw]

theorem barSuffix_zero (V : ModuleCat.{u} D) (s i : ℕ) :
    barSuffix k D X N V s i 0 = 0 := by
  ext v
  unfold barSuffix
  simp only [LinearMap.zero_apply, LinearMap.comp_apply, LinearMap.restrictScalars_apply]
  generalize (Multibar.twoSidedBarObjIso k D X V i).hom.hom v = w
  induction w using OAI.tensorInductionOn with
  | tmul x w =>
    change (inr x : A) ⊗ₜ[k] suffixEmbed k D X N V s 0 i w = 0
    have hz := suffixEmbed_smul_map k D X N V s i (0:k) (0 : V →ₗ[k] term k A N s) w
    simp only [zero_smul] at hz
    rw [hz, TensorProduct.tmul_zero]
  | add v w hv hw => simp only [map_add, hv, hw, add_zero]

/-- Prefix insertion commutes with exact degree casts on a suffix. -/
theorem barSuffix_termCast (V : ModuleCat.{u} D) {a b : ℕ} (h : a=b) (i : ℕ)
    (e : V →ₗ[k] term k A N a) (v : ((XB).obj V).X i) :
    barSuffix k D X N V b i ((termCast k D X N h).comp e) v =
      termCast k D X N (show (a+i)+1=(b+i)+1 by omega)
        (barSuffix k D X N V a i e v) := by
  subst b
  rfl

end DerivedBar.ParityBridge

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Bar_LeadingBarSuffix
attribute [-instance] _root_.OAI.DerivedBar.term_finite _root_.OAI.DerivedBar.term_finiteDimensional _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instAddCommGroup _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instRing
attribute [-simp] _root_.OAI.ExternalTensor.Section4.sum_hom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
open CategoryTheory CategoryTheory.Limits TensorProduct TrivSqZeroExt
open scoped TensorProduct DirectSum
noncomputable section
namespace DerivedBar.ParityBridge
universe u
variable (k D X : Type u) [Field k] [Ring D] [Algebra k D]
  [AddCommGroup X] [Module k X] [Module D X] [Module Dᵐᵒᵖ X]
  [SMulCommClass D Dᵐᵒᵖ X] [IsScalarTower k D X] [IsScalarTower k Dᵐᵒᵖ X]
variable (N : ModuleCat.{u} D)
local notation "A" => TrivSqZeroExt D X
local notation "DB" => barFunctor k D

attribute [local instance] OAI.DerivedBar.ParityBridge.leadingBarSuffixScalarModule
attribute [local instance] OAI.DerivedBar.ParityBridge.leadingBarSuffixScalarTower
attribute [local instance] OAI.DerivedBar.ParityBridge.leadingBarSuffixInflatedModule
attribute [local instance] OAI.DerivedBar.ParityBridge.leadingBarSuffixInflatedTower
/-- Retain the exterior D coefficient while applying an exact degree transport. -/
def outerCast {a b : ℕ} (h : a=b) :
    D ⊗[k] term k A N a →ₗ[D] D ⊗[k] term k A N b :=
  AlgebraTensorModule.lTensor D D (termCast k D X N h)

@[simp] theorem outerCast_refl (a : ℕ) : outerCast k D X N (rfl : a=a) = LinearMap.id := by
  ext value
  rfl

/-- The exterior free D bar uses its actual categorical coordinates. -/
def outerBarSuffix (V : ModuleCat.{u} D) (s i : ℕ)
    (e : V →ₗ[k] term k A N s) :
    ((DB).obj V).X i →ₗ[D] D ⊗[k] term k A N (s+i) :=
  (outerSuffixEmbed k D X N V s i e).comp (Multibar.freeBarObjIso k D V i).hom.hom

def outerBaseEmbed (i : ℕ) : D ⊗[k] term k D N i →ₗ[D] D ⊗[k] term k A N i :=
  AlgebraTensorModule.lTensor D D (baseEmbed k D X N i)

theorem coefficient_baseEmbed (i : ℕ) (v : term k D N (i+1)) :
    FreeBaseChange.coefficient (fstHom k D X) (term k A N i)
      (baseEmbed k D X N (i+1) v) = outerBaseEmbed k D X N i v := by
  induction v using OAI.tensorInductionOn with
  | tmul d v =>
    rw [baseEmbed_tmul, FreeBaseChange.coefficient_tmul]
    rfl
  | add v w hv hw => simp only [map_add, hv, hw]

end DerivedBar.ParityBridge

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Bar_RecursiveSuffixTotal
attribute [-instance] _root_.OAI.DerivedBar.term_finite _root_.OAI.DerivedBar.term_finiteDimensional _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instAddCommGroup _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
open CategoryTheory CategoryTheory.Limits TensorProduct TrivSqZeroExt
open scoped TensorProduct DirectSum
noncomputable section
namespace DerivedBar.ParityBridge
universe u
variable (k D X : Type u) [Field k] [Ring D] [Algebra k D]
  [AddCommGroup X] [Module k X] [Module D X] [Module Dᵐᵒᵖ X]
  [SMulCommClass D Dᵐᵒᵖ X] [IsScalarTower k D X] [IsScalarTower k Dᵐᵒᵖ X]
variable (N : ModuleCat.{u} D)
local notation "A" => TrivSqZeroExt D X
local notation "XB" => BimoduleTensor.twoSidedBarFunctor k D X
local notation "Z" => Functor.obj (ChainComplex.single₀ (ModuleCat D)) N
local notation "B" => (fun _ : ℕ => XB)

attribute [local instance] OAI.DerivedBar.ParityBridge.instModuleCarrier_solutions_3
attribute [local instance] OAI.DerivedBar.ParityBridge.instIsScalarTowerCarrier_solutions_3
local instance recursiveSuffixTotalIndexDecidableEq_r539ddc_1 (r n : ℕ) :
    DecidableEq (RecursiveTotal.Index r n) := Classical.decEq _
attribute [local instance] OAI.DerivedBar.ParityBridge.instModuleTrivSqZeroExtCarrier_solutions_2
attribute [local instance] OAI.DerivedBar.ParityBridge.instIsScalarTowerTrivSqZeroExtCarrier_solutions_2
/-- The same canonical embedding on the actual recursive total, through the
previously proved finite-sum flattening. -/
def innerTotalEmbedding (r n : ℕ) :
    (RecursiveTotal.iter B Z r).X n →ₗ[k] term k A N (r+n) :=
  (innerEmbedding k D X N r n).comp
    ((RecursiveTotal.flattenIso B Z r n (𝟭 _)).hom.hom.restrictScalars k)

end DerivedBar.ParityBridge

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Bar_RecursiveSuffixCoefficient
attribute [-instance] _root_.OAI.DerivedBar.term_finite _root_.OAI.DerivedBar.term_finiteDimensional _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instAddCommGroup _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instRing
attribute [-simp] _root_.OAI.DerivedBar.ParityBridge.outerCast_refl _root_.OAI.ExternalTensor.Section4.sum_hom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
open CategoryTheory CategoryTheory.Limits TensorProduct TrivSqZeroExt
open scoped TensorProduct DirectSum
noncomputable section
namespace DerivedBar.ParityBridge
universe u
variable (k D X : Type u) [Field k] [Ring D] [Algebra k D]
  [AddCommGroup X] [Module k X] [Module D X] [Module Dᵐᵒᵖ X]
  [SMulCommClass D Dᵐᵒᵖ X] [IsScalarTower k D X] [IsScalarTower k Dᵐᵒᵖ X]
variable (N : ModuleCat.{u} D)
local notation "A" => TrivSqZeroExt D X
local notation "XB" => BimoduleTensor.twoSidedBarFunctor k D X

attribute [local instance] OAI.DerivedBar.ParityBridge.instModuleCarrier_solutions_4
attribute [local instance] OAI.DerivedBar.ParityBridge.instIsScalarTowerCarrier_solutions_4
local instance recursiveSuffixCoefficientIndexDecidableEq_r539ddc_1 (r n : ℕ) :
    DecidableEq (RecursiveTotal.Index r n) := Classical.decEq _
local instance instModuleTrivSqZeroExtCarrier_solutions_3_r539ddc_1 : Module A N := inflatedModule D X N
local instance instIsScalarTowerTrivSqZeroExtCarrier_solutions_3_r539ddc_1 : IsScalarTower k A N := IsScalarTower.of_algebraMap_smul
    (fun a v => IsScalarTower.algebraMap_smul D a v)
theorem coefficient_termCast {a b : ℕ} (h : a=b) (h' : a+1=b+1)
    (v : term k A N (a+1)) :
    FreeBaseChange.coefficient (fstHom k D X) (term k A N b) (termCast k D X N h' v) =
      AlgebraTensorModule.lTensor D D (termCast k D X N h)
        (FreeBaseChange.coefficient (fstHom k D X) (term k A N a) v) := by
  subst b
  simp only [termCast, LinearMap.id_apply, AlgebraTensorModule.lTensor_id]

/-- The first X factor is killed by the exterior projection A -> D. -/
theorem barSuffix_coefficient_zero (V : ModuleCat.{u} D) (s i : ℕ)
    (e : V →ₗ[k] term k A N s) (v : ((XB).obj V).X i) :
    FreeBaseChange.coefficient (fstHom k D X) (term k A N (s+i))
      (barSuffix k D X N V s i e v) = 0 := by
  unfold barSuffix
  simp only [LinearMap.comp_apply, LinearMap.restrictScalars_apply]
  generalize (Multibar.twoSidedBarObjIso k D X V i).hom.hom v = w
  induction w using OAI.tensorInductionOn with
  | tmul x w =>
    rw [idealSuffixEmbed_tmul, FreeBaseChange.coefficient_tmul]
    simp
  | add v w hv hw => simp only [map_add, hv, hw, add_zero]

end DerivedBar.ParityBridge

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Bar_LeadingTotalEmbedding
attribute [-instance] _root_.OAI.DerivedBar.term_finite _root_.OAI.DerivedBar.term_finiteDimensional _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instAddCommGroup _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instRing
attribute [-simp] _root_.OAI.ExternalTensor.Section4.sum_hom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
open CategoryTheory CategoryTheory.Limits TensorProduct TrivSqZeroExt
open scoped TensorProduct DirectSum
noncomputable section
namespace DerivedBar.ParityBridge
universe u
variable (k D X : Type u) [Field k] [Ring D] [Algebra k D]
  [AddCommGroup X] [Module k X] [Module D X] [Module Dᵐᵒᵖ X]
  [SMulCommClass D Dᵐᵒᵖ X] [IsScalarTower k D X] [IsScalarTower k Dᵐᵒᵖ X]
variable (N : ModuleCat.{u} D)
local notation "A" => TrivSqZeroExt D X
local notation "XB" => BimoduleTensor.twoSidedBarFunctor k D X
local notation "Z" => Functor.obj (ChainComplex.single₀ (ModuleCat D)) N
local notation "B" => (fun _ : ℕ => XB)
local notation "c" => ComplexShape.down ℕ
local notation "I" => RecursiveTotal.iter B Z

attribute [local instance] OAI.DerivedBar.ParityBridge.instModuleCarrier_solutions_5
local instance instIsScalarTowerCarrier_solutions_5_r539ddc_1 (V : ModuleCat.{u} D) : IsScalarTower k D V :=
  IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
local instance instModuleTrivSqZeroExtCarrier_solutions_4_r539ddc_1 : Module A N := inflatedModule D X N
local instance instIsScalarTowerTrivSqZeroExtCarrier_solutions_4_r539ddc_1 : IsScalarTower k A N := IsScalarTower.of_algebraMap_smul
    (fun a v => IsScalarTower.algebraMap_smul D a v)
/-- The exterior D bar is assembled on its actual finite totalization diagonal. -/
def leadingTotalEmbedding (r n : ℕ) :
    (barTotal k D (I r)).X n ⟶ ModuleCat.of D (D ⊗[k] term k A N (r+n)) :=
  totalMapDesc (𝟭 _) (barBicomplex k D (I r)) (fun i q h =>
    ModuleCat.ofHom ((outerCast k D X N (show (r+q)+i=r+n by omega)).comp
      (outerBarSuffix k D X N ((I r).X q) (r+q) i (innerTotalEmbedding k D X N r q))))

@[reassoc (attr := simp)] theorem leadingTotalEmbedding_ι (r n i q : ℕ) (h : i+q=n) :
    (barBicomplex k D (I r)).ιTotal c i q n h ≫ leadingTotalEmbedding k D X N r n =
      ModuleCat.ofHom ((outerCast k D X N (show (r+q)+i=r+n by omega)).comp
        (outerBarSuffix k D X N ((I r).X q) (r+q) i (innerTotalEmbedding k D X N r q))) := by
  exact ι_totalMapDesc (𝟭 _) (barBicomplex k D (I r)) _ i q h

/-- The independently recursive inner total is the previously constructed explicit multibar. -/
theorem innerIter_eq_explicit (r : ℕ) : I r = explicitMultibar k D X r Z := by
  induction r with
  | zero => rfl
  | succ r ih =>
    simp only [RecursiveTotal.iter, RecursiveTotal.bicomplex, ih, explicitMultibar,
      BimoduleTensor.explicitBarTotal, BimoduleTensor.twoSidedBarBicomplex]
end DerivedBar.ParityBridge

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Bar_SupportedInnerCoordinates
attribute [-instance] _root_.OAI.DerivedBar.term_finite _root_.OAI.DerivedBar.term_finiteDimensional _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instAddCommGroup _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instRing
attribute [-simp] _root_.OAI.DerivedBar.ParityBridge.outerCast_refl _root_.OAI.ExternalTensor.Section4.sum_hom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

set_option backward.isDefEq.respectTransparency false

namespace OAI
open CategoryTheory CategoryTheory.Limits TensorProduct TrivSqZeroExt
open scoped TensorProduct DirectSum
noncomputable section
namespace DerivedBar.ParityBridge
open DerivedBar.Multibar DerivedBar.RecursiveTotal
universe u
variable (k D X : Type u) [Field k] [Ring D] [Algebra k D]
  [AddCommGroup X] [Module k X] [Module D X] [Module Dᵐᵒᵖ X]
  [SMulCommClass D Dᵐᵒᵖ X] [IsScalarTower k D X] [IsScalarTower k Dᵐᵒᵖ X]
variable (N : ModuleCat.{u} D)
local notation "A" => TrivSqZeroExt D X
local notation "XB" => BimoduleTensor.twoSidedBarFunctor k D X

attribute [local instance] OAI.DerivedBar.ParityBridge.supportedInnerCoordinatesScalarModule
attribute [local instance] OAI.DerivedBar.ParityBridge.supportedInnerCoordinatesScalarTower
local instance supportedInnerCoordinatesIndexDecidableEq_r539ddc_1 (r n : ℕ) :
    DecidableEq (Index r n) := Classical.decEq _
local instance supportedInnerCoordinatesInflatedModule_r539ddc_1 : Module A N := inflatedModule D X N
local instance supportedInnerCoordinatesInflatedTower_r539ddc_1 : IsScalarTower k A N :=
  IsScalarTower.of_algebraMap_smul
    (fun a v => IsScalarTower.algebraMap_smul D a v)
/-- Re-express a supplied k-linear map using the canonical scalars of ModuleCat D. -/
def canonicalLinear (V : Type u) [AddCommGroup V] [Module k V] [Module D V]
    [IsScalarTower k D V] (s : ℕ) (e : V →ₗ[k] term k A N s) :
    letI : Module k V := BimoduleTensor.scalarModule k D (ModuleCat.of D V)
    V →ₗ[k] term k A N s := by
  have h := BimoduleTensor.scalarModule_eq k D V
  cases h
  exact e

@[simp] theorem canonicalLinear_apply (V : Type u) [AddCommGroup V] [Module k V]
    [Module D V] [IsScalarTower k D V] (s : ℕ) (e : V →ₗ[k] term k A N s) (v : V) :
    canonicalLinear k D X N V s e v = e v := by
  have h := BimoduleTensor.scalarModule_eq k D V
  cases h
  rfl

/-- Prefixing a canonically re-expressed map recovers the supplied-scalars literal formula. -/
theorem barSuffix_canonicalLinear (V : Type u) [AddCommGroup V] [Module k V]
    [Module D V] [IsScalarTower k D V] (s i : ℕ) (e : V →ₗ[k] term k A N s)
    (v : ((XB).obj (ModuleCat.of D V)).X i) :
    barSuffix k D X N (ModuleCat.of D V) s i (canonicalLinear k D X N V s e) v =
      idealSuffixEmbed k D X N V s i e ((twoSidedBarObjIso k D X V i).hom.hom v) := by
  have h := BimoduleTensor.scalarModule_eq k D V
  cases h
  rfl

def canonicalRestrict (V W : ModuleCat.{u} D) (f : V ⟶ W) : V →ₗ[k] W :=
  f.hom.restrictScalars k

@[simp] theorem canonicalRestrict_apply (V W : ModuleCat.{u} D) (f : V ⟶ W) (v : V) :
    canonicalRestrict k D V W f v = f.hom v := rfl

end DerivedBar.ParityBridge

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Bar_IndexedPatternEmbedding
attribute [-instance] _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instAddCommGroup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
open CategoryTheory CategoryTheory.Limits TensorProduct TrivSqZeroExt
open scoped TensorProduct DirectSum
noncomputable section
namespace DerivedBar.ParityBridge
open DerivedBar.Multibar DerivedBar.RecursiveTotal
universe u
variable (k D X : Type u) [Field k] [Ring D] [Algebra k D]
  [AddCommGroup X] [Module k X] [Module D X] [Module Dᵐᵒᵖ X]
  [SMulCommClass D Dᵐᵒᵖ X] [IsScalarTower k D X] [IsScalarTower k Dᵐᵒᵖ X]
local instance indexedPatternEmbeddingScalarModule (V : ModuleCat.{u} D) :
    Module k V := BimoduleTensor.scalarModule k D V
end DerivedBar.ParityBridge

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Bar_RecursivePrefixInclusions
attribute [-instance] _root_.OAI.ExternalTensor.Section4.rightModuleK
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
open CategoryTheory CategoryTheory.Limits
noncomputable section
namespace DerivedBar.ParityBridge
universe u

open DerivedBar.RecursiveTotal
variable (k D X : Type u) [Field k] [Ring D] [Algebra k D]
  [AddCommGroup X] [Module k X] [Module D X] [Module Dᵐᵒᵖ X]
  [SMulCommClass D Dᵐᵒᵖ X] [IsScalarTower k D X] [IsScalarTower k Dᵐᵒᵖ X]
variable (N : ModuleCat.{u} D)
local notation "XB" => BimoduleTensor.twoSidedBarFunctor k D X
local notation "Z" => Functor.obj (ChainComplex.single₀ (ModuleCat D)) N
local notation "B" => (fun _ : ℕ => XB)

/-- The final total agrees with the actual exterior bar on the constant-X prefix. -/
theorem leadingIter_total (r : ℕ) :
    iter (leadingBarSequence k D X r) Z (r+1) = barTotal k D (iter B Z r) :=
  (leadingBarSequence_total k D X Z r).trans
    (congrArg (barTotal k D) (innerIter_eq_explicit k D X N r).symm)

end DerivedBar.ParityBridge

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Bar_FlatSupportedAssembly
attribute [-instance] _root_.OAI.DerivedBar.term_finite _root_.OAI.DerivedBar.term_finiteDimensional _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instAddCommGroup _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
open CategoryTheory CategoryTheory.Limits TensorProduct TrivSqZeroExt
open scoped TensorProduct DirectSum
noncomputable section
namespace DerivedBar.ParityBridge
open DerivedBar.Multibar DerivedBar.RecursiveTotal
universe u
variable (k D X : Type u) [Field k] [Ring D] [Algebra k D]
  [AddCommGroup X] [Module k X] [Module D X] [Module Dᵐᵒᵖ X]
  [SMulCommClass D Dᵐᵒᵖ X] [IsScalarTower k D X] [IsScalarTower k Dᵐᵒᵖ X]
local instance instModuleCarrier_solutions_9 (V : ModuleCat.{u} D) : Module k V := BimoduleTensor.scalarModule k D V
variable (N : ModuleCat.{u} D)
local notation "A" => TrivSqZeroExt D X
local notation "Z" => Functor.obj (ChainComplex.single₀ (ModuleCat D)) N

local instance instIsScalarTowerCarrier_solutions_9_r539ddc_1 (V : ModuleCat.{u} D) : IsScalarTower k D V :=
  IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
local instance instDecidableEqIndex_2_r539ddc_1 (r n : ℕ) : DecidableEq (Index r n) := Classical.decEq _
local instance instModuleTrivSqZeroExtCarrier_solutions_8_r539ddc_1 : Module A N := inflatedModule D X N
local instance instIsScalarTowerTrivSqZeroExtCarrier_solutions_8_r539ddc_1 : IsScalarTower k A N := IsScalarTower.of_algebraMap_smul
    (fun a v => IsScalarTower.algebraMap_smul D a v)
def flatEmbedding (r n : ℕ) : flat (leadingBarSequence k D X r) Z (r+1) n ⟶
    ModuleCat.of D (D ⊗[k] term k A N (r+n)) :=
  assemble (leadingBarSequence k D X r) Z (r+1) n ≫
    eqToHom (congrArg (fun W => W.X n) (leadingIter_total k D X N r)) ≫
      leadingTotalEmbedding k D X N r n

@[reassoc] theorem flatEmbedding_lof (r n : ℕ) (t : Index (r+1) n) :
    lof (leadingBarSequence k D X r) Z (r+1) n t ≫ flatEmbedding k D X N r n =
      inclusion (leadingBarSequence k D X r) Z (r+1) n t ≫
        eqToHom (congrArg (fun W => W.X n) (leadingIter_total k D X N r)) ≫
          leadingTotalEmbedding k D X N r n := by
  rw [flatEmbedding, lof_assemble_assoc]

end DerivedBar.ParityBridge

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Bar_IndexedAssemblyComparison
attribute [-instance] _root_.OAI.DerivedBar.term_finite _root_.OAI.DerivedBar.term_finiteDimensional _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instAddCommGroup _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
open CategoryTheory CategoryTheory.Limits TensorProduct TrivSqZeroExt
open scoped TensorProduct DirectSum
noncomputable section
namespace DerivedBar.ParityBridge
open DerivedBar.Multibar DerivedBar.RecursiveTotal

universe u
variable (k D X : Type u) [Field k] [Ring D] [Algebra k D]
  [AddCommGroup X] [Module k X] [Module D X] [Module Dᵐᵒᵖ X]
  [SMulCommClass D Dᵐᵒᵖ X] [IsScalarTower k D X] [IsScalarTower k Dᵐᵒᵖ X]
local instance instModuleCarrier_solutions_10 (V : ModuleCat.{u} D) : Module k V := BimoduleTensor.scalarModule k D V
variable (N : ModuleCat.{u} D)
local notation "A" => TrivSqZeroExt D X

local instance instIsScalarTowerCarrier_solutions_10_r539ddc_1 (V : ModuleCat.{u} D) : IsScalarTower k D V :=
  IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
local instance indexedAssemblyComparisonIndexDecidableEq_r539ddc_1 (r n : ℕ) :
    DecidableEq (Index r n) := Classical.decEq _
local instance instModuleTrivSqZeroExtCarrier_solutions_9_r539ddc_1 : Module A N := inflatedModule D X N
local instance instIsScalarTowerTrivSqZeroExtCarrier_solutions_9_r539ddc_1 : IsScalarTower k A N := IsScalarTower.of_algebraMap_smul
    (fun a v => IsScalarTower.algebraMap_smul D a v)
attribute [local instance] OAI.DerivedBar.ParityBridge.indexedAssemblyComparisonShapeDecidableEq
def shapeAssembly (r n : ℕ) : indexedModule k D X N r n ⟶
    ModuleCat.of D (D ⊗[k] term k A N (r+n)) :=
  ModuleCat.ofHom ((SquareZero.twoSidedWeight k D X N (r+n) r).subtype.comp
    (Multibar.Indexed.decomposition k D X N (r+n) r).toLinearMap)

@[reassoc] theorem shapeAssembly_lof (r n : ℕ) (p : Multibar.Indexed.Shape (r+n) r) :
    ModuleCat.ofHom (DirectSum.lof D _ (Multibar.Indexed.outerTensor k D X N) p) ≫
      shapeAssembly k D X N r n = ModuleCat.ofHom (Multibar.Indexed.outerInclusion k D X N p) := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro v
  change (Multibar.Indexed.assemble k D X N (r+n) r
    (DirectSum.lof D _ _ p v)).val = _
  simp only [Multibar.Indexed.assemble, DirectSum.toModule_lof, LinearMap.codRestrict_apply]
  rfl

end DerivedBar.ParityBridge

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Bar_SignedBlockExplicit
attribute [-instance] _root_.OAI.DerivedBar.Multibar.patternModule _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.DerivedBar.term_finite _root_.OAI.DerivedBar.term_finiteDimensional _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instAddCommGroup _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instRing
attribute [-simp] _root_.OAI.DerivedBar.ParityBridge.baseEmbed_tmul _root_.OAI.DerivedBar.ParityBridge.canonicalLinear_apply _root_.OAI.DerivedBar.ParityBridge.idealEmbed_tmul _root_.OAI.DerivedBar.ParityBridge.idealSuffixEmbed_tmul _root_.OAI.DerivedBar.ParityBridge.innerEmbedding_lof_succ _root_.OAI.DerivedBar.ParityBridge.outerCast_refl _root_.OAI.DerivedBar.ParityBridge.outerSuffixEmbed_tmul _root_.OAI.DerivedBar.ParityBridge.suffixEmbed_tmul _root_.OAI.DerivedBar.ParityBridge.termCast_refl _root_.OAI.DerivedBar.termMap_tmul _root_.OAI.ExternalTensor.Section4.sum_hom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
open CategoryTheory TensorProduct TrivSqZeroExt
open scoped TensorProduct DirectSum
noncomputable section
namespace DerivedBar.SquareZero
universe u
variable (k D X N : Type u) [Field k] [Ring D] [Algebra k D]
  [AddCommGroup X] [Module k X] [Module D X] [Module Dᵐᵒᵖ X]
  [SMulCommClass D Dᵐᵒᵖ X] [IsScalarTower k D X] [IsScalarTower k Dᵐᵒᵖ X]
  [AddCommGroup N] [Module k N]
  [Module (TrivSqZeroExt D X) N] [IsScalarTower k (TrivSqZeroExt D X) N]
local notation "A" => TrivSqZeroExt D X
variable (hN : ∀ (x : X) (v : N), (inr x : TrivSqZeroExt D X) • v = (0 : N))

include hN in
/-- The explicit faces equal the conjugated ordinary faces; this is a theorem,
not the definition of the independent differential. -/
theorem multibarTwoSided_eq_conjugate (n r : ℕ)
    {z : D ⊗[k] term k A N (n+1)} (hz : z ∈ twoSidedWeight k D X N (n+1) r) :
    multibarTwoSidedDifferential k D X N n z =
      (-1 : k)^r • twoSidedSignedProjection k D X N n r
        (twoSidedDifferential k A D N (fstHom k D X) n
          (twoSidedSignedProjection k D X N (n+1) r z)) := by
  have h := multibarTwoSided_sign k D X N hN n r (twoSidedSignedProjection_mem hz)
  rw [twoSidedSignedProjection_sq hz] at h
  exact h

include hN in
theorem multibarTwoSided_mem (n r : ℕ)
    {z : D ⊗[k] term k A N (n+1)} (hz : z ∈ twoSidedWeight k D X N (n+1) r) :
    multibarTwoSidedDifferential k D X N n z ∈ twoSidedWeight k D X N n r := by
  rw [multibarTwoSided_eq_conjugate k D X N hN n r hz]
  exact (twoSidedWeight k D X N n r).restrictScalars k |>.smul_mem _
    (twoSidedSignedProjection_mem (twoSidedDifferential_mem hN n r
      (twoSidedSignedProjection_mem hz)))

include hN in
theorem multibarTwoSided_shifted (n r : ℕ)
    {z : D ⊗[k] term k A N (n+1)} (hz : z ∈ twoSidedWeight k D X N (n+1) r) :
    (-1 : k)^r • multibarTwoSidedDifferential k D X N n z =
      twoSidedSignedProjection k D X N n r
        (twoSidedDifferential k A D N (fstHom k D X) n
          (twoSidedSignedProjection k D X N (n+1) r z)) := by
  rw [multibarTwoSided_eq_conjugate k D X N hN n r hz, smul_smul, ← mul_pow]
  simp

/-- Restriction of the independently defined literal faces to count r. -/
def multibarCountDifferential (n r : ℕ) :
    twoSidedWeight k D X N (n+1) r →ₗ[D] twoSidedWeight k D X N n r :=
  (multibarTwoSidedDifferential k D X N n).restrict
    (fun _ hz => multibarTwoSided_mem k D X N hN n r hz)

end DerivedBar.SquareZero
namespace DerivedBar.Multibar.Indexed
universe u
variable (k D X N : Type u) [Field k] [Ring D] [Algebra k D]
  [AddCommGroup X] [Module k X] [Module D X] [Module Dᵐᵒᵖ X]
  [SMulCommClass D Dᵐᵒᵖ X] [IsScalarTower k D X] [IsScalarTower k Dᵐᵒᵖ X]
  [AddCommGroup N] [Module k N]
  [Module (TrivSqZeroExt D X) N] [IsScalarTower k (TrivSqZeroExt D X) N]
variable (hN : ∀ (x : X) (v : N), (inr x : TrivSqZeroExt D X) • v = (0 : N))

/-- Literal multibar faces on the direct sum of actual tensor blocks, with the
[r] sign. Only the degreewise tensor decomposition is used for coordinates. -/
def explicitBlockDifferential (n r : ℕ) :
    (⨁ p : Shape (n+1) r, outerTensor k D X N p) →ₗ[D]
      (⨁ p : Shape n r, outerTensor k D X N p) :=
  (decomposition k D X N n r).symm.toLinearMap.comp
    (((-1 : k)^r • SquareZero.multibarCountDifferential k D X N hN n r).comp
      (decomposition k D X N (n+1) r).toLinearMap)

/-- The previously transported signed differential is identified with independent
literal faces, including the endpoint and square-zero empty-block cases. -/
theorem blockDifferential_eq_explicit (n r : ℕ) :
    blockDifferential k D X N hN n r = explicitBlockDifferential k D X N hN n r := by
  apply LinearMap.ext
  intro z
  apply (decomposition k D X N n r).injective
  apply Subtype.ext
  change ((decomposition k D X N n r)
    ((decomposition k D X N n r).symm
      ((SquareZero.signEquiv k D X N n r).symm
        (((SquareZero.twoSidedWeightComplex k D X N hN r).d (n+1) n).hom
          (SquareZero.signEquiv k D X N (n+1) r (decomposition k D X N (n+1) r z)))))).val =
    ((decomposition k D X N n r) ((decomposition k D X N n r).symm
      (((-1 : k)^r • SquareZero.multibarCountDifferential k D X N hN n r)
        (decomposition k D X N (n+1) r z)))).val
  rw [LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
  simp only [SquareZero.twoSidedWeightComplex, ChainComplex.of_d, ModuleCat.hom_ofHom]
  exact (SquareZero.multibarTwoSided_shifted k D X N hN n r
    (decomposition k D X N (n+1) r z).property).symm

end DerivedBar.Multibar.Indexed

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Bar_IntegerCountRestriction
attribute [-instance] _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instAddCommGroup _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
open CategoryTheory CategoryTheory.Limits TensorProduct TrivSqZeroExt HomologicalComplex
open scoped TensorProduct DirectSum
noncomputable section
namespace DerivedBar.ParityBridge
open DerivedBar.Multibar DerivedBar.RecursiveTotal
universe u
variable (k D X : Type u) [Field k] [Ring D] [Algebra k D]
  [AddCommGroup X] [Module k X] [Module D X] [Module Dᵐᵒᵖ X]
  [SMulCommClass D Dᵐᵒᵖ X] [IsScalarTower k D X] [IsScalarTower k Dᵐᵒᵖ X]
local instance integerCountRestrictionScalarModule (V : ModuleCat D) : Module k V :=
  BimoduleTensor.scalarModule k D V
local instance integerCountRestrictionScalarTower (V : ModuleCat D) : IsScalarTower k D V :=
  IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
variable (N : ModuleCat D)
local notation "A" => TrivSqZeroExt D X
local instance integerCountRestrictionIndexDecidableEq_r539ddc_1 (r n : ℕ) :
    DecidableEq (Index r n) := Classical.decEq _
local instance integerCountRestrictionShapeDecidableEq_r539ddc_1 (n r : ℕ) :
    DecidableEq (Multibar.Indexed.Shape n r) := Classical.decEq _
attribute [local instance] OAI.DerivedBar.ParityBridge.integerCountRestrictionInflatedModule
local instance integerCountRestrictionInflatedScalarTower : IsScalarTower k A N :=
  IsScalarTower.of_algebraMap_smul
    (fun a v => IsScalarTower.algebraMap_smul D a v)

local notation "C" => ModuleCat D
local notation "E" => ComplexShape.embeddingDownNat
local notation "K" => Multibar.Indexed.signedBlockComplex k D X N (inflated_ideal_zero D X N)

/-- The actual integer cochain count complex shifted by -r. -/
def deshiftedCount (r : ℕ) : CochainComplex C ℤ :=
  ((integerExtension D).obj (K r))⟦-(r:ℤ)⟧

def deshiftedCountRestriction (r : ℕ) : ChainComplex C ℕ :=
  (deshiftedCount k D X N r).restriction E

end DerivedBar.ParityBridge

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Bar_IntegerCountShift
attribute [-instance] _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instAddCommGroup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
open CategoryTheory CategoryTheory.Limits TensorProduct TrivSqZeroExt
open scoped TensorProduct DirectSum
noncomputable section
namespace DerivedBar.ParityBridge
open DerivedBar.Multibar DerivedBar.RecursiveTotal
universe u
variable (k D X : Type u) [Field k] [Ring D] [Algebra k D]
  [AddCommGroup X] [Module k X] [Module D X] [Module Dᵐᵒᵖ X]
  [SMulCommClass D Dᵐᵒᵖ X] [IsScalarTower k D X] [IsScalarTower k Dᵐᵒᵖ X]
local instance instModuleCarrier_solutions_12 (V : ModuleCat D) : Module k V := BimoduleTensor.scalarModule k D V
local instance instIsScalarTowerCarrier_solutions_12 (V : ModuleCat D) : IsScalarTower k D V :=
  IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
variable (N : ModuleCat D)
local notation "A" => TrivSqZeroExt D X
local instance instDecidableEqIndex_3_r539ddc_1 (r n : ℕ) : DecidableEq (Index r n) := Classical.decEq _
local instance instDecidableEqShape_r539ddc_1 (n r : ℕ) : DecidableEq (Multibar.Indexed.Shape n r) := Classical.decEq _
attribute [local instance] OAI.DerivedBar.ParityBridge.instModuleTrivSqZeroExtCarrier_solutions_11
local instance instIsScalarTowerTrivSqZeroExtCarrier_solutions_11 : IsScalarTower k A N := IsScalarTower.of_algebraMap_smul
    (fun a v => IsScalarTower.algebraMap_smul D a v)

end DerivedBar.ParityBridge

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Bar_DerivedCountShift
attribute [-instance] _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instAddCommGroup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
open CategoryTheory CategoryTheory.Limits TensorProduct TrivSqZeroExt
open scoped TensorProduct DirectSum
noncomputable section
namespace DerivedBar.ParityBridge
open DerivedBar.Multibar DerivedBar.RecursiveTotal
universe u
variable (k D X : Type u) [Field k] [Ring D] [Algebra k D]
  [AddCommGroup X] [Module k X] [Module D X] [Module Dᵐᵒᵖ X]
  [SMulCommClass D Dᵐᵒᵖ X] [IsScalarTower k D X] [IsScalarTower k Dᵐᵒᵖ X]
local instance instModuleCarrier_solutions_13 (V : ModuleCat D) : Module k V := BimoduleTensor.scalarModule k D V
local instance instIsScalarTowerCarrier_solutions_13 (V : ModuleCat D) : IsScalarTower k D V :=
  IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
variable (N : ModuleCat D)
local notation "A" => TrivSqZeroExt D X
local instance derivedCountShiftIndexDecidableEq_r539ddc_1 (r n : ℕ) :
    DecidableEq (Index r n) := Classical.decEq _
local instance derivedCountShiftShapeDecidableEq_r539ddc_1 (n r : ℕ) :
    DecidableEq (Multibar.Indexed.Shape n r) := Classical.decEq _
attribute [local instance] OAI.DerivedBar.ParityBridge.instModuleTrivSqZeroExtCarrier_solutions_12
local instance instIsScalarTowerTrivSqZeroExtCarrier_solutions_12 : IsScalarTower k A N := IsScalarTower.of_algebraMap_smul
    (fun a v => IsScalarTower.algebraMap_smul D a v)

end DerivedBar.ParityBridge

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Bar_IntegerCountObject
attribute [-instance] _root_.OAI.DerivedBar.IterateSupport.isLE_zero _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instAddCommGroup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
open CategoryTheory CategoryTheory.Limits TensorProduct TrivSqZeroExt
open scoped TensorProduct DirectSum
noncomputable section
namespace DerivedBar.ParityBridge
open DerivedBar.Multibar DerivedBar.RecursiveTotal
universe u
variable (k D X : Type u) [Field k] [Ring D] [Algebra k D]
  [AddCommGroup X] [Module k X] [Module D X] [Module Dᵐᵒᵖ X]
  [SMulCommClass D Dᵐᵒᵖ X] [IsScalarTower k D X] [IsScalarTower k Dᵐᵒᵖ X]
local instance integerCountScalarModule (V : ModuleCat D) : Module k V :=
  BimoduleTensor.scalarModule k D V
local instance integerCountScalarTower (V : ModuleCat D) : IsScalarTower k D V :=
  IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
variable (N : ModuleCat D)
local notation "A" => TrivSqZeroExt D X
local instance integerCountIndexDecidableEq_r539ddc_1 (r n : ℕ) : DecidableEq (Index r n) :=
  Classical.decEq _
local instance integerCountShapeDecidableEq_r539ddc_1 (n r : ℕ) :
    DecidableEq (Multibar.Indexed.Shape n r) := Classical.decEq _
attribute [local instance] OAI.DerivedBar.ParityBridge.integerCountInflatedModule
local instance integerCountInflatedScalarTower : IsScalarTower k A N := IsScalarTower.of_algebraMap_smul
    (fun a v => IsScalarTower.algebraMap_smul D a v)

/-- The original r-count object, with exactly the original scalar and inflated actions. -/
abbrev countObject (r : ℕ) :=
  (integerQ D).obj (SquareZero.twoSidedWeightComplex k D X N (inflated_ideal_zero D X N) r)

end DerivedBar.ParityBridge

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Encoding_ArrowBasisIso
attribute [-instance] _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.ExternalTensor.Section4.rightModuleK
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open CategoryTheory CategoryTheory.Limits
namespace LittleFinitistic.ArrowBasisIso
universe u
variable (k : Type u) [Field k] (d : ℕ)

theorem hom_proj (j : Fin (d+1)) :
    (iso k d).hom ≫ ModuleCat.ofHom (LinearMap.proj j) = biproduct.π (family k d) j := by
  rw [← ModuleCat.biproductIsoPi_inv_comp_π (family k d) j]
  simp only [iso,Iso.hom_inv_id_assoc]

end LittleFinitistic.ArrowBasisIso

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Rectification_SourceFiltration
attribute [-instance] _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.ExternalTensor.Section4.ArrowVertex.vertex_additive _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
open CategoryTheory CategoryTheory.Limits HomologicalComplex CochainComplex
open LittleFinitistic.RectificationTotal
open scoped TensorProduct ModuleCat.Algebra
noncomputable section
namespace ExternalTensor.Section4.SourceFiltration
universe u
variable {k B : Type u} [Field k] [Ring B] [Algebra k B]
variable {A J R : Type} [Fintype A] [Fintype J] [Fintype R]
variable (t : AssemblyData (C := BiComplex k B) (A := A) (J := J) (R := R))

variable (h : Homotopy (t.q ≫ t.p) 0)

def pGrade1 : F1₁ t ⟶ t.V₁ := biproduct.desc t.pb₁

end ExternalTensor.Section4.SourceFiltration

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Rectification_TensorArrowSum
attribute [-instance] _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.ExternalTensor.Section4.rightModuleK
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open CategoryTheory CategoryTheory.Limits
namespace LittleFinitistic.TensorArrowSum
universe u
variable (k : Type u) [Field k] (d : ℕ)

def insertion (a : Fin (d+1)) : ModuleCat.of k k ⟶ ModuleCat.of k (QuadraticEncoding.Arrows k d) :=
  biproduct.ι (ArrowBasisIso.family k d) a ≫ (ArrowBasisIso.iso k d).hom

end LittleFinitistic.TensorArrowSum

end

end OAI
end



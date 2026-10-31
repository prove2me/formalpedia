-- Prove2me | Definitions.Def_OAIQ023F017
-- name    : OAIQ023F017
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-30T16:38:59.497469+00:00
-- url     : https://prove2.me/theorems/31e6f6c3-55d1-4c97-ad7f-f6afc4ac064b
-- title:
--   Definitions bundle OAIQ023F017 of the split of OpenAI, An algebra of infinite little finitistic dimension (result family 198)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.LittleFinitistic.Main.exists_counterexample`, carved from OpenAI's openai/math development (OpenAI, *An algebra of infinite little finitistic dimension (result family 198)*, OpenAI Math Release, September 23, 2026, result family 198, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 51 declarations of OpenAI's Lean: 13 definitions, 3 instances and 35 theorems. The definitions and types are `OAI.DerivedBar.ParityBridge.countRetractsScalarModule`, `OAI.DerivedBar.ParityBridge.countTensorBarInclusion`, `OAI.DerivedBar.ParityBridge.countTensorBarProjection`, `OAI.DerivedBar.ParityBridge.instModuleCarrier_solutions_16`, `OAI.DerivedBar.ParityBridge.instModuleCarrier_solutions_17`, `OAI.DerivedBar.ParityBridge.recursiveSuffixCoefficientIndexDecidableEq`, `OAI.DerivedBar.ParityBridge.recursiveSuffixDifferentialIndexDecidableEq`, `OAI.DerivedBar.ParityBridge.recursiveSuffixInductionIndexDecidableEq`, `OAI.DerivedBar.ParityBridge.recursiveSuffixSumsIndexDecidableEq`, `OAI.DerivedBar.SquareZero.countSplitting`, `OAI.DerivedBar.SquareZero.tensorCountSplitting`, `OAI.DerivedBar.tensorBarIso`, `OAI.DerivedBar.twoSidedComplex`.
--
--   **Sources.** They come from these modules of lean/OAI/Algebra, in whole or in part: `Finitistic_Bar_ChainSplitting`, `Finitistic_Bar_CountHomologyDetection`, `Finitistic_Bar_CountProjective`, `Finitistic_Bar_CountRetracts`, `Finitistic_Bar_CountTorBounds`, `Finitistic_Bar_IndexedAssemblyComparison`, `Finitistic_Bar_InflatedParityFaces`, `Finitistic_Bar_LeadingBarSuffix`, `Finitistic_Bar_LeadingSuffixFaces`, `Finitistic_Bar_LeadingTotalComparison`, `Finitistic_Bar_LeadingTotalDifferential`, `Finitistic_Bar_RecursiveSuffixCoefficient`, `Finitistic_Bar_RecursiveSuffixDifferential`, `Finitistic_Bar_RecursiveSuffixFaces`, `Finitistic_Bar_RecursiveSuffixInduction`, `Finitistic_Bar_RecursiveSuffixSums`, `Finitistic_Bar_SuffixParityFaces`, `Finitistic_Bar_TensorModel`, `Finitistic_Bar_TwoSided`.
--
--   **Imports.** It imports the bundles `OAIQ023F010` and `OAIQ023F011` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ023F024` and `OAIQ023F039`.
-- source:
--   OpenAI, An algebra of infinite little finitistic dimension (result family 198), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 198; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/An-algebra-of-infinite-little-finitistic-dimension-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Algebra at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ023F010
import Definitions.Def_OAIQ023F011

section
-- module Solutions.OAIQ023_Fin.Finitistic_Bar_TwoSided
attribute [-instance] _root_.OAI.DerivedBar.Multibar.patternModule _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.DerivedBar.term_finite _root_.OAI.DerivedBar.term_finiteDimensional _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.BimoduleCoefficients.instAddCommGroupCarrierTensorProductMulOpposite _root_.OAI.LittleFinitistic.BimoduleCoefficients.instModuleCarrierTensorProductMulOpposite_1 _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instAddCommGroup _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instRing
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

/-- Actual D-linear two-sided bar complex with degree-n term D ⊗_k A^⊗n ⊗_k N. -/
def twoSidedComplex : ChainComplex (ModuleCat D) ℕ :=
  ChainComplex.of (fun n => ModuleCat.of D (D ⊗[k] term k A N n))
    (fun n => ModuleCat.ofHom (twoSidedDifferential k A D N f n))
    (fun n => ModuleCat.hom_ext (twoSidedDifferential_sq k A D N f n))
end DerivedBar

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Bar_ChainSplitting
attribute [-instance] _root_.OAI.DerivedBar.Multibar.patternModule _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.DerivedBar.term_finite _root_.OAI.DerivedBar.term_finiteDimensional _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.BimoduleCoefficients.instAddCommGroupCarrierTensorProductMulOpposite _root_.OAI.LittleFinitistic.BimoduleCoefficients.instModuleCarrierTensorProductMulOpposite_1 _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.ProductModules.firstModule _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instAddCommGroup _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
open scoped TensorProduct DirectSum
open TensorProduct CategoryTheory TrivSqZeroExt
noncomputable section

namespace DerivedBar
universe u

namespace SquareZero
variable (k D X N : Type u) [Field k] [Ring D] [Algebra k D]
  [AddCommGroup X] [Module k X] [Module D X] [Module Dᵐᵒᵖ X]
  [SMulCommClass D Dᵐᵒᵖ X] [IsScalarTower k D X] [IsScalarTower k Dᵐᵒᵖ X]
  [AddCommGroup N] [Module k N]
  [Module (TrivSqZeroExt D X) N] [IsScalarTower k (TrivSqZeroExt D X) N]
variable (hN : ∀ (x : X) (v : N), (inr x : TrivSqZeroExt D X) • v = 0)

/-- Chain-level count splitting of the actual two-sided absolute bar complex.
This is the first chain isomorphism in the proof of manuscript prop:bar-splitting.
Identification of these summands with derived tensor iterates is a separate dependency. -/
def countSplitting :
    directSumComplex (twoSidedWeightComplex k D X N hN) ≅
      twoSidedComplex k (TrivSqZeroExt D X) D N (fstHom k D X) :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n => (twoSidedWeightEquiv k D X N n).toModuleIso)
    (by
      intro i j hij
      change j+1 = i at hij
      subst i
      apply ModuleCat.hom_ext
      apply DirectSum.linearMap_ext
      intro r
      apply LinearMap.ext
      intro v
      simp only [directSumComplex, twoSidedComplex, ChainComplex.of_d,
        ModuleCat.hom_comp, ModuleCat.hom_ofHom, twoSidedWeightEquiv]
      change twoSidedDifferential k (TrivSqZeroExt D X) D N (fstHom k D X) j
          (DirectSum.coeLinearMap (twoSidedWeight k D X N (j+1))
            (DirectSum.lof D ℕ _ r v)) =
        DirectSum.coeLinearMap (twoSidedWeight k D X N j)
          (DirectSum.lmap (fun r => ((twoSidedWeightComplex k D X N hN r).d (j+1) j).hom)
            (DirectSum.lof D ℕ _ r v))
      rw [DirectSum.lmap_lof]
      erw [DirectSum.coeLinearMap_lof, DirectSum.coeLinearMap_lof]
      simp only [twoSidedWeightComplex, ChainComplex.of_d, ModuleCat.hom_ofHom]
      rfl)
end SquareZero
end DerivedBar

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Bar_TensorModel
attribute [-instance] _root_.OAI.DerivedBar.Multibar.patternModule _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.DerivedBar.term_finite _root_.OAI.DerivedBar.term_finiteDimensional _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.BimoduleCoefficients.instAddCommGroupCarrierTensorProductMulOpposite _root_.OAI.LittleFinitistic.BimoduleCoefficients.instModuleCarrierTensorProductMulOpposite_1 _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instAddCommGroup _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
open scoped TensorProduct DirectSum
open TensorProduct CategoryTheory TrivSqZeroExt
noncomputable section

namespace DerivedBar
universe u
variable {k A D : Type u} [Field k] [Ring A] [Algebra k A] [Ring D] [Algebra k D]
variable (f : A →ₐ[k] D)

variable (k A D N : Type u) [Field k] [Ring A] [Algebra k A] [Ring D] [Algebra k D]
  [AddCommGroup N] [Module k N] [Module A N] [IsScalarTower k A N]
variable (f : A →ₐ[k] D)

/-- The explicit two-sided bar is isomorphic to balanced tensor applied to a genuine projective resolution. -/
def tensorBarIso : tensorBarComplex k A D N f ≅ twoSidedComplex k A D N f :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n => (Balanced.freeEquiv f (term k A N n)).toModuleIso)
    (by
      intro i j hij
      change j+1 = i at hij
      subst i
      apply ModuleCat.hom_ext
      simp only [tensorBarComplex, twoSidedComplex, ChainComplex.of_d,
        ModuleCat.hom_comp, ModuleCat.hom_ofHom]
      exact (freeEquiv_natural f (term k A N (j+1)) (term k A N j)
        (differential k A N (j+1))).symm)

namespace SquareZero
variable (k D X N : Type u) [Field k] [Ring D] [Algebra k D]
  [AddCommGroup X] [Module k X] [Module D X] [Module Dᵐᵒᵖ X]
  [SMulCommClass D Dᵐᵒᵖ X] [IsScalarTower k D X] [IsScalarTower k Dᵐᵒᵖ X]
  [AddCommGroup N] [Module k N]
  [Module (TrivSqZeroExt D X) N] [IsScalarTower k (TrivSqZeroExt D X) N]

/-- The tensor of the actual free resolution splits by X-count as a D-module chain complex.
The identification of count r with the shifted r-fold derived tensor remains separate. -/
def tensorCountSplitting
    (hN : ∀ (x : X) (v : N), (inr x : TrivSqZeroExt D X) • v = 0) :
    tensorBarComplex k (TrivSqZeroExt D X) D N (fstHom k D X) ≅
      directSumComplex (twoSidedWeightComplex k D X N hN) :=
  tensorBarIso k (TrivSqZeroExt D X) D N (fstHom k D X) ≪≫
    (countSplitting k D X N hN).symm

end SquareZero
end DerivedBar

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Bar_InflatedParityFaces
attribute [-instance] _root_.OAI.DerivedBar.Multibar.patternModule _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.DerivedBar.term_finite _root_.OAI.DerivedBar.term_finiteDimensional _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.BimoduleCoefficients.instAddCommGroupCarrierTensorProductMulOpposite _root_.OAI.LittleFinitistic.BimoduleCoefficients.instModuleCarrierTensorProductMulOpposite_1 _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instAddCommGroup _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instRing
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

include hbase in
/-- All-D faces in the independently defined parity recursion are exactly
ordinary D-bar faces. This is an equality of actual maps on tensors. -/
theorem parity_baseEmbed (n : ℕ) (v : term k D N (n+1)) :
    SquareZero.multibarAugmentedDifferential k D X N n (baseEmbed k D X N (n+1) v) =
      baseEmbed k D X N n (DerivedBar.differential k D N n v) := by
  induction n with
  | zero =>
    induction v using OAI.tensorInductionOn with
    | tmul d v =>
      rw [baseEmbed_tmul, SquareZero.multibarAugmentedDifferential_zero,
        SquareZero.slotParity_base]
      exact hbase d v
    | add v w hv hw => simp only [map_add, hv, hw]
  | succ n ih =>
    induction v using OAI.tensorInductionOn with
    | tmul d v =>
      rw [baseEmbed_tmul, SquareZero.multibarAugmentedDifferential_succ,
        SquareZero.slotParity_base, ih, DerivedBar.differential_succ_tmul,
        map_sub, baseEmbed_smul k D X N hbase, baseEmbed_tmul]
    | add v w hv hw => simp only [map_add, hv, hw]

omit [Module D N] [IsScalarTower k D N] [Module A N] [IsScalarTower k A N] in
/-- Multiplying X by the first D entry is precisely the original right
D action used by the two-sided bar collapse map. -/
theorem ideal_action_baseEmbed (n : ℕ) (x : X) (v : term k D N (n+1)) :
    (inr x : A) • baseEmbed k D X N (n+1) v =
      idealEmbed k D X N n
        (BimoduleTensor.collapse k D X (term k D N n) (x ⊗ₜ[k] v)) := by
  induction v using OAI.tensorInductionOn with
  | tmul d v =>
    rw [baseEmbed_tmul, BimoduleTensor.collapse_tmul, idealEmbed_tmul]
    change ((inr x : A) * inl d) ⊗ₜ[k] baseEmbed k D X N n v =
      (inr (MulOpposite.op d • x) : A) ⊗ₜ[k] baseEmbed k D X N n v
    rw [inr_mul_inl]
  | add v w hv hw => simp only [map_add, smul_add, TensorProduct.tmul_add, hv, hw]

include hbase in
/-- The inner X bar is minus the augmented slot-parity recursion. The leading
D two-sided differential contributes the other minus sign in the full multibar. -/
theorem parity_idealEmbed (n : ℕ) (v : X ⊗[k] term k D N (n+1)) :
    SquareZero.multibarAugmentedDifferential k D X N (n+1) (idealEmbed k D X N (n+1) v) =
      -idealEmbed k D X N n (BimoduleTensor.barDifferential k D X N n v) := by
  induction v using OAI.tensorInductionOn with
  | tmul x v =>
    rw [idealEmbed_tmul, SquareZero.multibarAugmentedDifferential_succ,
      SquareZero.slotParity_ideal, parity_baseEmbed k D X N hbase,
      BimoduleTensor.barDifferential_tmul, map_sub, idealEmbed_tmul]
    have hneg : (-inr x : A) • baseEmbed k D X N (n+1) v =
        -((inr x : A) • baseEmbed k D X N (n+1) v) :=
      _root_.neg_smul (inr x : A) (baseEmbed k D X N (n+1) v)
    rw [hneg, ideal_action_baseEmbed, TensorProduct.neg_tmul, sub_neg_eq_add, neg_sub]
    exact add_comm _ _
  | add v w hv hw => simp only [map_add, hv, hw, neg_add]

end Compatible

/-- Direct specialization to the original module inflated along A -> D.
The inflation is a local instance for this N, never a blanket action on bar terms. -/
theorem inflated_parity_idealEmbed (n : ℕ) (v : X ⊗[k] term k D N (n+1)) :
    letI : Module A N := inflatedModule D X N
    letI : IsScalarTower k A N := IsScalarTower.of_algebraMap_smul
      (fun a v => IsScalarTower.algebraMap_smul D a v)
    SquareZero.multibarAugmentedDifferential k D X N (n+1) (idealEmbed k D X N (n+1) v) =
      -idealEmbed k D X N n (BimoduleTensor.barDifferential k D X N n v) := by
  let : Module A N := inflatedModule D X N
  let : IsScalarTower k A N := IsScalarTower.of_algebraMap_smul
    (fun a v => IsScalarTower.algebraMap_smul D a v)
  exact parity_idealEmbed k D X N (fun _ _ => rfl) n v

theorem inflated_parity_baseEmbed (n : ℕ) (v : term k D N (n+1)) :
    letI : Module A N := inflatedModule D X N
    letI : IsScalarTower k A N := IsScalarTower.of_algebraMap_smul
      (fun a v => IsScalarTower.algebraMap_smul D a v)
    SquareZero.multibarAugmentedDifferential k D X N n (baseEmbed k D X N (n+1) v) =
      baseEmbed k D X N n (DerivedBar.differential k D N n v) := by
  let : Module A N := inflatedModule D X N
  let : IsScalarTower k A N := IsScalarTower.of_algebraMap_smul
    (fun a v => IsScalarTower.algebraMap_smul D a v)
  exact parity_baseEmbed k D X N (fun _ _ => rfl) n v

end DerivedBar.ParityBridge

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Bar_SuffixParityFaces
attribute [-instance] _root_.OAI.DerivedBar.Multibar.patternModule _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.DerivedBar.term_finite _root_.OAI.DerivedBar.term_finiteDimensional _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.BimoduleCoefficients.instAddCommGroupCarrierTensorProductMulOpposite _root_.OAI.LittleFinitistic.BimoduleCoefficients.instModuleCarrierTensorProductMulOpposite_1 _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instAddCommGroup _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instRing
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

omit [IsScalarTower k D M] [IsScalarTower k A N] in
theorem suffixEmbed_smul (s n : ℕ) (e : M →ₗ[k] term k A N s)
    (he : ∀ (d : D) (v : M), e (d • v) = (inl d : A) • e v)
    (d : D) (v : term k D M n) :
    suffixEmbed k D X N M s e n (d • v) =
      (inl d : A) • suffixEmbed k D X N M s e n v := by
  cases n with
  | zero => exact he d v
  | succ n =>
    induction v using OAI.tensorInductionOn with
    | tmul b v =>
      change (inl (d*b) : A) ⊗ₜ[k] _ = ((inl d : A)*inl b) ⊗ₜ[k] _
      rw [inl_mul_inl]
    | add v w hv hw => simp only [smul_add, map_add, hv, hw]

omit [Module D M] [IsScalarTower k D M] [Module A N] [IsScalarTower k A N] in
/-- The original right D action supplies the first face for every suffix. -/
theorem ideal_action_suffixEmbed (s n : ℕ) (e : M →ₗ[k] term k A N s)
    (x : X) (v : term k D M (n+1)) :
    (inr x : A) • suffixEmbed k D X N M s e (n+1) v =
      idealSuffixEmbed k D X N M s n e
        (BimoduleTensor.collapse k D X (term k D M n) (x ⊗ₜ[k] v)) := by
  induction v using OAI.tensorInductionOn with
  | tmul d v =>
    rw [suffixEmbed_tmul, BimoduleTensor.collapse_tmul, idealSuffixEmbed_tmul]
    change ((inr x : A) * inl d) ⊗ₜ[k] _ = (inr (MulOpposite.op d • x) : A) ⊗ₜ[k] _
    rw [inr_mul_inl]
  | add v w hv hw => simp only [map_add, smul_add, TensorProduct.tmul_add, hv, hw]

omit [Module D M] [IsScalarTower k D M] in
/-- At an empty D block the ideal endpoint vanishes, leaving all suffix faces. -/
theorem parity_idealSuffixEmbed_zero (s : ℕ) (e : M →ₗ[k] term k A N (s+1))
    (he : ∀ (x : X) (v : M), (inr x : A) • e v = 0)
    (v : X ⊗[k] M) :
    SquareZero.multibarAugmentedDifferential k D X N (s+1)
      (idealSuffixEmbed k D X N M (s+1) 0 e v) =
    idealSuffixEmbed k D X N M s 0
      ((SquareZero.multibarAugmentedDifferential k D X N s).comp e) v := by
  induction v using OAI.tensorInductionOn with
  | tmul x v =>
    rw [idealSuffixEmbed_tmul, SquareZero.multibarAugmentedDifferential_succ,
      SquareZero.slotParity_ideal]
    change (-inr x : A) • e v - (-inr x : A) ⊗ₜ[k] _ = (inr x : A) ⊗ₜ[k] _
    have hn : (-inr x : A) • e v = -((inr x : A) • e v) :=
      _root_.neg_smul (inr x : A) (e v)
    rw [hn, he, neg_zero, TensorProduct.neg_tmul, zero_sub, neg_neg]
    rfl
  | add v w hv hw => simp only [map_add, hv, hw]
end DerivedBar.ParityBridge

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Bar_LeadingSuffixFaces
attribute [-instance] _root_.OAI.DerivedBar.Multibar.patternModule _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.DerivedBar.term_finite _root_.OAI.DerivedBar.term_finiteDimensional _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.BimoduleCoefficients.instAddCommGroupCarrierTensorProductMulOpposite _root_.OAI.LittleFinitistic.BimoduleCoefficients.instModuleCarrierTensorProductMulOpposite_1 _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instAddCommGroup _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instRing
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

omit [Module D M] [IsScalarTower k D M] in
/-- At a zero-length leading D block the projected X endpoint is zero. -/
theorem parity_outerSuffixEmbed_zero (s : ℕ) (e : M →ₗ[k] term k A N (s+1))
    (he : ∀ v, FreeBaseChange.coefficient (fstHom k D X) (term k A N s) (e v) = 0)
    (v : D ⊗[k] M) :
    SquareZero.multibarTwoSidedDifferential k D X N s
      (outerSuffixEmbed k D X N M (s+1) 0 e v) =
    -outerSuffixEmbed k D X N M s 0
      ((SquareZero.multibarAugmentedDifferential k D X N s).comp e) v := by
  induction v using OAI.tensorInductionOn with
  | tmul d v =>
    rw [outerSuffixEmbed_tmul, SquareZero.multibarTwoSidedDifferential_tmul]
    change d • FreeBaseChange.coefficient (fstHom k D X) (term k A N s) (e v) -
      d ⊗ₜ[k] SquareZero.multibarAugmentedDifferential k D X N s (e v) = _
    rw [he, smul_zero, zero_sub]
    rfl
  | add v w hv hw => simp only [map_add, hv, hw, neg_add]
end DerivedBar.ParityBridge

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Bar_RecursiveSuffixFaces
attribute [-instance] _root_.OAI.DerivedBar.term_finite _root_.OAI.DerivedBar.term_finiteDimensional _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.BimoduleCoefficients.instAddCommGroupCarrierTensorProductMulOpposite _root_.OAI.LittleFinitistic.BimoduleCoefficients.instModuleCarrierTensorProductMulOpposite _root_.OAI.LittleFinitistic.BimoduleCoefficients.instModuleCarrierTensorProductMulOpposite_1 _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instAddCommGroup _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instRing
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
local instance instDecidableEqIndex_1_r1944d5_1 (r n : ℕ) : DecidableEq (RecursiveTotal.Index r n) := Classical.decEq _
attribute [local instance] OAI.DerivedBar.ParityBridge.instModuleTrivSqZeroExtCarrier_solutions
attribute [local instance] OAI.DerivedBar.ParityBridge.instIsScalarTowerTrivSqZeroExtCarrier_solutions
/-- The original augmented parity operator commutes with degree transport. -/
theorem parity_termCast {a b : ℕ} (h : a=b) (h' : a+1=b+1)
    (v : term k A N (a+1)) :
    SquareZero.multibarAugmentedDifferential k D X N b (termCast k D X N h' v) =
      termCast k D X N h (SquareZero.multibarAugmentedDifferential k D X N a v) := by
  subst b
  rfl

/-- Empty blocks retain the suffix face with no extra sign. -/
theorem parity_barSuffix_zero (V : ModuleCat.{u} D) (s : ℕ)
    (e : V →ₗ[k] term k A N (s+1))
    (he : ∀ (x : X) (v : V), (inr x : A) • e v = 0)
    (v : ((XB).obj V).X 0) :
    SquareZero.multibarAugmentedDifferential k D X N (s+1)
      (barSuffix k D X N V (s+1) 0 e v) =
    barSuffix k D X N V s 0
      ((SquareZero.multibarAugmentedDifferential k D X N s).comp e) v :=
  parity_idealSuffixEmbed_zero k D X N V s e he _

end DerivedBar.ParityBridge

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Bar_LeadingBarSuffix
attribute [-instance] _root_.OAI.DerivedBar.term_finite _root_.OAI.DerivedBar.term_finiteDimensional _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.BalancedTensor.scalarLeftTower _root_.OAI.LittleFinitistic.BimoduleCoefficients.instAddCommGroupCarrierTensorProductMulOpposite _root_.OAI.LittleFinitistic.BimoduleCoefficients.instModuleCarrierTensorProductMulOpposite _root_.OAI.LittleFinitistic.BimoduleCoefficients.instModuleCarrierTensorProductMulOpposite_1 _root_.OAI.LittleFinitistic.BimoduleCoefficients.towerLeft _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instAddCommGroup _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instRing
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
theorem twoSidedParity_outerCast {a b : ℕ} (h : a=b) (h' : a+1=b+1)
    (v : D ⊗[k] term k A N (a+1)) :
    SquareZero.multibarTwoSidedDifferential k D X N b (outerCast k D X N h' v) =
    outerCast k D X N h (SquareZero.multibarTwoSidedDifferential k D X N a v) := by
  subst b
  simp only [outerCast_refl, LinearMap.id_apply]

theorem parity_outerBarSuffix_zero (V : ModuleCat.{u} D) (s : ℕ)
    (e : V →ₗ[k] term k A N (s+1))
    (he : ∀ v, FreeBaseChange.coefficient (fstHom k D X) (term k A N s) (e v) = 0)
    (v : ((DB).obj V).X 0) :
    SquareZero.multibarTwoSidedDifferential k D X N s
      (outerBarSuffix k D X N V (s+1) 0 e v) =
    -outerBarSuffix k D X N V s 0
      ((SquareZero.multibarAugmentedDifferential k D X N s).comp e) v :=
  parity_outerSuffixEmbed_zero k D X N V s e he _

theorem outerBarSuffix_neg (V : ModuleCat.{u} D) (s i : ℕ)
    (e : V →ₗ[k] term k A N s) :
    outerBarSuffix k D X N V s i (-e) = -outerBarSuffix k D X N V s i e := by
  ext v
  unfold outerBarSuffix
  simp only [LinearMap.neg_apply, LinearMap.comp_apply]
  generalize (Multibar.freeBarObjIso k D V i).hom.hom v = w
  induction w using OAI.tensorInductionOn with
  | tmul d w =>
    change d ⊗ₜ[k] suffixEmbed k D X N V s (-e) i w =
      -(d ⊗ₜ[k] suffixEmbed k D X N V s e i w)
    rw [← neg_one_smul k e, suffixEmbed_smul_map, neg_one_smul, TensorProduct.tmul_neg]
  | add v w hv hw => simp only [map_add, neg_add, hv, hw]

theorem outerBarSuffix_zero (V : ModuleCat.{u} D) (s i : ℕ) :
    outerBarSuffix k D X N V s i 0 = 0 := by
  ext v
  unfold outerBarSuffix
  simp only [LinearMap.zero_apply, LinearMap.comp_apply]
  generalize (Multibar.freeBarObjIso k D V i).hom.hom v = w
  induction w using OAI.tensorInductionOn with
  | tmul d w =>
    change d ⊗ₜ[k] suffixEmbed k D X N V s 0 i w = 0
    have hz := suffixEmbed_smul_map k D X N V s i (0:k) (0 : V →ₗ[k] term k A N s) w
    simp only [zero_smul] at hz
    rw [hz, TensorProduct.tmul_zero]
  | add v w hv hw => simp only [map_add, hv, hw, add_zero]

theorem parity_outerBaseEmbed (i : ℕ) (v : D ⊗[k] term k D N (i+1)) :
    SquareZero.multibarTwoSidedDifferential k D X N i (outerBaseEmbed k D X N (i+1) v) =
      outerBaseEmbed k D X N i (DerivedBar.differential k D N (i+1) v) := by
  induction v using OAI.tensorInductionOn with
  | tmul d v =>
    change SquareZero.multibarTwoSidedDifferential k D X N i
      (d ⊗ₜ[k] baseEmbed k D X N (i+1) v) = _
    rw [SquareZero.multibarTwoSidedDifferential_tmul, coefficient_baseEmbed,
      inflated_parity_baseEmbed, DerivedBar.differential_succ_tmul, map_sub, map_smul]
    rfl
  | add v w hv hw => simp only [map_add, hv, hw]

end DerivedBar.ParityBridge

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Bar_RecursiveSuffixSums
attribute [-instance] _root_.OAI.DerivedBar.term_finite _root_.OAI.DerivedBar.term_finiteDimensional _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.BalancedTensor.scalarLeftTower _root_.OAI.LittleFinitistic.BimoduleCoefficients.instAddCommGroupCarrierTensorProductMulOpposite _root_.OAI.LittleFinitistic.BimoduleCoefficients.instModuleCarrierTensorProductMulOpposite _root_.OAI.LittleFinitistic.BimoduleCoefficients.instModuleCarrierTensorProductMulOpposite_1 _root_.OAI.LittleFinitistic.BimoduleCoefficients.towerLeft _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instAddCommGroup _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instRing
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
universe u
variable (k D X : Type u) [Field k] [Ring D] [Algebra k D]
  [AddCommGroup X] [Module k X] [Module D X] [Module Dᵐᵒᵖ X]
  [SMulCommClass D Dᵐᵒᵖ X] [IsScalarTower k D X] [IsScalarTower k Dᵐᵒᵖ X]
local instance recursiveSuffixSumsIndexDecidableEq (r n : ℕ) :
    DecidableEq (RecursiveTotal.Index r n) := Classical.decEq _
variable (N : ModuleCat.{u} D)
local notation "A" => TrivSqZeroExt D X
local notation "XB" => BimoduleTensor.twoSidedBarFunctor k D X
local notation "Z" => Functor.obj (ChainComplex.single₀ (ModuleCat D)) N
local notation "B" => (fun _ : ℕ => XB)

attribute [local instance] OAI.DerivedBar.ParityBridge.recursiveSuffixSumsScalarModule
attribute [local instance] OAI.DerivedBar.ParityBridge.recursiveSuffixSumsScalarTower
/-- Suffix insertion commutes with the actual finite-sum distribution map
appearing in the independently defined vertical differential. -/
theorem innerEmbedding_sumDesc (r n i q : ℕ) (h : i+q=n)
    (v : (RecursiveTotal.degreeFunctor B r i).obj (RecursiveTotal.flat B Z r q)) :
    innerEmbedding k D X N (r+1) n
      ((RecursiveTotal.sumDesc (RecursiveTotal.summand B Z r q)
        (RecursiveTotal.degreeFunctor B r i)
        (fun t => RecursiveTotal.lof B Z (r+1) n ⟨⟨⟨i,q⟩,h⟩,t⟩)).hom v) =
    termCast k D X N (show ((r+q)+i)+1=(r+1)+n by omega)
      (barSuffix k D X N (RecursiveTotal.flat B Z r q) (r+q) i
        (innerEmbedding k D X N r q) v) := by
  let C := termCast k D X N (show ((r+q)+i)+1=(r+1)+n by omega)
  let S := RecursiveTotal.sumDesc (RecursiveTotal.summand B Z r q)
    (RecursiveTotal.degreeFunctor B r i)
    (fun t => RecursiveTotal.lof B Z (r+1) n ⟨⟨⟨i,q⟩,h⟩,t⟩)
  have he : (innerEmbedding k D X N (r+1) n).comp (S.hom.restrictScalars k) =
      C.comp (barSuffix k D X N (RecursiveTotal.flat B Z r q) (r+q) i
        (innerEmbedding k D X N r q)) := by
    apply sum_hom_ext_scalar k D (RecursiveTotal.summand B Z r q)
      (RecursiveTotal.degreeFunctor B r i) (term k A N ((r+1)+n))
    intro t
    ext w
    have hs := congrArg (fun f => f.hom w)
      (RecursiveTotal.lof_sumDesc (RecursiveTotal.summand B Z r q)
        (RecursiveTotal.degreeFunctor B r i)
        (fun t => RecursiveTotal.lof B Z (r+1) n ⟨⟨⟨i,q⟩,h⟩,t⟩) t)
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at hs
    simp only [LinearMap.comp_apply, LinearMap.restrictScalars_apply]
    change innerEmbedding k D X N (r+1) n (S.hom _) = C _
    erw [hs]
    erw [innerEmbedding_lof_succ k D X N r n i q h t w]
    change C _ = C (barSuffix k D X N (RecursiveTotal.flat B Z r q) (r+q) i
      (innerEmbedding k D X N r q) ((((XB).map (RecursiveTotal.lof B Z r q t)).f i).hom w))
    rw [barSuffix_map]
  exact congrArg (fun f => f v) he
end DerivedBar.ParityBridge

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Bar_RecursiveSuffixDifferential
attribute [-instance] _root_.OAI.DerivedBar.term_finite _root_.OAI.DerivedBar.term_finiteDimensional _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.BalancedTensor.scalarLeftTower _root_.OAI.LittleFinitistic.BimoduleCoefficients.instAddCommGroupCarrierTensorProductMulOpposite _root_.OAI.LittleFinitistic.BimoduleCoefficients.instModuleCarrierTensorProductMulOpposite _root_.OAI.LittleFinitistic.BimoduleCoefficients.instModuleCarrierTensorProductMulOpposite_1 _root_.OAI.LittleFinitistic.BimoduleCoefficients.towerLeft _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instAddCommGroup _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

set_option backward.isDefEq.respectTransparency false

namespace OAI
open CategoryTheory CategoryTheory.Limits CategoryTheory.Preadditive TensorProduct TrivSqZeroExt
open scoped TensorProduct DirectSum
noncomputable section
namespace DerivedBar.ParityBridge
universe u
variable (k D X : Type u) [Field k] [Ring D] [Algebra k D]
  [AddCommGroup X] [Module k X] [Module D X] [Module Dᵐᵒᵖ X]
  [SMulCommClass D Dᵐᵒᵖ X] [IsScalarTower k D X] [IsScalarTower k Dᵐᵒᵖ X]
local instance recursiveSuffixDifferentialIndexDecidableEq (r n : ℕ) :
    DecidableEq (RecursiveTotal.Index r n) := Classical.decEq _
variable (N : ModuleCat.{u} D)
local notation "A" => TrivSqZeroExt D X
local notation "XB" => BimoduleTensor.twoSidedBarFunctor k D X
local notation "Z" => Functor.obj (ChainComplex.single₀ (ModuleCat D)) N
local notation "B" => (fun _ : ℕ => XB)

attribute [local instance] OAI.DerivedBar.ParityBridge.recursiveSuffixDifferentialScalarModule
attribute [local instance] OAI.DerivedBar.ParityBridge.recursiveSuffixDifferentialScalarTower
attribute [local instance] OAI.DerivedBar.ParityBridge.recursiveSuffixDifferentialInflatedModule
attribute [local instance] OAI.DerivedBar.ParityBridge.recursiveSuffixDifferentialInflatedScalarTower
/-- The actual horizontal differential followed by the complete suffix embedding. -/
theorem innerEmbedding_horizontal (r n i q : ℕ) (h : (i+1)+q=n+1)
    (t : RecursiveTotal.Index r q)
    (v : (RecursiveTotal.degreeFunctor B r (i+1)).obj (RecursiveTotal.summand B Z r q t)) :
    innerEmbedding k D X N (r+1) n
      ((RecursiveTotal.horizontal B Z r n (i+1) q h t).hom v) =
    termCast k D X N (show ((r+q)+i)+1=(r+1)+n by omega)
      (barSuffix k D X N (RecursiveTotal.summand B Z r q t) (r+q) i
        ((innerEmbedding k D X N r q).comp
          ((RecursiveTotal.lof B Z r q t).hom.restrictScalars k))
        ((((XB).obj (RecursiveTotal.summand B Z r q t)).d (i+1) i).hom v)) := by
  simp only [RecursiveTotal.horizontal]
  exact innerEmbedding_lof_succ k D X N r n i q (by omega) t _

/-- The actual signed vertical face is computed after distribution over the
whole inner sum, rather than on an assumed single supported output summand. -/
theorem innerEmbedding_vertical (r n i q : ℕ) (h : i+(q+1)=n+1)
    (t : RecursiveTotal.Index r (q+1))
    (d : ∀ q, RecursiveTotal.flat B Z r (q+1) ⟶ RecursiveTotal.flat B Z r q)
    (v : (RecursiveTotal.degreeFunctor B r i).obj (RecursiveTotal.summand B Z r (q+1) t)) :
    innerEmbedding k D X N (r+1) n
      ((RecursiveTotal.vertical B Z r n i (q+1) h t d).hom v) =
    (-1:k)^i • termCast k D X N (show ((r+q)+i)+1=(r+1)+n by omega)
      (barSuffix k D X N (RecursiveTotal.summand B Z r (q+1) t) (r+q) i
        ((innerEmbedding k D X N r q).comp
          ((RecursiveTotal.lof B Z r (q+1) t ≫ d q).hom.restrictScalars k)) v) := by
  change innerEmbedding k D X N (r+1) n
    (((-1:ℤˣ)^i) •
      ((RecursiveTotal.sumDesc (RecursiveTotal.summand B Z r q)
        (RecursiveTotal.degreeFunctor B r i)
        (fun s => RecursiveTotal.lof B Z (r+1) n ⟨⟨⟨i,q⟩,by omega⟩,s⟩)).hom
          (((RecursiveTotal.degreeFunctor B r i).map
            (RecursiveTotal.lof B Z r (q+1) t ≫ d q)).hom v))) = _
  rw [totalSign_smul k (RecursiveTotal.flat B Z (r+1) n), map_smul,
    innerEmbedding_sumDesc]
  change (-1:k)^i • termCast k D X N _
    (barSuffix k D X N (RecursiveTotal.flat B Z r q) (r+q) i
      (innerEmbedding k D X N r q)
      ((((XB).map (RecursiveTotal.lof B Z r (q+1) t ≫ d q)).f i).hom v)) = _
  rw [barSuffix_map]

/-- Evaluation of the independently recursive differential on one input summand. -/
theorem innerEmbedding_differential_lof (r n i q : ℕ) (h : i+q=n+1)
    (t : RecursiveTotal.Index r q)
    (v : RecursiveTotal.summand B Z (r+1) (n+1) ⟨⟨⟨i,q⟩,h⟩,t⟩) :
    innerEmbedding k D X N (r+1) n
      ((RecursiveTotal.differential B Z (r+1) n).hom
        ((RecursiveTotal.lof B Z (r+1) (n+1) ⟨⟨⟨i,q⟩,h⟩,t⟩).hom v)) =
    innerEmbedding k D X N (r+1) n
      ((RecursiveTotal.horizontal B Z r n i q h t).hom v) +
    innerEmbedding k D X N (r+1) n
      ((RecursiveTotal.vertical B Z r n i q h t (RecursiveTotal.differential B Z r)).hom v) := by
  have he := congrArg (fun f => f.hom v)
    (RecursiveTotal.lof_differential_succ B Z r n i q h t)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at he
  erw [ModuleCat.hom_add, LinearMap.add_apply] at he
  erw [he, map_add]
  rfl

/-- Composition of the induction hypothesis with an actual summand inclusion. -/
theorem innerEmbedding_suffix_induction (r q : ℕ) (t : RecursiveTotal.Index r (q+1))
    (ih : ∀ (v : RecursiveTotal.flat B Z r (q+1)),
      SquareZero.multibarAugmentedDifferential k D X N (r+q)
        (innerEmbedding k D X N r (q+1) v) =
      -innerEmbedding k D X N r q ((RecursiveTotal.differential B Z r q).hom v)) :
    (SquareZero.multibarAugmentedDifferential k D X N (r+q)).comp
      ((innerEmbedding k D X N r (q+1)).comp
        ((RecursiveTotal.lof B Z r (q+1) t).hom.restrictScalars k)) =
    -((innerEmbedding k D X N r q).comp
      ((RecursiveTotal.lof B Z r (q+1) t ≫ RecursiveTotal.differential B Z r q).hom.restrictScalars k)) := by
  ext v
  exact ih ((RecursiveTotal.lof B Z r (q+1) t).hom v)
end DerivedBar.ParityBridge

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Bar_RecursiveSuffixInduction
attribute [-instance] _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.BimoduleCoefficients.instAddCommGroupCarrierTensorProductMulOpposite _root_.OAI.LittleFinitistic.BimoduleCoefficients.instModuleCarrierTensorProductMulOpposite_1 _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instAddCommGroup
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
local instance recursiveSuffixInductionIndexDecidableEq (r n : ℕ) :
    DecidableEq (RecursiveTotal.Index r n) := Classical.decEq _
variable (N : ModuleCat.{u} D)
local notation "A" => TrivSqZeroExt D X
local notation "XB" => BimoduleTensor.twoSidedBarFunctor k D X
local notation "Z" => Functor.obj (ChainComplex.single₀ (ModuleCat D)) N
local notation "B" => (fun _ : ℕ => XB)

/-- A zero final input term cannot contribute an element, at any recursive depth. -/
theorem innerSummand_positive_input_zero (r n : ℕ) (t : RecursiveTotal.Index r n)
    (h : RecursiveTotal.inputDegree r t ≠ 0) (v : RecursiveTotal.summand B Z r n t) : v=0 := by
  have hz := RecursiveTotal.summand_isZero B Z r n t
    (HomologicalComplex.isZero_single_obj_X (ComplexShape.down ℕ) 0 N _ h)
  exact congrArg (fun f : RecursiveTotal.summand B Z r n t ⟶
    RecursiveTotal.summand B Z r n t => f.hom v) (hz.eq_of_src (𝟙 _) 0)

end DerivedBar.ParityBridge

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Bar_RecursiveSuffixCoefficient
attribute [-instance] _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear
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
local instance recursiveSuffixCoefficientIndexDecidableEq (r n : ℕ) :
    DecidableEq (RecursiveTotal.Index r n) := Classical.decEq _
end DerivedBar.ParityBridge

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Bar_LeadingTotalDifferential
attribute [-instance] _root_.OAI.DerivedBar.term_finite _root_.OAI.DerivedBar.term_finiteDimensional _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.BimoduleCoefficients.instAddCommGroupCarrierTensorProductMulOpposite _root_.OAI.LittleFinitistic.BimoduleCoefficients.instModuleCarrierTensorProductMulOpposite_1 _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instAddCommGroup _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instRing
attribute [-simp] _root_.OAI.DerivedBar.ParityBridge.canonicalLinear_apply _root_.OAI.ExternalTensor.Section4.sum_hom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
open CategoryTheory CategoryTheory.Limits CategoryTheory.Preadditive TensorProduct TrivSqZeroExt
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
local notation "DB" => barFunctor k D
local notation "Z" => Functor.obj (ChainComplex.single₀ (ModuleCat D)) N
local notation "B" => (fun _ : ℕ => XB)
local notation "c" => ComplexShape.down ℕ
local notation "I" => RecursiveTotal.iter B Z
local notation "K" => barBicomplex k D

attribute [local instance] OAI.DerivedBar.ParityBridge.instModuleCarrier_solutions_6
theorem leadingTotalEmbedding_d₁ (r n i q : ℕ) (h : (i+1)+q=n+1)
    (v : (((DB).obj ((I r).X q)).X (i+1))) :
    (((K (I r)).d₁ c (i+1) q n ≫ leadingTotalEmbedding k D X N r n).hom v) =
    outerCast k D X N (show (r+q)+i=r+n by omega)
      (outerBarSuffix k D X N ((I r).X q) (r+q) i (innerTotalEmbedding k D X N r q)
        ((((DB).obj ((I r).X q)).d (i+1) i).hom v)) := by
  rw [HomologicalComplex₂.d₁_eq _ _ (by rfl : (c).Rel (i+1) i) q n (by change i+q=n; omega)]
  change (((1:ℤˣ) • ((((DB).obj ((I r).X q)).d (i+1) i) ≫
    (K (I r)).ιTotal c i q n (by change i+q=n; omega))) ≫ leadingTotalEmbedding k D X N r n).hom v = _
  erw [one_smul, Category.assoc, leadingTotalEmbedding_ι]
  rfl

/-- Both total faces vanish at the respective zero degree by the actual chain shape. -/
theorem leadingTotalEmbedding_d₁_zero (r n q : ℕ) :
    (K (I r)).d₁ c 0 q n ≫ leadingTotalEmbedding k D X N r n = 0 := by
  erw [HomologicalComplex₂.d₁_eq_zero _ _ _ _ _ (by simp), zero_comp]

theorem leadingTotalEmbedding_d₂_zero (r n i : ℕ) :
    (K (I r)).d₂ c i 0 n ≫ leadingTotalEmbedding k D X N r n = 0 := by
  erw [HomologicalComplex₂.d₂_eq_zero _ _ _ _ _ (by simp), zero_comp]

theorem leadingTotalEmbedding_ι_d (r n i q : ℕ) (h : i+q=n+1) :
    (K (I r)).ιTotal c i q (n+1) h ≫ (barTotal k D (I r)).d (n+1) n ≫
      leadingTotalEmbedding k D X N r n =
    (K (I r)).d₁ c i q n ≫ leadingTotalEmbedding k D X N r n +
      (K (I r)).d₂ c i q n ≫ leadingTotalEmbedding k D X N r n := by
  simp only [barTotal, HomologicalComplex₂.total_d]
  erw [add_comp, comp_add, HomologicalComplex₂.ι_D₁_assoc,
    HomologicalComplex₂.ι_D₂_assoc]
end DerivedBar.ParityBridge

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Bar_LeadingTotalComparison
attribute [-instance] _root_.OAI.DerivedBar.term_finite _root_.OAI.DerivedBar.term_finiteDimensional _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.BimoduleCoefficients.instAddCommGroupCarrierTensorProductMulOpposite _root_.OAI.LittleFinitistic.BimoduleCoefficients.instModuleCarrierTensorProductMulOpposite _root_.OAI.LittleFinitistic.BimoduleCoefficients.instModuleCarrierTensorProductMulOpposite_1 _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instAddCommGroup _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
open CategoryTheory CategoryTheory.Limits CategoryTheory.Preadditive TensorProduct TrivSqZeroExt
open scoped TensorProduct DirectSum
noncomputable section
namespace DerivedBar.ParityBridge
universe u
variable (k D X : Type u) [Field k] [Ring D] [Algebra k D]
  [AddCommGroup X] [Module k X] [Module D X] [Module Dᵐᵒᵖ X]
  [SMulCommClass D Dᵐᵒᵖ X] [IsScalarTower k D X] [IsScalarTower k Dᵐᵒᵖ X]
variable (N : ModuleCat.{u} D)
local notation "A" => TrivSqZeroExt D X

attribute [local instance] OAI.DerivedBar.ParityBridge.instModuleCarrier_solutions_7
attribute [local instance] OAI.DerivedBar.ParityBridge.instIsScalarTowerCarrier_solutions_7
attribute [local instance] OAI.DerivedBar.ParityBridge.instModuleTrivSqZeroExtCarrier_solutions_6
attribute [local instance] OAI.DerivedBar.ParityBridge.instIsScalarTowerTrivSqZeroExtCarrier_solutions_6
theorem outerCast_smul {a b : ℕ} (h : a=b) (z : k)
    (v : D ⊗[k] term k A N a) :
    outerCast k D X N h (z • v) = z • outerCast k D X N h v := by
  subst b
  simp only [outerCast_refl, LinearMap.id_apply]

end DerivedBar.ParityBridge

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Bar_IndexedAssemblyComparison
attribute [-instance] _root_.OAI.DerivedBar.term_finite _root_.OAI.DerivedBar.term_finiteDimensional _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.BimoduleCoefficients.instAddCommGroupCarrierTensorProductMulOpposite _root_.OAI.LittleFinitistic.BimoduleCoefficients.instModuleCarrierTensorProductMulOpposite _root_.OAI.LittleFinitistic.BimoduleCoefficients.instModuleCarrierTensorProductMulOpposite_1 _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.ProductModules.firstModule _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instAddCommGroup _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instRing
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
variable (N : ModuleCat.{u} D)
local notation "A" => TrivSqZeroExt D X

attribute [local instance] OAI.DerivedBar.ParityBridge.instModuleCarrier_solutions_10
local instance instIsScalarTowerCarrier_solutions_10_r1944d5_1 (V : ModuleCat.{u} D) : IsScalarTower k D V :=
  IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
local instance indexedAssemblyComparisonIndexDecidableEq_r1944d5_1 (r n : ℕ) :
    DecidableEq (Index r n) := Classical.decEq _
local instance instModuleTrivSqZeroExtCarrier_solutions_9_r1944d5_1 : Module A N := inflatedModule D X N
local instance instIsScalarTowerTrivSqZeroExtCarrier_solutions_9_r1944d5_1 : IsScalarTower k A N := IsScalarTower.of_algebraMap_smul
    (fun a v => IsScalarTower.algebraMap_smul D a v)
attribute [local instance] OAI.DerivedBar.ParityBridge.indexedAssemblyComparisonShapeDecidableEq
theorem shapeAssembly_injective (r n : ℕ) : Function.Injective (shapeAssembly k D X N r n).hom := by
  intro v w h
  exact (Multibar.Indexed.decomposition k D X N (r+n) r).injective (Subtype.ext h)

end DerivedBar.ParityBridge

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Bar_CountProjective
attribute [-instance] _root_.OAI.DerivedBar.term_finite _root_.OAI.DerivedBar.term_finiteDimensional _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.BimoduleCoefficients.instAddCommGroupCarrierTensorProductMulOpposite _root_.OAI.LittleFinitistic.BimoduleCoefficients.instModuleCarrierTensorProductMulOpposite_1 _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.ProductModules.firstModule _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instAddCommGroup _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
open CategoryTheory CategoryTheory.Limits TensorProduct TrivSqZeroExt
open scoped TensorProduct DirectSum
noncomputable section
namespace DerivedBar
universe u
variable (k D X N : Type u) [Field k] [Ring D] [Algebra k D]
  [AddCommGroup X] [Module k X] [Module D X] [Module Dᵐᵒᵖ X]
  [SMulCommClass D Dᵐᵒᵖ X] [IsScalarTower k D X] [IsScalarTower k Dᵐᵒᵖ X]
  [AddCommGroup N] [Module k N]
open Multibar.Indexed

local instance countProjectiveShapeDecidableEq_r1944d5_1 (n r : ℕ) : DecidableEq (Shape n r) :=
  Classical.decEq _
instance outerTensor_free {n r : ℕ} (p : Shape n r) :
    Module.Free D (outerTensor k D X N p) :=
  Module.Free.of_basis (Algebra.TensorProduct.basis D
    (Module.Free.chooseBasis k (tensor k D X N p)))

instance countWeight_free (n r : ℕ) :
    Module.Free D (SquareZero.twoSidedWeight k D X N n r) :=
  Module.Free.of_equiv (decomposition k D X N n r)

variable [Module (TrivSqZeroExt D X) N] [IsScalarTower k (TrivSqZeroExt D X) N]
  (hN : ∀ (x : X) (v : N), (inr x : TrivSqZeroExt D X) • v = 0)

instance countComplex_projective (r n : ℕ) :
    Projective ((SquareZero.twoSidedWeightComplex k D X N hN r).X n) := by
  change Projective (ModuleCat.of D (SquareZero.twoSidedWeight k D X N n r))
  infer_instance

end DerivedBar

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Bar_CountRetracts
attribute [-instance] _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.BalancedTensor.scalarLeftTower _root_.OAI.LittleFinitistic.BimoduleCoefficients.instAddCommGroupCarrierTensorProductMulOpposite _root_.OAI.LittleFinitistic.BimoduleCoefficients.instModuleCarrierTensorProductMulOpposite _root_.OAI.LittleFinitistic.BimoduleCoefficients.instModuleCarrierTensorProductMulOpposite_1 _root_.OAI.LittleFinitistic.BimoduleCoefficients.towerLeft _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instAddCommGroup _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instRing
attribute [-simp] _root_.OAI.ExternalTensor.Section4.sum_hom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
open CategoryTheory CategoryTheory.Limits HomologicalComplex TrivSqZeroExt
open scoped DirectSum
noncomputable section
namespace DerivedBar.ParityBridge

universe u
variable (k D X : Type u) [Field k] [Ring D] [Algebra k D]
  [AddCommGroup X] [Module k X] [Module D X] [Module Dᵐᵒᵖ X]
  [SMulCommClass D Dᵐᵒᵖ X] [IsScalarTower k D X] [IsScalarTower k Dᵐᵒᵖ X]
local instance countRetractsScalarModule (V : ModuleCat D) : Module k V :=
  BimoduleTensor.scalarModule k D V
local instance countRetractsScalarTower (V : ModuleCat D) : IsScalarTower k D V :=
  IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
variable (N : ModuleCat D)
local notation "A" => TrivSqZeroExt D X
attribute [local instance] OAI.DerivedBar.ParityBridge.countRetractsInflatedModule
local instance countRetractsInflatedScalarTower : IsScalarTower k A N :=
  IsScalarTower.of_algebraMap_smul
    (fun a v => IsScalarTower.algebraMap_smul D a v)
local notation "S" => SquareZero.twoSidedWeightComplex k D X N (inflated_ideal_zero D X N)
local notation "T" => tensorBarComplex k A D N (fstHom k D X)

/-- The original count subcomplex included into the actual balanced tensor bar. -/
def countTensorBarInclusion (r : ℕ) : S r ⟶ T :=
  directSumComplexInclusion D S r ≫
    (SquareZero.tensorCountSplitting k D X N (inflated_ideal_zero D X N)).inv

def countTensorBarProjection (r : ℕ) : T ⟶ S r :=
  (SquareZero.tensorCountSplitting k D X N (inflated_ideal_zero D X N)).hom ≫
    directSumComplexProjection D S r

@[simp] theorem countTensorBar_retract (r : ℕ) :
    countTensorBarInclusion k D X N r ≫ countTensorBarProjection k D X N r = 𝟙 (S r) := by
  simp only [countTensorBarInclusion, countTensorBarProjection, Category.assoc,
    Iso.inv_hom_id_assoc, directSumComplex_inclusion_projection]

end DerivedBar.ParityBridge

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Bar_CountHomologyDetection
attribute [-instance] _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.BalancedTensor.scalarLeftTower _root_.OAI.LittleFinitistic.BimoduleCoefficients.instAddCommGroupCarrierTensorProductMulOpposite _root_.OAI.LittleFinitistic.BimoduleCoefficients.instModuleCarrierTensorProductMulOpposite _root_.OAI.LittleFinitistic.BimoduleCoefficients.instModuleCarrierTensorProductMulOpposite_1 _root_.OAI.LittleFinitistic.BimoduleCoefficients.towerLeft _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instAddCommGroup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
open CategoryTheory CategoryTheory.Limits HomologicalComplex TrivSqZeroExt
noncomputable section
namespace DerivedBar.ParityBridge
universe u
variable (k D X : Type u) [Field k] [Ring D] [Algebra k D]
  [AddCommGroup X] [Module k X] [Module D X] [Module Dᵐᵒᵖ X]
  [SMulCommClass D Dᵐᵒᵖ X] [IsScalarTower k D X] [IsScalarTower k Dᵐᵒᵖ X]
local instance instModuleCarrier_solutions_16 (V : ModuleCat D) : Module k V := BimoduleTensor.scalarModule k D V
local instance instIsScalarTowerCarrier_solutions_16 (V : ModuleCat D) : IsScalarTower k D V :=
  IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
variable (N : ModuleCat D)
local notation "A" => TrivSqZeroExt D X
attribute [local instance] OAI.DerivedBar.ParityBridge.instModuleTrivSqZeroExtCarrier_solutions_15
local instance instIsScalarTowerTrivSqZeroExtCarrier_solutions_15 : IsScalarTower k A N := IsScalarTower.of_algebraMap_smul
    (fun a v => IsScalarTower.algebraMap_smul D a v)
end DerivedBar.ParityBridge

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Bar_CountTorBounds
attribute [-instance] _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.BalancedTensor.scalarLeftTower _root_.OAI.LittleFinitistic.BimoduleCoefficients.instAddCommGroupCarrierTensorProductMulOpposite _root_.OAI.LittleFinitistic.BimoduleCoefficients.instModuleCarrierTensorProductMulOpposite _root_.OAI.LittleFinitistic.BimoduleCoefficients.instModuleCarrierTensorProductMulOpposite_1 _root_.OAI.LittleFinitistic.BimoduleCoefficients.towerLeft _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instAddCommGroup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
open CategoryTheory CategoryTheory.Limits TrivSqZeroExt
noncomputable section
namespace DerivedBar.ParityBridge
universe u
variable (k D X : Type u) [Field k] [Ring D] [Algebra k D]
  [AddCommGroup X] [Module k X] [Module D X] [Module Dᵐᵒᵖ X]
  [SMulCommClass D Dᵐᵒᵖ X] [IsScalarTower k D X] [IsScalarTower k Dᵐᵒᵖ X]
local instance instModuleCarrier_solutions_17 (V : ModuleCat D) : Module k V := BimoduleTensor.scalarModule k D V
local instance instIsScalarTowerCarrier_solutions_17 (V : ModuleCat D) : IsScalarTower k D V :=
  IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
variable (N : ModuleCat D)
local notation "A" => TrivSqZeroExt D X
attribute [local instance] OAI.DerivedBar.ParityBridge.instModuleTrivSqZeroExtCarrier_solutions_16
local instance instIsScalarTowerTrivSqZeroExtCarrier_solutions_16 : IsScalarTower k A N := IsScalarTower.of_algebraMap_smul
    (fun a v => IsScalarTower.algebraMap_smul D a v)
end DerivedBar.ParityBridge

end

end OAI
end



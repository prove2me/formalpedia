-- Prove2me | Definitions.Def_OAIQ023F021
-- name    : OAIQ023F021
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-30T18:42:57.071278+00:00
-- url     : https://prove2.me/theorems/22750a33-0d3f-48fc-9566-926bf86a6980
-- title:
--   Definitions bundle OAIQ023F021 of the split of OpenAI, An algebra of infinite little finitistic dimension (result family 198)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.LittleFinitistic.Main.exists_counterexample`, carved from OpenAI's openai/math development (OpenAI, *An algebra of infinite little finitistic dimension (result family 198)*, OpenAI Math Release, September 23, 2026, result family 198, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 47 declarations of OpenAI's Lean: 8 definitions, 2 instances and 37 theorems. The definitions and types are `OAI.LittleFinitistic.QuadraticEncoding.Representation.Evaluation`, `OAI.LittleFinitistic.QuadraticEncoding.Representation.act`, `OAI.LittleFinitistic.QuadraticEncoding.Representation.pathAction`, `OAI.LittleFinitistic.QuadraticEncoding.arrow01`, `OAI.LittleFinitistic.QuadraticEncoding.arrow12`, `OAI.LittleFinitistic.QuadraticEncoding.lengthTwo`, `OAI.LittleFinitistic.QuadraticEncoding.pathMap`, `OAI.LittleFinitistic.SelectionEncoding.directedAlgebra`.
--
--   **Sources.** They come from these modules of lean/OAI/Algebra, in whole or in part: `Finitistic_Bar_GlobalIndexedComparison`, `Finitistic_Bar_IndexedAssemblyComparison`, `Finitistic_Bar_LeadingBarSuffix`, `Finitistic_Bar_LeadingSuffixFaces`, `Finitistic_Bar_LeadingTotalComparison`, `Finitistic_Bar_LeadingTotalDifferential`, `Finitistic_Bar_RecursiveSuffixCoefficient`, `Finitistic_Bar_RecursiveSuffixEmbedding`, `Finitistic_Bar_RecursiveSuffixFaces`, `Finitistic_Bar_RecursiveSuffixInduction`, `Finitistic_Bar_RecursiveSuffixTotal`, `Finitistic_Bar_SuffixParityFaces`, `Finitistic_Encoding_QuadraticEncoding`, `Finitistic_Localization_EvaluationModule`, `Finitistic_Selection_SelectionEncoding`.
--
--   **Imports.** It imports the bundles `OAIQ023F016` and `OAIQ023F039` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ023F025` and `OAIQ023F026`.
-- source:
--   OpenAI, An algebra of infinite little finitistic dimension (result family 198), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 198; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/An-algebra-of-infinite-little-finitistic-dimension-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Algebra at commit adc7f12

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIQ023F016
import Definitions.Def_OAIQ023F039

section
-- module Solutions.OAIQ023_Fin.Finitistic_Bar_SuffixParityFaces
attribute [-instance] _root_.OAI.DerivedBar.Multibar.patternModule _root_.OAI.DerivedBar.countWeight_free _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.DerivedBar.term_finite _root_.OAI.DerivedBar.term_finiteDimensional _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideModule _root_.OAI.LittleFinitistic.BimoduleCoefficients.instAddCommGroupCarrierTensorProductMulOpposite _root_.OAI.LittleFinitistic.BimoduleCoefficients.instModuleCarrierTensorProductMulOpposite_1 _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instAddCommGroup _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instRing _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated
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

/-- General D-block comparison, including the differential of an arbitrary
positive-length suffix. The second term is the totalization sign, not zero. -/
theorem parity_suffixEmbed (s n : ℕ) (e : M →ₗ[k] term k A N (s+1))
    (he : ∀ (d : D) (v : M), e (d • v) = (inl d : A) • e v)
    (v : term k D M (n+1)) :
    SquareZero.multibarAugmentedDifferential k D X N ((s+1)+n)
      (suffixEmbed k D X N M (s+1) e (n+1) v) =
    suffixEmbed k D X N M (s+1) e n (DerivedBar.differential k D M n v) +
      (-1 : k)^(n+1) • termCast k D X N (show s+(n+1)=(s+1)+n by omega)
        (suffixEmbed k D X N M s
          ((SquareZero.multibarAugmentedDifferential k D X N s).comp e) (n+1) v) := by
  induction n with
  | zero =>
    induction v using OAI.tensorInductionOn with
    | tmul d v =>
      rw [suffixEmbed_tmul, SquareZero.multibarAugmentedDifferential_succ,
        SquareZero.slotParity_base, DerivedBar.differential_zero_tmul,
        suffixEmbed_tmul]
      change (inl d : A) • e v - (inl d : A) ⊗ₜ[k] _ = e (d • v) + (-1:k)^1 • _
      rw [he]
      simp only [pow_one, neg_one_smul, sub_eq_add_neg]
      rfl
    | add v w hv hw => simp only [map_add, hv, hw, smul_add]; abel
  | succ n ih =>
    induction v using OAI.tensorInductionOn with
    | tmul d v =>
      rw [suffixEmbed_tmul]
      change SquareZero.slotParity k D X (inl d) • suffixEmbed k D X N M (s+1) e (n+1) v -
        SquareZero.slotParity k D X (inl d) ⊗ₜ[k]
          SquareZero.multibarAugmentedDifferential k D X N (s+1+n)
            (suffixEmbed k D X N M (s+1) e (n+1) v) = _
      rw [SquareZero.slotParity_base, ih, DerivedBar.differential_succ_tmul,
        map_sub, suffixEmbed_smul k D X N M (s+1) (n+1) e he,
        suffixEmbed_tmul, suffixEmbed_tmul]
      erw [termCast_tmul k D X N (show s+(n+1)=(s+1)+n by omega)
          (show (s+(n+1))+1=((s+1)+n)+1 by omega) (inl d)
          (suffixEmbed k D X N M s ((SquareZero.multibarAugmentedDifferential k D X N s).comp e) (n+1) v)]
      erw [TensorProduct.tmul_add, TensorProduct.tmul_smul]
      have hs : (-1 : k)^(n+1+1) = -((-1 : k)^(n+1)) := by
        rw [pow_succ, mul_neg_one]
      rw [hs]
      erw [neg_smul]
      abel
    | add v w hv hw => simp only [map_add, hv, hw, smul_add]; abel


/-- General two-sided X-bar comparison. Both horizontal and signed suffix
faces are retained; the right D action is the bimodule's original action. -/
theorem parity_idealSuffixEmbed (s n : ℕ) (e : M →ₗ[k] term k A N (s+1))
    (he : ∀ (d : D) (v : M), e (d • v) = (inl d : A) • e v)
    (v : X ⊗[k] term k D M (n+1)) :
    SquareZero.multibarAugmentedDifferential k D X N (((s+1)+n)+1)
      (idealSuffixEmbed k D X N M (s+1) (n+1) e v) =
    -idealSuffixEmbed k D X N M (s+1) n e (BimoduleTensor.barDifferential k D X M n v) +
      (-1 : k)^(n+1) • termCast k D X N (show (s+(n+1))+1=((s+1)+n)+1 by omega)
        (idealSuffixEmbed k D X N M s (n+1)
          ((SquareZero.multibarAugmentedDifferential k D X N s).comp e) v) := by
  induction v using OAI.tensorInductionOn with
  | tmul x v =>
    rw [idealSuffixEmbed_tmul, SquareZero.multibarAugmentedDifferential_succ,
      SquareZero.slotParity_ideal, parity_suffixEmbed k D X N M s n e he,
      BimoduleTensor.barDifferential_tmul, map_sub, idealSuffixEmbed_tmul,
      idealSuffixEmbed_tmul, termCast_tmul k D X N (show s+(n+1)=(s+1)+n by omega)]
    have hn : (-inr x : A) • suffixEmbed k D X N M (s+1) e (n+1) v =
        -((inr x : A) • suffixEmbed k D X N M (s+1) e (n+1) v) :=
      _root_.neg_smul (inr x : A) (suffixEmbed k D X N M (s+1) e (n+1) v)
    rw [hn, ideal_action_suffixEmbed]
    erw [TensorProduct.neg_tmul, TensorProduct.tmul_add, TensorProduct.tmul_smul]
    abel
  | add v w hv hw => simp only [map_add, hv, hw, neg_add, smul_add]; abel

end DerivedBar.ParityBridge

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Bar_LeadingSuffixFaces
attribute [-instance] _root_.OAI.DerivedBar.Multibar.patternModule _root_.OAI.DerivedBar.countWeight_free _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.DerivedBar.term_finite _root_.OAI.DerivedBar.term_finiteDimensional _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideModule _root_.OAI.LittleFinitistic.BimoduleCoefficients.instAddCommGroupCarrierTensorProductMulOpposite _root_.OAI.LittleFinitistic.BimoduleCoefficients.instModuleCarrierTensorProductMulOpposite_1 _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instAddCommGroup _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instRing _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated
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

/-- Exterior D comparison with the genuine free-bar differential and all later
suffix faces. Negating the suffix differential gives the total sign (-1)^i. -/
theorem parity_outerSuffixEmbed (s n : ℕ) (e : M →ₗ[k] term k A N (s+1))
    (he : ∀ (d : D) (v : M), e (d • v) = (inl d : A) • e v)
    (v : D ⊗[k] term k D M (n+1)) :
    SquareZero.multibarTwoSidedDifferential k D X N ((s+1)+n)
      (outerSuffixEmbed k D X N M (s+1) (n+1) e v) =
    outerSuffixEmbed k D X N M (s+1) n e (DerivedBar.differential k D M (n+1) v) +
      (-1 : k)^n • AlgebraTensorModule.lTensor D D
        (termCast k D X N (show s+(n+1)=(s+1)+n by omega))
        (outerSuffixEmbed k D X N M s (n+1)
          ((SquareZero.multibarAugmentedDifferential k D X N s).comp e) v) := by
  induction v using OAI.tensorInductionOn with
  | tmul d v =>
    rw [outerSuffixEmbed_tmul, SquareZero.multibarTwoSidedDifferential_tmul,
      coefficient_suffixEmbed, parity_suffixEmbed k D X N M s n e he,
      DerivedBar.differential_succ_tmul, map_sub, map_smul, outerSuffixEmbed_tmul,
      outerSuffixEmbed_tmul, AlgebraTensorModule.lTensor_tmul]
    erw [TensorProduct.tmul_add, TensorProduct.tmul_smul]
    have hs : (-1 : k)^(n+1) = -((-1 : k)^n) := by rw [pow_succ, mul_neg_one]
    rw [hs]
    have hn : (-((-1 : k)^n)) •
        (d ⊗ₜ[k] termCast k D X N (show s+(n+1)=(s+1)+n by omega)
          (suffixEmbed k D X N M s ((SquareZero.multibarAugmentedDifferential k D X N s).comp e) (n+1) v)) =
        -(((-1 : k)^n) • (d ⊗ₜ[k] termCast k D X N (show s+(n+1)=(s+1)+n by omega)
          (suffixEmbed k D X N M s ((SquareZero.multibarAugmentedDifferential k D X N s).comp e) (n+1) v))) :=
      _root_.neg_smul ((-1:k)^n)
        (d ⊗ₜ[k] termCast k D X N (show s+(n+1)=(s+1)+n by omega)
          (suffixEmbed k D X N M s ((SquareZero.multibarAugmentedDifferential k D X N s).comp e) (n+1) v))
    rw [hn]
    abel
  | add v w hv hw => simp only [map_add, hv, hw, smul_add]; abel

end DerivedBar.ParityBridge

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Bar_RecursiveSuffixEmbedding
attribute [-instance] _root_.OAI.DerivedBar.countWeight_free _root_.OAI.DerivedBar.term_finite _root_.OAI.DerivedBar.term_finiteDimensional _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideModule _root_.OAI.LittleFinitistic.BimoduleCoefficients.instAddCommGroupCarrierTensorProductMulOpposite _root_.OAI.LittleFinitistic.BimoduleCoefficients.instModuleCarrierTensorProductMulOpposite _root_.OAI.LittleFinitistic.BimoduleCoefficients.instModuleCarrierTensorProductMulOpposite_1 _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instAddCommGroup _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instRing _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated
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
/-- The complete finite-sum suffix map has its original D action. -/
theorem innerEmbedding_smul (r n : ℕ) (d : D) (v : RecursiveTotal.flat B Z r n) :
    letI : Module A N := inflatedModule D X N
    innerEmbedding k D X N r n (d • v) =
      (inl d : A) • innerEmbedding k D X N r n v := by
  let : Module A N := inflatedModule D X N
  induction v using DirectSum.induction_on with
  | zero => simp only [map_zero, smul_zero]
  | add v w hv hw => simp only [smul_add, map_add, hv, hw]
  | of t v =>
    change innerEmbedding k D X N r n
      (d • (RecursiveTotal.lof B Z r n t).hom v) =
        (inl d : A) • innerEmbedding k D X N r n ((RecursiveTotal.lof B Z r n t).hom v)
    rw [← map_smul]
    cases r with
    | zero =>
      cases n with
      | zero =>
        simp only [innerEmbedding, RecursiveTotal.lof, ModuleCat.hom_ofHom,
          DirectSum.lof_eq_of]
        erw [toModule_of_scalar, toModule_of_scalar]
        rfl
      | succ n => simp only [innerEmbedding, LinearMap.zero_apply, smul_zero]
    | succ r =>
      rcases t with ⟨⟨⟨i,q⟩,h⟩,t⟩
      erw [innerEmbedding_lof_succ, innerEmbedding_lof_succ, barSuffix_smul,
        termCast_smul]

/-- Every recursive X-leading sum is killed by the square-zero ideal;
the r=0 degree-zero input is killed by the specified inflation. -/
theorem innerEmbedding_ideal_zero (r n : ℕ) (x : X) (v : RecursiveTotal.flat B Z r n) :
    letI : Module A N := inflatedModule D X N
    (inr x : A) • innerEmbedding k D X N r n v = 0 := by
  let : Module A N := inflatedModule D X N
  induction v using DirectSum.induction_on with
  | zero => simp only [map_zero, smul_zero]
  | add v w hv hw => simp only [map_add, smul_add, hv, hw, add_zero]
  | of t v =>
    change (inr x : A) • innerEmbedding k D X N r n
      ((RecursiveTotal.lof B Z r n t).hom v) = 0
    cases r with
    | zero =>
      cases n with
      | zero => exact zero_smul D _
      | succ n => simp only [innerEmbedding, LinearMap.zero_apply, smul_zero]
    | succ r =>
      rcases t with ⟨⟨⟨i,q⟩,h⟩,t⟩
      erw [innerEmbedding_lof_succ, ← termCast_smul, barSuffix_ideal_zero, map_zero]
end DerivedBar.ParityBridge

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Bar_RecursiveSuffixFaces
attribute [-instance] _root_.OAI.DerivedBar.countWeight_free _root_.OAI.DerivedBar.term_finite _root_.OAI.DerivedBar.term_finiteDimensional _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.BalancedTensor.scalarLeftTower _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideModule _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideTower _root_.OAI.LittleFinitistic.BimoduleCoefficients.instAddCommGroupCarrierTensorProductMulOpposite _root_.OAI.LittleFinitistic.BimoduleCoefficients.instModuleCarrierTensorProductMulOpposite _root_.OAI.LittleFinitistic.BimoduleCoefficients.instModuleCarrierTensorProductMulOpposite_1 _root_.OAI.LittleFinitistic.BimoduleCoefficients.towerLeft _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.PDTensor.scalarModuleTower _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instAddCommGroup _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instRing _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated
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

attribute [local instance] OAI.DerivedBar.ParityBridge.instModuleCarrier_solutions_1
attribute [local instance] OAI.DerivedBar.ParityBridge.instIsScalarTowerCarrier_solutions_1
attribute [local instance] OAI.DerivedBar.ParityBridge.instDecidableEqIndex_1
attribute [local instance] OAI.DerivedBar.ParityBridge.instModuleTrivSqZeroExtCarrier_solutions
attribute [local instance] OAI.DerivedBar.ParityBridge.instIsScalarTowerTrivSqZeroExtCarrier_solutions
/-- Positive-block face comparison for the actual categorical bar functor. -/
theorem parity_barSuffix (V : ModuleCat.{u} D) (s i : ℕ)
    (e : V →ₗ[k] term k A N (s+1))
    (he : ∀ (d : D) (v : V), e (d • v) = (inl d : A) • e v)
    (v : ((XB).obj V).X (i+1)) :
    SquareZero.multibarAugmentedDifferential k D X N (((s+1)+i)+1)
      (barSuffix k D X N V (s+1) (i+1) e v) =
    -barSuffix k D X N V (s+1) i e ((((XB).obj V).d (i+1) i).hom v) +
      (-1:k)^(i+1) • termCast k D X N (show (s+(i+1))+1=((s+1)+i)+1 by omega)
        (barSuffix k D X N V s (i+1)
          ((SquareZero.multibarAugmentedDifferential k D X N s).comp e) v) := by
  have h := congrArg (fun g => g.hom v) (Multibar.twoSidedBarObjIso_d k D X V i)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_ofHom] at h
  unfold barSuffix
  simp only [LinearMap.comp_apply, LinearMap.restrictScalars_apply]
  erw [h]
  exact parity_idealSuffixEmbed k D X N V s i e he _

/-- A terminal empty block has zero face by the actual inflation of N. -/
theorem parity_barSuffix_endpoint (V : ModuleCat.{u} D)
    (e : V →ₗ[k] term k A N 0) (v : ((XB).obj V).X 0) :
    SquareZero.multibarAugmentedDifferential k D X N 0
      (barSuffix k D X N V 0 0 e v) = 0 := by
  unfold barSuffix
  simp only [LinearMap.comp_apply, LinearMap.restrictScalars_apply]
  generalize (Multibar.twoSidedBarObjIso k D X V 0).hom.hom v = w
  induction w using OAI.tensorInductionOn with
  | tmul x w =>
    exact SquareZero.multibarAugmented_ideal_endpoint k D X N
      (fun _ v => zero_smul D v) x (e w)
  | add v w hv hw => simp only [map_add, hv, hw, add_zero]

theorem suffixEmbed_id (i : ℕ) (v : term k D N i) :
    suffixEmbed k D X N N 0 LinearMap.id i v =
      termCast k D X N (Nat.zero_add i).symm (baseEmbed k D X N i v) := by
  induction i with
  | zero => rfl
  | succ i ih =>
    induction v using OAI.tensorInductionOn with
    | tmul d v =>
      rw [suffixEmbed_tmul, baseEmbed_tmul, ih]
      exact (termCast_tmul k D X N (Nat.zero_add i).symm
        (show i+1=(0+i)+1 by omega) (inl d) (baseEmbed k D X N i v)).symm
    | add v w hv hw => simp only [map_add, hv, hw]

theorem idealSuffixEmbed_id (i : ℕ) (v : X ⊗[k] term k D N i) :
    idealSuffixEmbed k D X N N 0 i LinearMap.id v =
      termCast k D X N (show i+1=(0+i)+1 by omega) (idealEmbed k D X N i v) := by
  induction v using OAI.tensorInductionOn with
  | tmul x v =>
    rw [idealSuffixEmbed_tmul, idealEmbed_tmul,
      termCast_tmul k D X N (Nat.zero_add i).symm, suffixEmbed_id]
  | add v w hv hw => simp only [map_add, hv, hw]

/-- The terminal positive X bar has exactly minus its original bar differential. -/
theorem parity_barSuffix_terminal (i : ℕ) (v : ((XB).obj N).X (i+1)) :
    SquareZero.multibarAugmentedDifferential k D X N ((0+i)+1)
      (barSuffix k D X N N 0 (i+1) LinearMap.id v) =
    -barSuffix k D X N N 0 i LinearMap.id
      ((((XB).obj N).d (i+1) i).hom v) := by
  have h := congrArg (fun g => g.hom v) (Multibar.twoSidedBarObjIso_d k D X N i)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_ofHom] at h
  unfold barSuffix
  simp only [LinearMap.comp_apply, LinearMap.restrictScalars_apply]
  erw [h]
  rw [idealSuffixEmbed_id, idealSuffixEmbed_id]
  erw [parity_termCast k D X N (show i+1=(0+i)+1 by omega)
    (show (i+1)+1=((0+i)+1)+1 by omega)]
  rw [inflated_parity_idealEmbed, map_neg]

/-- The augmented bottom face vanishes at every recursive depth. -/
theorem innerEmbedding_bottom (r : ℕ) (v : RecursiveTotal.flat B Z (r+1) 0) :
    SquareZero.multibarAugmentedDifferential k D X N r
      (termCast k D X N (show (r+1)+0=r+1 by omega)
        (innerEmbedding k D X N (r+1) 0 v)) = 0 := by
  induction r with
  | zero =>
    induction v using DirectSum.induction_on with
    | zero => simp only [map_zero]
    | add v w hv hw => simp only [map_add, hv, hw, add_zero]
    | of t v =>
      rcases t with ⟨⟨⟨i,q⟩,h⟩,t⟩
      have hi : i=0 := by omega
      have hq : q=0 := by omega
      subst i; subst q
      change SquareZero.multibarAugmentedDifferential k D X N 0
        (innerEmbedding k D X N 1 0 ((RecursiveTotal.lof B Z 1 0 _).hom v)) = 0
      rw [innerEmbedding_lof_succ]
      exact parity_barSuffix_endpoint k D X N _ _ v
  | succ r ih =>
    induction v using DirectSum.induction_on with
    | zero => simp only [map_zero]
    | add v w hv hw => simp only [map_add, hv, hw, add_zero]
    | of t v =>
      rcases t with ⟨⟨⟨i,q⟩,h⟩,t⟩
      have hi : i=0 := by omega
      have hq : q=0 := by omega
      subst i; subst q
      change SquareZero.multibarAugmentedDifferential k D X N (r+1)
        (innerEmbedding k D X N (r+1+1) 0 ((RecursiveTotal.lof B Z (r+1+1) 0 _).hom v)) = 0
      rw [innerEmbedding_lof_succ]
      change SquareZero.multibarAugmentedDifferential k D X N (r+1)
        (barSuffix k D X N _ (r+1) 0 _ v) = 0
      erw [parity_barSuffix_zero k D X N _ r _
        (fun x w => innerEmbedding_ideal_zero k D X N (r+1) 0 x
          ((RecursiveTotal.lof B Z (r+1) 0 t).hom w))]
      have hz : (SquareZero.multibarAugmentedDifferential k D X N r).comp
          ((innerEmbedding k D X N (r+1) 0).comp
            ((RecursiveTotal.lof B Z (r+1) 0 t).hom.restrictScalars k)) = 0 := by
        ext w
        exact ih _
      rw [hz]
      rw [barSuffix_zero]
      rfl
end DerivedBar.ParityBridge

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Bar_LeadingBarSuffix
attribute [-instance] _root_.OAI.DerivedBar.countWeight_free _root_.OAI.DerivedBar.term_finite _root_.OAI.DerivedBar.term_finiteDimensional _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.BalancedTensor.scalarLeftTower _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideModule _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideTower _root_.OAI.LittleFinitistic.BimoduleCoefficients.instAddCommGroupCarrierTensorProductMulOpposite _root_.OAI.LittleFinitistic.BimoduleCoefficients.instModuleCarrierTensorProductMulOpposite _root_.OAI.LittleFinitistic.BimoduleCoefficients.instModuleCarrierTensorProductMulOpposite_1 _root_.OAI.LittleFinitistic.BimoduleCoefficients.towerLeft _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.PDTensor.scalarModuleTower _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instAddCommGroup _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instRing _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated
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
theorem parity_outerBarSuffix (V : ModuleCat.{u} D) (s i : ℕ)
    (e : V →ₗ[k] term k A N (s+1))
    (he : ∀ (d : D) (v : V), e (d • v) = (inl d : A) • e v)
    (v : ((DB).obj V).X (i+1)) :
    SquareZero.multibarTwoSidedDifferential k D X N ((s+1)+i)
      (outerBarSuffix k D X N V (s+1) (i+1) e v) =
    outerBarSuffix k D X N V (s+1) i e ((((DB).obj V).d (i+1) i).hom v) +
      (-1:k)^i • outerCast k D X N (show s+(i+1)=(s+1)+i by omega)
        (outerBarSuffix k D X N V s (i+1)
          ((SquareZero.multibarAugmentedDifferential k D X N s).comp e) v) := by
  have h := congrArg (fun g => g.hom v) (Multibar.freeBarObjIso_d k D V i)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_ofHom] at h
  unfold outerBarSuffix
  simp only [LinearMap.comp_apply]
  erw [h]
  exact parity_outerSuffixEmbed k D X N V s i e he _

theorem outerSuffixEmbed_id (i : ℕ) (v : D ⊗[k] term k D N i) :
    outerSuffixEmbed k D X N N 0 i LinearMap.id v =
      outerCast k D X N (Nat.zero_add i).symm (outerBaseEmbed k D X N i v) := by
  induction v using OAI.tensorInductionOn with
  | tmul d v =>
    rw [outerSuffixEmbed_tmul, suffixEmbed_id]
    rfl
  | add v w hv hw => simp only [map_add, hv, hw]

theorem parity_outerBarSuffix_terminal (i : ℕ) (v : ((DB).obj N).X (i+1)) :
    SquareZero.multibarTwoSidedDifferential k D X N (0+i)
      (outerBarSuffix k D X N N 0 (i+1) LinearMap.id v) =
    outerBarSuffix k D X N N 0 i LinearMap.id ((((DB).obj N).d (i+1) i).hom v) := by
  have h := congrArg (fun g => g.hom v) (Multibar.freeBarObjIso_d k D N i)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_ofHom] at h
  unfold outerBarSuffix
  simp only [LinearMap.comp_apply]
  erw [h]
  rw [outerSuffixEmbed_id, outerSuffixEmbed_id]
  erw [twoSidedParity_outerCast k D X N (Nat.zero_add i).symm
    (show i+1=(0+i)+1 by omega), parity_outerBaseEmbed]
end DerivedBar.ParityBridge

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Bar_RecursiveSuffixInduction
attribute [-instance] _root_.OAI.DerivedBar.countWeight_free _root_.OAI.DerivedBar.term_finite _root_.OAI.DerivedBar.term_finiteDimensional _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.BalancedTensor.scalarLeftTower _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideModule _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideTower _root_.OAI.LittleFinitistic.BimoduleCoefficients.instAddCommGroupCarrierTensorProductMulOpposite _root_.OAI.LittleFinitistic.BimoduleCoefficients.instModuleCarrierTensorProductMulOpposite _root_.OAI.LittleFinitistic.BimoduleCoefficients.instModuleCarrierTensorProductMulOpposite_1 _root_.OAI.LittleFinitistic.BimoduleCoefficients.towerLeft _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.PDTensor.scalarModuleTower _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instAddCommGroup _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instRing _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated
attribute [-simp] _root_.OAI.DerivedBar.ParityBridge.canonicalLinear_apply _root_.OAI.DerivedBar.ParityBridge.outerCast_refl _root_.OAI.ExternalTensor.Section4.sum_hom
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

attribute [local instance] OAI.DerivedBar.ParityBridge.instModuleCarrier_solutions_2
attribute [local instance] OAI.DerivedBar.ParityBridge.instIsScalarTowerCarrier_solutions_2
attribute [local instance] OAI.DerivedBar.ParityBridge.recursiveSuffixInductionIndexDecidableEq
attribute [local instance] OAI.DerivedBar.ParityBridge.instModuleTrivSqZeroExtCarrier_solutions_1
attribute [local instance] OAI.DerivedBar.ParityBridge.instIsScalarTowerTrivSqZeroExtCarrier_solutions_1
theorem innerEmbedding_generator_positive (r n i q : ℕ) (h : i+(q+1)=n+1)
    (t : RecursiveTotal.Index r (q+1))
    (ih : ∀ (v : RecursiveTotal.flat B Z r (q+1)),
      SquareZero.multibarAugmentedDifferential k D X N (r+q)
        (innerEmbedding k D X N r (q+1) v) =
      -innerEmbedding k D X N r q ((RecursiveTotal.differential B Z r q).hom v))
    (v : RecursiveTotal.summand B Z (r+1) (n+1) ⟨⟨⟨i,q+1⟩,h⟩,t⟩) :
    SquareZero.multibarAugmentedDifferential k D X N ((r+1)+n)
      (innerEmbedding k D X N (r+1) (n+1)
        ((RecursiveTotal.lof B Z (r+1) (n+1) ⟨⟨⟨i,q+1⟩,h⟩,t⟩).hom v)) =
    -innerEmbedding k D X N (r+1) n
      ((RecursiveTotal.differential B Z (r+1) n).hom
        ((RecursiveTotal.lof B Z (r+1) (n+1) ⟨⟨⟨i,q+1⟩,h⟩,t⟩).hom v)) := by
  erw [innerEmbedding_differential_lof, neg_add, innerEmbedding_lof_succ]
  have hδ := innerEmbedding_suffix_induction k D X N r q t ih
  let V := RecursiveTotal.summand B Z r (q+1) t
  let e : V →ₗ[k] term k A N ((r+q)+1) :=
    (innerEmbedding k D X N r (q+1)).comp
      ((RecursiveTotal.lof B Z r (q+1) t).hom.restrictScalars k)
  have he : ∀ (d : D) (w : V), e (d • w) = (inl d : A) • e w := by
    intro d w
    change innerEmbedding k D X N r (q+1)
      ((RecursiveTotal.lof B Z r (q+1) t).hom (d • w)) =
        (inl d : A) • innerEmbedding k D X N r (q+1)
          ((RecursiveTotal.lof B Z r (q+1) t).hom w)
    rw [map_smul]
    exact innerEmbedding_smul k D X N r (q+1) d _
  cases i with
  | zero =>
    have hn : n=q := by omega
    subst n
    erw [parity_termCast k D X N (show ((r+(q+1))+0)=(r+1)+q by omega)
      (show ((r+(q+1))+0)+1=((r+1)+q)+1 by omega)]
    erw [parity_barSuffix_zero k D X N V (r+q) e
      (fun x w => innerEmbedding_ideal_zero k D X N r (q+1) x
        ((RecursiveTotal.lof B Z r (q+1) t).hom w))]
    erw [hδ, barSuffix_neg, LinearMap.neg_apply, map_neg, innerEmbedding_vertical]
    simp only [RecursiveTotal.horizontal, ModuleCat.hom_zero, pow_zero, one_smul]
    erw [LinearMap.zero_apply (σ₁₂ := RingHom.id D)
      (M₂ := RecursiveTotal.flat B Z (r+1) q) v]
    simp only [map_zero, neg_zero, zero_add]
    rfl
  | succ i =>
    erw [parity_termCast k D X N (show ((r+(q+1))+(i+1))=(r+1)+n by omega)
      (show ((r+(q+1))+(i+1))+1=((r+1)+n)+1 by omega)]
    erw [parity_barSuffix k D X N V (r+q) i e he]
    simp only [e, hδ, barSuffix_neg, map_add, map_neg, map_smul]
    erw [LinearMap.neg_apply, map_neg, map_neg, smul_neg]
    erw [innerEmbedding_horizontal k D X N r n i (q+1) h t v]
    erw [innerEmbedding_vertical k D X N r n (i+1) q h t (RecursiveTotal.differential B Z r) v]
    erw [termCast_trans k D X N
      (show ((r+q)+(i+1))+1=((r+q+1)+i)+1 by omega)
      (show ((r+q+1)+i)+1=(r+1)+n by omega)]
    rfl

/-- The only remaining generator case has suffix total degree zero. Its tail
face vanishes by the already proved augmented bottom identity. -/
theorem innerEmbedding_generator_bottom (r n i : ℕ) (h : i+0=n+1)
    (t : RecursiveTotal.Index r 0)
    (v : RecursiveTotal.summand B Z (r+1) (n+1) ⟨⟨⟨i,0⟩,h⟩,t⟩) :
    SquareZero.multibarAugmentedDifferential k D X N ((r+1)+n)
      (innerEmbedding k D X N (r+1) (n+1)
        ((RecursiveTotal.lof B Z (r+1) (n+1) ⟨⟨⟨i,0⟩,h⟩,t⟩).hom v)) =
    -innerEmbedding k D X N (r+1) n
      ((RecursiveTotal.differential B Z (r+1) n).hom
        ((RecursiveTotal.lof B Z (r+1) (n+1) ⟨⟨⟨i,0⟩,h⟩,t⟩).hom v)) := by
  have hi : i=n+1 := by omega
  subst i
  erw [innerEmbedding_differential_lof, innerEmbedding_lof_succ]
  simp only [RecursiveTotal.vertical, ModuleCat.hom_zero]
  erw [LinearMap.zero_apply (σ₁₂ := RingHom.id D)
    (M₂ := RecursiveTotal.flat B Z (r+1) n) v]
  simp only [map_zero, add_zero]
  erw [innerEmbedding_horizontal]
  cases r with
  | zero =>
    cases t
    erw [innerEmbedding_zero_lof]
    erw [parity_termCast k D X N (show (0+0)+(n+1)=(0+1)+n by omega)
      (show ((0+0)+(n+1))+1=((0+1)+n)+1 by omega)]
    erw [parity_barSuffix_terminal, map_neg]
    rfl
  | succ r =>
    erw [parity_termCast k D X N (show ((r+1)+0)+(n+1)=((r+1)+1)+n by omega)
      (show (((r+1)+0)+(n+1))+1=(((r+1)+1)+n)+1 by omega)]
    erw [parity_barSuffix k D X N (RecursiveTotal.summand B Z (r+1) 0 t) r n
      ((innerEmbedding k D X N (r+1) 0).comp
        ((RecursiveTotal.lof B Z (r+1) 0 t).hom.restrictScalars k))
      (fun d w => by
        change innerEmbedding k D X N (r+1) 0
          ((RecursiveTotal.lof B Z (r+1) 0 t).hom (d • w)) =
            (inl d : A) • innerEmbedding k D X N (r+1) 0
              ((RecursiveTotal.lof B Z (r+1) 0 t).hom w)
        rw [map_smul]
        exact innerEmbedding_smul k D X N (r+1) 0 d _)]
    have hz : (SquareZero.multibarAugmentedDifferential k D X N r).comp
        ((innerEmbedding k D X N (r+1) 0).comp
          ((RecursiveTotal.lof B Z (r+1) 0 t).hom.restrictScalars k)) = 0 := by
      ext w
      exact innerEmbedding_bottom k D X N r _
    simp only [hz, barSuffix_zero]
    erw [LinearMap.zero_apply]
    simp only [map_zero, smul_zero, add_zero, map_neg]

/-- The canonical inner finite-sum embedding compares the actual independently
recursive differential with minus augmented slot parity, at every depth and degree. -/
theorem innerEmbedding_differential (r n : ℕ) (v : RecursiveTotal.flat B Z r (n+1)) :
    SquareZero.multibarAugmentedDifferential k D X N (r+n)
      (innerEmbedding k D X N r (n+1) v) =
    -innerEmbedding k D X N r n ((RecursiveTotal.differential B Z r n).hom v) := by
  induction r generalizing n with
  | zero =>
    induction v using DirectSum.induction_on with
    | zero => simp only [map_zero, neg_zero]
    | add v w hv hw => simp only [map_add, hv, hw, neg_add]
    | of t v =>
      have hv := innerSummand_positive_input_zero k D X N 0 (n+1) t (by simp [RecursiveTotal.inputDegree]) v
      subst v
      simp only [map_zero, neg_zero]
  | succ r ih =>
    induction v using DirectSum.induction_on with
    | zero => simp only [map_zero, neg_zero]
    | add v w hv hw => simp only [map_add, hv, hw, neg_add]
    | of t v =>
      rcases t with ⟨⟨⟨i,q⟩,h⟩,t⟩
      change SquareZero.multibarAugmentedDifferential k D X N ((r+1)+n)
        (innerEmbedding k D X N (r+1) (n+1)
          ((RecursiveTotal.lof B Z (r+1) (n+1) ⟨⟨⟨i,q⟩,h⟩,t⟩).hom v)) = _
      cases q with
      | zero => exact innerEmbedding_generator_bottom k D X N r n i h t v
      | succ q => exact innerEmbedding_generator_positive k D X N r n i q h t (ih q) v
end DerivedBar.ParityBridge

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Bar_RecursiveSuffixTotal
attribute [-instance] _root_.OAI.DerivedBar.countWeight_free _root_.OAI.DerivedBar.term_finite _root_.OAI.DerivedBar.term_finiteDimensional _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideModule _root_.OAI.LittleFinitistic.BimoduleCoefficients.instAddCommGroupCarrierTensorProductMulOpposite _root_.OAI.LittleFinitistic.BimoduleCoefficients.instModuleCarrierTensorProductMulOpposite _root_.OAI.LittleFinitistic.BimoduleCoefficients.instModuleCarrierTensorProductMulOpposite_1 _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instAddCommGroup _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instRing _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated
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
local instance recursiveSuffixTotalIndexDecidableEq_r849486_1 (r n : ℕ) :
    DecidableEq (RecursiveTotal.Index r n) := Classical.decEq _
attribute [local instance] OAI.DerivedBar.ParityBridge.instModuleTrivSqZeroExtCarrier_solutions_2
attribute [local instance] OAI.DerivedBar.ParityBridge.instIsScalarTowerTrivSqZeroExtCarrier_solutions_2
theorem innerTotalEmbedding_differential (r n : ℕ)
    (v : (RecursiveTotal.iter B Z r).X (n+1)) :
    SquareZero.multibarAugmentedDifferential k D X N (r+n)
      (innerTotalEmbedding k D X N r (n+1) v) =
    -innerTotalEmbedding k D X N r n (((RecursiveTotal.iter B Z r).d (n+1) n).hom v) := by
  obtain ⟨w,rfl⟩ := (RecursiveTotal.flattenIso B Z r (n+1) (𝟭 _)).toLinearEquiv.symm.surjective v
  change SquareZero.multibarAugmentedDifferential k D X N (r+n)
    (innerTotalEmbedding k D X N r (n+1) ((RecursiveTotal.assemble B Z r (n+1)).hom w)) = _
  rw [innerTotalEmbedding_assemble, innerEmbedding_differential]
  have h := congrArg (fun f => f.hom w) (RecursiveTotal.differential_assemble B Z r n)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h
  erw [← h, innerTotalEmbedding_assemble]

theorem innerTotalEmbedding_smul (r n : ℕ) (d : D)
    (v : (RecursiveTotal.iter B Z r).X n) :
    innerTotalEmbedding k D X N r n (d • v) =
      (inl d : A) • innerTotalEmbedding k D X N r n v := by
  change innerEmbedding k D X N r n
    ((RecursiveTotal.flattenIso B Z r n (𝟭 _)).hom.hom (d • v)) =
      (inl d : A) • innerEmbedding k D X N r n
        ((RecursiveTotal.flattenIso B Z r n (𝟭 _)).hom.hom v)
  rw [map_smul]
  exact innerEmbedding_smul k D X N r n d _

theorem innerTotalEmbedding_bottom (r : ℕ) (v : (RecursiveTotal.iter B Z (r+1)).X 0) :
    SquareZero.multibarAugmentedDifferential k D X N r
      (innerTotalEmbedding k D X N (r+1) 0 v) = 0 :=
  innerEmbedding_bottom k D X N r _

end DerivedBar.ParityBridge

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Bar_RecursiveSuffixCoefficient
attribute [-instance] _root_.OAI.DerivedBar.countWeight_free _root_.OAI.DerivedBar.term_finite _root_.OAI.DerivedBar.term_finiteDimensional _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideModule _root_.OAI.LittleFinitistic.BimoduleCoefficients.instAddCommGroupCarrierTensorProductMulOpposite _root_.OAI.LittleFinitistic.BimoduleCoefficients.instModuleCarrierTensorProductMulOpposite _root_.OAI.LittleFinitistic.BimoduleCoefficients.instModuleCarrierTensorProductMulOpposite_1 _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instAddCommGroup _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instRing _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated
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

attribute [local instance] OAI.DerivedBar.ParityBridge.instModuleCarrier_solutions_4
attribute [local instance] OAI.DerivedBar.ParityBridge.instIsScalarTowerCarrier_solutions_4
attribute [local instance] OAI.DerivedBar.ParityBridge.recursiveSuffixCoefficientIndexDecidableEq
local instance instModuleTrivSqZeroExtCarrier_solutions_3_r849486_1 : Module A N := inflatedModule D X N
local instance instIsScalarTowerTrivSqZeroExtCarrier_solutions_3_r849486_1 : IsScalarTower k A N := IsScalarTower.of_algebraMap_smul
    (fun a v => IsScalarTower.algebraMap_smul D a v)
/-- The exterior endpoint vanishes at every positive suffix degree, including
zero input summands when no X has yet been inserted. -/
theorem innerEmbedding_coefficient_of_pos (r n s : ℕ) (hs : r+n=s+1)
    (v : RecursiveTotal.flat B Z r n) :
    FreeBaseChange.coefficient (fstHom k D X) (term k A N s)
      (termCast k D X N hs (innerEmbedding k D X N r n v)) = 0 := by
  cases r with
  | zero =>
    cases n with
    | zero => omega
    | succ n => simp only [innerEmbedding, LinearMap.zero_apply, map_zero]
  | succ r =>
    induction v using DirectSum.induction_on with
    | zero => simp only [map_zero]
    | add v w hv hw => simp only [map_add, hv, hw, add_zero]
    | of t v =>
      rcases t with ⟨⟨⟨i,q⟩,h⟩,t⟩
      change FreeBaseChange.coefficient (fstHom k D X) (term k A N s)
        (termCast k D X N hs (innerEmbedding k D X N (r+1) n
          ((RecursiveTotal.lof B Z (r+1) n ⟨⟨⟨i,q⟩,h⟩,t⟩).hom v))) = 0
      erw [innerEmbedding_lof_succ k D X N r n i q h t v]
      erw [termCast_trans k D X N (show ((r+q)+i)+1=(r+1)+n by omega) hs]
      erw [coefficient_termCast k D X N (show (r+q)+i=s by omega)
        (show ((r+q)+i)+1=s+1 by omega)]
      erw [barSuffix_coefficient_zero k D X N (RecursiveTotal.summand B Z r q t)
        (r+q) i _ v]
      exact map_zero _

theorem innerTotalEmbedding_coefficient_of_pos (r n s : ℕ) (hs : r+n=s+1)
    (v : (RecursiveTotal.iter B Z r).X n) :
    FreeBaseChange.coefficient (fstHom k D X) (term k A N s)
      (termCast k D X N hs (innerTotalEmbedding k D X N r n v)) = 0 :=
  innerEmbedding_coefficient_of_pos k D X N r n s hs _

end DerivedBar.ParityBridge

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Bar_LeadingTotalDifferential
attribute [-instance] _root_.OAI.DerivedBar.countWeight_free _root_.OAI.DerivedBar.term_finite _root_.OAI.DerivedBar.term_finiteDimensional _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.BalancedTensor.scalarLeftTower _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideModule _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideTower _root_.OAI.LittleFinitistic.BimoduleCoefficients.instAddCommGroupCarrierTensorProductMulOpposite _root_.OAI.LittleFinitistic.BimoduleCoefficients.instModuleCarrierTensorProductMulOpposite _root_.OAI.LittleFinitistic.BimoduleCoefficients.instModuleCarrierTensorProductMulOpposite_1 _root_.OAI.LittleFinitistic.BimoduleCoefficients.towerLeft _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.PDTensor.scalarModuleTower _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instAddCommGroup _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instRing _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated
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
attribute [local instance] OAI.DerivedBar.ParityBridge.instIsScalarTowerCarrier_solutions_6
local instance instModuleTrivSqZeroExtCarrier_solutions_5_r849486_1 : Module A N := inflatedModule D X N
local instance instIsScalarTowerTrivSqZeroExtCarrier_solutions_5_r849486_1 : IsScalarTower k A N := IsScalarTower.of_algebraMap_smul
    (fun a v => IsScalarTower.algebraMap_smul D a v)
theorem leadingTotalEmbedding_d₂ (r n i q : ℕ) (h : i+(q+1)=n+1)
    (v : (((DB).obj ((I r).X (q+1))).X i)) :
    (((K (I r)).d₂ c i (q+1) n ≫ leadingTotalEmbedding k D X N r n).hom v) =
    (-1:k)^i • outerCast k D X N (show (r+q)+i=r+n by omega)
      (outerBarSuffix k D X N ((I r).X (q+1)) (r+q) i
        ((innerTotalEmbedding k D X N r q).comp
          (((I r).d (q+1) q).hom.restrictScalars k)) v) := by
  rw [HomologicalComplex₂.d₂_eq _ _ i (by rfl : (c).Rel (q+1) q) n (by change i+q=n; omega)]
  change ((((-1:ℤˣ)^i) • (((DB).map ((I r).d (q+1) q)).f i ≫
    (K (I r)).ιTotal c i q n (by change i+q=n; omega))) ≫ leadingTotalEmbedding k D X N r n).hom v = _
  erw [Linear.units_smul_comp, Category.assoc, leadingTotalEmbedding_ι]
  change ((-1:ℤˣ)^i) •
    outerCast k D X N _
      (outerBarSuffix k D X N ((I r).X q) (r+q) i (innerTotalEmbedding k D X N r q)
        ((((DB).map ((I r).d (q+1) q)).f i).hom v)) = _
  rw [totalSign_smul k (D ⊗[k] term k A N (r+n)), outerBarSuffix_map]

end DerivedBar.ParityBridge

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Bar_LeadingTotalComparison
attribute [-instance] _root_.OAI.DerivedBar.countWeight_free _root_.OAI.DerivedBar.term_finite _root_.OAI.DerivedBar.term_finiteDimensional _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.BalancedTensor.scalarLeftTower _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideModule _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideTower _root_.OAI.LittleFinitistic.BimoduleCoefficients.instAddCommGroupCarrierTensorProductMulOpposite _root_.OAI.LittleFinitistic.BimoduleCoefficients.instModuleCarrierTensorProductMulOpposite _root_.OAI.LittleFinitistic.BimoduleCoefficients.instModuleCarrierTensorProductMulOpposite_1 _root_.OAI.LittleFinitistic.BimoduleCoefficients.towerLeft _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.PDTensor.scalarModuleTower _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instAddCommGroup _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instRing _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated
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

attribute [local instance] OAI.DerivedBar.ParityBridge.instModuleCarrier_solutions_7
attribute [local instance] OAI.DerivedBar.ParityBridge.instIsScalarTowerCarrier_solutions_7
attribute [local instance] OAI.DerivedBar.ParityBridge.instModuleTrivSqZeroExtCarrier_solutions_6
attribute [local instance] OAI.DerivedBar.ParityBridge.instIsScalarTowerTrivSqZeroExtCarrier_solutions_6
theorem leadingTotalComparison_positive (r n i q : ℕ) (h : i+(q+1)=n+1)
    (v : (((DB).obj ((I r).X (q+1))).X i)) :
    SquareZero.multibarTwoSidedDifferential k D X N (r+n)
      (outerCast k D X N (show (r+(q+1))+i=r+(n+1) by omega)
        (outerBarSuffix k D X N ((I r).X (q+1)) (r+(q+1)) i
          (innerTotalEmbedding k D X N r (q+1)) v)) =
    (((K (I r)).d₁ c i (q+1) n ≫ leadingTotalEmbedding k D X N r n).hom v) +
      (((K (I r)).d₂ c i (q+1) n ≫ leadingTotalEmbedding k D X N r n).hom v) := by
  have hδ : (SquareZero.multibarAugmentedDifferential k D X N (r+q)).comp
      (innerTotalEmbedding k D X N r (q+1)) =
    -((innerTotalEmbedding k D X N r q).comp (((I r).d (q+1) q).hom.restrictScalars k)) := by
    ext w
    exact innerTotalEmbedding_differential k D X N r q w
  cases i with
  | zero =>
    have hn : n=q := by omega
    subst n
    simp only [Nat.add_zero, outerCast_refl, LinearMap.id_apply]
    erw [parity_outerBarSuffix_zero k D X N ((I r).X (q+1)) (r+q)
      (innerTotalEmbedding k D X N r (q+1))
      (fun w => innerTotalEmbedding_coefficient_of_pos k D X N r (q+1) (r+q) rfl w)]
    rw [hδ, outerBarSuffix_neg, LinearMap.neg_apply, neg_neg]
    rw [leadingTotalEmbedding_d₁_zero]
    erw [leadingTotalEmbedding_d₂ k D X N r q 0 q h v]
    simp only [ModuleCat.hom_zero,
      pow_zero, one_smul, Nat.add_zero, outerCast_refl, LinearMap.id_apply]
    erw [LinearMap.zero_apply (σ₁₂ := RingHom.id D)
      (M₂ := D ⊗[k] term k A N (r+q)) v, zero_add]
  | succ i =>
    erw [twoSidedParity_outerCast k D X N
      (show (r+(q+1))+i=r+n by omega)
      (show ((r+(q+1))+i)+1=(r+n)+1 by omega)]
    erw [parity_outerBarSuffix k D X N ((I r).X (q+1)) (r+q) i
      (innerTotalEmbedding k D X N r (q+1)) (innerTotalEmbedding_smul k D X N r (q+1))]
    simp only [hδ, outerBarSuffix_neg, LinearMap.neg_apply, map_add, outerCast_smul, map_neg]
    erw [leadingTotalEmbedding_d₁ k D X N r n i (q+1) h v]
    erw [leadingTotalEmbedding_d₂ k D X N r n (i+1) q h v]
    apply congrArg₂ (· + ·) (by rfl)
    let w := outerBarSuffix k D X N ((I r).X (q+1)) (r+q) (i+1)
      ((innerTotalEmbedding k D X N r q).comp (((I r).d (q+1) q).hom.restrictScalars k)) v
    have hc := outerCast_trans k D X N
      (show (r+q)+(i+1)=(r+q+1)+i by omega)
      (show (r+q+1)+i=r+n by omega) w
    change (-1:k)^i • -(outerCast k D X N (show (r+q+1)+i=r+n by omega)
      (outerCast k D X N (show (r+q)+(i+1)=(r+q+1)+i by omega) w)) =
      (-1:k)^(i+1) • outerCast k D X N (show (r+q)+(i+1)=r+n by omega) w
    rw [hc]
    have hs : (-1:k)^(i+1) = -((-1:k)^i) := by rw [pow_succ, mul_neg_one]
    rw [hs]
    exact (smul_neg _ _).trans (_root_.neg_smul _ _).symm

theorem leadingTotalComparison_bottom (r n i : ℕ) (h : i+0=n+1)
    (v : (((DB).obj ((I r).X 0)).X i)) :
    SquareZero.multibarTwoSidedDifferential k D X N (r+n)
      (outerCast k D X N (show (r+0)+i=r+(n+1) by omega)
        (outerBarSuffix k D X N ((I r).X 0) (r+0) i
          (innerTotalEmbedding k D X N r 0) v)) =
    (((K (I r)).d₁ c i 0 n ≫ leadingTotalEmbedding k D X N r n).hom v) +
      (((K (I r)).d₂ c i 0 n ≫ leadingTotalEmbedding k D X N r n).hom v) := by
  have hi : i=n+1 := by omega
  subst i
  simp only [Nat.add_zero, outerCast_refl, LinearMap.id_apply]
  rw [leadingTotalEmbedding_d₂_zero]
  simp only [ModuleCat.hom_zero]
  erw [LinearMap.zero_apply (σ₁₂ := RingHom.id D)
    (M₂ := D ⊗[k] term k A N (r+n)) v]
  simp only [add_zero]
  erw [leadingTotalEmbedding_d₁ k D X N r n n 0 h v]
  simp only [Nat.add_zero, outerCast_refl, LinearMap.id_apply]
  cases r with
  | zero =>
    rw [innerTotalEmbedding_zero]
    exact parity_outerBarSuffix_terminal k D X N n v
  | succ r =>
    erw [parity_outerBarSuffix k D X N ((I (r+1)).X 0) r n
      (innerTotalEmbedding k D X N (r+1) 0) (innerTotalEmbedding_smul k D X N (r+1) 0)]
    have hz : (SquareZero.multibarAugmentedDifferential k D X N r).comp
      (innerTotalEmbedding k D X N (r+1) 0) = 0 := by
      ext w
      exact innerTotalEmbedding_bottom k D X N r w
    simp only [hz, outerBarSuffix_zero, LinearMap.zero_apply, map_zero, smul_zero, add_zero]

/-- The canonical leading total embedding intertwines its original total
horizontal/vertical differential with the literal square-zero-extension faces. -/
theorem leadingTotalEmbedding_differential (r n : ℕ) :
    leadingTotalEmbedding k D X N r (n+1) ≫
      ModuleCat.ofHom (SquareZero.multibarTwoSidedDifferential k D X N (r+n)) =
    (barTotal k D (I r)).d (n+1) n ≫ leadingTotalEmbedding k D X N r n := by
  apply HomologicalComplex₂.total.hom_ext
  intro i q h
  erw [← Category.assoc, leadingTotalEmbedding_ι, leadingTotalEmbedding_ι_d]
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro v
  change SquareZero.multibarTwoSidedDifferential k D X N (r+n)
    (outerCast k D X N _ (outerBarSuffix k D X N ((I r).X q) (r+q) i
      (innerTotalEmbedding k D X N r q) v)) = _
  cases q with
  | zero => exact leadingTotalComparison_bottom k D X N r n i h v
  | succ q => exact leadingTotalComparison_positive k D X N r n i q h v
end DerivedBar.ParityBridge

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Bar_IndexedAssemblyComparison
attribute [-instance] _root_.OAI.DerivedBar.countWeight_free _root_.OAI.DerivedBar.outerTensor_free _root_.OAI.DerivedBar.term_finite _root_.OAI.DerivedBar.term_finiteDimensional _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideModule _root_.OAI.LittleFinitistic.BimoduleCoefficients.instAddCommGroupCarrierTensorProductMulOpposite _root_.OAI.LittleFinitistic.BimoduleCoefficients.instModuleCarrierTensorProductMulOpposite _root_.OAI.LittleFinitistic.BimoduleCoefficients.instModuleCarrierTensorProductMulOpposite_1 _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instAddCommGroup _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instRing _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated
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
local instance instIsScalarTowerCarrier_solutions_10_r849486_1 (V : ModuleCat.{u} D) : IsScalarTower k D V :=
  IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
local instance indexedAssemblyComparisonIndexDecidableEq_r849486_1 (r n : ℕ) :
    DecidableEq (Index r n) := Classical.decEq _
local instance instModuleTrivSqZeroExtCarrier_solutions_9_r849486_1 : Module A N := inflatedModule D X N
local instance instIsScalarTowerTrivSqZeroExtCarrier_solutions_9_r849486_1 : IsScalarTower k A N := IsScalarTower.of_algebraMap_smul
    (fun a v => IsScalarTower.algebraMap_smul D a v)
attribute [local instance] OAI.DerivedBar.ParityBridge.indexedAssemblyComparisonShapeDecidableEq
/-- The new embedding is exactly the old Shape assembly after the old inverse
coordinates. No new differential or replacement coordinate system is used. -/
theorem moduleFlatCoordinates_inv_flatEmbedding (r n : ℕ) :
    (moduleFlatCoordinates k D X N r n).inv ≫ flatEmbedding k D X N r n =
      shapeAssembly k D X N r n := by
  apply ModuleCat.hom_ext
  apply DirectSum.linearMap_ext
  intro p
  change (ModuleCat.ofHom (DirectSum.lof D _ (Multibar.Indexed.outerTensor k D X N) p) ≫
    (moduleFlatCoordinates k D X N r n).inv ≫ flatEmbedding k D X N r n).hom =
    (ModuleCat.ofHom (DirectSum.lof D _ (Multibar.Indexed.outerTensor k D X N) p) ≫
      shapeAssembly k D X N r n).hom
  apply congrArg ModuleCat.Hom.hom
  exact assembly_eq (moduleFlatCoordinates_inv_lof k D X N r n p)
    (flatEmbedding_supported k D X N r n ((moduleShapeEquiv r n).symm p))
    (reindexedModuleSummand_assembly k D X N r n p) (shapeAssembly_lof k D X N r n p)

theorem flatEmbedding_coordinates (r n : ℕ) : flatEmbedding k D X N r n =
    (moduleFlatCoordinates k D X N r n).hom ≫ shapeAssembly k D X N r n := by
  apply (cancel_epi (moduleFlatCoordinates k D X N r n).inv).mp
  rw [moduleFlatCoordinates_inv_flatEmbedding, Iso.inv_hom_id_assoc]
end DerivedBar.ParityBridge

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Bar_GlobalIndexedComparison
attribute [-instance] _root_.OAI.DerivedBar.countWeight_free _root_.OAI.DerivedBar.outerTensor_free _root_.OAI.DerivedBar.term_finite _root_.OAI.DerivedBar.term_finiteDimensional _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideModule _root_.OAI.LittleFinitistic.BimoduleCoefficients.instAddCommGroupCarrierTensorProductMulOpposite _root_.OAI.LittleFinitistic.BimoduleCoefficients.instModuleCarrierTensorProductMulOpposite _root_.OAI.LittleFinitistic.BimoduleCoefficients.instModuleCarrierTensorProductMulOpposite_1 _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.ProductModules.firstModule _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instAddCommGroup _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instRing _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated
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
local notation "Z" => Functor.obj (ChainComplex.single₀ (ModuleCat D)) N

attribute [local instance] OAI.DerivedBar.ParityBridge.instModuleCarrier_solutions_11
attribute [local instance] OAI.DerivedBar.ParityBridge.instIsScalarTowerCarrier_solutions_11
local instance globalIndexedComparisonIndexDecidableEq_r849486_1 (r n : ℕ) :
    DecidableEq (Index r n) := Classical.decEq _
attribute [local instance] OAI.DerivedBar.ParityBridge.instModuleTrivSqZeroExtCarrier_solutions_10
attribute [local instance] OAI.DerivedBar.ParityBridge.instIsScalarTowerTrivSqZeroExtCarrier_solutions_10
/-- The full leading comparison transferred through the actual flattening. -/
theorem flatEmbedding_differential (r n : ℕ) :
    flatEmbedding k D X N r (n+1) ≫
      ModuleCat.ofHom (SquareZero.multibarTwoSidedDifferential k D X N (r+n)) =
    RecursiveTotal.differential (leadingBarSequence k D X r) Z (r+1) n ≫ flatEmbedding k D X N r n := by
  simp only [flatEmbedding, Category.assoc, leadingTotalEmbedding_differential]
  rw [← eqToHom_chain_d_assoc (h := leadingIter_total k D X N r)]
  rw [← Category.assoc, ← differential_assemble, Category.assoc]

/-- The original Shape differential intertwines the independently defined literal
parity faces through the original tensor-block assembly. -/
theorem indexedDifferential_assembly (r n : ℕ) :
    indexedDifferential k D X N r n ≫ shapeAssembly k D X N r n =
      shapeAssembly k D X N r (n+1) ≫
        ModuleCat.ofHom (SquareZero.multibarTwoSidedDifferential k D X N (r+n)) := by
  simp only [indexedDifferential, flatLeadingMultibar, flatComplex, ChainComplex.of_d]
  exact conjugated_differential_comp _ _ _ _ _ _ _ _
    (flatEmbedding_coordinates k D X N r n)
    (moduleFlatCoordinates_inv_flatEmbedding k D X N r (n+1))
    (flatEmbedding_differential k D X N r n)

/-- The global comparison identifies the independently defined recursive differential,
Shape coordinates, signed block differential, and both sign identities. -/
theorem globalIndexedComparison (r n : ℕ) :
    (indexedDifferential k D X N r n).hom =
      (-1:k)^r • Multibar.Indexed.blockDifferential k D X N
        (fun x v => inflated_ideal_zero D X N x v) (r+n) r := by
  apply LinearMap.ext
  intro v
  apply shapeAssembly_injective k D X N r n
  have hd := congrArg (fun f => f.hom v) (indexedDifferential_assembly k D X N r n)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_ofHom] at hd
  rw [hd]
  rw [Multibar.Indexed.blockDifferential_eq_explicit]
  change SquareZero.multibarTwoSidedDifferential k D X N (r+n)
      (Multibar.Indexed.decomposition k D X N (r+(n+1)) r v).val =
    (Multibar.Indexed.decomposition k D X N (r+n) r
      ((-1:k)^r • ((Multibar.Indexed.decomposition k D X N (r+n) r).symm
        ((-1:k)^r • SquareZero.multibarCountDifferential k D X N
          (fun x v => inflated_ideal_zero D X N x v) (r+n) r
          (Multibar.Indexed.decomposition k D X N (r+(n+1)) r v))))).val
  have hs := ((Multibar.Indexed.decomposition k D X N (r+n) r).toLinearMap.restrictScalars k).map_smul
    ((-1:k)^r) ((Multibar.Indexed.decomposition k D X N (r+n) r).symm
        ((-1:k)^r • SquareZero.multibarCountDifferential k D X N
          (fun x v => inflated_ideal_zero D X N x v) (r+n) r
          (Multibar.Indexed.decomposition k D X N (r+(n+1)) r v)))
  change Multibar.Indexed.decomposition k D X N (r+n) r (_ • _) =
    _ • Multibar.Indexed.decomposition k D X N (r+n) r _ at hs
  rw [hs, LinearEquiv.apply_symm_apply, smul_smul, ← mul_pow]
  simp only [neg_one_mul, neg_neg, one_pow, one_smul]
  rfl
end DerivedBar.ParityBridge

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Encoding_QuadraticEncoding
attribute [-instance] _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.BimoduleBalancedTensor.leftModule _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated
attribute [-simp] _root_.OAI.ExternalTensor.Section4.sum_hom _root_.OAI.LittleFinitistic.CornerProjection.projection_apply _root_.OAI.LittleFinitistic.QuadraticEncoding.Representation.arrowAction_basis _root_.OAI.LittleFinitistic.QuadraticEncoding.Representation.rawPathAction_tmul _root_.OAI.LittleFinitistic.QuotientAction.quotientAction_generator _root_.OAI.LittleFinitistic.TensorArrowSum.insertion_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open scoped TensorProduct
namespace LittleFinitistic.QuadraticEncoding
universe u v
variable {k : Type u} [Field k] {d t : ℕ}

variable (P : Relations k d t)

/-- Includes a length-two residue class as the 0-to-2 component. -/
def lengthTwo : (Paths k d ⧸ relationSpace P) →ₗ[k] B P where
  toFun z := (0, 0, 0, 0, 0, z)
  map_add' x y := by
    change ((0, 0, 0, 0, 0, x+y) : B P) = (0, 0, 0, 0, 0, x) + (0, 0, 0, 0, 0, y)
    rw [ThreeVertexAlgebra.add_eq (composition P)]
    simp
  map_smul' c x := by
    change ((0, 0, 0, 0, 0, c • x) : B P) = c • (0, 0, 0, 0, 0, x)
    rw [ThreeVertexAlgebra.smul_eq (composition P)]
    simp

def pathMap : Paths k d →ₗ[k] B P := (lengthTwo P).comp (relationSpace P).mkQ

/-- Arrows s,a_1,...,a_d from vertex 0 to 1; index zero is s. -/
def arrow01 (i : Fin (d + 1)) : B P := (0, 0, 0, basis i, 0, 0)
/-- Arrows s',a'_1,...,a'_d from vertex 1 to 2; index zero is s'. -/
def arrow12 (i : Fin (d + 1)) : B P := (0, 0, 0, 0, basis i, 0)

end LittleFinitistic.QuadraticEncoding

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Localization_EvaluationModule
attribute [-instance] _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.BimoduleBalancedTensor.leftModule _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated
attribute [-simp] _root_.OAI.ExternalTensor.Section4.sum_hom _root_.OAI.LittleFinitistic.QuotientAction.quotientAction_generator _root_.OAI.LittleFinitistic.TensorArrowSum.insertion_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open scoped TensorProduct
namespace LittleFinitistic.QuadraticEncoding
universe u v
variable {k : Type u} [Field k] {d t : ℕ}
variable {Y : Type v} [AddCommGroup Y] [Module k Y]

namespace Representation
variable {P : Relations k d t} (X : Representation P Y)

 theorem relations_killed : relationSpace P ≤ X.rawPathAction.ker := by
  rw [relationSpace, Submodule.span_le]
  rintro z (⟨h, rfl⟩ | ⟨j, rfl⟩)
  · simp [LinearMap.mem_ker, commutation]
  · simpa [LinearMap.mem_ker, homogenized] using X.relation j

/-- The actual descended length-two action, using the proved relation ideal. -/
def pathAction : (Paths k d ⧸ relationSpace P) →ₗ[k] Module.End k Y :=
  (relationSpace P).liftQ X.rawPathAction X.relations_killed

@[simp] theorem pathAction_mk (z : Paths k d) :
    X.pathAction ((relationSpace P).mkQ z) = X.rawPathAction z := rfl

@[simp] theorem pathAction_composition (w v : Arrows k d) :
    X.pathAction (composition P w v) = X.arrowAction w * X.arrowAction v := rfl

/-- Three copies of Y, with its representation kept in the type. -/
def Evaluation (_X : Representation P Y) := Y × Y × Y
instance instAddCommGroupEvaluation : AddCommGroup X.Evaluation := inferInstanceAs (AddCommGroup (Y × Y × Y))
instance instModuleEvaluation : Module k X.Evaluation := inferInstanceAs (Module k (Y × Y × Y))

@[simp] theorem evaluation_add (y z : X.Evaluation) :
    y + z = (y.1+z.1,y.2.1+z.2.1,y.2.2+z.2.2) := rfl
@[simp] theorem evaluation_zero : (0 : X.Evaluation) = (0,0,0) := rfl
@[simp] theorem evaluation_smul (c : k) (y : X.Evaluation) :
    c • y = (c • y.1,c • y.2.1,c • y.2.2) := rfl

def act (a : B P) (y : X.Evaluation) : X.Evaluation :=
  (a.1 • y.1,
   X.arrowAction a.2.2.2.1 y.1 + a.2.1 • y.2.1,
   X.pathAction a.2.2.2.2.2 y.1 + X.arrowAction a.2.2.2.2.1 y.2.1 + a.2.2.1 • y.2.2)

end Representation
end LittleFinitistic.QuadraticEncoding

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Selection_SelectionEncoding
attribute [-instance] _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace LittleFinitistic.SelectionEncoding
open QuadraticPresentation QuadraticEncoding

universe u v w
variable {k : Type u} {R : Type v} [Field k] [Ring R] [Algebra k R] (E : Encoding k R)

abbrev directedAlgebra := B E.relations

end LittleFinitistic.SelectionEncoding

end OAI
end



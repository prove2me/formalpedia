-- Prove2me | Definitions.Def_OAIQ023F016
-- name    : OAIQ023F016
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-30T16:13:35.893244+00:00
-- url     : https://prove2.me/theorems/d5cb0256-647a-467e-a4c8-90cc9169f7b9
-- title:
--   Definitions bundle OAIQ023F016 of the split of OpenAI, An algebra of infinite little finitistic dimension (result family 198)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.LittleFinitistic.Main.exists_counterexample`, carved from OpenAI's openai/math development (OpenAI, *An algebra of infinite little finitistic dimension (result family 198)*, OpenAI Math Release, September 23, 2026, result family 198, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 59 declarations of OpenAI's Lean: 8 definitions, 1 instance and 50 theorems. The definitions and types are `OAI.DerivedBar.ParityBridge.deshiftedCountXIso`, `OAI.DerivedBar.ParityBridge.instDecidableEqIndex_1`, `OAI.DerivedBar.ParityBridge.instModuleCarrier_solutions_11`, `OAI.DerivedBar.ParityBridge.instModuleCarrier_solutions_8`, `OAI.DerivedBar.ParityBridge.supportedInnerIso`, `OAI.DerivedBar.ParityBridge.supportedLeadingIso`, `OAI.DerivedBar.ParityBridge.supportedOuterScalarModule`, `OAI.LittleFinitistic.InducedRectification.rightTotal`.
--
--   **Sources.** They come from these modules of lean/OAI/Algebra, in whole or in part: `Finitistic_Bar_BarPatternEmbedding`, `Finitistic_Bar_ExplicitSignedDifferential`, `Finitistic_Bar_FlatSupportedAssembly`, `Finitistic_Bar_GlobalIndexedComparison`, `Finitistic_Bar_IndexedAssemblyComparison`, `Finitistic_Bar_IndexedPatternEmbedding`, `Finitistic_Bar_IntegerCountRestriction`, `Finitistic_Bar_IntegerCountShift`, `Finitistic_Bar_LeadingBarSuffix`, `Finitistic_Bar_LeadingSupportedComparison`, `Finitistic_Bar_PatternPrefixCoordinates`, `Finitistic_Bar_RecursivePrefixInclusions`, `Finitistic_Bar_RecursiveSuffixDifferential`, `Finitistic_Bar_RecursiveSuffixEmbedding`, `Finitistic_Bar_RecursiveSuffixFaces`, `Finitistic_Bar_RecursiveSuffixTotal`, `Finitistic_Bar_SuffixNaturality`, `Finitistic_Bar_SuffixParityFaces`, `Finitistic_Bar_SupportedInnerCoordinates`, `Finitistic_Bar_SupportedOuterCoordinates`, `Finitistic_Rectification_InducedRectification`.
--
--   **Imports.** It imports the bundles `OAIQ023F010` and `OAIQ023F011` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ023F021`.
-- source:
--   OpenAI, An algebra of infinite little finitistic dimension (result family 198), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 198; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/An-algebra-of-infinite-little-finitistic-dimension-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Algebra at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ023F010
import Definitions.Def_OAIQ023F011

section
-- module Solutions.OAIQ023_Fin.Finitistic_Bar_ExplicitSignedDifferential
attribute [-instance] _root_.OAI.DerivedBar.Multibar.patternModule _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.DerivedBar.term_finite _root_.OAI.DerivedBar.term_finiteDimensional _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.BimoduleCoefficients.instAddCommGroupCarrierTensorProductMulOpposite _root_.OAI.LittleFinitistic.BimoduleCoefficients.instModuleCarrierTensorProductMulOpposite_1 _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instAddCommGroup _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instRing
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

/-- At the inflated module endpoint, an X action vanishes. -/
theorem multibarAugmented_ideal_endpoint
    (hN : ∀ (x : X) (v : N), (inr x : TrivSqZeroExt D X) • v = (0 : N))
    (x : X) (v : N) :
    multibarAugmentedDifferential k D X N 0 ((inr x : A) ⊗ₜ[k] v) = 0 := by
  rw [multibarAugmentedDifferential_zero, slotParity_ideal, _root_.neg_smul, hN, neg_zero]

end DerivedBar.SquareZero

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

theorem termCast_tmul {a b : ℕ} (h : a=b) (h' : a+1=b+1)
    (x : A) (v : term k A N a) :
    termCast k D X N h' (x ⊗ₜ[k] v) = x ⊗ₜ[k] termCast k D X N h v := by
  subst b
  rfl

end DerivedBar.ParityBridge

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Bar_PatternPrefixCoordinates
attribute [-instance] _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.DerivedBar.term_finite _root_.OAI.DerivedBar.term_finiteDimensional _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.BimoduleCoefficients.instAddCommGroupCarrierTensorProductMulOpposite _root_.OAI.LittleFinitistic.BimoduleCoefficients.instModuleCarrierTensorProductMulOpposite_1 _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instAddCommGroup _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instRing
attribute [-simp] _root_.OAI.DerivedBar.ParityBridge.canonicalLinear_apply _root_.OAI.DerivedBar.ParityBridge.innerEmbedding_lof_succ _root_.OAI.DerivedBar.ParityBridge.outerCast_refl _root_.OAI.DerivedBar.ParityBridge.outerSuffixEmbed_tmul _root_.OAI.ExternalTensor.Section4.sum_hom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
open CategoryTheory TensorProduct TrivSqZeroExt
open scoped TensorProduct
noncomputable section
namespace DerivedBar.ParityBridge
open DerivedBar.Multibar
universe u
variable (k D X N : Type u) [Field k] [Ring D] [Algebra k D]
  [AddCommGroup X] [Module k X] [Module D X] [Module Dᵐᵒᵖ X]
  [SMulCommClass D Dᵐᵒᵖ X] [IsScalarTower k D X] [IsScalarTower k Dᵐᵒᵖ X]
  [AddCommGroup N] [Module k N] [Module D N] [IsScalarTower k D N]
local notation "A" => TrivSqZeroExt D X
variable [Module (TrivSqZeroExt D X) N] [IsScalarTower k (TrivSqZeroExt D X) N]


omit [Module Dᵐᵒᵖ X] [SMulCommClass D Dᵐᵒᵖ X] [IsScalarTower k Dᵐᵒᵖ X]
  [Module A N] [IsScalarTower k A N] in
/-- Prefix coordinates act literally on each tensor generator. -/
theorem termPatternIso_hom_tmul (i : ℕ) (p : List Bool) (d : D)
    (v : term k D (patternTerm k D X N p) i) :
    (termPatternIso k D X N (i+1) p).hom.hom (d ⊗ₜ[k] v) =
      d ⊗ₜ[k] (termPatternIso k D X N i p).hom.hom v := rfl

omit [Module A N] [IsScalarTower k A N] in
/-- The recursive suffix embedding is exactly the existing literal block embedding,
with every degree cast exposed. -/
theorem embed_termPatternIso (i : ℕ) (p : List Bool)
    (v : term k D (patternTerm k D X N p) i) :
    embed k D X N (List.replicate i false ++ p)
      ((termPatternIso k D X N i p).hom.hom v) =
    termCast k D X N (show p.length+i=(List.replicate i false ++ p).length by simp; omega)
      (suffixEmbed k D X N (patternTerm k D X N p) p.length (embed k D X N p) i v) := by
  induction i with
  | zero => rfl
  | succ i ih =>
    induction v using OAI.tensorInductionOn with
    | tmul d v =>
      rw [termPatternIso_hom_tmul, suffixEmbed_tmul]
      change (inl d : A) ⊗ₜ[k]
        embed k D X N (List.replicate i false ++ p) ((termPatternIso k D X N i p).hom.hom v) = _
      rw [ih]
      exact (termCast_tmul k D X N
        (show p.length+i=(List.replicate i false ++ p).length by simp; omega)
        (show (p.length+i)+1=(List.replicate i false ++ p).length+1 by simp; omega)
        (inl d) (suffixEmbed k D X N _ p.length (embed k D X N p) i v)).symm
    | add v w hv hw => simp only [map_add, hv, hw]
end DerivedBar.ParityBridge

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Bar_BarPatternEmbedding
attribute [-instance] _root_.OAI.DerivedBar.BimoduleTensor.twoSidedBarFunctor_additive _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.DerivedBar.term_finite _root_.OAI.DerivedBar.term_finiteDimensional _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.BalancedTensor.scalarLeftTower _root_.OAI.LittleFinitistic.BimoduleCoefficients.instAddCommGroupCarrierTensorProductMulOpposite _root_.OAI.LittleFinitistic.BimoduleCoefficients.instModuleCarrierTensorProductMulOpposite_1 _root_.OAI.LittleFinitistic.BimoduleCoefficients.towerLeft _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instAddCommGroup _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instRing
attribute [-simp] _root_.OAI.DerivedBar.ParityBridge.canonicalLinear_apply _root_.OAI.DerivedBar.ParityBridge.innerEmbedding_lof_succ _root_.OAI.DerivedBar.ParityBridge.outerCast_refl _root_.OAI.DerivedBar.ParityBridge.outerSuffixEmbed_tmul _root_.OAI.ExternalTensor.Section4.sum_hom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
open CategoryTheory TensorProduct TrivSqZeroExt
open scoped TensorProduct
noncomputable section
namespace DerivedBar.ParityBridge
open DerivedBar.Multibar
universe u
variable (k D X N : Type u) [Field k] [Ring D] [Algebra k D]
  [AddCommGroup X] [Module k X] [Module D X] [Module Dᵐᵒᵖ X]
  [SMulCommClass D Dᵐᵒᵖ X] [IsScalarTower k D X] [IsScalarTower k Dᵐᵒᵖ X]
  [AddCommGroup N] [Module k N] [Module D N] [IsScalarTower k D N]
local notation "A" => TrivSqZeroExt D X


/-- The categorical X-bar pattern coordinates and the suffix formula have
exactly the same embedding into the original A bar, including the degree cast. -/
theorem embed_twoSidedBarPatternIso (i : ℕ) (p : List Bool)
    (v : ((BimoduleTensor.twoSidedBarFunctor k D X).obj
      (ModuleCat.of D (patternTerm k D X N p))).X i) :
    embed k D X N (true :: (List.replicate i false ++ p))
      ((twoSidedBarPatternIso k D X N i p).hom.hom v) =
    termCast k D X N
      (show (p.length+i)+1=(true :: (List.replicate i false ++ p)).length by simp; omega)
      (idealSuffixEmbed k D X N (patternTerm k D X N p) p.length i (embed k D X N p)
        ((twoSidedBarObjIso k D X (patternTerm k D X N p) i).hom.hom v)) := by
  let e := (termPatternIso k D X N i p).toLinearEquiv.restrictScalars k
  suffices h : ∀ w : X ⊗[k] term k D (patternTerm k D X N p) i,
      embed k D X N (true :: (List.replicate i false ++ p))
        (AlgebraTensorModule.congr (LinearEquiv.refl D X) e w) =
      termCast k D X N
        (show (p.length+i)+1=(true :: (List.replicate i false ++ p)).length by simp; omega)
        (idealSuffixEmbed k D X N (patternTerm k D X N p) p.length i (embed k D X N p) w) from
    h ((twoSidedBarObjIso k D X (patternTerm k D X N p) i).hom.hom v)
  intro w
  induction w using OAI.tensorInductionOn with
  | tmul x w =>
    change (inr x : A) ⊗ₜ[k]
      embed k D X N (List.replicate i false ++ p) ((termPatternIso k D X N i p).hom.hom w) = _
    rw [embed_termPatternIso, idealSuffixEmbed_tmul]
    exact (termCast_tmul k D X N
      (show p.length+i=(List.replicate i false ++ p).length by simp; omega)
      (show (p.length+i)+1=(List.replicate i false ++ p).length+1 by simp; omega)
      (inr x) (suffixEmbed k D X N _ p.length (embed k D X N p) i w)).symm
  | add v w hv hw => simp only [map_add, hv, hw]

end DerivedBar.ParityBridge

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Bar_SuffixNaturality
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

variable (W : Type u) [AddCommGroup W] [Module k W] [Module D W] [IsScalarTower k D W]

omit [Module A N] [IsScalarTower k A N] in
/-- Exterior D coefficients commute with all vertical suffix maps. -/
theorem outerSuffixEmbed_termMap (s n : ℕ) (e : W →ₗ[k] term k A N s)
    (f : M →ₗ[D] W) (v : D ⊗[k] term k D M n) :
    outerSuffixEmbed k D X N W s n e (termMap k D M W f (n+1) v) =
    outerSuffixEmbed k D X N M s n (e.comp (f.restrictScalars k)) v := by
  induction v using OAI.tensorInductionOn with
  | tmul d v =>
    rw [termMap_tmul, outerSuffixEmbed_tmul, outerSuffixEmbed_tmul, suffixEmbed_termMap]
  | add v w hv hw => simp only [map_add, hv, hw]

end DerivedBar.ParityBridge

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Bar_RecursiveSuffixEmbedding
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

attribute [local instance] OAI.DerivedBar.ParityBridge.instModuleCarrier_solutions
attribute [local instance] OAI.DerivedBar.ParityBridge.instIsScalarTowerCarrier_solutions
attribute [local instance] OAI.DerivedBar.ParityBridge.instDecidableEqIndex
theorem termCast_smul {a b : ℕ} (h : a=b) (d : A) (v : term k A N a) :
    letI : Module A N := inflatedModule D X N
    termCast k D X N h (d • v) = d • termCast k D X N h v := by
  subst b
  rfl

end DerivedBar.ParityBridge

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Bar_RecursiveSuffixFaces
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
local instance instDecidableEqIndex_1 (r n : ℕ) : DecidableEq (RecursiveTotal.Index r n) := Classical.decEq _
variable (N : ModuleCat.{u} D)
local notation "A" => TrivSqZeroExt D X
local notation "XB" => BimoduleTensor.twoSidedBarFunctor k D X
local notation "Z" => Functor.obj (ChainComplex.single₀ (ModuleCat D)) N
local notation "B" => (fun _ : ℕ => XB)

attribute [local instance] OAI.DerivedBar.ParityBridge.instModuleCarrier_solutions_1
attribute [local instance] OAI.DerivedBar.ParityBridge.instIsScalarTowerCarrier_solutions_1
attribute [local instance] OAI.DerivedBar.ParityBridge.instModuleTrivSqZeroExtCarrier_solutions
attribute [local instance] OAI.DerivedBar.ParityBridge.instIsScalarTowerTrivSqZeroExtCarrier_solutions
/-- The degree-zero input embedding is the identity on its sole summand. -/
theorem innerEmbedding_zero_lof (t : RecursiveTotal.Index 0 0) :
    (innerEmbedding k D X N 0 0).comp
      ((RecursiveTotal.lof B Z 0 0 t).hom.restrictScalars k) = LinearMap.id := by
  ext v
  simp only [innerEmbedding, RecursiveTotal.lof, ModuleCat.hom_ofHom,
    LinearMap.comp_apply, LinearMap.restrictScalars_apply, DirectSum.lof_eq_of]
  erw [toModule_of_scalar]

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
theorem outerCast_trans {a b c : ℕ} (h : a=b) (g : b=c)
    (v : D ⊗[k] term k A N a) :
    outerCast k D X N g (outerCast k D X N h v) = outerCast k D X N (h.trans g) v := by
  subst b; subst c
  simp only [outerCast_refl, LinearMap.id_apply]

theorem outerBarSuffix_map (V W : ModuleCat.{u} D) (s i : ℕ)
    (e : W →ₗ[k] term k A N s) (f : V ⟶ W) (v : ((DB).obj V).X i) :
    outerBarSuffix k D X N W s i e ((((DB).map f).f i).hom v) =
    outerBarSuffix k D X N V s i (e.comp (f.hom.restrictScalars k)) v := by
  have h := congrArg (fun g => g.hom v) (Multibar.freeBarObjIso_map k D V W f.hom i)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_ofHom] at h
  unfold outerBarSuffix
  simp only [LinearMap.comp_apply]
  erw [h]
  exact outerSuffixEmbed_termMap k D X N V W s i e f.hom _

end DerivedBar.ParityBridge

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Bar_RecursiveSuffixDifferential
attribute [-instance] _root_.OAI.DerivedBar.term_finite _root_.OAI.DerivedBar.term_finiteDimensional _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.BimoduleCoefficients.instAddCommGroupCarrierTensorProductMulOpposite _root_.OAI.LittleFinitistic.BimoduleCoefficients.instModuleCarrierTensorProductMulOpposite _root_.OAI.LittleFinitistic.BimoduleCoefficients.instModuleCarrierTensorProductMulOpposite_1 _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instAddCommGroup _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instRing
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
variable (N : ModuleCat.{u} D)
local notation "A" => TrivSqZeroExt D X

attribute [local instance] OAI.DerivedBar.ParityBridge.recursiveSuffixDifferentialScalarModule
attribute [local instance] OAI.DerivedBar.ParityBridge.recursiveSuffixDifferentialScalarTower
local instance recursiveSuffixDifferentialIndexDecidableEq_ra06998_1 (r n : ℕ) :
    DecidableEq (RecursiveTotal.Index r n) := Classical.decEq _
attribute [local instance] OAI.DerivedBar.ParityBridge.recursiveSuffixDifferentialInflatedModule
attribute [local instance] OAI.DerivedBar.ParityBridge.recursiveSuffixDifferentialInflatedScalarTower
/-- Degree transports compose by equality elimination alone. -/
theorem termCast_trans {a b c : ℕ} (h : a=b) (g : b=c) (v : term k A N a) :
    termCast k D X N g (termCast k D X N h v) = termCast k D X N (h.trans g) v := by
  subst b; subst c
  rfl

end DerivedBar.ParityBridge

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Bar_RecursiveSuffixTotal
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
local notation "Z" => Functor.obj (ChainComplex.single₀ (ModuleCat D)) N
local notation "B" => (fun _ : ℕ => XB)

attribute [local instance] OAI.DerivedBar.ParityBridge.instModuleCarrier_solutions_3
attribute [local instance] OAI.DerivedBar.ParityBridge.instIsScalarTowerCarrier_solutions_3
local instance recursiveSuffixTotalIndexDecidableEq_ra06998_1 (r n : ℕ) :
    DecidableEq (RecursiveTotal.Index r n) := Classical.decEq _
attribute [local instance] OAI.DerivedBar.ParityBridge.instModuleTrivSqZeroExtCarrier_solutions_2
attribute [local instance] OAI.DerivedBar.ParityBridge.instIsScalarTowerTrivSqZeroExtCarrier_solutions_2
theorem innerTotalEmbedding_assemble (r n : ℕ) (v : RecursiveTotal.flat B Z r n) :
    innerTotalEmbedding k D X N r n ((RecursiveTotal.assemble B Z r n).hom v) =
      innerEmbedding k D X N r n v := by
  change innerEmbedding k D X N r n
    ((RecursiveTotal.flattenIso B Z r n (𝟭 _)).hom.hom
      ((RecursiveTotal.flattenIso B Z r n (𝟭 _)).inv.hom v)) = _
  have h := congrArg (fun f => f.hom v) (RecursiveTotal.flattenIso B Z r n (𝟭 _)).inv_hom_id
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_id, LinearMap.id_apply] at h
  exact congrArg (innerEmbedding k D X N r n) h

theorem innerTotalEmbedding_inclusion (r n : ℕ) (t : RecursiveTotal.Index r n)
    (v : RecursiveTotal.summand B Z r n t) :
    innerTotalEmbedding k D X N r n ((RecursiveTotal.inclusion B Z r n t).hom v) =
      innerEmbedding k D X N r n ((RecursiveTotal.lof B Z r n t).hom v) := by
  have h := congrArg (fun f => f.hom v) (RecursiveTotal.lof_assemble B Z r n t)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h
  rw [← h, innerTotalEmbedding_assemble]

theorem innerTotalEmbedding_zero : innerTotalEmbedding k D X N 0 0 = LinearMap.id := by
  ext v
  have h := innerTotalEmbedding_inclusion k D X N 0 0 () v
  change innerTotalEmbedding k D X N 0 0 v = _ at h
  have he := congrArg (fun f => f v) (innerEmbedding_zero_lof k D X N ())
  exact h.trans he

end DerivedBar.ParityBridge

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Bar_SupportedInnerCoordinates
attribute [-instance] _root_.OAI.DerivedBar.term_finite _root_.OAI.DerivedBar.term_finiteDimensional _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.BalancedTensor.scalarLeftTower _root_.OAI.LittleFinitistic.BimoduleCoefficients.instAddCommGroupCarrierTensorProductMulOpposite _root_.OAI.LittleFinitistic.BimoduleCoefficients.instModuleCarrierTensorProductMulOpposite _root_.OAI.LittleFinitistic.BimoduleCoefficients.instModuleCarrierTensorProductMulOpposite_1 _root_.OAI.LittleFinitistic.BimoduleCoefficients.towerLeft _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instAddCommGroup _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instRing
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
local notation "Z" => Functor.obj (ChainComplex.single₀ (ModuleCat D)) N
local notation "B" => (fun _ : ℕ => XB)
local notation "c" => ComplexShape.down ℕ

attribute [local instance] OAI.DerivedBar.ParityBridge.supportedInnerCoordinatesScalarModule
attribute [local instance] OAI.DerivedBar.ParityBridge.supportedInnerCoordinatesScalarTower
local instance supportedInnerCoordinatesIndexDecidableEq_ra06998_1 (r n : ℕ) :
    DecidableEq (Index r n) := Classical.decEq _
local instance supportedInnerCoordinatesInflatedModule_ra06998_1 : Module A N := inflatedModule D X N
local instance supportedInnerCoordinatesInflatedTower_ra06998_1 : IsScalarTower k A N :=
  IsScalarTower.of_algebraMap_smul
    (fun a v => IsScalarTower.algebraMap_smul D a v)
/-- The same literal inner coordinates, with the proved degree-zero input made explicit. -/
def supportedInnerIso : (r n : ℕ) → (t : Index r n) → (h : inputDegree r t=0) →
    summand B Z r n t ≅ ModuleCat.of D (patternTerm k D X N (innerPattern r t))
  | 0, n, t, h => by
      change n=0 at h
      subst n
      exact Iso.refl _
  | r+1, _, ⟨p,t⟩, h =>
      (XB ⋙ HomologicalComplex.eval _ c p.val.1).mapIso (supportedInnerIso r p.val.2 t h) ≪≫
        twoSidedBarPatternIso k D X N p.val.1 (innerPattern r t)

/-- Transport of the terminal input along an equality of D-modules commutes
with the genuine categorical bar pattern coordinates. -/
theorem twoSidedBarPatternIso_eqToIso (V W : ModuleCat.{u} D) (h : V=W)
    (i : ℕ) (p : List Bool) :
    (XB ⋙ HomologicalComplex.eval _ c i).mapIso
      (eqToIso (congrArg (fun V : ModuleCat D => ModuleCat.of D (patternTerm k D X V p)) h)) ≪≫
        twoSidedBarPatternIso k D X W i p =
    twoSidedBarPatternIso k D X V i p ≪≫
      eqToIso (congrArg (fun V : ModuleCat D =>
        ModuleCat.of D (patternTerm k D X V (true :: (List.replicate i false ++ p)))) h) := by
  subst W
  simp

/-- The supported recursion equals the already existing innerSummandIso,
followed only by the forced zero-degree input transport. -/
theorem supportedInnerIso_eq (r n : ℕ) (t : Index r n) (h : inputDegree r t=0) :
    supportedInnerIso k D X N r n t h =
      innerSummandIso k D X Z r n t ≪≫ eqToIso
        (congrArg (fun V : ModuleCat D => ModuleCat.of D (patternTerm k D X V (innerPattern r t)))
          (show (Z).X (inputDegree r t)=N by rw [h]; rfl)) := by
  induction r generalizing n with
  | zero =>
    change n=0 at h
    subst n
    rfl
  | succ r ih =>
    rcases t with ⟨⟨⟨i,q⟩,hq⟩,t⟩
    let F := XB ⋙ HomologicalComplex.eval _ c i
    let p := innerPattern r t
    let V := (Z).X (inputDegree r t)
    have hv : V=N := by change (Z).X (inputDegree r t)=N; rw [show inputDegree r t=0 from h]; rfl
    change F.mapIso (supportedInnerIso k D X N r q t h) ≪≫
      twoSidedBarPatternIso k D X N i p =
      (F.mapIso (innerSummandIso k D X Z r q t) ≪≫ twoSidedBarPatternIso k D X V i p) ≪≫
        eqToIso (congrArg (fun W : ModuleCat D =>
          ModuleCat.of D (patternTerm k D X W (true :: (List.replicate i false ++ p)))) hv)
    rw [ih q t h, Functor.mapIso_trans, Iso.trans_assoc, Iso.trans_assoc]
    congr 1
    exact twoSidedBarPatternIso_eqToIso k D X V N hv i p

/-- Every surviving summand has exactly r+n literal internal slots. -/
theorem supportedInner_length (r n : ℕ) (t : Index r n) (h : inputDegree r t=0) :
    (innerPattern r t).length = r+n := by
  have ht := length_innerPattern r n t
  omega

/-- The canonical recursive embedding agrees with the original literal word
embedding on every supported summand, through the actual bar coordinate maps. -/
theorem innerEmbedding_supported (r n : ℕ) (t : Index r n) (h : inputDegree r t=0)
    (v : summand B Z r n t) :
    innerEmbedding k D X N r n ((lof B Z r n t).hom v) =
      termCast k D X N (supportedInner_length r n t h)
        (embed k D X N (innerPattern r t) ((supportedInnerIso k D X N r n t h).hom.hom v)) := by
  induction r generalizing n with
  | zero =>
    change n=0 at h
    subst n
    have he := congrArg (fun f => f v) (innerEmbedding_zero_lof k D X N t)
    exact he
  | succ r ih =>
    rcases t with ⟨⟨⟨i,q⟩,hq⟩,t⟩
    let p := innerPattern r t
    let V := summand B Z r q t
    let W := ModuleCat.of D (patternTerm k D X N p)
    let f : V ⟶ W := (supportedInnerIso k D X N r q t h).hom
    let e := canonicalLinear k D X N (patternTerm k D X N p) p.length (embed k D X N p)
    have hp : p.length=r+q := supportedInner_length r q t h
    have he : (innerEmbedding k D X N r q).comp ((lof B Z r q t).hom.restrictScalars k) =
        (termCast k D X N hp).comp (e.comp (canonicalRestrict k D V W f)) := by
      ext w
      change innerEmbedding k D X N r q ((lof B Z r q t).hom w) =
        termCast k D X N hp
          (canonicalLinear k D X N (patternTerm k D X N p) p.length (embed k D X N p)
            ((supportedInnerIso k D X N r q t h).hom.hom w))
      rw [canonicalLinear_apply]
      exact ih q t h w
    erw [innerEmbedding_lof_succ k D X N r n i q hq t v, he]
    erw [barSuffix_termCast k D X N V hp i (e.comp (canonicalRestrict k D V W f)) v]
    erw [← barSuffix_map k D X N V W p.length i e f v]
    change termCast k D X N (show ((r+q)+i)+1=(r+1)+n by omega)
      (termCast k D X N (show (p.length+i)+1=((r+q)+i)+1 by omega)
      (barSuffix k D X N W p.length i e ((((XB).map f).f i).hom v))) = _
    erw [barSuffix_canonicalLinear k D X N (patternTerm k D X N p) p.length i
      (embed k D X N p)]
    change _ = termCast k D X N
      (show (true :: (List.replicate i false ++ p)).length=(r+1)+n by
        simp only [List.length_cons, List.length_append, List.length_replicate]; omega)
      (embed k D X N (true :: (List.replicate i false ++ p))
        ((twoSidedBarPatternIso k D X N i p).hom.hom ((((XB).map f).f i).hom v)))
    erw [embed_twoSidedBarPatternIso k D X N i p]
    erw [termCast_trans k D X N
      (show (p.length+i)+1=((r+q)+i)+1 by omega)
      (show ((r+q)+i)+1=(r+1)+n by omega)]
    erw [termCast_trans k D X N
      (show (p.length+i)+1=(true :: (List.replicate i false ++ p)).length by simp; omega)
      (show (true :: (List.replicate i false ++ p)).length=(r+1)+n by
        simp only [List.length_cons, List.length_append, List.length_replicate]; omega)]
end DerivedBar.ParityBridge

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Bar_IndexedPatternEmbedding
attribute [-instance] _root_.OAI.DerivedBar.term_finite _root_.OAI.DerivedBar.term_finiteDimensional _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.BimoduleCoefficients.instAddCommGroupCarrierTensorProductMulOpposite _root_.OAI.LittleFinitistic.BimoduleCoefficients.instModuleCarrierTensorProductMulOpposite _root_.OAI.LittleFinitistic.BimoduleCoefficients.instModuleCarrierTensorProductMulOpposite_1 _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instAddCommGroup _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instRing
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
open DerivedBar.Multibar DerivedBar.RecursiveTotal
universe u
variable (k D X : Type u) [Field k] [Ring D] [Algebra k D]
  [AddCommGroup X] [Module k X] [Module D X] [Module Dᵐᵒᵖ X]
  [SMulCommClass D Dᵐᵒᵖ X] [IsScalarTower k D X] [IsScalarTower k Dᵐᵒᵖ X]
variable (N : ModuleCat.{u} D)
local notation "A" => TrivSqZeroExt D X

attribute [local instance] OAI.DerivedBar.ParityBridge.indexedPatternEmbeddingScalarModule
local instance indexedPatternEmbeddingScalarTower_ra06998_1 (V : ModuleCat.{u} D) :
    IsScalarTower k D V :=
  IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
local instance indexedPatternEmbeddingIndexDecidableEq_ra06998_1 (r n : ℕ) :
    DecidableEq (Index r n) := Classical.decEq _
local instance indexedPatternEmbeddingInflatedModule_ra06998_1 : Module A N := inflatedModule D X N
local instance indexedPatternEmbeddingInflatedScalarTower_ra06998_1 : IsScalarTower k A N :=
  IsScalarTower.of_algebraMap_smul
    (fun a v => IsScalarTower.algebraMap_smul D a v)
/-- The old indexed inclusion and old list-pattern embedding agree; transports
come solely from the proved equality of their tensor objects and their degrees. -/
theorem indexedInclusion_toList {n r : ℕ} (p : Multibar.Indexed.Shape n r)
    (v : Multibar.Indexed.tensor k D X N p) :
    Multibar.Indexed.inclusion k D X N p v =
      termCast k D X N (Multibar.Indexed.length_toList p)
        (embed k D X N (Multibar.Indexed.toList p)
          ((eqToHom (Multibar.Indexed.tensor_toList k D X N p)).hom v)) := by
  induction p with
  | nil => rfl
  | @base n r p ih =>
    induction v using OAI.tensorInductionOn with
    | tmul d v =>
      change (inl d : A) ⊗ₜ[k] Multibar.Indexed.inclusion k D X N p v =
        termCast k D X N (show (false :: Multibar.Indexed.toList p).length=n+1 by simp)
          (embed k D X N (false :: Multibar.Indexed.toList p)
            ((eqToHom (congrArg (fun T : ModuleCat k => ModuleCat.of k (D ⊗[k] T))
              (Multibar.Indexed.tensor_toList k D X N p))).hom (d ⊗ₜ[k] v)))
      rw [eqToHom_tensor_tmul k D (Multibar.Indexed.tensor k D X N p)
        (patternTerm k D X N (Multibar.Indexed.toList p))
        (Multibar.Indexed.tensor_toList k D X N p) d v]
      change (inl d : A) ⊗ₜ[k] Multibar.Indexed.inclusion k D X N p v =
        termCast k D X N (show (false :: Multibar.Indexed.toList p).length=n+1 by simp) ((inl d : A) ⊗ₜ[k] _)
      rw [ih]
      exact (termCast_tmul k D X N (Multibar.Indexed.length_toList p)
        (by simp) _ _).symm
    | add v w hv hw => simp only [map_add, hv, hw]
  | @ideal n r p ih =>
    induction v using OAI.tensorInductionOn with
    | tmul x v =>
      change (inr x : A) ⊗ₜ[k] Multibar.Indexed.inclusion k D X N p v =
        termCast k D X N (show (true :: Multibar.Indexed.toList p).length=n+1 by simp)
          (embed k D X N (true :: Multibar.Indexed.toList p)
            ((eqToHom (congrArg (fun T : ModuleCat k => ModuleCat.of k (X ⊗[k] T))
              (Multibar.Indexed.tensor_toList k D X N p))).hom (x ⊗ₜ[k] v)))
      rw [eqToHom_tensor_tmul k X (Multibar.Indexed.tensor k D X N p)
        (patternTerm k D X N (Multibar.Indexed.toList p))
        (Multibar.Indexed.tensor_toList k D X N p) x v]
      change (inr x : A) ⊗ₜ[k] Multibar.Indexed.inclusion k D X N p v =
        termCast k D X N (show (true :: Multibar.Indexed.toList p).length=n+1 by simp) ((inr x : A) ⊗ₜ[k] _)
      rw [ih]
      exact (termCast_tmul k D X N (Multibar.Indexed.length_toList p)
        (by simp) _ _).symm
    | add v w hv hw => simp only [map_add, hv, hw]

theorem outerInclusion_toList {n r : ℕ} (p : Multibar.Indexed.Shape n r)
    (v : Multibar.Indexed.outerTensor k D X N p) :
    Multibar.Indexed.outerInclusion k D X N p v =
      outerCast k D X N (Multibar.Indexed.length_toList p)
        (AlgebraTensorModule.lTensor D D (embed k D X N (Multibar.Indexed.toList p))
          ((eqToHom (congrArg (fun T : ModuleCat k => ModuleCat.of D (D ⊗[k] T))
            (Multibar.Indexed.tensor_toList k D X N p))).hom v)) := by
  induction v using OAI.tensorInductionOn with
  | tmul d v =>
    rw [eqToHom_outer_tmul k D (Multibar.Indexed.tensor k D X N p)
      (patternTerm k D X N (Multibar.Indexed.toList p))
      (Multibar.Indexed.tensor_toList k D X N p) d v]
    change d ⊗ₜ[k] Multibar.Indexed.inclusion k D X N p v =
      d ⊗ₜ[k] termCast k D X N _
        (embed k D X N (Multibar.Indexed.toList p)
          ((eqToHom (Multibar.Indexed.tensor_toList k D X N p)).hom v))
    rw [indexedInclusion_toList]
  | add v w hv hw => simp only [map_add, hv, hw]

theorem outerInclusion_pattern {n r : ℕ} (s : Multibar.Indexed.Shape n r)
    (p : List Bool) (hp : Multibar.Indexed.toList s=p)
    (ht : Multibar.Indexed.tensor k D X N s=patternTerm k D X N p)
    (hl : p.length=n) (v : Multibar.Indexed.outerTensor k D X N s) :
    Multibar.Indexed.outerInclusion k D X N s v =
      outerCast k D X N hl (AlgebraTensorModule.lTensor D D (embed k D X N p)
        ((eqToHom (congrArg (fun T : ModuleCat k => ModuleCat.of D (D ⊗[k] T)) ht)).hom v)) := by
  subst p
  exact outerInclusion_toList k D X N s v
end DerivedBar.ParityBridge

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Bar_RecursivePrefixInclusions
attribute [-instance] _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.BimoduleCoefficients.instAddCommGroupCarrierTensorProductMulOpposite _root_.OAI.LittleFinitistic.BimoduleCoefficients.instModuleCarrierTensorProductMulOpposite_1 _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instAddCommGroup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
open CategoryTheory CategoryTheory.Limits
noncomputable section
namespace DerivedBar.ParityBridge
universe u
local notation "c" => ComplexShape.down ℕ

open DerivedBar.RecursiveTotal
variable (k D X : Type u) [Field k] [Ring D] [Algebra k D]
  [AddCommGroup X] [Module k X] [Module D X] [Module Dᵐᵒᵖ X]
  [SMulCommClass D Dᵐᵒᵖ X] [IsScalarTower k D X] [IsScalarTower k Dᵐᵒᵖ X]
variable (N : ModuleCat.{u} D)
local notation "XB" => BimoduleTensor.twoSidedBarFunctor k D X
local notation "Z" => Functor.obj (ChainComplex.single₀ (ModuleCat D)) N
local notation "B" => (fun _ : ℕ => XB)

theorem leadingIter_prefix (r m : ℕ) (h : m ≤ r) :
    iter (leadingBarSequence k D X r) Z m = iter B Z m :=
  (leadingBarSequence_prefix k D X Z r m h).trans (innerIter_eq_explicit k D X N m).symm

/-- Literal recursive inclusions depend only on the functors in their prefix. -/
theorem leadingInclusion_prefix_heq (r m n : ℕ) (h : m ≤ r) (t : Index m n) :
    HEq (inclusion (leadingBarSequence k D X r) Z m n t) (inclusion B Z m n t) := by
  induction m generalizing n with
  | zero => rfl
  | succ m ih =>
    rcases t with ⟨⟨⟨i,q⟩,hq⟩,t⟩
    have hm : m < r := by omega
    have he := barInclusionStep_heq (leadingBarSequence k D X r m) XB
      (by simp only [leadingBarSequence, ite_eq_left hm])
      (leadingSummand_prefix k D X Z r m q (by omega) t)
      (leadingIter_prefix k D X N r m (by omega)) i q n hq
      (inclusion (leadingBarSequence k D X r) Z m q t) (inclusion B Z m q t)
      (ih q (by omega) t)
    exact he

theorem leadingInclusion_prefix (r m n : ℕ) (h : m ≤ r) (t : Index m n) :
    inclusion (leadingBarSequence k D X r) Z m n t ≫
      eqToHom (congrArg (fun W => W.X n) (leadingIter_prefix k D X N r m h)) =
    eqToHom (leadingSummand_prefix k D X Z r m n h t) ≫ inclusion B Z m n t :=
  hom_square_of_heq _ _ _ _ (leadingInclusion_prefix_heq k D X N r m n h t)

theorem leadingSummand_last (r n i q : ℕ) (h : i+q=n) (t : Index r q) :
    summand (leadingBarSequence k D X r) Z (r+1) n ⟨⟨⟨i,q⟩,h⟩,t⟩ =
      (barFunctor k D ⋙ HomologicalComplex.eval _ c i).obj
        (summand (leadingBarSequence k D X r) Z r q t) := by
  simp only [summand, degreeFunctor, leadingBarSequence, lt_self_iff_false, ite_false, if_false]

/-- The exterior inclusion is exactly the free-bar map of the original inner inclusion. -/
theorem leadingInclusion_total (r n i q : ℕ) (h : i+q=n) (t : Index r q) :
    inclusion (leadingBarSequence k D X r) Z (r+1) n ⟨⟨⟨i,q⟩,h⟩,t⟩ ≫
      eqToHom (congrArg (fun W => W.X n) (leadingIter_total k D X N r)) =
    eqToHom (leadingSummand_last k D X N r n i q h t) ≫
    (barFunctor k D ⋙ HomologicalComplex.eval _ c i).map
      (eqToHom (leadingSummand_prefix k D X Z r r q le_rfl t) ≫ inclusion B Z r q t) ≫
        (barBicomplex k D (iter B Z r)).ιTotal c i q n h := by
  have hi := hom_heq_of_square
    (congrArg (fun W => W.X q) (leadingIter_prefix k D X N r r le_rfl))
    (inclusion (leadingBarSequence k D X r) Z r q t)
    (eqToHom (leadingSummand_prefix k D X Z r r q le_rfl t) ≫ inclusion B Z r q t)
    (leadingInclusion_prefix k D X N r r q le_rfl t)
  have he := barInclusionStep_heq (leadingBarSequence k D X r r) (barFunctor k D)
    (by simp only [leadingBarSequence, lt_self_iff_false, ite_false, if_false]) rfl
    (leadingIter_prefix k D X N r r le_rfl) i q n h
    (inclusion (leadingBarSequence k D X r) Z r q t)
    (eqToHom (leadingSummand_prefix k D X Z r r q le_rfl t) ≫ inclusion B Z r q t) hi
  exact hom_square_of_heq _ _ _ _ he
end DerivedBar.ParityBridge

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Bar_SupportedOuterCoordinates
attribute [-instance] _root_.OAI.DerivedBar.term_finite _root_.OAI.DerivedBar.term_finiteDimensional _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.BalancedTensor.scalarLeftTower _root_.OAI.LittleFinitistic.BimoduleCoefficients.instAddCommGroupCarrierTensorProductMulOpposite _root_.OAI.LittleFinitistic.BimoduleCoefficients.instModuleCarrierTensorProductMulOpposite _root_.OAI.LittleFinitistic.BimoduleCoefficients.instModuleCarrierTensorProductMulOpposite_1 _root_.OAI.LittleFinitistic.BimoduleCoefficients.towerLeft _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instAddCommGroup _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instRing
attribute [-simp] _root_.OAI.ExternalTensor.Section4.sum_hom
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
local instance supportedOuterScalarModule (V : ModuleCat.{u} D) : Module k V :=
  BimoduleTensor.scalarModule k D V
local instance supportedOuterScalarTower (V : ModuleCat.{u} D) : IsScalarTower k D V :=
  IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
variable (N : ModuleCat.{u} D)
local notation "A" => TrivSqZeroExt D X
local notation "c" => ComplexShape.down ℕ

local instance supportedOuterIndexDecidableEq_ra06998_1 (r n : ℕ) : DecidableEq (Index r n) :=
  Classical.decEq _
local instance supportedOuterInflatedModule_ra06998_1 : Module A N := inflatedModule D X N
local instance supportedOuterInflatedScalarTower_ra06998_1 : IsScalarTower k A N := IsScalarTower.of_algebraMap_smul
    (fun a v => IsScalarTower.algebraMap_smul D a v)
/-- The projected exterior coefficient remains D while the internal word uses
exactly the old literal pattern embedding. -/
theorem outerEmbed_freeBarPatternIso (i : ℕ) (p : List Bool)
    (v : ((barFunctor k D).obj (ModuleCat.of D (patternTerm k D X N p))).X i) :
    AlgebraTensorModule.lTensor D D (embed k D X N (List.replicate i false ++ p))
      ((freeBarPatternIso k D X N i p).hom.hom v) =
    outerCast k D X N
      (show p.length+i=(List.replicate i false ++ p).length by simp; omega)
      (outerSuffixEmbed k D X N (patternTerm k D X N p) p.length i (embed k D X N p)
        ((freeBarObjIso k D (patternTerm k D X N p) i).hom.hom v)) := by
  suffices h : ∀ w : D ⊗[k] term k D (patternTerm k D X N p) i,
      AlgebraTensorModule.lTensor D D (embed k D X N (List.replicate i false ++ p))
        ((termPatternIso k D X N (i+1) p).hom.hom w) =
      outerCast k D X N
        (show p.length+i=(List.replicate i false ++ p).length by simp; omega)
        (outerSuffixEmbed k D X N (patternTerm k D X N p) p.length i (embed k D X N p) w) from
    h ((freeBarObjIso k D (patternTerm k D X N p) i).hom.hom v)
  intro w
  induction w using OAI.tensorInductionOn with
  | tmul d w =>
    change d ⊗ₜ[k] embed k D X N (List.replicate i false ++ p)
      ((termPatternIso k D X N i p).hom.hom w) =
      d ⊗ₜ[k] termCast k D X N _
        (suffixEmbed k D X N (patternTerm k D X N p) p.length (embed k D X N p) i w)
    rw [embed_termPatternIso]
  | add v w hv hw => simp only [map_add, hv, hw]

theorem outerBarSuffix_canonicalLinear (V : Type u) [AddCommGroup V] [Module k V]
    [Module D V] [IsScalarTower k D V] (s i : ℕ) (e : V →ₗ[k] term k A N s)
    (v : ((barFunctor k D).obj (ModuleCat.of D V)).X i) :
    outerBarSuffix k D X N (ModuleCat.of D V) s i (canonicalLinear k D X N V s e) v =
      outerSuffixEmbed k D X N V s i e ((freeBarObjIso k D V i).hom.hom v) := by
  have h := BimoduleTensor.scalarModule_eq k D V
  cases h
  rfl

theorem outerBarSuffix_termCast (V : ModuleCat.{u} D) {a b : ℕ} (h : a=b)
    (i : ℕ) (e : V →ₗ[k] term k A N a)
    (v : ((barFunctor k D).obj V).X i) :
    outerBarSuffix k D X N V b i ((termCast k D X N h).comp e) v =
      outerCast k D X N (congrArg (fun n => n+i) h)
        (outerBarSuffix k D X N V a i e v) := by
  subst b
  rw [show termCast k D X N (rfl : a=a) = LinearMap.id from rfl, LinearMap.id_comp,
    outerCast_refl, LinearMap.id_apply]

omit [Module Dᵐᵒᵖ X] [SMulCommClass D Dᵐᵒᵖ X] [IsScalarTower k Dᵐᵒᵖ X] in
theorem freeBarPatternIso_eqToIso (V W : ModuleCat.{u} D) (h : V=W)
    (i : ℕ) (p : List Bool) :
    (barFunctor k D ⋙ HomologicalComplex.eval _ c i).mapIso
      (eqToIso (congrArg (fun V : ModuleCat D => ModuleCat.of D (patternTerm k D X V p)) h)) ≪≫
        freeBarPatternIso k D X W i p =
    freeBarPatternIso k D X V i p ≪≫
      eqToIso (congrArg (fun V : ModuleCat D =>
        ModuleCat.of D (patternTerm k D X V (List.replicate (i+1) false ++ p))) h) := by
  subst W
  simp
end DerivedBar.ParityBridge

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Bar_LeadingSupportedComparison
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
open DerivedBar.Multibar DerivedBar.RecursiveTotal

universe u
variable (k D X : Type u) [Field k] [Ring D] [Algebra k D]
  [AddCommGroup X] [Module k X] [Module D X] [Module Dᵐᵒᵖ X]
  [SMulCommClass D Dᵐᵒᵖ X] [IsScalarTower k D X] [IsScalarTower k Dᵐᵒᵖ X]
local instance instModuleCarrier_solutions_8 (V : ModuleCat.{u} D) : Module k V := BimoduleTensor.scalarModule k D V
local instance instIsScalarTowerCarrier_solutions_8 (V : ModuleCat.{u} D) : IsScalarTower k D V :=
  IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
variable (N : ModuleCat.{u} D)
local notation "A" => TrivSqZeroExt D X
local notation "XB" => BimoduleTensor.twoSidedBarFunctor k D X
local notation "Z" => Functor.obj (ChainComplex.single₀ (ModuleCat D)) N
local notation "B" => (fun _ : ℕ => XB)
local notation "c" => ComplexShape.down ℕ

local instance leadingSupportedComparisonIndexDecidableEq_ra06998_1 (r n : ℕ) :
    DecidableEq (Index r n) := Classical.decEq _
local instance instModuleTrivSqZeroExtCarrier_solutions_7_ra06998_1 : Module A N := inflatedModule D X N
local instance instIsScalarTowerTrivSqZeroExtCarrier_solutions_7_ra06998_1 : IsScalarTower k A N := IsScalarTower.of_algebraMap_smul
    (fun a v => IsScalarTower.algebraMap_smul D a v)
def supportedLeadingIso (r n : ℕ) (t : Index (r+1) n) (h : inputDegree (r+1) t=0) :
    summand (leadingBarSequence k D X r) Z (r+1) n t ≅
      ModuleCat.of D (D ⊗[k] patternTerm k D X N (leadingPattern r n t)) := by
  rcases t with ⟨⟨⟨i,q⟩,hq⟩,t⟩
  exact eqToIso (leadingSummand_last k D X N r n i q hq t) ≪≫
    (barFunctor k D ⋙ HomologicalComplex.eval _ c i).mapIso
    (eqToIso (leadingSummand_prefix k D X Z r r q le_rfl t) ≪≫
      supportedInnerIso k D X N r q t h) ≪≫ freeBarPatternIso k D X N i (innerPattern r t)

theorem leadingSummandIso_explicit (r n i q : ℕ) (hq : i+q=n) (t : Index r q) :
    leadingSummandIso k D X Z r n ⟨⟨⟨i,q⟩,hq⟩,t⟩ =
      eqToIso (leadingSummand_last k D X N r n i q hq t) ≪≫
        (barFunctor k D ⋙ HomologicalComplex.eval _ c i).mapIso
          (eqToIso (leadingSummand_prefix k D X Z r r q le_rfl t) ≪≫
            innerSummandIso k D X Z r q t) ≪≫
          freeBarPatternIso k D X ((Z).X (inputDegree r t)) i (innerPattern r t) := by
  unfold leadingSummandIso
  change Eq.mpr (congrArg (fun W : ModuleCat D => W ≅
      ModuleCat.of D (D ⊗[k] patternTerm k D X ((Z).X (inputDegree r t))
        (List.replicate i false ++ innerPattern r t)))
      (leadingSummand_last k D X N r n i q hq t)) _ = _
  erw [iso_mpr_source]
  rfl

theorem supportedLeadingIso_eq (r n : ℕ) (t : Index (r+1) n) (h : inputDegree (r+1) t=0) :
    supportedLeadingIso k D X N r n t h = leadingSummandIso k D X Z r n t ≪≫
      eqToIso (congrArg (fun V : ModuleCat D => ModuleCat.of D
        (D ⊗[k] patternTerm k D X V (leadingPattern r n t)))
        (show (Z).X (inputDegree (r+1) t)=N by rw [h]; rfl)) := by
  rcases t with ⟨⟨⟨i,q⟩,hq⟩,t⟩
  let F := barFunctor k D ⋙ HomologicalComplex.eval _ c i
  let p := innerPattern r t
  let V := (Z).X (inputDegree r t)
  have hv : V=N := by change (Z).X (inputDegree r t)=N; rw [show inputDegree r t=0 from h]; rfl
  rw [leadingSummandIso_explicit]
  dsimp only [supportedLeadingIso]
  erw [Iso.trans_assoc]
  congr 1
  change F.mapIso (eqToIso _ ≪≫ supportedInnerIso k D X N r q t h) ≪≫
    freeBarPatternIso k D X N i p =
    F.mapIso (eqToIso _ ≪≫ innerSummandIso k D X Z r q t) ≪≫ (freeBarPatternIso k D X V i p ≪≫
      eqToIso (congrArg (fun W : ModuleCat D =>
        ModuleCat.of D (patternTerm k D X W (List.replicate (i+1) false ++ p))) hv))
  erw [supportedInnerIso_eq]
  exact mapIso_trans_congr F _ _ _ _ _ (freeBarPatternIso_eqToIso k D X V N hv i p)

theorem supportedLeading_length (r n : ℕ) (t : Index (r+1) n) (h : inputDegree (r+1) t=0) :
    (leadingPattern r n t).length=r+n := by
  have ht := length_leadingPattern r n t
  omega

theorem innerTotalEmbedding_supported_comp (r q : ℕ) (t : Index r q)
    (h : inputDegree r t = 0) :
    let p := innerPattern r t
    let V := summand B Z r q t
    let W := ModuleCat.of D (patternTerm k D X N p)
    let e := canonicalLinear k D X N (patternTerm k D X N p) p.length (embed k D X N p)
    (innerTotalEmbedding k D X N r q).comp
      (canonicalRestrict k D V ((iter B Z r).X q) (inclusion B Z r q t)) =
      (termCast k D X N (supportedInner_length r q t h)).comp
        (e.comp (canonicalRestrict k D V W (supportedInnerIso k D X N r q t h).hom)) := by
  dsimp only
  ext w
  change innerTotalEmbedding k D X N r q ((inclusion B Z r q t).hom w) =
    termCast k D X N (supportedInner_length r q t h)
      (canonicalLinear k D X N (patternTerm k D X N (innerPattern r t))
        (innerPattern r t).length (embed k D X N (innerPattern r t))
        ((supportedInnerIso k D X N r q t h).hom.hom w))
  rw [canonicalLinear_apply, innerTotalEmbedding_inclusion]
  exact innerEmbedding_supported k D X N r q t h w

theorem leadingTotalEmbedding_on_summand (r n i q : ℕ) (hq : i+q=n)
    (t : Index r q)
    (v : summand (leadingBarSequence k D X r) Z (r+1) n ⟨⟨⟨i,q⟩,hq⟩,t⟩) :
    let g := eqToHom (leadingSummand_prefix k D X Z r r q le_rfl t)
    let v' := (eqToHom (leadingSummand_last k D X N r n i q hq t)).hom v
    let u := ((barFunctor k D ⋙ HomologicalComplex.eval _ c i).map g).hom v'
    ((inclusion (leadingBarSequence k D X r) Z (r+1) n ⟨⟨⟨i,q⟩,hq⟩,t⟩ ≫
      eqToHom (congrArg (fun W => W.X n) (leadingIter_total k D X N r)) ≫
      leadingTotalEmbedding k D X N r n).hom v) =
    outerCast k D X N (show (r+q)+i=r+n by omega)
      (outerBarSuffix k D X N ((iter B Z r).X q) (r+q) i
        (innerTotalEmbedding k D X N r q)
        ((((barFunctor k D).map (inclusion B Z r q t)).f i).hom u)) := by
  dsimp only
  rw [← Category.assoc, leadingInclusion_total]
  erw [Category.assoc, Category.assoc, leadingTotalEmbedding_ι]
  simp only [Functor.map_comp, Category.assoc, ModuleCat.hom_comp, LinearMap.comp_apply,
    ModuleCat.hom_ofHom]
  rfl

theorem supportedLeadingIso_apply (r n i q : ℕ) (hq : i+q=n)
    (t : Index r q) (h : inputDegree r t = 0)
    (v : summand (leadingBarSequence k D X r) Z (r+1) n ⟨⟨⟨i,q⟩,hq⟩,t⟩) :
    let p := innerPattern r t
    let g := eqToHom (leadingSummand_prefix k D X Z r r q le_rfl t)
    let f := (supportedInnerIso k D X N r q t h).hom
    let v' := (eqToHom (leadingSummand_last k D X N r n i q hq t)).hom v
    let u := ((barFunctor k D ⋙ HomologicalComplex.eval _ c i).map g).hom v'
    (supportedLeadingIso k D X N r n ⟨⟨⟨i,q⟩,hq⟩,t⟩ h).hom.hom v =
      (freeBarPatternIso k D X N i p).hom.hom ((((barFunctor k D).map f).f i).hom u) := by
  dsimp only
  simp only [supportedLeadingIso, Iso.trans_hom,
    ModuleCat.hom_comp, LinearMap.comp_apply, eqToIso.hom]
  erw [Iso.trans_hom, Functor.mapIso_hom, Iso.trans_hom, Functor.map_comp]
  rfl

theorem outerBarSuffix_of_pattern (V : ModuleCat.{u} D) (p : List Bool)
    (f : V ⟶ ModuleCat.of D (patternTerm k D X N p)) (i b m : ℕ)
    (hp : p.length=b) (h₁ : b+i=m) (h₂ : (List.replicate i false ++ p).length=m)
    (v : ((barFunctor k D).obj V).X i) :
    outerCast k D X N h₁
      (outerBarSuffix k D X N V b i
        ((termCast k D X N hp).comp
          ((canonicalLinear k D X N (patternTerm k D X N p) p.length (embed k D X N p)).comp
            (canonicalRestrict k D V (ModuleCat.of D (patternTerm k D X N p)) f))) v) =
    outerCast k D X N h₂
      (AlgebraTensorModule.lTensor D D (embed k D X N (List.replicate i false ++ p))
        ((freeBarPatternIso k D X N i p).hom.hom ((((barFunctor k D).map f).f i).hom v))) := by
  rw [outerBarSuffix_termCast]
  erw [← outerBarSuffix_map k D X N V (ModuleCat.of D (patternTerm k D X N p))
    p.length i (canonicalLinear k D X N (patternTerm k D X N p) p.length
      (embed k D X N p)) f v]
  erw [outerBarSuffix_canonicalLinear k D X N (patternTerm k D X N p) p.length i
    (embed k D X N p)]
  rw [outerEmbed_freeBarPatternIso, outerCast_trans, outerCast_trans]

theorem outerBarSuffix_supported (r n i q : ℕ) (hq : i+q=n)
    (t : Index r q) (h : inputDegree r t=0)
    (u : ((barFunctor k D).obj (summand B Z r q t)).X i) :
    outerCast k D X N (show (r+q)+i=r+n by omega)
      (outerBarSuffix k D X N (summand B Z r q t) (r+q) i
        ((innerTotalEmbedding k D X N r q).comp
          (canonicalRestrict k D (summand B Z r q t) ((iter B Z r).X q)
            (inclusion B Z r q t))) u) =
    outerCast k D X N (supportedLeading_length r n ⟨⟨⟨i,q⟩,hq⟩,t⟩ h)
      (AlgebraTensorModule.lTensor D D (embed k D X N (List.replicate i false ++ innerPattern r t))
        ((freeBarPatternIso k D X N i (innerPattern r t)).hom.hom
          ((((barFunctor k D).map (supportedInnerIso k D X N r q t h).hom).f i).hom u))) := by
  let p := innerPattern r t
  let V := summand B Z r q t
  let W := ModuleCat.of D (patternTerm k D X N p)
  let f : V ⟶ W := (supportedInnerIso k D X N r q t h).hom
  let e := canonicalLinear k D X N (patternTerm k D X N p) p.length (embed k D X N p)
  have hp : p.length=r+q := supportedInner_length r q t h
  have he : (innerTotalEmbedding k D X N r q).comp
      (canonicalRestrict k D V ((iter B Z r).X q) (inclusion B Z r q t)) =
      (termCast k D X N hp).comp (e.comp (canonicalRestrict k D V W f)) :=
    innerTotalEmbedding_supported_comp k D X N r q t h
  rw [he]
  exact outerBarSuffix_of_pattern k D X N V p f i (r+q) (r+n) hp _ _ u

/-- The leading total embedding on every surviving recursive summand is the
original literal tensor inclusion under the previously constructed coordinates. -/
theorem leadingTotalEmbedding_supported (r n i q : ℕ) (hq : i+q=n) (t : Index r q)
    (h : inputDegree r t=0)
    (v : summand (leadingBarSequence k D X r) Z (r+1) n ⟨⟨⟨i,q⟩,hq⟩,t⟩) :
    ((inclusion (leadingBarSequence k D X r) Z (r+1) n ⟨⟨⟨i,q⟩,hq⟩,t⟩ ≫
      eqToHom (congrArg (fun W => W.X n) (leadingIter_total k D X N r)) ≫
      leadingTotalEmbedding k D X N r n).hom v) =
    outerCast k D X N (supportedLeading_length r n ⟨⟨⟨i,q⟩,hq⟩,t⟩ h)
      (AlgebraTensorModule.lTensor D D (embed k D X N (List.replicate i false ++ innerPattern r t))
        ((supportedLeadingIso k D X N r n ⟨⟨⟨i,q⟩,hq⟩,t⟩ h).hom.hom v)) := by
  let p := innerPattern r t
  let V := summand B Z r q t
  let g : summand (leadingBarSequence k D X r) Z r q t ⟶ V :=
    eqToHom (leadingSummand_prefix k D X Z r r q le_rfl t)
  let v' := (eqToHom (leadingSummand_last k D X N r n i q hq t)).hom v
  let u := (((barFunctor k D ⋙ HomologicalComplex.eval _ c i).map g).hom v')
  refine (leadingTotalEmbedding_on_summand k D X N r n i q hq t v).trans ?_
  change outerCast k D X N (show (r+q)+i=r+n by omega)
    (outerBarSuffix k D X N ((iter B Z r).X q) (r+q) i (innerTotalEmbedding k D X N r q)
      ((((barFunctor k D).map (inclusion B Z r q t)).f i).hom u)) = _
  rw [outerBarSuffix_map]
  change outerCast k D X N _ (outerBarSuffix k D X N V (r+q) i
    ((innerTotalEmbedding k D X N r q).comp
      (canonicalRestrict k D V ((iter B Z r).X q) (inclusion B Z r q t))) u) = _
  refine (outerBarSuffix_supported k D X N r n i q hq t h u).trans ?_
  exact (congrArg (fun w =>
    outerCast k D X N (supportedLeading_length r n ⟨⟨⟨i,q⟩,hq⟩,t⟩ h)
      (AlgebraTensorModule.lTensor D D (embed k D X N (List.replicate i false ++ p)) w))
    (supportedLeadingIso_apply k D X N r n i q hq t h v)).symm
end DerivedBar.ParityBridge

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Bar_FlatSupportedAssembly
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
open DerivedBar.Multibar DerivedBar.RecursiveTotal
universe u
variable (k D X : Type u) [Field k] [Ring D] [Algebra k D]
  [AddCommGroup X] [Module k X] [Module D X] [Module Dᵐᵒᵖ X]
  [SMulCommClass D Dᵐᵒᵖ X] [IsScalarTower k D X] [IsScalarTower k Dᵐᵒᵖ X]
variable (N : ModuleCat.{u} D)
local notation "A" => TrivSqZeroExt D X
local notation "Z" => Functor.obj (ChainComplex.single₀ (ModuleCat D)) N

attribute [local instance] OAI.DerivedBar.ParityBridge.instModuleCarrier_solutions_9
local instance instIsScalarTowerCarrier_solutions_9_ra06998_1 (V : ModuleCat.{u} D) : IsScalarTower k D V :=
  IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
local instance instDecidableEqIndex_2_ra06998_1 (r n : ℕ) : DecidableEq (Index r n) := Classical.decEq _
local instance instModuleTrivSqZeroExtCarrier_solutions_8_ra06998_1 : Module A N := inflatedModule D X N
local instance instIsScalarTowerTrivSqZeroExtCarrier_solutions_8_ra06998_1 : IsScalarTower k A N := IsScalarTower.of_algebraMap_smul
    (fun a v => IsScalarTower.algebraMap_smul D a v)
theorem moduleSummandIso_supported (r n : ℕ)
    (t : {t : Index (r+1) n // inputDegree (r+1) t=0})
    (ht : Multibar.Indexed.tensor k D X N (moduleShapeEquiv r n t)=
      patternTerm k D X N (leadingPattern r n t.val)) :
    moduleSummandIso k D X N r n t = supportedLeadingIso k D X N r n t.val t.property ≪≫
      eqToIso (congrArg (fun V : ModuleCat k => ModuleCat.of D (D ⊗[k] V)) ht.symm) := by
  rw [supportedLeadingIso_eq]
  rfl

theorem flatEmbedding_supported (r n : ℕ)
    (t : {t : Index (r+1) n // inputDegree (r+1) t=0}) :
    lof (leadingBarSequence k D X r) Z (r+1) n t.val ≫ flatEmbedding k D X N r n =
      (moduleSummandIso k D X N r n t).hom ≫
        ModuleCat.ofHom (Multibar.Indexed.outerInclusion k D X N (moduleShapeEquiv r n t)) := by
  rw [flatEmbedding_lof]
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro v
  let p := leadingPattern r n t.val
  let s := moduleShapeEquiv r n t
  have hp : Multibar.Indexed.toList s=p := moduleShape_toList r n t
  have ht : Multibar.Indexed.tensor k D X N s=patternTerm k D X N p := by
    rw [Multibar.Indexed.tensor_toList, hp]
  have hl : p.length=r+n := supportedLeading_length r n t.val t.property
  have hs := outerInclusion_pattern k D X N s p hp ht hl
    ((moduleSummandIso k D X N r n t).hom.hom v)
  have hc : (eqToHom (congrArg (fun V : ModuleCat k => ModuleCat.of D (D ⊗[k] V)) ht)).hom
      ((moduleSummandIso k D X N r n t).hom.hom v) =
      (supportedLeadingIso k D X N r n t.val t.property).hom.hom v := by
    rw [moduleSummandIso_supported k D X N r n t ht]
    simp only [Iso.trans_hom, eqToIso.hom, ModuleCat.hom_comp, LinearMap.comp_apply]
    have he := congrArg (fun f => f.hom
      ((supportedLeadingIso k D X N r n t.val t.property).hom.hom v))
      (eqToHom_trans (congrArg (fun V : ModuleCat k => ModuleCat.of D (D ⊗[k] V)) ht.symm)
        (congrArg (fun V : ModuleCat k => ModuleCat.of D (D ⊗[k] V)) ht))
    simpa only [ModuleCat.hom_comp, LinearMap.comp_apply, eqToHom_refl,
      ModuleCat.hom_id, LinearMap.id_apply] using he
  rw [hc] at hs
  change _ = Multibar.Indexed.outerInclusion k D X N s ((moduleSummandIso k D X N r n t).hom.hom v)
  rw [hs]
  rcases t with ⟨⟨⟨⟨i,q⟩,hq⟩,t⟩,h⟩
  exact leadingTotalEmbedding_supported k D X N r n i q hq t h v
end DerivedBar.ParityBridge

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Bar_IndexedAssemblyComparison
attribute [-instance] _root_.OAI.DerivedBar.term_finite _root_.OAI.DerivedBar.term_finiteDimensional _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.BimoduleCoefficients.instAddCommGroupCarrierTensorProductMulOpposite _root_.OAI.LittleFinitistic.BimoduleCoefficients.instModuleCarrierTensorProductMulOpposite _root_.OAI.LittleFinitistic.BimoduleCoefficients.instModuleCarrierTensorProductMulOpposite_1 _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instAddCommGroup _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instRing
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
open DerivedBar.Multibar DerivedBar.RecursiveTotal

universe u
variable (k D X : Type u) [Field k] [Ring D] [Algebra k D]
  [AddCommGroup X] [Module k X] [Module D X] [Module Dᵐᵒᵖ X]
  [SMulCommClass D Dᵐᵒᵖ X] [IsScalarTower k D X] [IsScalarTower k Dᵐᵒᵖ X]
variable (N : ModuleCat.{u} D)
local notation "A" => TrivSqZeroExt D X

attribute [local instance] OAI.DerivedBar.ParityBridge.instModuleCarrier_solutions_10
local instance instIsScalarTowerCarrier_solutions_10_ra06998_1 (V : ModuleCat.{u} D) : IsScalarTower k D V :=
  IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
local instance indexedAssemblyComparisonIndexDecidableEq_ra06998_1 (r n : ℕ) :
    DecidableEq (Index r n) := Classical.decEq _
local instance instModuleTrivSqZeroExtCarrier_solutions_9_ra06998_1 : Module A N := inflatedModule D X N
local instance instIsScalarTowerTrivSqZeroExtCarrier_solutions_9_ra06998_1 : IsScalarTower k A N := IsScalarTower.of_algebraMap_smul
    (fun a v => IsScalarTower.algebraMap_smul D a v)
attribute [local instance] OAI.DerivedBar.ParityBridge.indexedAssemblyComparisonShapeDecidableEq
theorem outerInclusion_eqToHom {n r : ℕ} (p q : Multibar.Indexed.Shape n r) (h : p=q) :
    eqToHom (congrArg (fun t => ModuleCat.of D (Multibar.Indexed.outerTensor k D X N t)) h) ≫
      ModuleCat.ofHom (Multibar.Indexed.outerInclusion k D X N q) =
    ModuleCat.ofHom (Multibar.Indexed.outerInclusion k D X N p) := by
  subst q
  simp

theorem reindexedModuleSummand_assembly (r n : ℕ) (p : Multibar.Indexed.Shape (r+n) r) :
    (reindexedModuleSummandIso k D X N r n p).inv ≫
      (moduleSummandIso k D X N r n ((moduleShapeEquiv r n).symm p)).hom ≫
        ModuleCat.ofHom (Multibar.Indexed.outerInclusion k D X N
          (moduleShapeEquiv r n ((moduleShapeEquiv r n).symm p))) =
    ModuleCat.ofHom (Multibar.Indexed.outerInclusion k D X N p) := by
  simp only [reindexedModuleSummandIso, Iso.trans_inv, Category.assoc, Iso.inv_hom_id_assoc]
  exact outerInclusion_eqToHom k D X N _ _ ((moduleShapeEquiv r n).apply_symm_apply p).symm

end DerivedBar.ParityBridge

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Bar_GlobalIndexedComparison
attribute [-instance] _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.BalancedTensor.scalarLeftTower _root_.OAI.LittleFinitistic.BimoduleCoefficients.instAddCommGroupCarrierTensorProductMulOpposite _root_.OAI.LittleFinitistic.BimoduleCoefficients.instModuleCarrierTensorProductMulOpposite _root_.OAI.LittleFinitistic.BimoduleCoefficients.instModuleCarrierTensorProductMulOpposite_1 _root_.OAI.LittleFinitistic.BimoduleCoefficients.towerLeft _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instAddCommGroup
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
local instance instModuleCarrier_solutions_11 (V : ModuleCat.{u} D) : Module k V := BimoduleTensor.scalarModule k D V
local instance instIsScalarTowerCarrier_solutions_11 (V : ModuleCat.{u} D) : IsScalarTower k D V :=
  IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
variable (N : ModuleCat.{u} D)
local notation "A" => TrivSqZeroExt D X
local instance globalIndexedComparisonIndexDecidableEq_ra06998_1 (r n : ℕ) :
    DecidableEq (Index r n) := Classical.decEq _
attribute [local instance] OAI.DerivedBar.ParityBridge.instModuleTrivSqZeroExtCarrier_solutions_10
local instance instIsScalarTowerTrivSqZeroExtCarrier_solutions_10 : IsScalarTower k A N := IsScalarTower.of_algebraMap_smul
    (fun a v => IsScalarTower.algebraMap_smul D a v)

end DerivedBar.ParityBridge

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Bar_IntegerCountRestriction
attribute [-instance] _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.BimoduleCoefficients.instAddCommGroupCarrierTensorProductMulOpposite _root_.OAI.LittleFinitistic.BimoduleCoefficients.instModuleCarrierTensorProductMulOpposite _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instAddCommGroup _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instRing
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
variable (N : ModuleCat D)
local notation "A" => TrivSqZeroExt D X
local notation "E" => ComplexShape.embeddingDownNat
local notation "K" => Multibar.Indexed.signedBlockComplex k D X N (inflated_ideal_zero D X N)

attribute [local instance] OAI.DerivedBar.ParityBridge.integerCountRestrictionScalarModule
attribute [local instance] OAI.DerivedBar.ParityBridge.integerCountRestrictionScalarTower
local instance integerCountRestrictionIndexDecidableEq_ra06998_1 (r n : ℕ) :
    DecidableEq (Index r n) := Classical.decEq _
local instance integerCountRestrictionShapeDecidableEq_ra06998_1 (n r : ℕ) :
    DecidableEq (Multibar.Indexed.Shape n r) := Classical.decEq _
attribute [local instance] OAI.DerivedBar.ParityBridge.integerCountRestrictionInflatedModule
attribute [local instance] OAI.DerivedBar.ParityBridge.integerCountRestrictionInflatedScalarTower
def deshiftedCountXIso (r n : ℕ) : (deshiftedCountRestriction k D X N r).X n ≅
    indexedModule k D X N r n :=
  (K r).extendXIso E
    (show (E).f (r+n) = (E).f n + -(r:ℤ) by change -((r+n:ℕ):ℤ) = -(n:ℤ) + -(r:ℤ); push_cast; omega)

end DerivedBar.ParityBridge

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Bar_IntegerCountShift
attribute [-instance] _root_.OAI.ExternalTensor.Section4.SourceFiltration.zeroTermSubsingleton _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.BimoduleCoefficients.instAddCommGroupCarrierTensorProductMulOpposite _root_.OAI.LittleFinitistic.BimoduleCoefficients.instModuleCarrierTensorProductMulOpposite _root_.OAI.LittleFinitistic.BimoduleCoefficients.instModuleCarrierTensorProductMulOpposite_1 _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instAddCommGroup _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instRing
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
open DerivedBar.Multibar DerivedBar.RecursiveTotal
universe u
variable (k D X : Type u) [Field k] [Ring D] [Algebra k D]
  [AddCommGroup X] [Module k X] [Module D X] [Module Dᵐᵒᵖ X]
  [SMulCommClass D Dᵐᵒᵖ X] [IsScalarTower k D X] [IsScalarTower k Dᵐᵒᵖ X]
variable (N : ModuleCat D)
local notation "A" => TrivSqZeroExt D X
local notation "E" => ComplexShape.embeddingDownNat
local notation "K" => Multibar.Indexed.signedBlockComplex k D X N (inflated_ideal_zero D X N)

local instance instDecidableEqIndex_3_ra06998_1 (r n : ℕ) : DecidableEq (Index r n) := Classical.decEq _
local instance instDecidableEqShape_ra06998_1 (n r : ℕ) : DecidableEq (Multibar.Indexed.Shape n r) := Classical.decEq _
theorem shapeCount_le {n r : ℕ} (p : Multibar.Indexed.Shape n r) : r≤n := by
  induction p <;> omega

attribute [local instance] OAI.DerivedBar.ParityBridge.instModuleCarrier_solutions_12
attribute [local instance] OAI.DerivedBar.ParityBridge.instIsScalarTowerCarrier_solutions_12
attribute [local instance] OAI.DerivedBar.ParityBridge.instModuleTrivSqZeroExtCarrier_solutions_11
attribute [local instance] OAI.DerivedBar.ParityBridge.instIsScalarTowerTrivSqZeroExtCarrier_solutions_11
theorem signedBlock_isZero_of_lt (n r : ℕ) (h : n < r) : IsZero ((K r).X n) := by
  have : IsEmpty (Multibar.Indexed.Shape n r) :=
    ⟨fun shape => (Nat.not_le_of_lt h) (shapeCount_le shape)⟩
  change IsZero (ModuleCat.of D (⨁ p : Multibar.Indexed.Shape n r, Multibar.Indexed.outerTensor k D X N p))
  exact ModuleCat.isZero_of_subsingleton _

/-- The actual -r-shifted count complex is strictly zero in positive cochain
degrees, including the range cut off by the lower count bound. -/
theorem deshiftedCount_isZero_positive (r : ℕ) (j : ℤ) (hj : 0<j) :
    IsZero ((deshiftedCount k D X N r).X j) := by
  change IsZero (((K r).extend E).X (j + -(r:ℤ)))
  by_cases hle : j + -(r:ℤ) ≤ 0
  · let n := (-(j + -(r:ℤ))).toNat
    have hn : (E).f n=j + -(r:ℤ) := by
      change -(n:ℤ)=j + -(r:ℤ)
      dsimp [n]
      rw [Int.toNat_of_nonneg (by omega)]
      omega
    have hnr : n < r := by
      change -(n:ℤ)=j + -(r:ℤ) at hn
      omega
    exact (signedBlock_isZero_of_lt k D X N n r hnr).of_iso ((K r).extendXIso E hn)
  · exact (K r).isZero_extend_X E _ (fun i hi => by
      change -(i:ℤ)=j + -(r:ℤ) at hi
      omega)

instance deshiftedCount_strictSupport (r : ℕ) : (deshiftedCount k D X N r).IsStrictlySupported E where
  isZero j hj := deshiftedCount_isZero_positive k D X N r j (by
    by_contra h
    have hle : j≤0 := by omega
    apply hj (-j).toNat
    change -((-j).toNat:ℤ)=j
    rw [Int.toNat_of_nonneg (by omega)]
    omega)

end DerivedBar.ParityBridge

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Rectification_InducedRectification
attribute [-instance] _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.ExternalTensor.Section4.ArrowVertex.vertex_additive _root_.OAI.ExternalTensor.Section4.SourceFiltration.inclusion2_isIso _root_.OAI.ExternalTensor.Section4.SourceFiltration.zeroCone_inclusion_isIso _root_.OAI.ExternalTensor.Section4.SourceFiltration.zeroTermSubsingleton _root_.OAI.ExternalTensor.Section4.forgetK_additive _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instAddCommGroup _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open CategoryTheory CategoryTheory.Limits
namespace LittleFinitistic.InducedRectification
open ExternalTensor.Section4
universe u
variable {k B : Type u} [Field k] [Ring B] [Algebra k B]
variable {A J R : Type} [Fintype A] [Fintype J] [Fintype R]
variable (s : Quadratic k B (A := A) (J := J) (R := R))
variable (D₀ D₁ D₂ : RightComplex B)
variable (f : A → (D₀ ⟶ D₁)) (g : J → (D₁ ⟶ D₂))
variable (H : ∀ r, Homotopy (relationMap s D₀ D₁ D₂ f g r) 0)

/-- Its right-module restriction, retaining the original bimodule construction. -/
def rightTotal : RightComplex B :=
  ((forgetRight k B).mapHomologicalComplex (.up ℤ)).obj (total s D₀ D₁ D₂ f g H)

end LittleFinitistic.InducedRectification

end

end OAI
end



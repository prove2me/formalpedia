-- Prove2me | Definitions.Def_OAIQ023F011
-- name    : OAIQ023F011
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-30T16:02:04.071258+00:00
-- url     : https://prove2.me/theorems/6861ca07-0df7-4640-945e-c3c9338b9a43
-- title:
--   Definitions bundle OAIQ023F011 of the split of OpenAI, An algebra of infinite little finitistic dimension (result family 198)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.LittleFinitistic.Main.exists_counterexample`, carved from OpenAI's openai/math development (OpenAI, *An algebra of infinite little finitistic dimension (result family 198)*, OpenAI Math Release, September 23, 2026, result family 198, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 58 declarations of OpenAI's Lean: 24 definitions, 7 instances and 27 theorems. The definitions and types are `OAI.DerivedBar.SquareZero.twoSidedWeightEquiv`, `OAI.ExternalTensor.Section4.ArrowVertex.NativeBridge.nativeCompatibility12`, `OAI.ExternalTensor.Section4.SourceFiltration.Exactness.P`, `OAI.ExternalTensor.Section4.SourceFiltration.Exactness.i1`, `OAI.ExternalTensor.Section4.SourceFiltration.Exactness.i2`, `OAI.ExternalTensor.Section4.SourceFiltration.Exactness.pi0`, `OAI.ExternalTensor.Section4.SourceFiltration.coneIso`, `OAI.ExternalTensor.Section4.SourceFiltration.h2`, `OAI.ExternalTensor.Section4.SourceFiltration.include1`, `OAI.ExternalTensor.Section4.SourceFiltration.include2`, `OAI.ExternalTensor.Section4.SourceFiltration.inducedInclude1`, `OAI.ExternalTensor.Section4.SourceFiltration.inducedQuotient0`, `OAI.ExternalTensor.Section4.SourceFiltration.p2`, `OAI.ExternalTensor.Section4.SourceFiltration.quotient0`, `OAI.ExternalTensor.Section4.SourceFiltration.twoColumnIso`, `OAI.ExternalTensor.Section4.SourceFiltration.v2Inclusion`, `OAI.ExternalTensor.Section4.SourceFiltration.v2Iso`, `OAI.ExternalTensor.Section4.columnRightIso`, `OAI.ExternalTensor.Section4.forgetK`, `OAI.ExternalTensor.Section4.h`, `OAI.ExternalTensor.Section4.termK`, `OAI.ExternalTensor.Section4.termRight`, `OAI.LittleFinitistic.AdjacentArrowSum.vertexComplex`, `OAI.LittleFinitistic.QuadraticEncoding.commutation`.
--
--   **Sources.** They come from these modules of lean/OAI/Algebra, in whole or in part: `Finitistic_Bar_BlockCoordinateGenerators`, `Finitistic_Bar_Projection`, `Finitistic_Bar_Splitting`, `Finitistic_Bar_TensorModel`, `Finitistic_Bar_TotalBarTensor`, `Finitistic_Encoding_QuadraticEncoding`, `Finitistic_Localization_NativeArrowBridge`, `Finitistic_Rectification_AdjacentArrowSum`, `Finitistic_Rectification_ColumnFinite`, `Finitistic_Rectification_ColumnProperties`, `Finitistic_Rectification_FiltrationExactness`, `Finitistic_Rectification_InducedDiagram`, `Finitistic_Rectification_SourceFiltration`, `Finitistic_Rectification_SourceFiltrationComplex`, `Finitistic_Rectification_SourceFiltrationCone`, `Finitistic_Rectification_SourceFiltrationExact`, `Finitistic_Rectification_SourceFiltrationReal`.
--
--   **Imports.** It imports the bundles `OAIQ023F005`, `OAIQ023F006` and `OAIQ023F007` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ023F016`, `OAIQ023F017`, `OAIQ023F018` and `OAIQ023F019`.
-- source:
--   OpenAI, An algebra of infinite little finitistic dimension (result family 198), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 198; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/An-algebra-of-infinite-little-finitistic-dimension-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Algebra at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ023F005
import Definitions.Def_OAIQ023F006
import Definitions.Def_OAIQ023F007

set_option maxHeartbeats 1000000

section
-- module Solutions.OAIQ023_Fin.Finitistic_Bar_TotalBarTensor
attribute [-instance] _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
open CategoryTheory CategoryTheory.Limits HomologicalComplex
noncomputable section
namespace DerivedBar
universe u
variable (k D : Type u) [Field k] [Ring D] [Algebra k D]

variable (X : Type u) [AddCommGroup X] [Module k X] [Module D X] [Module Dᵐᵒᵖ X]
  [SMulCommClass D Dᵐᵒᵖ X] [IsScalarTower k D X] [IsScalarTower k Dᵐᵒᵖ X]

/-- On a projective chain input, tensoring the augmentation is a quasi-isomorphism,
even when X is not flat. This identifies the construction with tensor of that projective model. -/
instance tensorTotalAugmentation_quasiIso (P : ChainComplex (ModuleCat.{u} D) ℕ)
    [∀ n, Projective (P.X n)] :
    QuasiIso (((BimoduleTensor.tensorFunctor k D X).mapHomologicalComplex (ComplexShape.down ℕ)).map
      (barTotalAugmentation k D P)) := by
  let : ∀ n, Projective ((barTotal k D P).X n) := barTotal_projective k D P
  exact additive_map_quasiIso_of_projective D (BimoduleTensor.tensorFunctor k D X)
    (barTotalAugmentation k D P)

instance tensorTotalIterate_map_quasiIso (r : ℕ) {Z W : ChainComplex (ModuleCat.{u} D) ℕ}
    (f : Z ⟶ W) [QuasiIso f] : QuasiIso ((tensorTotalIterate k D X r).map f) := by
  induction r with
  | zero => exact inferInstanceAs (QuasiIso f)
  | succ r ih =>
    let := ih
    exact tensorTotalFunctor_map_quasiIso k D X ((tensorTotalIterate k D X r).map f)
end DerivedBar

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Bar_Projection
attribute [-instance] _root_.OAI.DerivedBar.Multibar.patternModule _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.DerivedBar.term_finite _root_.OAI.DerivedBar.term_finiteDimensional _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.BimoduleCoefficients.instAddCommGroupCarrierTensorProductMulOpposite _root_.OAI.LittleFinitistic.BimoduleCoefficients.instModuleCarrierTensorProductMulOpposite_1 _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instAddCommGroup _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instRing
attribute [-simp] _root_.OAI.DerivedBar.SquareZero.signedProjection_base _root_.OAI.DerivedBar.SquareZero.signedProjection_ideal_succ _root_.OAI.DerivedBar.SquareZero.signedProjection_ideal_zero _root_.OAI.DerivedBar.SquareZero.twoSidedProjection_tmul _root_.OAI.DerivedBar.termMap_tmul _root_.OAI.ExternalTensor.Section4.sum_hom
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

/-- The projections separate homogeneous bar words exactly. -/
theorem projection_word {n s : ℕ} {v : term k (TrivSqZeroExt D X) N n}
    (hv : Word k D X N n s v) (r : ℕ) :
    projection k D X N n r v = if r = s then v else 0 := by
  induction hv generalizing r with
  | nil v => cases r <;> simp [projection]
  | @base n s v d h ih =>
    rw [projection_base, ih]
    split <;> simp_all
  | @ideal n s v x h ih =>
    cases r with
    | zero =>
      rw [projection_ideal_zero k D X N n x v]
      simp
    | succ r =>
      rw [projection_ideal_succ, ih]
      by_cases hrs : r = s <;> simp [hrs]


variable (k D X N)

/-- Expanding each actual algebra entry as D ⊕ X spans every absolute bar term. -/
theorem all_words_span (n : ℕ) :
    Submodule.span k {v : term k (TrivSqZeroExt D X) N n |
      ∃ r, Word k D X N n r v} = ⊤ := by
  induction n with
  | zero =>
    apply top_unique
    intro v _
    exact Submodule.subset_span ⟨0, Word.nil v⟩
  | succ n ih =>
    apply top_unique
    intro v _
    induction v using OAI.tensorInductionOn with
    | add x y hx hy => exact Submodule.add_mem _ (hx trivial) (hy trivial)
    | tmul a v =>
      let T := Submodule.span k {w : term k (TrivSqZeroExt D X) N (n+1) |
        ∃ r, Word k D X N (n+1) r w}
      let g := TensorProduct.mk k (TrivSqZeroExt D X) (term k (TrivSqZeroExt D X) N n) a
      have hle : Submodule.span k {w | ∃ r, Word k D X N n r w} ≤ T.comap g := by
        apply Submodule.span_le.mpr
        rintro w ⟨r, hw⟩
        change a ⊗ₜ[k] w ∈ T
        rw [← inl_fst_add_inr_snd_eq a, TensorProduct.add_tmul]
        exact Submodule.add_mem _
          (Submodule.subset_span ⟨r, Word.base a.fst hw⟩)
          (Submodule.subset_span ⟨r+1, Word.ideal a.snd hw⟩)
      apply hle
      rw [ih]
      trivial

end DerivedBar.SquareZero

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Bar_Splitting
attribute [-instance] _root_.OAI.DerivedBar.Multibar.patternModule _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.DerivedBar.term_finite _root_.OAI.DerivedBar.term_finiteDimensional _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.BimoduleCoefficients.instAddCommGroupCarrierTensorProductMulOpposite _root_.OAI.LittleFinitistic.BimoduleCoefficients.instModuleCarrierTensorProductMulOpposite_1 _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.ProductModules.firstModule _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instAddCommGroup _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
open scoped TensorProduct DirectSum
open TensorProduct CategoryTheory TrivSqZeroExt
noncomputable section

namespace DerivedBar.SquareZero
universe u

variable (k D X N : Type u) [Field k] [Ring D] [Algebra k D]
  [AddCommGroup X] [Module k X] [Module D X] [Module Dᵐᵒᵖ X]
  [SMulCommClass D Dᵐᵒᵖ X] [IsScalarTower k D X] [IsScalarTower k Dᵐᵒᵖ X]
  [AddCommGroup N] [Module k N]

variable {k D X N}

theorem twoSidedProjection_self {n r : ℕ}
    {v : D ⊗[k] term k (TrivSqZeroExt D X) N n} (hv : v ∈ twoSidedWeight k D X N n r) :
    twoSidedProjection k D X N n r v = v := by
  have hle : twoSidedWeight k D X N n r ≤
      (twoSidedProjection k D X N n r - LinearMap.id).ker := by
    apply Submodule.span_le.mpr
    rintro w ⟨d, z, hz, rfl⟩
    change d ⊗ₜ[k] projection k D X N n r z - d ⊗ₜ[k] z = 0
    rw [projection_word hz r, ite_eq_left rfl, sub_self]
  have hz := hle hv
  change twoSidedProjection k D X N n r v - v = 0 at hz
  exact sub_eq_zero.mp hz

theorem twoSidedProjection_other {n r s : ℕ} (hrs : r ≠ s)
    {v : D ⊗[k] term k (TrivSqZeroExt D X) N n} (hv : v ∈ twoSidedWeight k D X N n s) :
    twoSidedProjection k D X N n r v = 0 := by
  have hle : twoSidedWeight k D X N n s ≤ (twoSidedProjection k D X N n r).ker := by
    apply Submodule.span_le.mpr
    rintro w ⟨d, z, hz, rfl⟩
    change d ⊗ₜ[k] projection k D X N n r z = 0
    rw [projection_word hz r, ite_eq_right hrs, TensorProduct.tmul_zero]
  exact hle hv

variable (k D X N)

/-- Expansion of internal A entries as D ⊕ X spans the two-sided bar term as a D-module. -/
theorem twoSidedWeight_iSup (n : ℕ) : (⨆ r, twoSidedWeight k D X N n r) = ⊤ := by
  apply top_unique
  intro v hv
  clear hv
  induction v using OAI.tensorInductionOn with
  | add x y hx hy => exact Submodule.add_mem _ hx hy
  | tmul d v =>
    let T := (⨆ r, twoSidedWeight k D X N n r)
    let g := TensorProduct.mk k D (term k (TrivSqZeroExt D X) N n) d
    have hle : Submodule.span k {w | ∃ r, Word k D X N n r w} ≤
        (T.restrictScalars k).comap g := by
      apply Submodule.span_le.mpr
      rintro w ⟨r, hw⟩
      exact (le_iSup (twoSidedWeight k D X N n) r)
        (Submodule.subset_span ⟨d, w, hw, rfl⟩)
    apply hle
    rw [all_words_span]
    trivial

/-- The genuine D-module decomposition of each two-sided bar term by X-count. -/
theorem twoSidedWeight_internal (n : ℕ) : DirectSum.IsInternal (twoSidedWeight k D X N n) :=
  internal_of_projections _ (twoSidedProjection k D X N n)
    (fun _ _ h => twoSidedProjection_self h)
    (fun _ _ h _ hv => twoSidedProjection_other h hv)
    (twoSidedWeight_iSup k D X N n)

/-- Canonical sum of homogeneous tensors, as a linear equivalence. -/
def twoSidedWeightEquiv (n : ℕ) :
    (⨁ r : ℕ, twoSidedWeight k D X N n r) ≃ₗ[D]
      D ⊗[k] term k (TrivSqZeroExt D X) N n :=
  LinearEquiv.ofBijective (DirectSum.coeLinearMap _) (twoSidedWeight_internal k D X N n)
end DerivedBar.SquareZero

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Bar_BlockCoordinateGenerators
attribute [-instance] _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.BimoduleCoefficients.instAddCommGroupCarrierTensorProductMulOpposite _root_.OAI.LittleFinitistic.BimoduleCoefficients.instModuleCarrierTensorProductMulOpposite _root_.OAI.LittleFinitistic.BimoduleCoefficients.instModuleCarrierTensorProductMulOpposite_1 _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instAddCommGroup _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
open CategoryTheory CategoryTheory.Limits TensorProduct
open scoped TensorProduct DirectSum
noncomputable section
namespace DerivedBar.RecursiveTotal
universe u

variable (k D X : Type u) [Field k] [Ring D] [Algebra k D]
  [AddCommGroup X] [Module k X] [Module D X] [Module Dᵐᵒᵖ X]
  [SMulCommClass D Dᵐᵒᵖ X] [IsScalarTower k D X] [IsScalarTower k Dᵐᵒᵖ X]
variable (N : ModuleCat.{u} D)
local notation "Z" => (Functor.obj (ChainComplex.single₀ (ModuleCat D)) N)

attribute [local instance] OAI.DerivedBar.RecursiveTotal.instModuleCarrier_solutions_3
local instance instIsScalarTowerCarrier_solutions_3_r56f92a_1 (N : ModuleCat.{u} D) : IsScalarTower k D N :=
  IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
attribute [local instance] OAI.DerivedBar.RecursiveTotal.instDecidableEqIndex_3
attribute [local instance] OAI.DerivedBar.RecursiveTotal.instDecidableEqShape_1
/-- The inverse coordinate map on a literal block generator is exactly its
recursive tensor inclusion, with the proved tensor-coordinate isomorphism. -/
theorem moduleFlatCoordinates_inv_lof (r n : ℕ) (p : Multibar.Indexed.Shape (r+n) r) :
    ModuleCat.ofHom (DirectSum.lof D (Multibar.Indexed.Shape (r+n) r)
      (Multibar.Indexed.outerTensor k D X N) p) ≫ (moduleFlatCoordinates k D X N r n).inv =
    (reindexedModuleSummandIso k D X N r n p).inv ≫
      lof (leadingBarSequence k D X r) Z (r+1) n ((moduleShapeEquiv r n).symm p).val := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro v
  dsimp only [moduleFlatCoordinates]
  erw [Iso.trans_inv, Iso.trans_inv]
  simp only [ModuleCat.hom_comp,
    LinearEquiv.toModuleIso_inv, ModuleCat.hom_ofHom, LinearMap.comp_apply,
    LinearEquiv.coe_coe]
  erw [congrLinearEquiv_symm_lof, DirectSum.lequivCongrLeft_symm_lof]
  simp only [supportIso]
  exact DirectSum.toModule_lof D
    (N := flat (leadingBarSequence k D X r) Z (r+1) n)
    (M := fun t : {t : Index (r+1) n // inputDegree (r+1) t=0} =>
      summand (leadingBarSequence k D X r) Z (r+1) n t.val)
    ((moduleShapeEquiv r n).symm p) ((reindexedModuleSummandIso k D X N r n p).inv.hom v)

end DerivedBar.RecursiveTotal

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Bar_TensorModel
attribute [-instance] _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instAddCommGroup
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

/-- The balanced free-tensor equivalence respects arbitrary A-linear maps, including bar faces. -/
theorem freeEquiv_natural (V W : Type u) [AddCommGroup V] [Module k V]
    [AddCommGroup W] [Module k W] (h : A ⊗[k] V →ₗ[A] A ⊗[k] W) :
    (Balanced.descend f W).comp (Balanced.map f (A ⊗[k] V) (A ⊗[k] W) h) =
      (FreeBaseChange.map f V W h).comp (Balanced.descend f V) := by
  apply (Balanced.relations f (A ⊗[k] V)).linearMap_qext
  apply AlgebraTensorModule.ext
  intro d z
  change d • FreeBaseChange.coefficient f W (h z) =
    FreeBaseChange.map f V W h (d • FreeBaseChange.coefficient f V z)
  rw [LinearMap.map_smul, FreeBaseChange.map_coefficient]

end DerivedBar

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Encoding_QuadraticEncoding
attribute [-instance] _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear
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

def commutation (h : Fin d) : Paths k d :=
  basis h.succ ⊗ₜ[k] basis 0 - basis 0 ⊗ₜ[k] basis h.succ

end LittleFinitistic.QuadraticEncoding

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Rectification_InducedDiagram
attribute [-instance] _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.ExternalTensor.Section4.ArrowVertex.vertex_additive _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instAddCommGroup _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped TensorProduct ModuleCat.Algebra
noncomputable section
namespace ExternalTensor.Section4
universe u
variable (k B : Type u) [Field k] [Ring B] [Algebra k B]

variable {A J R : Type} [Fintype A] [Fintype J] [Fintype R]

variable {k B}
variable (s : Quadratic k B (A := A) (J := J) (R := R))
variable (D₀ D₁ D₂ : RightComplex B)
variable (f : A → (D₀ ⟶ D₁)) (g : J → (D₁ ⟶ D₂))

variable (H : ∀ r, Homotopy (relationMap s D₀ D₁ D₂ f g r) 0)

/-- The manuscript h, with zero components away from degree minus one. -/
def h (i j : ℤ) := (positiveHomotopy s D₀ D₁ D₂ f g H).hom i j

theorem h_formula (i j : ℤ) : h s D₀ D₁ D₂ f g H i j =
    ∑ r, (biproduct.π (inducedData s D₀ D₁ D₂ f g).W r).f i ≫
      (columnFunctor k B s.e₂).map ((H r).hom i j) ≫
      (inducedData s D₀ D₁ D₂ f g).in₂.f j := rfl

end ExternalTensor.Section4

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Rectification_ColumnProperties
attribute [-instance] _root_.OAI.DerivedBar.Multibar.patternModule _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.DerivedBar.termModule _root_.OAI.ExternalTensor.Section4.ArrowVertex.vertex_additive _root_.OAI.LittleFinitistic.BalancedTensor.scalarModuleTower _root_.OAI.LittleFinitistic.BimoduleCoefficients.instAddCommGroupCarrierTensorProductMulOpposite _root_.OAI.LittleFinitistic.BimoduleCoefficients.instModuleCarrierTensorProductMulOpposite _root_.OAI.LittleFinitistic.BimoduleCoefficients.instModuleCarrierTensorProductMulOpposite_1 _root_.OAI.LittleFinitistic.BimoduleCoefficients.towerRight _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.ProductModules.firstModule _root_.OAI.LittleFinitistic.TensorComplex.scalarTower _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instAddCommGroup _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instRing
attribute [-simp] _root_.OAI.ExternalTensor.Section4.ArrowVertex.arrow_id _root_.OAI.ExternalTensor.Section4.ArrowVertex.arrow_original _root_.OAI.ExternalTensor.Section4.ArrowVertex.iota_original _root_.OAI.ExternalTensor.Section4.ArrowVertex.left_mul _root_.OAI.ExternalTensor.Section4.ArrowVertex.map_left _root_.OAI.ExternalTensor.Section4.ArrowVertex.mem_space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped TensorProduct ModuleCat.Algebra
noncomputable section
namespace ExternalTensor.Section4
universe u
variable (k B : Type u) [Field k] [Ring B] [Algebra k B]
attribute [local instance] ExternalTensor.bimodule ExternalTensor.rightModule

instance forgetRight_additive : (forgetRight k B).Additive := by
  dsimp [forgetRight]
  infer_instance

/-- The restricted action is the right action already verified for the actual tensor. -/
def columnRightIso (e : B) (N : ModuleCat.{u} Bᵐᵒᵖ) :
    (forgetRight k B).obj ((columnFunctor k B e).obj N) ≅
      ModuleCat.of Bᵐᵒᵖ (Column k B N e) :=
  (show ((forgetRight k B).obj ((columnFunctor k B e).obj N)) ≃ₗ[Bᵐᵒᵖ]
      (ModuleCat.of Bᵐᵒᵖ (Column k B N e)) from
    { toFun := id
      invFun := id
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl
      map_smul' := fun c x => by
        change ((1 ⊗ₜ[k] c : Enveloping k B) • (show Column k B N e from x)) =
          c • (show Column k B N e from x)
        exact (right_eq_enveloping k B (leftIdeal B e) N c x).symm }).toModuleIso

abbrev termRight (n : ℤ) : BiComplex k B ⥤ ModuleCat.{u} Bᵐᵒᵖ :=
  eval _ _ n ⋙ forgetRight k B

theorem biprod_right_projective (K L : BiComplex k B) (n : ℤ)
    (hK : Projective ((termRight k B n).obj K))
    (hL : Projective ((termRight k B n).obj L)) :
    Projective ((termRight k B n).obj (K ⊞ L)) := by
  let := hK
  let := hL
  let := preservesBinaryBiproducts_of_preservesBiproducts (termRight k B n)
  exact Projective.of_iso ((termRight k B n).mapBiprod K L).symm (by infer_instance)

theorem biprod_term_isZero (K L : BiComplex k B) (n : ℤ)
    (hK : IsZero (K.X n)) (hL : IsZero (L.X n)) : IsZero ((K ⊞ L).X n) := by
  apply ((HomologicalComplex.eval _ _ n).mapBiprod K L).isZero_iff.mpr
  exact (biprod_isZero_iff _ _).mpr ⟨hK, hL⟩

end ExternalTensor.Section4

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Localization_NativeArrowBridge
attribute [-instance] _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
open CategoryTheory HomologicalComplex
open scoped TensorProduct
noncomputable section
namespace ExternalTensor.Section4.ArrowVertex.NativeBridge
universe u
variable (k B : Type u) [Field k] [Ring B] [Algebra k B]

variable {k B}
variable {A J R : Type} [Fintype A] [Fintype J] [Fintype R]
variable (s : Quadratic k B (A := A) (J := J) (R := R))
variable (D₀ D₁ D₂ : RightComplex B)
variable (f : A → (D₀ ⟶ D₁)) (g : J → (D₁ ⟶ D₂))
variable (H : ∀ r, Homotopy (relationMap s D₀ D₁ D₂ f g r) 0)

/-- Actual arrow-12 compatibility with the native P, vertex functors and inclusions. -/
def nativeCompatibility12 (h₁ : s.e₁ * s.e₁ = s.e₁) (h₂ : s.e₂ * s.e₂ = s.e₂)
    (b : J) (hb : s.e₂ * s.b b = s.b b) :
    Homotopy
      (originalIota s D₀ D₁ D₂ f g H s.e₁ h₁ D₁ (inducedData s D₀ D₁ D₂ f g).in₁ ≫
        arrowComplex k B s.e₁ s.e₂ (s.b b) hb
          (LittleFinitistic.InducedRectification.total s D₀ D₁ D₂ f g H))
      (g b ≫ originalIota s D₀ D₁ D₂ f g H s.e₂ h₂ D₂
        (inducedData s D₀ D₁ D₂ f g).in₂) := by
  have ht := compatibility12 s D₀ D₁ D₂ f g H h₁ h₂ b hb
  dsimp only [iota1, iota2] at ht
  erw [iota_eq_original s D₀ D₁ D₂ f g H,
    iota_eq_original s D₀ D₁ D₂ f g H] at ht
  exact ht
end ExternalTensor.Section4.ArrowVertex.NativeBridge

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Rectification_AdjacentArrowSum
attribute [-instance] _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct ModuleCat.Algebra
namespace LittleFinitistic.AdjacentArrowSum
universe u
variable {k V W U : Type u} [Field k] [AddCommGroup V] [Module k V]
  [AddCommGroup W] [Module k W] [AddCommGroup U] [Module k U]
variable (μ : W →ₗ[k] V →ₗ[k] U)
variable (D : CochainComplex (ModuleCat.{u} (ThreeVertexAlgebra μ)ᵐᵒᵖ) ℤ)
local notation "T" => ThreeVertexAlgebra μ
local instance instHasFiniteBiproductsCochainComplexModuleCatMulOppositeThreeVertexAlgebraInt : HasFiniteBiproducts (CochainComplex (ModuleCat.{u} Tᵐᵒᵖ) ℤ) :=
  HasFiniteBiproducts.of_hasFiniteProducts
abbrev vertexComplex (v : Fin 3) :=
  (BimoduleVertex.functor k T (ThreeVertexAlgebra.vertex μ v)).mapHomologicalComplex (.up ℤ)

end LittleFinitistic.AdjacentArrowSum

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Rectification_ColumnFinite
attribute [-instance] _root_.OAI.DerivedBar.Multibar.patternModule _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.DerivedBar.termModule _root_.OAI.ExternalTensor.Section4.ArrowVertex.vertex_additive _root_.OAI.LittleFinitistic.BimoduleCoefficients.instAddCommGroupCarrierTensorProductMulOpposite _root_.OAI.LittleFinitistic.BimoduleCoefficients.instModuleCarrierTensorProductMulOpposite_1 _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instAddCommGroup _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instRing
attribute [-simp] _root_.OAI.ExternalTensor.Section4.ArrowVertex.arrow_id _root_.OAI.ExternalTensor.Section4.ArrowVertex.arrow_original _root_.OAI.ExternalTensor.Section4.ArrowVertex.iota_original _root_.OAI.ExternalTensor.Section4.ArrowVertex.left_mul _root_.OAI.ExternalTensor.Section4.ArrowVertex.map_left _root_.OAI.ExternalTensor.Section4.ArrowVertex.mem_space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped TensorProduct ModuleCat.Algebra
noncomputable section
namespace ExternalTensor.Section4
universe u
variable (k B : Type u) [Field k] [Ring B] [Algebra k B]
attribute [local instance] ExternalTensor.bimodule ExternalTensor.rightModule

def forgetK : ModuleCat.{u} (Enveloping k B) ⥤ ModuleCat.{u} k :=
  ModuleCat.restrictScalars (algebraMap k (Enveloping k B))
instance forgetK_additive : (forgetK k B).Additive := by
  dsimp [forgetK]
  infer_instance

abbrev termK (n : ℤ) : BiComplex k B ⥤ ModuleCat.{u} k :=
  eval _ _ n ⋙ forgetK k B

theorem biprod_term_finite (K L : BiComplex k B) (n : ℤ)
    (hK : FiniteDimensional k ((termK k B n).obj K))
    (hL : FiniteDimensional k ((termK k B n).obj L)) :
    FiniteDimensional k ((termK k B n).obj (K ⊞ L)) := by
  let := preservesBinaryBiproducts_of_preservesBiproducts (termK k B n)
  exact finite_of_iso k ((termK k B n).mapBiprod K L) (biprod_finite k hK hL)

end ExternalTensor.Section4

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Rectification_SourceFiltration
attribute [-instance] _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.ExternalTensor.Section4.ArrowVertex.vertex_additive _root_.OAI.ExternalTensor.Section4.forgetK_additive _root_.OAI.ExternalTensor.Section4.forgetRight_additive _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.LittleFinitistic.BimoduleCoefficients.instAddCommGroupCarrierTensorProductMulOpposite _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instAddCommGroup _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instRing
attribute [-simp] _root_.OAI.ExternalTensor.Section4.ArrowVertex.arrow_id _root_.OAI.ExternalTensor.Section4.ArrowVertex.arrow_original _root_.OAI.ExternalTensor.Section4.ArrowVertex.iota_original _root_.OAI.ExternalTensor.Section4.ArrowVertex.left_mul _root_.OAI.ExternalTensor.Section4.ArrowVertex.map_left _root_.OAI.ExternalTensor.Section4.ArrowVertex.mem_space
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
/-- The original summand inclusion, as a triple preserving the specified homotopy. -/
def include1 : MapData (p1 t) 0 (h1 t) t.p t.q h where
  f₀ := biprod.inr
  f₁ := biprod.inr
  f₂ := 0
  commP := in_p t
  commQ := by simp
  commH i j := by simp [h1]

/-- Projection onto the actual source-zero quotient. The condition only records
that the supplied homotopy increases source index; it is proved for Section4 inputs below. -/
def quotient0 (hh : ∀ i j, h.hom i j ≫ (biprod.fst : t.L₀ ⟶ t.V₀).f j = 0) :
    MapData t.p t.q h (p0 t) (q0 t) (h0 t) where
  f₀ := biprod.fst
  f₁ := biprod.fst
  f₂ := 𝟙 _
  commP := (p_out t).symm
  commQ := by simpa using (q_out t).symm
  commH i j := by simpa [h0] using (hh i j).symm

/-- The second filtration step and its source-one quotient. -/
def p2 : Z (k := k) (B := B) ⟶ t.V₂ := 0

def h2 : Homotopy ((0 : Z ⟶ Z) ≫ p2 t) 0 where
  hom _ _ := 0
  zero _ _ _ := rfl
  comm _ := by simp [p2, dNext, prevD]

def include2 : MapData (p2 t) 0 (h2 t) (p1 t) 0 (h1 t) where
  f₀ := biprod.inr
  f₁ := 0
  f₂ := 𝟙 _
  commP := by simp [p2]
  commQ := by simp
  commH i j := by simp [h1, h2]

/-- Changing the endpoint proofs does not change a homotopy's components. -/
theorem cast_hom {X Y : BiComplex k B} {a b a' b' : X ⟶ Y}
    (ha : a = a') (hb : b = b') (e : Homotopy a b = Homotopy a' b')
    (v : Homotopy a b) : (cast e v).hom = v.hom := by
  subst a'
  subst b'
  rfl

variable (s : Quadratic k B (A := A) (J := J) (R := R))
variable (D₀ D₁ D₂ : RightComplex B)
variable (f : A → (D₀ ⟶ D₁)) (g : J → (D₁ ⟶ D₂))
variable (H : ∀ r, Homotopy (relationMap s D₀ D₁ D₂ f g r) 0)

theorem induced_h_out (i j : ℤ) :
    (nullHomotopy s D₀ D₁ D₂ f g H).hom i j ≫
      (biprod.fst : L0Prime s D₀ D₁ D₂ f g ⟶
        (inducedData s D₀ D₁ D₂ f g).V₀).f j = 0 := by
  classical
  unfold nullHomotopy
  simp only [eq_mpr_eq_cast, eq_mp_eq_cast]
  rw [cast_hom (by simp [AssemblyData.composite]) (by simp)]
  rw [cast_hom (ha := ?_) (hb := ?_)]
  rotate_left
  · simp
  · simp
  change ((-1 : k) • h s D₀ D₁ D₂ f g H i j) ≫ _ = 0
  rw [Linear.smul_comp]
  suffices h s D₀ D₁ D₂ f g H i j ≫
      (biprod.fst : L0Prime s D₀ D₁ D₂ f g ⟶
        (inducedData s D₀ D₁ D₂ f g).V₀).f j = 0 by rw [this, smul_zero]
  rw [h_formula, Preadditive.sum_comp]
  apply Finset.sum_eq_zero
  intro r _
  dsimp only [AssemblyData.in₂]
  erw [Category.assoc, Category.assoc, ← comp_f, Category.assoc, biprod.inr_fst,
    CategoryTheory.Limits.comp_zero]

/-- Actual Section 4 source filtration inclusion; no decomposition is assumed. -/
abbrev inducedInclude1 := include1 (inducedData s D₀ D₁ D₂ f g)
  (nullHomotopy s D₀ D₁ D₂ f g H)
/-- Actual Section 4 source quotient; homotopy compatibility is proved above. -/
abbrev inducedQuotient0 := quotient0 (inducedData s D₀ D₁ D₂ f g)
  (nullHomotopy s D₀ D₁ D₂ f g H) (induced_h_out s D₀ D₁ D₂ f g H)
end ExternalTensor.Section4.SourceFiltration

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Rectification_SourceFiltrationExact
attribute [-instance] _root_.OAI.DerivedBar.Multibar.patternModule _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.DerivedBar.termModule _root_.OAI.ExternalTensor.Section4.ArrowVertex.vertex_additive _root_.OAI.ExternalTensor.Section4.forgetK_additive _root_.OAI.ExternalTensor.Section4.forgetRight_additive _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.LittleFinitistic.BimoduleCoefficients.instAddCommGroupCarrierTensorProductMulOpposite _root_.OAI.LittleFinitistic.BimoduleCoefficients.instModuleCarrierTensorProductMulOpposite_1 _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instAddCommGroup _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
open CategoryTheory CategoryTheory.Limits HomologicalComplex CochainComplex
open LittleFinitistic.RectificationTotal
noncomputable section
namespace ExternalTensor.Section4.SourceFiltration
universe u
variable {k B : Type u} [Field k] [Ring B] [Algebra k B]
variable {A J R : Type} [Fintype A] [Fintype J] [Fintype R]
instance zeroTermSubsingleton (n : ℤ) : Subsingleton ((Z (k := k) (B := B)).X n) := by
  change Subsingleton PUnit
  infer_instance

variable (t : AssemblyData (C := BiComplex k B) (A := A) (J := J) (R := R))
variable (h : Homotopy (t.q ≫ t.p) 0)
variable (hh : ∀ i j, h.hom i j ≫ (biprod.fst : t.L₀ ⟶ t.V₀).f j = 0)

theorem source0_component0 (n : ℤ) :
    Function.Injective ((include1 t h).f₀.f n) ∧
    Function.Exact ((include1 t h).f₀.f n) ((quotient0 t h hh).f₀.f n) ∧
    Function.Surjective ((quotient0 t h hh).f₀.f n) :=
  inr_fst_shortExact t.V₀ (t.V₁ ⊞ t.V₂) n

theorem source0_component1 (n : ℤ) :
    Function.Injective ((include1 t h).f₁.f n) ∧
    Function.Exact ((include1 t h).f₁.f n) ((quotient0 t h hh).f₁.f n) ∧
    Function.Surjective ((quotient0 t h hh).f₁.f n) :=
  inr_fst_shortExact (⨁ t.U) (⨁ t.V) n

theorem source0_component2 (n : ℤ) :
    Function.Injective ((include1 t h).f₂.f n) ∧
    Function.Exact ((include1 t h).f₂.f n) ((quotient0 t h hh).f₂.f n) ∧
    Function.Surjective ((quotient0 t h hh).f₂.f n) :=
  zero_id_shortExact t.L₂ Z (fun _ => inferInstance) n

/-- The actual F>=1 inclusion and source-zero quotient are termwise short exact. -/
theorem source0_shortExact (n : ℤ) :
    Function.Injective ((include1 t h).totalMap.f n) ∧
    Function.Exact ((include1 t h).totalMap.f n) ((quotient0 t h hh).totalMap.f n) ∧
    Function.Surjective ((quotient0 t h hh).totalMap.f n) := by
  exact (include1 t h).totalMap_shortExact (quotient0 t h hh)
    (fun n => (source0_component0 t h hh n).2.1)
    (fun n => (source0_component1 t h hh n).2.1)
    (fun n => (source0_component2 t h hh n).2.1)
    (fun n => (source0_component0 t h hh n).1)
    (fun n => (source0_component1 t h hh n).1)
    (fun n => (source0_component2 t h hh n).1)
    (fun n => (source0_component0 t h hh n).2.2)
    (fun n => (source0_component1 t h hh n).2.2)
    (fun n => (source0_component2 t h hh n).2.2) n

variable (s : Quadratic k B (A := A) (J := J) (R := R))
variable (D₀ D₁ D₂ : RightComplex B)
variable (f : A → (D₀ ⟶ D₁)) (g : J → (D₁ ⟶ D₂))
variable (H : ∀ r, Homotopy (relationMap s D₀ D₁ D₂ f g r) 0)

/-- No short-exactness or filtration assumption: all component properties are
proved from the actual induced Section 4 sources. -/
theorem induced_source0_shortExact (n : ℤ) :
    Function.Injective ((inducedInclude1 s D₀ D₁ D₂ f g H).totalMap.f n) ∧
    Function.Exact ((inducedInclude1 s D₀ D₁ D₂ f g H).totalMap.f n)
      ((inducedQuotient0 s D₀ D₁ D₂ f g H).totalMap.f n) ∧
    Function.Surjective ((inducedQuotient0 s D₀ D₁ D₂ f g H).totalMap.f n) :=
  source0_shortExact _ _ _ n
end ExternalTensor.Section4.SourceFiltration

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Rectification_SourceFiltrationReal
attribute [-instance] _root_.OAI.DerivedBar.Multibar.patternModule _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.DerivedBar.termModule _root_.OAI.ExternalTensor.Section4.ArrowVertex.vertex_additive _root_.OAI.ExternalTensor.Section4.forgetK_additive _root_.OAI.ExternalTensor.Section4.forgetRight_additive _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.LittleFinitistic.BimoduleCoefficients.instAddCommGroupCarrierTensorProductMulOpposite _root_.OAI.LittleFinitistic.BimoduleCoefficients.instModuleCarrierTensorProductMulOpposite_1 _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instAddCommGroup _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
open CategoryTheory CategoryTheory.Limits HomologicalComplex CochainComplex
open LittleFinitistic.RectificationTotal
noncomputable section
namespace ExternalTensor.Section4.SourceFiltration
universe u
variable {k B : Type u} [Field k] [Ring B] [Algebra k B]
variable {A J R : Type} [Fintype A] [Fintype J] [Fintype R]
variable (t : AssemblyData (C := BiComplex k B) (A := A) (J := J) (R := R))

omit [Fintype R] in
/-- The canonical zero-column inclusion has exactly its original term coordinate. -/
theorem inclusion_product (n : ℤ) :
    (inclusion (p2 t) 0 (h2 t)).f n ≫ (totalTermIso (p2 t) 0 (h2 t) n).hom =
      ModuleCat.ofHom (LinearMap.inr (Enveloping k B)
        (Z.X (n+2) × Z.X (n+1)) (t.V₂.X n)) := by
  dsimp only [totalTermIso, termIso, LittleFinitistic.RectificationTotal.inclusion]
  erw [Iso.trans_hom, Iso.trans_hom, Iso.trans_hom,
    biprod.mapIso_hom, Iso.refl_hom, biprod.mapIso_hom, Iso.refl_hom]
  erw [← Category.assoc, ← Category.assoc, ← Category.assoc,
    cone_inr_termIso, biprod.inr_map, Category.id_comp, biprod.inr_map, Category.id_comp]
  exact inr_prod _ _

omit [Fintype R] in
/-- Removing the two zero columns preserves the actual V2 inclusion. -/
theorem inclusion2_bijective (n : ℤ) :
    Function.Bijective ((inclusion (p2 t) 0 (h2 t)).f n) := by
  let e := (totalTermIso (p2 t) 0 (h2 t) n).toLinearEquiv
  have he (x : t.V₂.X n) : e ((inclusion (p2 t) 0 (h2 t)).f n x) = ((0,0),x) :=
    congrArg (fun a => a x) (inclusion_product t n)
  refine ⟨?_, ?_⟩
  · intro x y hxy
    have := congrArg e hxy
    simpa only [he] using congrArg Prod.snd this
  · intro y
    refine ⟨(e y).2, e.injective ?_⟩
    rw [he]
    exact Prod.ext (Subsingleton.elim _ _) rfl

instance inclusion2_isIso : IsIso (inclusion (p2 t) 0 (h2 t)) := by
  have (n : ℤ) : IsIso ((inclusion (p2 t) 0 (h2 t)).f n) :=
    (ConcreteCategory.isIso_iff_bijective _).2 (inclusion2_bijective t n)
  exact HomologicalComplex.Hom.isIso_of_components _

def v2Iso : t.V₂ ≅ total (p2 t) 0 (h2 t) := asIso (inclusion (p2 t) 0 (h2 t))

/-- F>=2 really is V2, embedded by its original vertex summand inclusion. -/
def v2Inclusion : t.V₂ ⟶ total (p1 t) 0 (h1 t) :=
  biprod.inr ≫ inclusion (p1 t) 0 (h1 t)

omit [Fintype R] in
theorem v2Inclusion_eq : v2Inclusion t = (v2Iso t).hom ≫ (include2 t).totalMap := by
  symm
  exact (include2 t).inclusion_totalMap

variable (h : Homotopy (t.q ≫ t.p) 0)
/-- The composite filtration inclusion is the original V2-to-total map. -/
theorem v2_nested : v2Inclusion t ≫ (include1 t h).totalMap =
    t.in₂ ≫ inclusion t.p t.q h := by
  dsimp only [v2Inclusion]
  rw [Category.assoc, (include1 t h).inclusion_totalMap]
  rfl
end ExternalTensor.Section4.SourceFiltration

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Rectification_SourceFiltrationCone
attribute [-instance] _root_.OAI.DerivedBar.Multibar.patternModule _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.DerivedBar.termModule _root_.OAI.ExternalTensor.Section4.ArrowVertex.vertex_additive _root_.OAI.ExternalTensor.Section4.forgetK_additive _root_.OAI.ExternalTensor.Section4.forgetRight_additive _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.LittleFinitistic.BimoduleCoefficients.instAddCommGroupCarrierTensorProductMulOpposite _root_.OAI.LittleFinitistic.BimoduleCoefficients.instModuleCarrierTensorProductMulOpposite_1 _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instAddCommGroup _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instRing
attribute [-simp] _root_.OAI.ExternalTensor.Section4.ArrowVertex.arrow_id _root_.OAI.ExternalTensor.Section4.ArrowVertex.arrow_original _root_.OAI.ExternalTensor.Section4.ArrowVertex.iota_original _root_.OAI.ExternalTensor.Section4.ArrowVertex.left_mul _root_.OAI.ExternalTensor.Section4.ArrowVertex.map_left _root_.OAI.ExternalTensor.Section4.ArrowVertex.mem_space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
open CategoryTheory CategoryTheory.Limits HomologicalComplex CochainComplex
open LittleFinitistic.RectificationTotal
noncomputable section
namespace ExternalTensor.Section4.SourceFiltration
universe u
variable {k B : Type u} [Field k] [Ring B] [Algebra k B]

/-- An isomorphism of the two input columns gives an isomorphism of actual cones. -/
def coneIso {X Y X' Y' : BiComplex k B} (p : X ⟶ Y) (p' : X' ⟶ Y')
    (a : X ≅ X') (b : Y ≅ Y') (w : a.hom ≫ p' = p ≫ b.hom) :
    mappingCone p ≅ mappingCone p' where
  hom := coneMap p p' a.hom b.hom w
  inv := coneMap p' p a.inv b.inv (by
    apply (cancel_epi a.hom).1
    simp only [← Category.assoc, Iso.hom_inv_id, Category.id_comp]
    rw [w, Category.assoc, Iso.hom_inv_id, Category.comp_id])
  hom_inv_id := by rw [← coneMap_comp]; simp
  inv_hom_id := by rw [← coneMap_comp]; simp

variable (X : BiComplex k B)

theorem zeroCone_inclusion_product (n : ℤ) :
    (mappingCone.inr (0 : Z ⟶ X)).f n ≫
      ((homotopyCofiber.XIsoBiprod (0 : Z ⟶ X) n (n+1) rfl) ≪≫
        ModuleCat.biprodIsoProd _ _).hom =
      ModuleCat.ofHom (LinearMap.inr (Enveloping k B) (Z.X (n+1)) (X.X n)) := by
  erw [Iso.trans_hom, ← Category.assoc, cone_inr_termIso]
  exact inr_prod _ _

theorem zeroCone_inclusion_bijective (n : ℤ) :
    Function.Bijective ((mappingCone.inr (0 : Z ⟶ X)).f n) := by
  let e := ((homotopyCofiber.XIsoBiprod (0 : Z ⟶ X) n (n+1) rfl) ≪≫
    ModuleCat.biprodIsoProd _ _).toLinearEquiv
  have he (x : X.X n) : e ((mappingCone.inr (0 : Z ⟶ X)).f n x) = (0,x) :=
    congrArg (fun a => a x) (zeroCone_inclusion_product X n)
  refine ⟨?_, ?_⟩
  · intro x y hxy
    have := congrArg e hxy
    simpa only [he] using congrArg Prod.snd this
  · intro y
    refine ⟨(e y).2, e.injective ?_⟩
    rw [he]
    exact Prod.ext (Subsingleton.elim _ _) rfl

instance zeroCone_inclusion_isIso : IsIso (mappingCone.inr (0 : Z ⟶ X)) := by
  have (n : ℤ) : IsIso ((mappingCone.inr (0 : Z ⟶ X)).f n) :=
    (ConcreteCategory.isIso_iff_bijective _).2 (zeroCone_inclusion_bijective X n)
  exact HomologicalComplex.Hom.isIso_of_components _

/-- The ordinary two-column total identifies with the three-column API having
zero relation column; its zero-column inclusion is unchanged. -/
def twoColumnIso {Y : BiComplex k B} (p : X ⟶ Y)
    (h : Homotopy ((0 : Z ⟶ X) ≫ p) 0) : mappingCone p ≅ total p 0 h :=
  coneIso p (rectifyingMap p 0 h) (asIso (mappingCone.inr (0 : Z ⟶ X)))
    (Iso.refl _) (by simp [rectifyingMap])

end ExternalTensor.Section4.SourceFiltration

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Rectification_FiltrationExactness
attribute [-instance] _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.ExternalTensor.Section4.ArrowVertex.vertex_additive _root_.OAI.ExternalTensor.Section4.forgetK_additive _root_.OAI.ExternalTensor.Section4.forgetRight_additive _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
open CategoryTheory CategoryTheory.Limits HomologicalComplex CochainComplex
open LittleFinitistic.RectificationTotal
open scoped TensorProduct ModuleCat.Algebra
noncomputable section
namespace ExternalTensor.Section4.SourceFiltration.Exactness
universe u
variable {k B : Type u} [Field k] [Ring B] [Algebra k B]
variable {A J R : Type} [Fintype A] [Fintype J] [Fintype R]
variable (s : Quadratic k B (A := A) (J := J) (R := R))
variable (D₀ D₁ D₂ : RightComplex B)
variable (f : A → (D₀ ⟶ D₁)) (g : J → (D₁ ⟶ D₂))
variable (H : ∀ r, Homotopy (relationMap s D₀ D₁ D₂ f g r) 0)

abbrev P := total (p s D₀ D₁ D₂ f g) (q s D₀ D₁ D₂ f g)
  (nullHomotopy s D₀ D₁ D₂ f g H)

abbrev i1 : F1 s D₀ D₁ D₂ f g ⟶ P s D₀ D₁ D₂ f g H :=
  (inducedInclude1 s D₀ D₁ D₂ f g H).totalMap
abbrev pi0 : P s D₀ D₁ D₂ f g H ⟶ G0 s D₀ D₁ D₂ f g :=
  (inducedQuotient0 s D₀ D₁ D₂ f g H).totalMap
abbrev i2 : (columnComplex k B s.e₂).obj D₂ ⟶ F1 s D₀ D₁ D₂ f g :=
  v2Inclusion (data s D₀ D₁ D₂ f g)
end ExternalTensor.Section4.SourceFiltration.Exactness

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Rectification_SourceFiltrationComplex
attribute [-instance] _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.ExternalTensor.Section4.ArrowVertex.vertex_additive _root_.OAI.ExternalTensor.Section4.forgetK_additive _root_.OAI.ExternalTensor.Section4.forgetRight_additive _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open CategoryTheory CategoryTheory.Limits HomologicalComplex

namespace ExternalTensor.Section4.SourceFiltration.Complex
universe u
variable {k B : Type u} [Field k] [Ring B] [Algebra k B]
variable {A J R : Type} [Fintype A] [Fintype J] [Fintype R]
variable (s : Quadratic k B (A := A) (J := J) (R := R))
variable (D₀ D₁ D₂ : RightComplex B)
variable (f : A → (D₀ ⟶ D₁)) (g : J → (D₁ ⟶ D₂))
variable (H : ∀ r, Homotopy (relationMap s D₀ D₁ D₂ f g r) 0)
open Exactness LittleFinitistic

/-- Every original source filtration remains short exact after taking a left vertex. -/
theorem vertex_shortExact (e : B) (he : e*e=e)
    (S : ShortComplex (BiComplex k B)) (hS : S.ShortExact) :
    (S.map ((BimoduleVertex.functor k B e).mapHomologicalComplex (.up ℤ))).ShortExact := by
  apply HomologicalComplex.shortExact_of_degreewise_shortExact
  intro n
  exact BimoduleVertex.map_shortExact k B e he
    (S.map (HomologicalComplex.eval _ _ n))
    ((HomologicalComplex.shortExact_iff_degreewise_shortExact S).1 hS n)
end ExternalTensor.Section4.SourceFiltration.Complex

end

end OAI
end



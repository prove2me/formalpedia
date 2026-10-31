-- Prove2me | Definitions.Def_OAIQ023F008
-- name    : OAIQ023F008
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-30T15:44:30.023141+00:00
-- url     : https://prove2.me/theorems/7aa7b0cb-9f52-4fa3-8697-18948bc1fe9e
-- title:
--   Definitions bundle OAIQ023F008 of the split of OpenAI, An algebra of infinite little finitistic dimension (result family 198)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.LittleFinitistic.Main.exists_counterexample`, carved from OpenAI's openai/math development (OpenAI, *An algebra of infinite little finitistic dimension (result family 198)*, OpenAI Math Release, September 23, 2026, result family 198, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 297 declarations of OpenAI's Lean: 118 definitions, 3 inductive types or structures, 30 instances and 146 theorems. The definitions and types are `OAI.LittleFinitistic.BimoduleBarComparison.instModuleCarrier_solutions`, `OAI.LittleFinitistic.BimoduleTotal.integerSingleIso`, `OAI.LittleFinitistic.DirectedBound.DirectedSystem.Cover`, `OAI.LittleFinitistic.DirectedBound.DirectedSystem.Supported`, `OAI.LittleFinitistic.DirectedBound.DirectedSystem.coverMap`, `OAI.LittleFinitistic.DirectedBound.DirectedSystem.opposite`, `OAI.LittleFinitistic.FiniteColumnComplex.Differential`, `OAI.LittleFinitistic.FiniteColumnComplex.Horizontal`, `OAI.LittleFinitistic.FiniteColumnComplex.complex`, `OAI.LittleFinitistic.FiniteColumnComplex.complexMap`, `OAI.LittleFinitistic.FiniteColumnComplex.componentMap`, `OAI.LittleFinitistic.FiniteColumnComplex.coneDifferential`, `OAI.LittleFinitistic.FiniteColumnComplex.coneEquiv`, `OAI.LittleFinitistic.FiniteColumnComplex.coneIso`, `OAI.LittleFinitistic.FiniteColumnComplex.coneSource`, `OAI.LittleFinitistic.FiniteColumnComplex.coneTarget`, `OAI.LittleFinitistic.FiniteColumnComplex.coneTriangular`, `OAI.LittleFinitistic.FiniteColumnComplex.diagonal`, `OAI.LittleFinitistic.FiniteColumnComplex.pairEquiv`, `OAI.LittleFinitistic.FiniteColumnComplex.total`, `OAI.LittleFinitistic.FiniteColumnComplex.totalCone`, `OAI.LittleFinitistic.FiniteColumnComplex.totalDifferential`, `OAI.LittleFinitistic.FinitePresentation.CovariantData.toSelection`, `OAI.LittleFinitistic.FinitePresentation.SeedData.toCovariant`, `OAI.LittleFinitistic.FinitePresentation.SeedData.toSelection`, `OAI.LittleFinitistic.FinitePresentation.fromModel`, `OAI.LittleFinitistic.FinitePresentation.modelLift`, `OAI.LittleFinitistic.FinitePresentation.modelSeedData`, `OAI.LittleFinitistic.FinitePresentation.presentationEquiv`, `OAI.LittleFinitistic.FinitePresentation.toModel`, `OAI.LittleFinitistic.FiniteQuotientGroup`, `OAI.LittleFinitistic.FiniteSelectionFamily.H`, `OAI.LittleFinitistic.FiniteSelectionFamily.S`, `OAI.LittleFinitistic.FiniteSelectionFamily.test`, `OAI.LittleFinitistic.FiniteSelectionFamily.vector`, `OAI.LittleFinitistic.FunctorExtension.iso`, `OAI.LittleFinitistic.GroupAlgebraPresentation.auxiliaryGroupAlgebraZeroEquiv`, `OAI.LittleFinitistic.IdentityAt`, `OAI.LittleFinitistic.IntegerExtensionFunctor.complexIso`, `OAI.LittleFinitistic.IntegerExtensionFunctor.naturalIso` and 81 more.
--
--   **Sources.** They come from these modules of lean/OAI/Algebra, in whole or in part: `Finitistic_Bimodule_BimoduleBarStalk`, `Finitistic_Bimodule_BimoduleBarTensorComparison`, `Finitistic_Encoding_AuxiliaryQuadraticPresentation`, `Finitistic_Encoding_DirectedBound`, `Finitistic_Encoding_PresentationReindex`, `Finitistic_Encoding_QuadraticCoefficients`, `Finitistic_Encoding_QuadraticPresentation`, `Finitistic_Encoding_ThreeVertexAlgebra`, `Finitistic_Localization_BoundedQuotientEvaluation`, `Finitistic_Localization_FormalSummandAction`, `Finitistic_Localization_IntegerExtensionFunctor`, `Finitistic_Localization_QuotientAction`, `Finitistic_Localization_SourceActionEvaluation`, `Finitistic_Localization_SourceCornerEvaluation`, `Finitistic_Localization_SourceImageEvaluation`, `Finitistic_Localization_TwoConeVerdier`, `Finitistic_Localization_VerdierEvaluationExact`, `Finitistic_Ordinary_OrdinaryBimodule`, `Finitistic_Ordinary_OrdinaryChainAlgebra`, `Finitistic_Ordinary_OrdinaryFiniteColumnComplex`, `Finitistic_Ordinary_OrdinaryFiniteConeReindex`, `Finitistic_Ordinary_OrdinaryFiniteConeTriangular`, `Finitistic_Ordinary_OrdinaryFiniteTotal`, `Finitistic_Ordinary_OrdinaryFiniteTotalMaps`, `Finitistic_Ordinary_OrdinaryFunctorExtension`, `Finitistic_Ordinary_OrdinaryOffDiagonalComplex`, `Finitistic_Ordinary_OrdinaryOffDiagonalObjects`, `Finitistic_Ordinary_OrdinaryOffDiagonalProjective`, `Finitistic_Ordinary_OrdinaryProductDimension`, `Finitistic_Ordinary_OrdinaryProductSecondDimension`, `Finitistic_Ordinary_OrdinarySupportedExtension`, `Finitistic_Ordinary_OrdinaryTensorDirected`, `Finitistic_Rectification_LeftVertexHomology`, `Finitistic_Rectification_RectificationAcyclic`, `Finitistic_Rectification_RectificationTotal`, `Finitistic_Rectification_TotalInterchange`, `Finitistic_Rectification_VertexHomology`, `Finitistic_Rectification_VertexTensorLinear`, `Finitistic_Rectification_ZeroColumnTotal`, `Finitistic_Rectification_ZeroLastColumn`, `Finitistic_Selected_SelectedFixedDiagram`, `Finitistic_Selected_SelectedImageComparison`, `Finitistic_Selected_SelectedNativeAction`, `Finitistic_Selected_SelectedNativeEvaluation`, `Finitistic_Selected_SelectedRealization`, `Finitistic_Selected_SelectedTargetHomology`, `Finitistic_Selection_AuxiliaryGroupAlgebraPresentation`, `Finitistic_Selection_FinitePresentation`, `Finitistic_Selection_FiniteQuotient`, `Finitistic_Selection_FiniteSelectionFamily`, `Finitistic_Selection_GroupSelection`, `Finitistic_Selection_MatrixModel`, `Finitistic_Selection_SelectionAlgebra`, `Finitistic_Selection_SelectionEncoding`, `Finitistic_Selection_SelectionIteration`, `Finitistic_Selection_TestModules`.
--
--   **Imports.** It imports the bundles `OAIQ023F000`, `OAIQ023F001`, `OAIQ023F002`, `OAIQ023F003` and `OAIQ023F004` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ023F012`, `OAIQ023F014` and `OAIQ023F015`.
-- source:
--   OpenAI, An algebra of infinite little finitistic dimension (result family 198), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 198; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/An-algebra-of-infinite-little-finitistic-dimension-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Algebra at commit adc7f12

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIQ023F000
import Definitions.Def_OAIQ023F001
import Definitions.Def_OAIQ023F002
import Definitions.Def_OAIQ023F003
import Definitions.Def_OAIQ023F004

section
-- module Solutions.OAIQ023_Fin.Compat
attribute [-instance] _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated
attribute [-simp] _root_.OAI.ExternalTensor.Section4.sum_hom
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
@[simp] theorem fin3_lit_0_2 : ((0 : Fin 3) = 2) ↔ False := by decide
@[simp] theorem fin3_lit_1_2 : ((1 : Fin 3) = 2) ↔ False := by decide
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Encoding_DirectedBound
attribute [-instance] _root_.OAI.DerivedBar.Multibar.patternModule _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.DerivedBar.termModule _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.BimoduleCoefficients.instAddCommGroupCarrierTensorProductMulOpposite _root_.OAI.LittleFinitistic.BimoduleCoefficients.instModuleCarrierTensorProductMulOpposite_1 _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.ProductModules.firstModule _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instAddCommGroup _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instRing _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated
attribute [-simp] _root_.OAI.ExternalTensor.Section4.sum_hom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open scoped TensorProduct
open TensorProduct
namespace LittleFinitistic.DirectedBound
universe u v
variable {k A : Type u} [Field k] [Ring A] [Algebra k A] {n : ℕ}

namespace DirectedSystem
variable (D : DirectedSystem k A n)
variable (M : Type v) [AddCommGroup M] [Module A M] [Module k M]
  [IsScalarTower k A M]

/-- Vanishing of vertex components below p, for arbitrary modules. -/
def Supported (p : ℕ) : Prop := ∀ j : Fin n, j.val < p → ∀ m : M, D.e j • m = 0


lemma projection_vertexTensor (i : Fin n) (a : A) (m : M) :
    D.projection M ((a * D.e i) ⊗ₜ[k] (D.e i • m)) =
      (a * D.e i) ⊗ₜ[k] (D.e i • m) := by
  rw [projection_tmul, Finset.sum_eq_single i]
  · simp only [mul_assoc, D.idem, ← mul_smul]
  · intro j _ hji
    rw [mul_assoc, D.orthogonal i j hji.symm, mul_zero, zero_tmul]
  · simp

lemma projection_idempotent (x : A ⊗[k] M) :
    D.projection M (D.projection M x) = D.projection M x := by
  induction x using OAI.tensorInductionOn with
  | tmul a m =>
    rw [projection_tmul, map_sum]
    simp only [projection_vertexTensor]
  | add x y hx hy => simp only [map_add, hx, hy]

lemma evaluation_projection (x : A ⊗[k] M) :
    evaluation M D (D.projection M x) = evaluation M D x := by
  induction x using OAI.tensorInductionOn with
  | tmul a m =>
    simp only [projection_tmul, map_sum, evaluation_tmul, ← mul_smul, mul_assoc, D.idem]
    rw [← Finset.sum_smul, ← Finset.mul_sum, D.complete, mul_one]
  | add x y hx hy => simp only [map_add, hx, hy]

/-- The manuscript's projective cover, realized as an actual direct summand. -/
abbrev Cover := LinearMap.range (D.projection M)

instance cover_addCommGroup : AddCommGroup (D.Cover M) :=
  Submodule.addCommGroup _

instance cover_projective : Module.Projective A (D.Cover M) := by
  apply Module.Projective.of_split (D.projection M).range.subtype
    (D.projection M).rangeRestrict
  ext x
  obtain ⟨t, ht⟩ := x.property
  change D.projection M x.val = x.val
  rw [← ht, projection_idempotent]

/-- Evaluation restricted to the projective summand. -/
abbrev coverMap : D.Cover M →ₗ[A] M :=
  (evaluation M D).comp (D.projection M).range.subtype

lemma coverMap_surjective : Function.Surjective (D.coverMap M) := by
  intro m
  refine ⟨(D.projection M).rangeRestrict (1 ⊗ₜ[k] m), ?_⟩
  change evaluation M D (D.projection M (1 ⊗ₜ[k] m)) = m
  rw [evaluation_projection, evaluation_tmul, one_smul]

lemma low_tensor {p : ℕ} (hM : D.Supported M p) (j : Fin n) (hj : j.val ≤ p)
    (i : Fin n) (a : A) (m : M) :
    (D.e j * a * D.e i) ⊗ₜ[k] (D.e i • m) =
      D.e j ⊗ₜ[k] ((D.e j * a * D.e i) • (D.e i • m)) := by
  by_cases hij : i = j
  · subst i
    obtain ⟨c, hc⟩ := D.diagonal j a
    rw [hc, smul_tmul, smul_assoc, ← mul_smul, D.idem, tmul_smul]
  · rcases lt_or_gt_of_ne hij with hij | hij
    · have hz := hM i (by omega) m
      simp [hz]
    · rw [D.directed i j hij a]
      simp

lemma low_projection {p : ℕ} (hM : D.Supported M p) (j : Fin n) (hj : j.val ≤ p)
    (x : A ⊗[k] M) :
    D.e j • D.projection M x =
      D.e j ⊗ₜ[k] evaluation M D (D.e j • D.projection M x) := by
  induction x using OAI.tensorInductionOn with
  | tmul a m =>
    simp only [projection_tmul, Finset.smul_sum, smul_tmul', smul_eq_mul, map_sum,
      evaluation_tmul, tmul_sum]
    apply Finset.sum_congr rfl
    intro i _
    simpa only [← mul_assoc] using D.low_tensor M hM j hj i a m
  | add x y hx hy =>
    simp only [map_add, smul_add, tmul_add]
    exact congrArg₂ (· + ·) hx hy

/-- One syzygy raises the lower bound on the support by one. -/
lemma kernel_supported {p : ℕ} (hM : D.Supported M p) :
    D.Supported (LinearMap.ker (D.coverMap M)) (p + 1) := by
  intro j hj x
  apply Subtype.ext
  apply Subtype.ext
  change D.e j • x.val.val = 0
  obtain ⟨t, ht⟩ := x.val.property
  have h := D.low_projection M hM j (by omega) t
  rw [ht] at h
  rw [h, map_smul]
  have hz : evaluation M D x.val.val = 0 := x.property
  rw [hz, smul_zero, tmul_zero]

open CategoryTheory

omit [Module k M] [IsScalarTower k A M] in
lemma supported_subsingleton (hM : D.Supported M n) : Subsingleton M := by
  have hz (m : M) : m = 0 := by
    calc
      m = (1 : A) • m := (one_smul A m).symm
      _ = (∑ i, D.e i) • m := by rw [D.complete]
      _ = ∑ i, D.e i • m := Finset.sum_smul
      _ = 0 := Finset.sum_eq_zero (fun i _ => hM i i.isLt m)
  exact ⟨fun x y => (hz x).trans (hz y).symm⟩

/-- The support induction uses genuine projective dimensions (vanishing Ext),
via mathlib's short exact sequence dimension-shifting theorem. -/
theorem supported_projectiveDimensionLT (r : ℕ) :
    ∀ (p : ℕ), p + r = n → ∀ (N : Type (max u v))
      [AddCommGroup N] [Module A N] [Module k N] [IsScalarTower k A N],
      D.Supported N p → HasProjectiveDimensionLT (ModuleCat.of A N) r := by
  induction r with
  | zero =>
    intro p hp N _ _ _ _ hN
    have hp' : p = n := by omega
    subst p
    have := D.supported_subsingleton N hN
    exact (ModuleCat.isZero_iff_subsingleton.mpr inferInstance).hasProjectiveDimensionLT_zero
  | succ r ih =>
    intro p hp N _ _ _ _ hN
    have hK := ih (p + 1) (by omega) (LinearMap.ker (D.coverMap N))
      (D.kernel_supported N hN)
    have hP : HasProjectiveDimensionLT (ModuleCat.of A (D.Cover N)) (r + 1) :=
      hasProjectiveDimensionLT_of_ge _ 1 (r + 1) (by omega)
    exact (LinearMap.shortExact_shortComplexKer (D.coverMap_surjective N)).hasProjectiveDimensionLT_X₃ r hK hP

include D

/-- Every left module is covered, with no finite generation restriction. -/
theorem all_modules_projectiveDimensionLT (N : ModuleCat.{max u v} A) :
    HasProjectiveDimensionLT N n := by
  let : Module k N := Module.compHom N (algebraMap k A)
  let : IsScalarTower k A N := IsScalarTower.of_compHom k A N
  exact D.supported_projectiveDimensionLT n 0 (by omega) N (by
    intro j hj
    omega)

theorem all_modules_projectiveDimension_le (N : ModuleCat.{max u v} A) :
    projectiveDimension N ≤ (n - 1 : ℕ) := by
  have := D.all_modules_projectiveDimensionLT N
  apply (projectiveDimension_le_iff N (n - 1)).mpr
  exact hasProjectiveDimensionLT_of_ge N n ((n - 1) + 1) (by omega)

/-- Reversing the vertices transfers exactly the hypotheses to right modules. -/
def opposite : DirectedSystem k Aᵐᵒᵖ n where
  e i := MulOpposite.op (D.e i.rev)
  idem i := by
    apply MulOpposite.unop_injective
    exact D.idem i.rev
  orthogonal i j hij := by
    apply MulOpposite.unop_injective
    exact D.orthogonal j.rev i.rev (fun h => hij (Fin.rev_injective h.symm))
  complete := by
    apply MulOpposite.unop_injective
    change (MulOpposite.opAddEquiv.symm : Aᵐᵒᵖ ≃+ A)
      (∑ i : Fin n, MulOpposite.op (D.e i.rev)) = 1
    rw [map_sum]
    change (∑ i : Fin n, D.e i.rev) = 1
    calc
      ∑ i : Fin n, D.e i.rev = ∑ i, D.e i := Equiv.sum_comp Fin.revPerm D.e
      _ = 1 := D.complete
  diagonal i a := by
    obtain ⟨c, hc⟩ := D.diagonal i.rev a.unop
    refine ⟨c, ?_⟩
    apply MulOpposite.unop_injective
    simpa only [MulOpposite.unop_mul, MulOpposite.unop_op, MulOpposite.unop_smul,
      mul_assoc] using hc
  directed i j hij a := by
    apply MulOpposite.unop_injective
    simpa only [MulOpposite.unop_mul, MulOpposite.unop_op, MulOpposite.unop_zero,
      mul_assoc] using D.directed j.rev i.rev (Fin.rev_lt_rev.mpr hij) a.unop

/-- The global dimensions are the suprema of the actual module projective dimensions. -/
theorem both_sides_globalDimension_le :
    (⨆ N : ModuleCat.{max u v} A, projectiveDimension N) ≤ (n - 1 : ℕ) ∧
    (⨆ N : ModuleCat.{max u v} Aᵐᵒᵖ, projectiveDimension N) ≤ (n - 1 : ℕ) :=
  ⟨iSup_le D.all_modules_projectiveDimension_le,
   iSup_le D.opposite.all_modules_projectiveDimension_le⟩
end DirectedSystem

open CategoryTheory
end LittleFinitistic.DirectedBound

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Encoding_ThreeVertexAlgebra
attribute [-instance] _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
namespace LittleFinitistic
universe u v
variable {k V W U : Type u} [Field k]
  [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W]
  [AddCommGroup U] [Module k U]

namespace ThreeVertexAlgebra
variable (μ : W →ₗ[k] V →ₗ[k] U)

open CategoryTheory
/-- The three-vertex coordinate algebra has global dimension at most two on both sides. -/
theorem globalDimension_le_two :
    (⨆ N : ModuleCat.{max u v} (ThreeVertexAlgebra μ), projectiveDimension N) ≤ (2 : ℕ) ∧
    (⨆ N : ModuleCat.{max u v} (ThreeVertexAlgebra μ)ᵐᵒᵖ, projectiveDimension N) ≤ (2 : ℕ) :=
  (directedSystem μ).both_sides_globalDimension_le
end ThreeVertexAlgebra
end LittleFinitistic

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Rectification_RectificationTotal
attribute [-instance] _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instRing _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace LittleFinitistic.RectificationTotal
open CategoryTheory CategoryTheory.Limits HomologicalComplex CochainComplex HomComplex

variable {C : Type*} [Category C] [Preadditive C] [HasBinaryBiproducts C]
variable {L₀ L₁ L₂ : CochainComplex C ℤ} (p : L₁ ⟶ L₀) (q : L₂ ⟶ L₁)
  (h : Homotopy (q ≫ p) 0)

/-- Bounded columns give a bounded actual total complex. -/
theorem total_bounded (lo hi : ℤ)
    (h₀ : ∀ i, i < lo ∨ hi < i → IsZero (L₀.X i))
    (h₁ : ∀ i, i < lo ∨ hi < i → IsZero (L₁.X i))
    (h₂ : ∀ i, i < lo ∨ hi < i → IsZero (L₂.X i)) :
    ∀ i, i < lo-2 ∨ hi < i → IsZero ((total p q h).X i) := by
  intro i hi'
  rw [total_isZero]
  exact ⟨⟨h₂ _ (by omega),h₁ _ (by omega)⟩,h₀ _ (by omega)⟩

variable {D : Type*} [Category D] [Preadditive D] [HasBinaryBiproducts D]

/-- Projectivity after an additive forgetful functor, needed for right projectivity
of a total built in the category of bimodules. -/
theorem total_projective_after (F : C ⥤ D) [F.Additive]
    (h₀ : ∀ i, Projective (F.obj (L₀.X i)))
    (h₁ : ∀ i, Projective (F.obj (L₁.X i)))
    (h₂ : ∀ i, Projective (F.obj (L₂.X i))) :
    ∀ i, Projective (F.obj ((total p q h).X i)) := by
  intro i
  let := h₀ i
  let := h₁ (i+1)
  let := h₂ (i+2)
  let := preservesBinaryBiproducts_of_preservesBiproducts F
  let e := F.mapIso (termIso p q h i) ≪≫ F.mapBiprod _ _ ≪≫
    biprod.mapIso (F.mapBiprod _ _) (Iso.refl _)
  apply Projective.of_iso e.symm
  infer_instance
end LittleFinitistic.RectificationTotal

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Rectification_RectificationAcyclic
attribute [-instance] _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instAddCommGroup _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instRing _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated
attribute [-simp] _root_.OAI.ExternalTensor.Section4.sum_hom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace LittleFinitistic.RectificationAcyclic
open CategoryTheory CategoryTheory.Limits HomologicalComplex CochainComplex

variable {C : Type*} [Category C] [Abelian C]

/-- The total of a strict short exact sequence of complexes is acyclic. This is
applied to the associated graded source-index pieces in rectification. -/
theorem short_exact_total_acyclic (S : ShortComplex (CochainComplex C ℤ))
    (hS : S.ShortExact) :
    (RectificationTotal.total S.g S.f (Homotopy.ofEq S.zero)).Acyclic := by
  have he : RectificationTotal.rectifyingMap S.g S.f (Homotopy.ofEq S.zero) =
      mappingCone.descShortComplex S := by
    simp only [RectificationTotal.rectifyingMap,CochainComplex.HomComplex.Cochain.ofHomotopy_ofEq,
      mappingCone.descShortComplex]
  change (mappingCone (RectificationTotal.rectifyingMap S.g S.f (Homotopy.ofEq S.zero))).Acyclic
  rw [he]
  let := mappingCone.quasiIso_descShortComplex hS
  exact cone_acyclic _

/-- A quasi-isomorphism between bounded-above projective complexes has an actual
chain-map inverse up to specified homotopies, retaining the given forward map. -/
theorem bounded_projective_homotopy_inverse {K L : CochainComplex C ℤ}
    (f : K ⟶ L) [QuasiIso f] (hi : ℤ) [K.IsStrictlyLE hi] [L.IsStrictlyLE hi]
    [∀ i, Projective (K.X i)] [∀ i, Projective (L.X i)] :
    ∃ g : L ⟶ K, Nonempty (Homotopy (f ≫ g) (𝟙 K)) ∧
      Nonempty (Homotopy (g ≫ f) (𝟙 L)) := by
  classical
  have : (mappingCone f).IsStrictlyLE hi := by
    rw [isStrictlyLE_iff]
    intro i hi'
    rw [mappingCone.isZero_X_iff]
    exact ⟨K.isZero_of_isStrictlyLE hi _ (by omega),L.isZero_of_isStrictlyLE hi _ hi'⟩
  have (degree : ℤ) : Projective ((mappingCone f).X degree) := by
    apply Projective.of_iso (homotopyCofiber.XIsoBiprod f degree (degree+1) (by simp)).symm
    infer_instance
  let q := HomotopyCategory.quotient C (.up ℤ)
  have hzero : IsZero (q.obj (mappingCone f)) :=
    (HomotopyCategory.isZero_quotient_obj_iff _).2
      ⟨contractBoundedProjective _ hi (cone_acyclic f)⟩
  have : IsIso (q.map f) :=
    ((mappingCone.triangleh f).isZero₃_iff_isIso₁
      (HomotopyCategory.mappingCone_triangleh_distinguished f)).1 hzero
  let g := q.preimage (inv (q.map f))
  have hg : q.map g = inv (q.map f) := q.map_preimage _
  refine ⟨g,⟨HomotopyCategory.homotopyOfEq _ _ ?_⟩,
    ⟨HomotopyCategory.homotopyOfEq _ _ ?_⟩⟩
  · change q.map (f ≫ g) = q.map (𝟙 K)
    rw [Functor.map_comp,hg,IsIso.hom_inv_id,q.map_id]
  · change q.map (g ≫ f) = q.map (𝟙 L)
    rw [Functor.map_comp,hg,IsIso.inv_hom_id,q.map_id]

end LittleFinitistic.RectificationAcyclic

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Rectification_VertexTensorLinear
attribute [-instance] _root_.OAI.DerivedBar.Multibar.patternModule _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.DerivedBar.termModule _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.LittleFinitistic.BimoduleCoefficients.instAddCommGroupCarrierTensorProductMulOpposite _root_.OAI.LittleFinitistic.BimoduleCoefficients.instModuleCarrierTensorProductMulOpposite_1 _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open CategoryTheory
open scoped TensorProduct ModuleCat.Algebra
namespace LittleFinitistic.BimoduleVertex
universe u
variable (k B : Type u) [Field k] [Ring B] [Algebra k B]

instance linear (e : B) : (functor k B e).Linear k where
  map_smul := by
    intro M N f c
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    change algebraMap k (B ⊗[k] Bᵐᵒᵖ) c • (f.hom x.val) =
      restriction k B (algebraMap k Bᵐᵒᵖ c) • (f.hom x.val)
    rw [show restriction k B (algebraMap k Bᵐᵒᵖ c) =
      algebraMap k (B ⊗[k] Bᵐᵒᵖ) c from
      (Algebra.TensorProduct.includeRight : Bᵐᵒᵖ →ₐ[k] B ⊗[k] Bᵐᵒᵖ).commutes c]
end LittleFinitistic.BimoduleVertex

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Ordinary_OrdinaryFiniteColumnComplex
attribute [-instance] _root_.OAI.DerivedBar.Multibar.patternModule _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.DerivedBar.termModule _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.BimoduleCoefficients.instAddCommGroupCarrierTensorProductMulOpposite _root_.OAI.LittleFinitistic.BimoduleCoefficients.instModuleCarrierTensorProductMulOpposite_1 _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instAddCommGroup _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instRing _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated
attribute [-simp] _root_.OAI.ExternalTensor.Section4.sum_hom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open CategoryTheory
namespace LittleFinitistic.FiniteColumnComplex
universe u
variable {R : Type u} [Ring R] {l : ℕ}
variable (K : Fin l → CochainComplex (ModuleCat.{u} R) ℤ)

/-- A finite-column total differential, recorded independently of a chosen direct-sum presentation. -/
structure Differential where
  d : ∀ n : ℤ, term K n →ₗ[R] term K (n+1)
  square : ∀ n, (d (n+1)).comp (d n) = 0
  triangular : ∀ (n : ℤ) (i : Fin l) (z : term K n),
    (∀ j : Fin l, j.val < i.val → z j = 0) →
    d n z i = ((K i).d n (n+1)).hom (z i)

variable (δ : Differential K)

def complex : CochainComplex (ModuleCat.{u} R) ℤ :=
  CochainComplex.of (fun n => ModuleCat.of R (term K n))
    (fun n => ModuleCat.ofHom (δ.d n)) (fun n => ModuleCat.hom_ext (δ.square n))

@[simp] theorem complex_d (n : ℤ) :
    (complex K δ).d n (n+1) = ModuleCat.ofHom (δ.d n) := by
  exact CochainComplex.of_d (fun n => ModuleCat.of R (term K n))
    (fun n => ModuleCat.ofHom (δ.d n)) n

@[simp] theorem complex_d_hom (n : ℤ) :
    ((complex K δ).d n (n+1)).hom = δ.d n := by
  rw [complex_d]
  rfl

theorem lower_single (n : ℤ) (i : Fin l) (x : (K i).X n) (j : Fin l) (hji : j.val < i.val) :
    δ.d n (Pi.single i x : term K n) j = 0 := by
  classical
  have ht : ∀ t : Fin l, t.val < j.val → (Pi.single i x : term K n) t = 0 := by
    intro t ht
    simp [show t ≠ i from by intro h; subst t; omega]
  rw [δ.triangular n j (Pi.single i x) ht]
  rw [Pi.single_eq_of_ne (show j ≠ i from by intro h; subst j; omega),map_zero]

theorem diagonal_single (n : ℤ) (i : Fin l) (x : (K i).X n) :
    δ.d n (Pi.single i x) i = ((K i).d n (n+1)).hom x := by
  classical
  have ht : ∀ j : Fin l, j.val < i.val → (Pi.single i x : term K n) j = 0 := by
    intro j hj
    simp [show j ≠ i from by intro h; subst j; omega]
  rw [δ.triangular n i (Pi.single i x) ht,Pi.single_eq_same]

/-- Finite totalization preserves acyclicity when every column is acyclic. -/
theorem acyclic (hK : ∀ i, (K i).Acyclic) : (complex K δ).Acyclic := by
  intro n
  have hn : n-1+1=n := by omega
  suffices hh : (complex K δ).ExactAt (n-1+1) by simpa only [hn] using hh
  apply (HomologicalComplex.exactAt_iff' _ (n-1) (n-1+1) ((n-1+1)+1) (by simp) (by simp)).2
  rw [ShortComplex.moduleCat_exact_iff]
  have hex (i : Fin l) : Function.Exact
      ((K i).d (n-1) (n-1+1)).hom ((K i).d (n-1+1) ((n-1+1)+1)).hom := by
    have hh := (HomologicalComplex.exactAt_iff' (K i) (n-1) (n-1+1) ((n-1+1)+1)
      (by simp) (by simp)).mp (hK i _)
    exact (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mp hh
  have ht := TriangularExactness.exact_of_diagonal
    (fun i => (K i).X (n-1)) (fun i => (K i).X (n-1+1)) (fun i => (K i).X ((n-1+1)+1))
    (δ.d (n-1)) (δ.d (n-1+1))
    (fun i => ((K i).d (n-1) (n-1+1)).hom)
    (fun i => ((K i).d (n-1+1) ((n-1+1)+1)).hom)
    (δ.square (n-1)) (lower_single K δ (n-1)) (diagonal_single K δ (n-1))
    (δ.triangular (n-1+1)) hex
  change ∀ (z : term K (n-1+1)),
    ((complex K δ).d (n-1+1) ((n-1+1)+1)).hom z = 0 →
    ∃ w : term K (n-1), ((complex K δ).d (n-1) (n-1+1)).hom w = z
  simp only [complex_d_hom]
  exact fun z hz => (ht z).mp hz
end LittleFinitistic.FiniteColumnComplex

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Ordinary_OrdinaryFiniteTotal
attribute [-instance] _root_.OAI.DerivedBar.Multibar.patternModule _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.DerivedBar.termModule _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.BimoduleCoefficients.instAddCommGroupCarrierTensorProductMulOpposite _root_.OAI.LittleFinitistic.BimoduleCoefficients.instModuleCarrierTensorProductMulOpposite_1 _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instAddCommGroup _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instRing _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated
attribute [-simp] _root_.OAI.ExternalTensor.Section4.sum_hom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open CategoryTheory
namespace LittleFinitistic.FiniteColumnComplex
universe u
variable {R : Type u} [Ring R] {l : ℕ}
variable (K : Fin l → CochainComplex (ModuleCat.{u} R) ℤ)

/-- The vertical differential on the finite direct sum of the columns. -/
def diagonal (n : ℤ) : term K n →ₗ[R] term K (n+1) :=
  LinearMap.pi (fun i => ((K i).d n (n+1)).hom.comp (LinearMap.proj i))

@[simp] theorem diagonal_apply (n : ℤ) (z : term K n) (i : Fin l) :
    diagonal K n z i = ((K i).d n (n+1)).hom (z i) := rfl

theorem diagonal_square (n : ℤ) : (diagonal K (n+1)).comp (diagonal K n) = 0 := by
  apply LinearMap.ext
  intro z
  funext i
  exact congrArg (fun f => f.hom (z i)) ((K i).d_comp_d n (n+1) ((n+1)+1))

/-- A horizontal differential on signed columns, with its actual square and mixed relation. -/
structure Horizontal where
  d : ∀ n : ℤ, term K n →ₗ[R] term K (n+1)
  square : ∀ n, (d (n+1)).comp (d n) = 0
  mixed : ∀ n, (diagonal K (n+1)).comp (d n) + (d (n+1)).comp (diagonal K n) = 0
  strictUpper : ∀ (n : ℤ) (i : Fin l) (z : term K n),
    (∀ j : Fin l, j.val < i.val → z j = 0) → d n z i = 0

variable (H : Horizontal K)

/-- The full differential is the sum of the signed vertical and horizontal differentials. -/
def totalDifferential : Differential K where
  d n := diagonal K n + H.d n
  square n := by
    apply LinearMap.ext
    intro z
    funext i
    have hv := congrArg (fun f : term K n →ₗ[R] term K ((n+1)+1) => f z i) (diagonal_square K n)
    have hh := congrArg (fun f : term K n →ₗ[R] term K ((n+1)+1) => f z i) (H.square n)
    have hm := congrArg (fun f : term K n →ₗ[R] term K ((n+1)+1) => f z i) (H.mixed n)
    simp only [LinearMap.comp_apply,LinearMap.add_apply,LinearMap.zero_apply,Pi.add_apply,Pi.zero_apply] at hv hh hm ⊢
    simp only [map_add,Pi.add_apply]
    simp only [diagonal_apply] at hv hh hm ⊢
    rw [hv,hh]
    simpa only [zero_add,add_zero] using hm
  triangular n i z hz := by
    change diagonal K n z i + H.d n z i = _
    rw [H.strictUpper n i z hz,add_zero]
    rfl

def total : CochainComplex (ModuleCat.{u} R) ℤ := complex K (totalDifferential K H)

end LittleFinitistic.FiniteColumnComplex

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Ordinary_OrdinaryFiniteTotalMaps
attribute [-instance] _root_.OAI.DerivedBar.Multibar.patternModule _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.DerivedBar.termModule _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.BimoduleCoefficients.instAddCommGroupCarrierTensorProductMulOpposite _root_.OAI.LittleFinitistic.BimoduleCoefficients.instModuleCarrierTensorProductMulOpposite_1 _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instAddCommGroup _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instRing _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated
attribute [-simp] _root_.OAI.ExternalTensor.Section4.sum_hom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open CategoryTheory
namespace LittleFinitistic.FiniteColumnComplex
universe u
variable {R : Type u} [Ring R] {l : ℕ}
variable (K L : Fin l → CochainComplex (ModuleCat.{u} R) ℤ)
variable (δ : Differential K) (ε : Differential L)
variable (f : ∀ i, K i ⟶ L i)

/-- The degreewise map between the actual finite sums of columns. -/
def componentMap (n : ℤ) : term K n →ₗ[R] term L n :=
  LinearMap.pi (fun i => ((f i).f n).hom.comp (LinearMap.proj i))

@[simp] theorem componentMap_apply (n : ℤ) (z : term K n) (i : Fin l) :
    componentMap K L f n z i = ((f i).f n).hom (z i) := rfl

/-- A compatible family of column maps gives an actual map of total complexes. -/
def complexMap (hc : ∀ n,
    (ε.d n).comp (componentMap K L f n) = (componentMap K L f (n+1)).comp (δ.d n)) :
    complex K δ ⟶ complex L ε where
  f n := ModuleCat.ofHom (componentMap K L f n)
  comm' n m h := by
    change n+1=m at h
    subst m
    rw [complex_d,complex_d]
    apply ModuleCat.hom_ext
    exact hc n
end LittleFinitistic.FiniteColumnComplex

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Ordinary_OrdinaryFiniteConeReindex
attribute [-instance] _root_.OAI.DerivedBar.Multibar.patternModule _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.DerivedBar.termModule _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.BimoduleCoefficients.instAddCommGroupCarrierTensorProductMulOpposite _root_.OAI.LittleFinitistic.BimoduleCoefficients.instModuleCarrierTensorProductMulOpposite_1 _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instAddCommGroup _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instRing _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated
attribute [-simp] _root_.OAI.ExternalTensor.Section4.sum_hom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open CategoryTheory
namespace LittleFinitistic.FiniteColumnComplex
universe u
variable {R : Type u} [Ring R] {l : ℕ}
variable (K L : Fin l → CochainComplex (ModuleCat.{u} R) ℤ)
variable (δ : Differential K) (ε : Differential L)
variable (f : ∀ i, K i ⟶ L i)
variable (hc : ∀ n,
    (ε.d n).comp (componentMap K L f n) = (componentMap K L f (n+1)).comp (δ.d n))

abbrev totalCone := CochainComplex.mappingCone (complexMap K L δ ε f hc)

/-- Distribution of a binary module product over the finite family of columns. -/
def pairEquiv (n : ℤ) : (term K (n+1) × term L n) ≃ₗ[R] (∀ i, (K i).X (n+1) × (L i).X n) where
  toFun z i := (z.1 i,z.2 i)
  invFun z := (fun i => (z i).1,fun i => (z i).2)
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Reindex the actual cone of a total map into the actual cones of its column maps. -/
def coneEquiv (n : ℤ) : (totalCone K L δ ε f hc).X n ≃ₗ[R] term (coneColumn K L f) n :=
  (ConeCoordinates.coordinateEquiv (complexMap K L δ ε f hc) n).trans
    ((pairEquiv K L n).trans
      (LinearEquiv.piCongrRight (fun i => (ConeCoordinates.coordinateEquiv (f i) n).symm)))

@[simp] theorem coneEquiv_coordinate (n : ℤ) (z : (totalCone K L δ ε f hc).X n) (i : Fin l) :
    ConeCoordinates.coordinateEquiv (f i) n (coneEquiv K L δ ε f hc n z i) =
      ((ConeCoordinates.coordinateEquiv (complexMap K L δ ε f hc) n z).1 i,
       (ConeCoordinates.coordinateEquiv (complexMap K L δ ε f hc) n z).2 i) := by
  exact (ConeCoordinates.coordinateEquiv (f i) n).apply_symm_apply _

@[simp] theorem coneEquiv_symm_coordinate (n : ℤ) (z : term (coneColumn K L f) n) (i : Fin l) :
    ((ConeCoordinates.coordinateEquiv (complexMap K L δ ε f hc) n ((coneEquiv K L δ ε f hc n).symm z)).1 i,
     (ConeCoordinates.coordinateEquiv (complexMap K L δ ε f hc) n ((coneEquiv K L δ ε f hc n).symm z)).2 i) =
      ConeCoordinates.coordinateEquiv (f i) n (z i) := by
  have hh := coneEquiv_coordinate K L δ ε f hc n ((coneEquiv K L δ ε f hc n).symm z) i
  rw [LinearEquiv.apply_symm_apply] at hh
  exact hh.symm

/-- Transport the genuine cone differential through this coordinate equivalence. -/
def coneDifferential (n : ℤ) : term (coneColumn K L f) n →ₗ[R] term (coneColumn K L f) (n+1) :=
  (coneEquiv K L δ ε f hc (n+1)).toLinearMap.comp
    (((totalCone K L δ ε f hc).d n (n+1)).hom.comp (coneEquiv K L δ ε f hc n).symm.toLinearMap)

theorem coneDifferential_square (n : ℤ) :
    (coneDifferential K L δ ε f hc (n+1)).comp (coneDifferential K L δ ε f hc n) = 0 := by
  apply LinearMap.ext
  intro z
  change coneEquiv K L δ ε f hc ((n+1)+1)
    (((totalCone K L δ ε f hc).d (n+1) ((n+1)+1)).hom
      ((coneEquiv K L δ ε f hc (n+1)).symm
        (coneEquiv K L δ ε f hc (n+1)
          (((totalCone K L δ ε f hc).d n (n+1)).hom ((coneEquiv K L δ ε f hc n).symm z))))) = 0
  rw [LinearEquiv.symm_apply_apply]
  have hh := congrArg (fun g => g.hom ((coneEquiv K L δ ε f hc n).symm z))
    ((totalCone K L δ ε f hc).d_comp_d n (n+1) ((n+1)+1))
  change ((totalCone K L δ ε f hc).d (n+1) ((n+1)+1)).hom
    (((totalCone K L δ ε f hc).d n (n+1)).hom ((coneEquiv K L δ ε f hc n).symm z)) = 0 at hh
  rw [hh,map_zero]
end LittleFinitistic.FiniteColumnComplex

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Ordinary_OrdinaryFiniteConeTriangular
attribute [-instance] _root_.OAI.DerivedBar.Multibar.patternModule _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.DerivedBar.termModule _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.BimoduleCoefficients.instAddCommGroupCarrierTensorProductMulOpposite _root_.OAI.LittleFinitistic.BimoduleCoefficients.instModuleCarrierTensorProductMulOpposite_1 _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instAddCommGroup _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instRing _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open CategoryTheory
namespace LittleFinitistic.FiniteColumnComplex
universe u
variable {R : Type u} [Ring R] {l : ℕ}
variable (K L : Fin l → CochainComplex (ModuleCat.{u} R) ℤ)
variable (δ : Differential K) (ε : Differential L)
variable (f : ∀ i, K i ⟶ L i)
variable (hc : ∀ n,
    (ε.d n).comp (componentMap K L f n) = (componentMap K L f (n+1)).comp (δ.d n))

abbrev coneSource (n : ℤ) (z : term (coneColumn K L f) n) : term K (n+1) :=
  fun i => (ConeCoordinates.coordinateEquiv (f i) n (z i)).1
abbrev coneTarget (n : ℤ) (z : term (coneColumn K L f) n) : term L n :=
  fun i => (ConeCoordinates.coordinateEquiv (f i) n (z i)).2

theorem coneEquiv_symm_pair (n : ℤ) (z : term (coneColumn K L f) n) :
    ConeCoordinates.coordinateEquiv (complexMap K L δ ε f hc) n
      ((coneEquiv K L δ ε f hc n).symm z) = (coneSource K L f n z,coneTarget K L f n z) := by
  apply Prod.ext
  · funext i
    exact congrArg Prod.fst (coneEquiv_symm_coordinate K L δ ε f hc n z i)
  · funext i
    exact congrArg Prod.snd (coneEquiv_symm_coordinate K L δ ε f hc n z i)

/-- The conjugated genuine cone differential has the expected finite-column formula. -/
theorem coneDifferential_coordinate (n : ℤ) (z : term (coneColumn K L f) n) (i : Fin l) :
    ConeCoordinates.coordinateEquiv (f i) (n+1) (coneDifferential K L δ ε f hc n z i) =
      (-(δ.d (n+1) (coneSource K L f n z)) i,
       ((f i).f (n+1)).hom (coneSource K L f n z i) + (ε.d n (coneTarget K L f n z)) i) := by
  change ConeCoordinates.coordinateEquiv (f i) (n+1)
    (coneEquiv K L δ ε f hc (n+1)
      (((totalCone K L δ ε f hc).d n (n+1)).hom ((coneEquiv K L δ ε f hc n).symm z)) i) = _
  rw [coneEquiv_coordinate,ConeCoordinates.differential_fst,ConeCoordinates.differential_snd,
    coneEquiv_symm_pair]
  simp only [complex_d_hom]
  rfl

/-- The cone of a componentwise total map is triangular with the actual column cones on its diagonal. -/
def coneTriangular : Differential (coneColumn K L f) where
  d := coneDifferential K L δ ε f hc
  square := coneDifferential_square K L δ ε f hc
  triangular n i z hz := by
    apply (ConeCoordinates.coordinateEquiv (f i) (n+1)).injective
    rw [coneDifferential_coordinate]
    have hSource : ∀ j : Fin l, j.val < i.val → coneSource K L f n z j = 0 := by
      intro j hj
      simp only [coneSource,hz j hj,map_zero,Prod.fst_zero]
    have hTarget : ∀ j : Fin l, j.val < i.val → coneTarget K L f n z j = 0 := by
      intro j hj
      simp only [coneTarget,hz j hj,map_zero,Prod.snd_zero]
    rw [δ.triangular (n+1) i _ hSource,ε.triangular n i _ hTarget]
    apply Prod.ext
    · exact (ConeCoordinates.differential_fst (f i) n (z i)).symm
    · exact (ConeCoordinates.differential_snd (f i) n (z i)).symm

/-- The triangular cone model is isomorphic to the native cone, not an assumed cone replacement. -/
def coneIso : totalCone K L δ ε f hc ≅ complex (coneColumn K L f) (coneTriangular K L δ ε f hc) :=
  HomologicalComplex.Hom.isoOfComponents (fun n => (coneEquiv K L δ ε f hc n).toModuleIso) (by
    intro n m h
    change n+1=m at h
    subst m
    rw [complex_d]
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    change coneEquiv K L δ ε f hc (n+1)
      (((totalCone K L δ ε f hc).d n (n+1)).hom
        ((coneEquiv K L δ ε f hc n).symm (coneEquiv K L δ ε f hc n z))) =
      coneEquiv K L δ ε f hc (n+1) (((totalCone K L δ ε f hc).d n (n+1)).hom z)
    rw [LinearEquiv.symm_apply_apply])

/-- Quasi-isomorphisms in every column induce a quasi-isomorphism of the actual finite totals. -/
theorem complexMap_quasiIso [∀ i, QuasiIso (f i)] : QuasiIso (complexMap K L δ ε f hc) := by
  apply (LittleFinitistic.quasiIso_iff_mappingCone_acyclic _).mpr
  have ha := acyclic (coneColumn K L f) (coneTriangular K L δ ε f hc)
    (fun i => (LittleFinitistic.quasiIso_iff_mappingCone_acyclic (f i)).mp inferInstance)
  intro n
  exact (exactAt_iff_of_quasiIsoAt (coneIso K L δ ε f hc).hom n).mpr (ha n)
end LittleFinitistic.FiniteColumnComplex

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Ordinary_OrdinaryChainAlgebra
attribute [-instance] _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instAddCommGroup _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instRing _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated
attribute [-simp] _root_.OAI.ExternalTensor.Section4.sum_hom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open scoped TensorProduct
namespace LittleFinitistic.OrdinarySimulation
universe u
variable (k : Type u) [Field k] (l : ℕ)

namespace ChainAlgebra
instance instModule : Module k (ChainAlgebra k l) :=
  inferInstanceAs (Module k ((Fin (l+1) → k) × (Fin l → k)))

@[simp] theorem zero_eq : (0 : ChainAlgebra k l) = (0,0) := rfl
@[simp] theorem add_eq (x y : ChainAlgebra k l) : x+y = (x.1+y.1,x.2+y.2) := rfl
@[simp] theorem smul_eq (c : k) (x : ChainAlgebra k l) : c • x = (c • x.1,c • x.2) := rfl

def unit : ChainAlgebra k l := (fun _ => 1, fun _ => 0)

end ChainAlgebra

end LittleFinitistic.OrdinarySimulation

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Ordinary_OrdinaryBimodule
attribute [-instance] _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instAddCommGroup _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instRing _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated
attribute [-simp] _root_.OAI.ExternalTensor.Section4.sum_hom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open CategoryTheory
open scoped TensorProduct
namespace LittleFinitistic.OrdinarySimulation
universe u
variable {k B : Type u} [Field k] [Ring B] [Algebra k B]

/-- O from the genuine dg B-bimodule, as an ordinary finite sum of its terms. -/
def BimoduleO (P : CochainComplex (ModuleCat.{u} (Enveloping k B)) ℤ)
    (a : ℤ) (l : ℕ) := Compression P a l

namespace BimoduleO
variable (P : CochainComplex (ModuleCat.{u} (Enveloping k B)) ℤ) (a : ℤ) (l : ℕ)
instance instAddCommGroup : AddCommGroup (BimoduleO P a l) := inferInstanceAs (AddCommGroup (Compression P a l))
instance instModuleEnveloping : Module (Enveloping k B) (BimoduleO P a l) := inferInstanceAs (Module (Enveloping k B) (Compression P a l))
instance instModule_1 : Module B (BimoduleO P a l) :=
  Module.compHom (Compression P a l) (Algebra.TensorProduct.includeLeft (R := k) (S := k) (B := Bᵐᵒᵖ)).toRingHom
instance instModuleMulOpposite : Module Bᵐᵒᵖ (BimoduleO P a l) :=
  Module.compHom (Compression P a l) (Algebra.TensorProduct.includeRight (R := k) (A := B)).toRingHom

instance commuteLeftRight : SMulCommClass B Bᵐᵒᵖ (BimoduleO P a l) where
  smul_comm b r v := by
    change ((b ⊗ₜ[k] (1:Bᵐᵒᵖ)) : Enveloping k B) •
      (((1:B) ⊗ₜ[k] r) • (v : Compression P a l)) =
      ((1:B) ⊗ₜ[k] r) • ((b ⊗ₜ[k] (1:Bᵐᵒᵖ)) • (v : Compression P a l))
    rw [← mul_smul, ← mul_smul]
    simp [Algebra.TensorProduct.tmul_mul_tmul]

end BimoduleO
end LittleFinitistic.OrdinarySimulation

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Bimodule_BimoduleBarTensorComparison
attribute [-instance] _root_.OAI.DerivedBar.Multibar.patternModule _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.LittleFinitistic.BimoduleCoefficients.instAddCommGroupCarrierTensorProductMulOpposite _root_.OAI.LittleFinitistic.BimoduleCoefficients.instModuleCarrierTensorProductMulOpposite _root_.OAI.LittleFinitistic.BimoduleCoefficients.instModuleCarrierTensorProductMulOpposite_1 _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open CategoryTheory
open scoped TensorProduct
namespace LittleFinitistic.BimoduleBarComparison
open ExternalTensor.Section4 BimoduleTotal
universe u
variable (k B : Type u) [Field k] [Ring B] [Algebra k B]
variable (M : ModuleCat.{u} (Enveloping k B))

variable (N : ModuleCat.{u} B)
local instance instModuleCarrier_solutions (N : ModuleCat.{u} B) : Module k N := DerivedBar.BimoduleTensor.scalarModule k B N
local instance instIsScalarTowerCarrier_solutions (N : ModuleCat.{u} B) : IsScalarTower k B N :=
  IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)

end LittleFinitistic.BimoduleBarComparison

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Localization_IntegerExtensionFunctor
attribute [-instance] _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instAddCommGroup _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instRing _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

set_option backward.isDefEq.respectTransparency false

namespace OAI
noncomputable section
open CategoryTheory CategoryTheory.Limits
namespace LittleFinitistic.IntegerExtensionFunctor
universe u
variable {B : Type u} [Ring B]
variable (F : ModuleCat.{u} B ⥤ ModuleCat.{u} B) [F.Additive]
variable (Z : ChainComplex (ModuleCat.{u} B) ℕ)
local notation "c" => ComplexShape.down ℕ

/-- Applying an additive module functor commutes with the actual n ↦ -n zero extension. -/
def complexIso : (F.mapHomologicalComplex (.up ℤ)).obj ((DerivedBar.integerExtension B).obj Z) ≅
    (DerivedBar.integerExtension B).obj ((F.mapHomologicalComplex c).obj Z) :=
  HomologicalComplex.Hom.isoOfComponents (fun n => termIso F Z (ComplexShape.embeddingDownNat.r n))
    (by intro n m h; exact termIso_d F Z (ComplexShape.embeddingDownNat.r n) (ComplexShape.embeddingDownNat.r m))

variable {Z} {Z' : ChainComplex (ModuleCat.{u} B) ℕ}

/-- Naturality holds on every chain map, including the added zero degrees. -/
def naturalIso : DerivedBar.integerExtension B ⋙ F.mapHomologicalComplex (.up ℤ) ≅
    F.mapHomologicalComplex c ⋙ DerivedBar.integerExtension B :=
  NatIso.ofComponents (complexIso F) (by
    intro Z Z' f
    apply HomologicalComplex.Hom.ext
    funext n
    exact termIso_natural F f (ComplexShape.embeddingDownNat.r n))
end LittleFinitistic.IntegerExtensionFunctor

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Bimodule_BimoduleBarStalk
attribute [-instance] _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open CategoryTheory CategoryTheory.Functor
namespace LittleFinitistic.BimoduleTotal
open ExternalTensor.Section4
universe u
variable {k B : Type u} [Field k] [Ring B] [Algebra k B]
variable {P : BiComplex k B} {X : ModuleCat.{u} (Enveloping k B)}

attribute [local instance] OAI.LittleFinitistic.BimoduleTotal.instHasDerivedCategoryModuleCat_solutions_4
/-- The chain stalk's integer extension is the native integer stalk. -/
def integerSingleIso (N : ModuleCat.{u} B) :
    (DerivedBar.integerQ B).obj ((ChainComplex.single₀ _).obj N) ≅
      DerivedCategory.Q.obj (singleInput B N) :=
  DerivedCategory.Q.mapIso
    (HomologicalComplex.extendSingleIso ComplexShape.embeddingDownNat N 0 0 (by simp))

end LittleFinitistic.BimoduleTotal

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Encoding_QuadraticPresentation
attribute [-instance] _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instAddCommGroup _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instRing _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated
attribute [-simp] _root_.OAI.ExternalTensor.Section4.sum_hom _root_.OAI.LittleFinitistic.PresentationReindex.rename_word
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
namespace LittleFinitistic.QuadraticPresentation

variable (R : Type*) [CommRing R] (α : Type*)

/-- Degree at most n means an R-linear combination of words of length at most n.
This definition includes zero, constants, and linear terms. -/
def degreeLE (n : ℕ) : Submodule R (FreeAlgebra R α) :=
  Submodule.span R {p | ∃ w : List α, w.length ≤ n ∧ p = word R α w}

variable {R α}
theorem word_mem_degreeLE (w : List α) (n : ℕ) (h : w.length ≤ n) :
    word R α w ∈ degreeLE R α n :=
  Submodule.subset_span ⟨w,h,rfl⟩

theorem one_mem_degreeLE (n : ℕ) : (1 : FreeAlgebra R α) ∈ degreeLE R α n := by
  simpa using word_mem_degreeLE (R := R) ([] : List α) n (Nat.zero_le n)

theorem generator_mem_degreeLE (a : α) : FreeAlgebra.ι R a ∈ degreeLE R α 2 := by
  simpa using word_mem_degreeLE (R := R) [a] 2 (by simp)

theorem product_mem_degreeLE (a b : α) :
    FreeAlgebra.ι R a * FreeAlgebra.ι R b ∈ degreeLE R α 2 := by
  simpa [word] using word_mem_degreeLE (R := R) [a,b] 2 (by simp)

variable (R α)
/-- A single common bound for every monomial in finitely many relations. -/
theorem exists_word_bound {κ : Type*} [Finite κ] (p : κ → FreeAlgebra R α) :
    ∃ N : ℕ, ∀ i w, w ∈ (coefficients R α (p i)).support → w.toList.length ≤ N := by
  let := Fintype.ofFinite κ
  classical
  refine ⟨Finset.univ.sup (fun i => (coefficients R α (p i)).support.sup
    (fun w => w.toList.length)), ?_⟩
  intro i w hw
  exact (Finset.le_sup (f := fun w : FreeMonoid α => w.toList.length) hw).trans
    (Finset.le_sup (f := fun i => (coefficients R α (p i)).support.sup
      (fun w => w.toList.length)) (Finset.mem_univ i))



instance word_finite [Finite α] (N : ℕ) : Finite (Word α N) :=
  List.finite_length_le α N

instance step_finite [Finite α] (N : ℕ) : Finite (Step α N) := by
  apply Finite.of_injective (fun s : Step α N =>
    ((⟨s.val.1, by have := s.property; simp only [List.length_append,
      List.length_singleton] at this; omega⟩ : Word α N), s.val.2))
  intro a b h
  apply Subtype.ext
  exact Prod.ext (congrArg (fun x => x.1.val) h) (congrArg (fun x : Word α N × α => x.2) h)

theorem linearize_degree (N : ℕ) (p : FreeAlgebra R α) :
    linearize R α N p ∈ degreeLE R (Letter α N) 2 := by
  classical
  apply Submodule.sum_mem
  intro w hw
  apply Submodule.smul_mem
  unfold encodeWord
  split
  · apply generator_mem_degreeLE
  · apply Submodule.zero_mem

variable {κ : Type*} (p : κ → FreeAlgebra R α) (N : ℕ)

theorem relation_degree (i : EquationIndex α N (κ := κ)) :
    relation R α p N i ∈ degreeLE R (Letter α N) 2 := by
  rcases i with i | (u | s)
  · exact linearize_degree R α N (p i)
  · exact Submodule.sub_mem _ (generator_mem_degreeLE _) (one_mem_degreeLE _)
  · exact Submodule.sub_mem _ (generator_mem_degreeLE _) (product_mem_degreeLE _ _)

theorem linearize_in_quotient (f : FreeAlgebra R α)
    (h : ∀ w ∈ (coefficients R α f).support, w.toList.length ≤ N) :
    quadraticMap R α p N (linearize R α N f) = oldInNew R α p N f := by
  conv_rhs => rw [← expansion R α f]
  simp only [linearize, Finsupp.sum, map_sum, map_smul]
  apply Finset.sum_congr rfl
  intro w hw
  simp only [encodeWord, dite_eq_left (h w hw)]
  rw [auxiliary_eq_word]

variable (bound : ∀ i w, w ∈ (coefficients R α (p i)).support → w.toList.length ≤ N)

def toQuadratic : Original R α p →ₐ[R] Quadratic R α p N :=
  (original R α p).liftₐ (oldInNew R α p N)
    (RingCon.ringConGen_le.mpr (by
      rintro x y ⟨i,rfl,rfl⟩
      change oldInNew R α p N (p i) = oldInNew R α p N 0
      rw [map_zero, ← linearize_in_quotient R α p N (p i) (bound i)]
      exact quadratic_relation R α p N (.inl i)))

@[simp] theorem toQuadratic_quotient (f : FreeAlgebra R α) :
    toQuadratic R α p N bound (originalMap R α p f) = oldInNew R α p N f := rfl

/-- Eliminating auxiliaries after including the old generators fixes the old algebra. -/
theorem original_roundtrip :
    (toOriginal R α p N bound).comp (toQuadratic R α p N bound) =
      AlgHom.id R (Original R α p) := by
  have h : ((toOriginal R α p N bound).comp (toQuadratic R α p N bound)).comp
      (originalMap R α p) = originalMap R α p := by
    apply FreeAlgebra.hom_ext
    funext a
    simp [oldInNew, inclusion, eliminate, AlgHom.comp_apply,
      toQuadratic_quotient, toOriginal_quotient]
  apply AlgHom.ext
  intro x
  obtain ⟨f,rfl⟩ := (original R α p).mkₐ_surjective (α := R) x
  exact DFunLike.congr_fun h f

/-- Prefix equations prove that the other composite fixes every new generator too. -/
theorem quadratic_roundtrip :
    (toQuadratic R α p N bound).comp (toOriginal R α p N bound) =
      AlgHom.id R (Quadratic R α p N) := by
  have h : ((toQuadratic R α p N bound).comp (toOriginal R α p N bound)).comp
      (quadraticMap R α p N) = quadraticMap R α p N := by
    apply FreeAlgebra.hom_ext
    funext a
    rcases a with a | ⟨w,hw⟩
    · simp [oldInNew, inclusion, eliminate, AlgHom.comp_apply,
        toQuadratic_quotient, toOriginal_quotient]
    · change toQuadratic R α p N bound
        (toOriginal R α p N bound (quadraticMap R α p N
          (FreeAlgebra.ι R (.inr ⟨w,hw⟩)))) = _
      rw [toOriginal_quotient]
      simp only [eliminate, FreeAlgebra.lift_ι_apply, Sum.elim_inr]
      rw [toQuadratic_quotient]
      exact (auxiliary_eq_word R α p N w hw).symm
  apply AlgHom.ext
  intro x
  obtain ⟨f,rfl⟩ := (quadratic R α p N).mkₐ_surjective (α := R) x
  exact DFunLike.congr_fun h f

/-- An algebra equivalence with mutually inverse composites. -/
def quadraticEquiv : Quadratic R α p N ≃ₐ[R] Original R α p :=
  AlgEquiv.ofAlgHom (toOriginal R α p N bound) (toQuadratic R α p N bound)
    (original_roundtrip R α p N bound) (quadratic_roundtrip R α p N bound)



end LittleFinitistic.QuadraticPresentation

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Selection_GroupSelection
attribute [-instance] _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated
attribute [-simp] _root_.OAI.ExternalTensor.Section4.sum_hom _root_.OAI.LittleFinitistic.FinitePresentation.selection_U_orbit _root_.OAI.LittleFinitistic.FinitePresentation.selection_V_orbit _root_.OAI.LittleFinitistic.FinitePresentation.selection_W_orbit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
/-! Group identities used in Section 2 of v5s9.15. -/

open scoped commutatorElement

namespace LittleFinitistic

namespace SelectionGroupData

variable {G : Type*} [Group G] (D : SelectionGroupData G)

theorem split_transfer (i j : Fin 3) (a b c d : ℤ)
    (hij : i ≠ j) (hsum : a+b = c+d) :
    ⁅D.U i a, D.V i b⁆ = ⁅D.U j c, D.V j d⁆ := by
  have hU : D.U i a * D.W i j (c-a) =
      D.U j c * D.W i j (c-a) * D.U i a := by
    have h := D.commutator_UW i j a (c-a) hij
    have hc : a + (c-a) = c := by omega
    rw [hc] at h
    rw [← h]
    simp [commutatorElement_def, mul_assoc]
  have hV : D.W i j (c-a) * D.V j d =
      D.V i b * D.V j d * D.W i j (c-a) := by
    have h := D.commutator_WV i j (c-a) d hij
    have hb : c-a+d = b := by omega
    rw [hb] at h
    rw [← h]
    simp [commutatorElement_def, mul_assoc]
  exact commutator_transfer (D.U i a) (D.W i j (c-a)) (D.V j d)
    (D.U j c) (D.V i b) hU hV (D.commute_UV i j a d hij)
    (D.commute_UV j i c b hij.symm).symm (D.commute_VV i j b d hij)

theorem splitting_independent (i j : Fin 3) (a b c d : ℤ)
    (hsum : a+b = c+d) : ⁅D.U i a,D.V i b⁆ = ⁅D.U j c,D.V j d⁆ := by
  obtain ⟨k, hki, hkj⟩ := Fin.exists_ne_and_ne_of_two_lt i j (by decide)
  calc
    ⁅D.U i a,D.V i b⁆ = ⁅D.U k 0,D.V k (a+b)⁆ :=
      D.split_transfer i k a b 0 (a+b) hki.symm (by omega)
    _ = ⁅D.U j c,D.V j d⁆ :=
      D.split_transfer k j 0 (a+b) c d hkj (by omega)

def centralZ (N : ℤ) : G := ⁅D.U 0 0,D.V 0 N⁆

theorem centralZ_eq (N : ℤ) (i : Fin 3) (a b : ℤ) (h : a+b=N) :
    D.centralZ N = ⁅D.U i a,D.V i b⁆ := by
  exact D.splitting_independent 0 i 0 N a b (by omega)

theorem centralZ_commute_U (N : ℤ) (h : Fin 3) (a : ℤ) :
    Commute (D.centralZ N) (D.U h a) := by
  obtain ⟨i, hih, _⟩ := Fin.exists_ne_and_ne_of_two_lt h h (by decide)
  rw [D.centralZ_eq N i 0 N (by omega), commutatorElement_def]
  have hU := D.commute_UU i h 0 a hih
  have hV := (D.commute_UV h i a N hih.symm).symm
  exact ((hU.mul_left hV).mul_left hU.inv_left).mul_left hV.inv_left

theorem centralZ_commute_V (N : ℤ) (h : Fin 3) (a : ℤ) :
    Commute (D.centralZ N) (D.V h a) := by
  obtain ⟨i, hih, _⟩ := Fin.exists_ne_and_ne_of_two_lt h h (by decide)
  rw [D.centralZ_eq N i 0 N (by omega), commutatorElement_def]
  have hU := D.commute_UV i h 0 a hih
  have hV := D.commute_VV i h N a hih
  exact ((hU.mul_left hV).mul_left hU.inv_left).mul_left hV.inv_left

theorem centralZ_commute_W (N : ℤ) (i j : Fin 3) (a : ℤ) :
    Commute (D.centralZ N) (D.W i j a) := by
  obtain ⟨h, hhi, hhj⟩ := Fin.exists_ne_and_ne_of_two_lt i j (by decide)
  rw [D.centralZ_eq N h 0 N (by omega), commutatorElement_def]
  have hU := (D.commute_WU i j h a 0 hhi).symm
  have hV := (D.commute_WV i j h a N hhj).symm
  exact ((hU.mul_left hV).mul_left hU.inv_left).mul_left hV.inv_left

theorem centralZ_involution (N : ℤ) : D.centralZ N * D.centralZ N = 1 := by
  apply central_commutator_involution (D.U 0 0) (D.V 0 N) (D.square_U 0 0)
  exact (D.centralZ_commute_U N 0 0).symm

theorem centralZ_commute_T (N : ℤ) (l : Fin 3) : Commute (D.centralZ N) (D.T l) := by
  have hconj : D.T l * D.centralZ N * (D.T l)⁻¹ = D.centralZ N := by
    rw [centralZ, conjugate_commutatorElement, D.conj_TU, D.conj_TV]
    exact (D.centralZ_eq N 0 _ _ (by omega)).symm
  show D.centralZ N * D.T l = D.T l * D.centralZ N
  calc
    D.centralZ N * D.T l = (D.T l * D.centralZ N * (D.T l)⁻¹) * D.T l := by rw [hconj]
    _ = D.T l * D.centralZ N := by group

end SelectionGroupData

namespace Presentation

def z (N : ℤ) : AuxiliaryGroup := data.centralZ N

theorem z_involution (N : ℤ) : z N * z N = 1 := data.centralZ_involution N

theorem z_central (N : ℤ) (g : AuxiliaryGroup) : Commute (z N) g := by
  have hg : g ∈ Subgroup.closure (Set.range (PresentedGroup.of : Generator → AuxiliaryGroup)) := by
    rw [PresentedGroup.closure_range_of]
    trivial
  induction hg using Subgroup.closure_induction with
  | mem g hg =>
      obtain ⟨s,rfl⟩ := hg
      cases s with
      | T i => exact data.centralZ_commute_T N i
      | U i a => exact data.centralZ_commute_U N i a
      | V i a => exact data.centralZ_commute_V N i a
      | W i j a => exact data.centralZ_commute_W N i j a
  | one => exact Commute.one_right _
  | mul a b ha hb ia ib => exact ia.mul_right ib
  | inv a ha ia => exact ia.inv_right

theorem shiftHom_comp (k l : ℤ) : (shiftHom k).comp (shiftHom l) = shiftHom (l+k) := by
  apply PresentedGroup.ext
  intro s
  cases s <;> simp [MonoidHom.comp_apply,shiftHom,shiftData,data,evaluate,add_assoc]

theorem shiftHom_zero : shiftHom 0 = MonoidHom.id AuxiliaryGroup := by
  apply PresentedGroup.ext
  intro s
  cases s <;> simp [shiftHom,shiftData,data,evaluate]

def shiftAut (k : ℤ) : AuxiliaryGroup ≃* AuxiliaryGroup where
  toFun := shiftHom k
  invFun := shiftHom (-k)
  left_inv a := by
    have h := DFunLike.congr_fun (shiftHom_comp (-k) k) a
    simpa only [add_neg_cancel,shiftHom_zero,MonoidHom.id_apply,MonoidHom.comp_apply] using h
  right_inv a := by
    have h := DFunLike.congr_fun (shiftHom_comp k (-k)) a
    simpa only [neg_add_cancel,shiftHom_zero,MonoidHom.id_apply,MonoidHom.comp_apply] using h
  map_mul' := (shiftHom k).map_mul

end Presentation

end LittleFinitistic

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Selection_FinitePresentation
attribute [-instance] _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticPresentation.step_finite _root_.OAI.LittleFinitistic.QuadraticPresentation.word_finite _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated
attribute [-simp] _root_.OAI.ExternalTensor.Section4.sum_hom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
open scoped commutatorElement
namespace LittleFinitistic.FinitePresentation

/-! Target: Group.IsFinitelyPresented Presentation.AuxiliaryGroup.
Section 2, Lemma group-finite-presentation. No finite-presentation hypothesis
is permitted on the target group. Diagonal W generators are redundant.
-/


section Torus
variable {G : Type*} [Group G]

theorem torus_U (T : Fin 3 → G) (U : Fin 3 → ℤ → G)
    (hf : ∀ l i r, T l * U i r * (T l)⁻¹ = U i (r-if l=i then 1 else 0))
    (n : Lattice) (i : Fin 3) (r : ℤ) :
    torus T n * U i r * (torus T n)⁻¹ = U i (r+wtU i n) := by
  have h := family_torus T (U i) (fun l => -(if l=i then 1 else 0))
    (fun l r => by simpa only [sub_eq_add_neg] using hf l i r) n r
  convert h using 2 <;> first | (with_reducible_and_instances rfl) | (fin_cases i <;> simp [wtU])

theorem torus_V (T : Fin 3 → G) (V : Fin 3 → ℤ → G)
    (hf : ∀ l i r, T l * V i r * (T l)⁻¹ = V i (r+if l=i then 1 else 0))
    (n : Lattice) (i : Fin 3) (r : ℤ) :
    torus T n * V i r * (torus T n)⁻¹ = V i (r+wtV i n) := by
  have h := family_torus T (V i) (fun l => if l=i then 1 else 0)
    (fun l r => hf l i r) n r
  convert h using 2 <;> first | (with_reducible_and_instances rfl) | (fin_cases i <;> simp [wtV])

theorem torus_W (T : Fin 3 → G) (W : Fin 3 → Fin 3 → ℤ → G)
    (hf : ∀ l i j r, T l * W i j r * (T l)⁻¹ =
      W i j (r+(if l=i then 1 else 0)-if l=j then 1 else 0))
    (n : Lattice) (i j : Fin 3) (r : ℤ) :
    torus T n * W i j r * (torus T n)⁻¹ = W i j (r+wtW i j n) := by
  have h := family_torus T (W i j) (fun l => (if l=i then 1 else 0)-(if l=j then 1 else 0))
    (fun l r => by simpa only [add_sub_assoc] using hf l i j r) n r
  convert h using 2 <;> first | (with_reducible_and_instances rfl) | (fin_cases i <;> fin_cases j <;> simp [wtW] <;> ring)
end Torus


namespace CovariantData
variable {G : Type*} [Group G] (D : CovariantData G)

@[simp] theorem act_U (n : Lattice) (i : Fin 3) (a : ℤ) :
    D.act n (D.U i a) = D.U i (a+wtU i n) := torus_U D.T D.U D.TU n i a
@[simp] theorem act_V (n : Lattice) (i : Fin 3) (a : ℤ) :
    D.act n (D.V i a) = D.V i (a+wtV i n) := torus_V D.T D.V D.TV n i a
@[simp] theorem act_W (n : Lattice) (i j : Fin 3) (a : ℤ) :
    D.act n (D.W i j a) = D.W i j (a+wtW i j n) := torus_W D.T D.W D.TW n i j a

/-- All infinite relators follow from the finite zero-argument patterns. -/
def toSelection : SelectionGroupData G where
  T := D.T
  U := D.U
  V := D.V
  W := D.W
  commute_TT := D.TT
  conj_TU := D.TU
  conj_TV := D.TV
  conj_TW := D.TW
  diagonal_W := D.diagonal
  square_U i a := by
    have ha : wtU i (coord i (-a)) = a := by simp [wtU, coord]
    have h := congrArg (D.act (coord i (-a))) (D.square i)
    simpa only [map_mul, map_one, act_U, zero_add, ha] using h
  commute_UU i j a b hij := by
    obtain ⟨n, ha, hb⟩ := table_UU i j hij a b
    have h := (D.UU i j hij).map (D.act n)
    simpa only [act_U, zero_add, ha, hb] using h
  commute_VV i j a b hij := by
    obtain ⟨n, ha, hb⟩ := table_VV i j hij a b
    have h := (D.VV i j hij).map (D.act n)
    simpa only [act_V, zero_add, ha, hb] using h
  commute_UV i j a b hij := by
    obtain ⟨n, ha, hb⟩ := table_UV i j hij a b
    have h := (D.UV i j hij).map (D.act n)
    simpa only [act_U, act_V, zero_add, ha, hb] using h
  commute_WU i j h a b hhi := by
    by_cases hij : i=j
    · subst j
      rw [D.diagonal]
      exact Commute.one_left _
    · obtain ⟨n, ha, hb⟩ := table_WU i j h hij hhi a b
      have hh := (D.WU i j h hhi).map (D.act n)
      simpa only [act_U, act_W, zero_add, ha, hb] using hh
  commute_WV i j h a b hhj := by
    by_cases hij : i=j
    · subst j
      rw [D.diagonal]
      exact Commute.one_left _
    · obtain ⟨n, ha, hb⟩ := table_WV i j h hij hhj a b
      have hh := (D.WV i j h hhj).map (D.act n)
      simpa only [act_V, act_W, zero_add, ha, hb] using hh
  commutator_UW i j a b hij := by
    obtain ⟨n, ha, hb⟩ := table_UW i j hij a b
    have hout : wtU j n = a+b := by dsimp [wtU, wtW] at *; omega
    have h := congrArg (D.act n) (D.UWout i j hij)
    simpa only [map_commutatorElement, act_U, act_W, zero_add, ha, hb, hout] using h
  commutator_WV i j a b hij := by
    obtain ⟨n, ha, hb⟩ := table_WV_output i j hij a b
    have hout : wtV i n = a+b := by dsimp [wtV, wtW] at *; omega
    have h := congrArg (D.act n) (D.WVout i j hij)
    simpa only [map_commutatorElement, act_V, act_W, zero_add, ha, hb, hout] using h
end CovariantData

namespace SeedData
variable {G : Type*} [Group G] (D : SeedData G)

def toCovariant : CovariantData G where
  T := D.T
  U i r := orbit (D.T i) (D.u i) (-r)
  V i r := orbit (D.T i) (D.v i) r
  W i j r := orbit (D.T i) (D.w i j) r
  TT := D.TT
  TU l i a := by
    rw [orbit_covariance _ _ _ (D.TT l i) _ (D.Tu l i)]
    congr 1
    omega
  TV l i a := orbit_covariance _ _ _ (D.TT l i) _ (D.Tv l i) a
  TW l i j a := by
    rw [orbit_covariance _ _ _ (D.TT l i) _ (D.Tw l i j)]
    congr 1
    omega
  diagonal i a := by simp [orbit, D.diagonal]
  square i := by simpa using D.square i
  UU i j h := by simpa using D.UU i j h
  VV i j h := by simpa using D.VV i j h
  UV i j h := by simpa using D.UV i j h
  WU i j h hh := by simpa using D.WU i j h hh
  WV i j h hh := by simpa using D.WV i j h hh
  UWout i j h := by simpa using D.UWout i j h
  WVout i j h := by simpa using D.WVout i j h

def toSelection : SelectionGroupData G := D.toCovariant.toSelection
end SeedData


instance instIsFinitelyPresentedModel : Group.IsFinitelyPresented Model := inferInstance

def modelSeedData : SeedData Model where
  toSeedValues := modelValues
  TT i j := by simpa [equation, Commute, SemiconjBy] using model_equation (.TT i j)
  Tu l i := model_equation (.Tu l i)
  Tv l i := model_equation (.Tv l i)
  Tw l i j := model_equation (.Tw l i j)
  diagonal i := model_equation (.diagonal i)
  square i := model_equation (.square i)
  UU i j h := by simpa [equation, h, Commute, SemiconjBy] using model_equation (.UU i j)
  VV i j h := by simpa [equation, h, Commute, SemiconjBy] using model_equation (.VV i j)
  UV i j h := by simpa [equation, h, Commute, SemiconjBy] using model_equation (.UV i j)
  WU i j h hh := by simpa [equation, hh, Commute, SemiconjBy] using model_equation (.WU i j h)
  WV i j h hh := by simpa [equation, hh, Commute, SemiconjBy] using model_equation (.WV i j h)
  UWout i j h := by simpa [equation, h] using model_equation (.UWout i j)
  WVout i j h := by simpa [equation, h] using model_equation (.WVout i j)

/-- The homomorphism from the supplied infinite presentation to the finite model. -/
def toModel : Presentation.AuxiliaryGroup →* Model :=
  Presentation.ofData modelSeedData.toSelection


theorem seed_equation {G : Type*} [Group G] (D : SeedData G) (r : Rule) :
    (equation D.toSeedValues r).1 = (equation D.toSeedValues r).2 := by
  cases r with
  | TT i j => exact (D.TT i j).eq
  | Tu l i => exact D.Tu l i
  | Tv l i => exact D.Tv l i
  | Tw l i j => exact D.Tw l i j
  | diagonal i => exact D.diagonal i
  | square i => exact D.square i
  | UU i j =>
      by_cases h : i≠j
      · simpa only [equation, ite_eq_left h] using (D.UU i j h).eq
      · simp [equation, h]
  | VV i j =>
      by_cases h : i≠j
      · simpa only [equation, ite_eq_left h] using (D.VV i j h).eq
      · simp [equation, h]
  | UV i j =>
      by_cases h : i≠j
      · simpa only [equation, ite_eq_left h] using (D.UV i j h).eq
      · simp [equation, h]
  | WU i j k =>
      by_cases h : k≠i
      · simpa only [equation, ite_eq_left h] using (D.WU i j k h).eq
      · simp [equation, h]
  | WV i j k =>
      by_cases h : k≠j
      · simpa only [equation, ite_eq_left h] using (D.WV i j k h).eq
      · simp [equation, h]
  | UWout i j => by_cases h : i≠j <;> simp [equation, h, (D.UWout i j)]
  | WVout i j => by_cases h : i≠j <;> simp [equation, h, (D.WVout i j)]

/-- Universal evaluation of the finite presentation in any proved seed data. -/
def modelLift {G : Type*} [Group G] (D : SeedData G) : Model →* G :=
  PresentedGroup.toGroup (f := evalSeeds D.toSeedValues) (by
    intro r hr
    obtain ⟨s,rfl⟩ := hr
    dsimp only [relator]
    rw [map_mul, map_inv, (equation_evaluate D.toSeedValues s).1,
      (equation_evaluate D.toSeedValues s).2, seed_equation D s, mul_inv_cancel])

@[simp] theorem modelLift_of {G : Type*} [Group G] (D : SeedData G) (s : SeedGenerator) :
    modelLift D (PresentedGroup.of s) = evalSeeds D.toSeedValues s := PresentedGroup.toGroup.of _

def fromModel : Model →* Presentation.AuxiliaryGroup :=
  modelLift (originalSeeds Presentation.data)


@[simp] theorem toModel_T (i : Fin 3) :
    toModel (Presentation.data.T i) = modelValues.T i :=
  Presentation.ofData_of modelSeedData.toSelection (.T i)
@[simp] theorem toModel_U (i : Fin 3) (a : ℤ) :
    toModel (Presentation.data.U i a) = orbit (modelValues.T i) (modelValues.u i) (-a) :=
  Presentation.ofData_of modelSeedData.toSelection (.U i a)
@[simp] theorem toModel_V (i : Fin 3) (a : ℤ) :
    toModel (Presentation.data.V i a) = orbit (modelValues.T i) (modelValues.v i) a :=
  Presentation.ofData_of modelSeedData.toSelection (.V i a)
@[simp] theorem toModel_W (i j : Fin 3) (a : ℤ) :
    toModel (Presentation.data.W i j a) = orbit (modelValues.T i) (modelValues.w i j) a :=
  Presentation.ofData_of modelSeedData.toSelection (.W i j a)

@[simp] theorem fromModel_T (i : Fin 3) :
    fromModel (modelValues.T i) = Presentation.data.T i :=
  modelLift_of (originalSeeds Presentation.data) (.T i)
@[simp] theorem fromModel_u (i : Fin 3) :
    fromModel (modelValues.u i) = Presentation.data.U i 0 :=
  modelLift_of (originalSeeds Presentation.data) (.U i)
@[simp] theorem fromModel_v (i : Fin 3) :
    fromModel (modelValues.v i) = Presentation.data.V i 0 :=
  modelLift_of (originalSeeds Presentation.data) (.V i)
@[simp] theorem fromModel_w (i j : Fin 3) :
    fromModel (modelValues.w i j) = Presentation.data.W i j 0 :=
  modelLift_of (originalSeeds Presentation.data) (.W i j)

theorem fromModel_toModel : fromModel.comp toModel = MonoidHom.id Presentation.AuxiliaryGroup := by
  apply PresentedGroup.ext
  intro s
  cases s with
  | T i =>
      change fromModel (toModel (Presentation.data.T i)) = Presentation.data.T i
      simp
  | U i a =>
      change fromModel (toModel (Presentation.data.U i a)) = Presentation.data.U i a
      simp
  | V i a =>
      change fromModel (toModel (Presentation.data.V i a)) = Presentation.data.V i a
      simp
  | W i j a =>
      change fromModel (toModel (Presentation.data.W i j a)) = Presentation.data.W i j a
      simp

theorem toModel_fromModel : toModel.comp fromModel = MonoidHom.id Model := by
  apply PresentedGroup.ext
  intro s
  cases s with
  | T i =>
      change toModel (fromModel (modelValues.T i)) = modelValues.T i
      simp
  | U i =>
      change toModel (fromModel (modelValues.u i)) = modelValues.u i
      simp
  | V i =>
      change toModel (fromModel (modelValues.v i)) = modelValues.v i
      simp
  | W i j =>
      change toModel (fromModel (modelValues.w i j)) = modelValues.w i j
      simp

/-- Equivalence of the explicit finite presentation and the supplied infinite presentation. -/
def presentationEquiv : Model ≃* Presentation.AuxiliaryGroup where
  toFun := fromModel
  invFun := toModel
  left_inv x := DFunLike.congr_fun toModel_fromModel x
  right_inv x := DFunLike.congr_fun fromModel_toModel x
  map_mul' := fromModel.map_mul

end LittleFinitistic.FinitePresentation

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Selection_AuxiliaryGroupAlgebraPresentation
attribute [-instance] _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
namespace LittleFinitistic.GroupAlgebraPresentation

/-- Same explicit presentation expressed as polynomial zero relations. -/
def auxiliaryGroupAlgebraZeroEquiv :
    (zeroRelations ℂ FinitePresentation.SeedGenerator FinitePresentation.finiteRelators).Quotient ≃ₐ[ℂ]
      MonoidAlgebra ℂ Presentation.AuxiliaryGroup :=
  (zeroQuotientEquiv ℂ FinitePresentation.SeedGenerator FinitePresentation.finiteRelators).trans
    (MonoidAlgebra.domCongr ℂ ℂ FinitePresentation.presentationEquiv)

end LittleFinitistic.GroupAlgebraPresentation

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Encoding_AuxiliaryQuadraticPresentation
attribute [-instance] _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instRing _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
namespace LittleFinitistic.QuadraticPresentation

abbrev AuxiliaryOldLetter := GroupAlgebraPresentation.Letter FinitePresentation.SeedGenerator
abbrev AuxiliaryOldEquation := GroupAlgebraPresentation.EquationIndex
  FinitePresentation.SeedGenerator FinitePresentation.finiteRelators

def auxiliaryOriginalRelation (i : AuxiliaryOldEquation) : FreeAlgebra ℂ AuxiliaryOldLetter :=
  GroupAlgebraPresentation.equation ℂ FinitePresentation.SeedGenerator
    FinitePresentation.finiteRelators i - 1

def auxiliaryWordBound : ℕ :=
  Classical.choose (exists_word_bound ℂ AuxiliaryOldLetter auxiliaryOriginalRelation)

theorem auxiliaryWordBound_spec (i : AuxiliaryOldEquation) (w : FreeMonoid AuxiliaryOldLetter)
    (hw : w ∈ (coefficients ℂ AuxiliaryOldLetter (auxiliaryOriginalRelation i)).support) :
    w.toList.length ≤ auxiliaryWordBound :=
  Classical.choose_spec (exists_word_bound ℂ AuxiliaryOldLetter auxiliaryOriginalRelation) i w hw

abbrev AuxiliaryLetter := Letter AuxiliaryOldLetter auxiliaryWordBound
abbrev AuxiliaryEquation := EquationIndex AuxiliaryOldLetter auxiliaryWordBound (κ := AuxiliaryOldEquation)

def auxiliaryRelation : AuxiliaryEquation → FreeAlgebra ℂ AuxiliaryLetter :=
  relation ℂ AuxiliaryOldLetter auxiliaryOriginalRelation auxiliaryWordBound

instance instFiniteAuxiliaryLetter : Finite AuxiliaryLetter := inferInstanceAs (Finite (Letter AuxiliaryOldLetter auxiliaryWordBound))
instance instFiniteAuxiliaryEquation : Finite AuxiliaryEquation := inferInstanceAs
  (Finite (EquationIndex AuxiliaryOldLetter auxiliaryWordBound (κ := AuxiliaryOldEquation)))

theorem auxiliaryRelation_degree (i : AuxiliaryEquation) :
    auxiliaryRelation i ∈ degreeLE ℂ AuxiliaryLetter 2 :=
  relation_degree ℂ AuxiliaryOldLetter auxiliaryOriginalRelation auxiliaryWordBound i

/-- Concrete quadratic quotient and actual algebra equivalence, retaining the
proved stable group's generators and relators and eliminating its word auxiliaries. -/
def auxiliaryQuadraticEquiv : Original ℂ AuxiliaryLetter auxiliaryRelation ≃ₐ[ℂ]
    MonoidAlgebra ℂ Presentation.AuxiliaryGroup :=
  (quadraticEquiv ℂ AuxiliaryOldLetter auxiliaryOriginalRelation auxiliaryWordBound
    auxiliaryWordBound_spec).trans GroupAlgebraPresentation.auxiliaryGroupAlgebraZeroEquiv

end LittleFinitistic.QuadraticPresentation

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Encoding_QuadraticCoefficients
attribute [-instance] _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instRing _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated
attribute [-simp] _root_.OAI.ExternalTensor.Section4.sum_hom _root_.OAI.LittleFinitistic.PresentationReindex.rename_word
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
namespace LittleFinitistic.QuadraticPresentation

variable (R : Type*) [CommRing R] (α : Type*)

/-- The degree bound is exactly the span of constants, generators, and ordered
products of two generators. The two factors are never commuted. -/
theorem degreeLE_two_eq_span :
    degreeLE R α 2 = Submodule.span R (Set.range (term R α)) := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro f ⟨w,hw,rfl⟩
    apply Submodule.subset_span
    cases w with
    | nil => exact ⟨.inl (), rfl⟩
    | cons a w =>
      cases w with
      | nil => exact ⟨.inr (.inl a), by simp [term, word]⟩
      | cons b w =>
        cases w with
        | nil => exact ⟨.inr (.inr (a,b)), by simp [term, word]⟩
        | cons c w => simp only [List.length_cons] at hw; omega
  · apply Submodule.span_le.mpr
    rintro f ⟨i,rfl⟩
    rcases i with u | (a | ⟨a,b⟩)
    · exact one_mem_degreeLE 2
    · exact generator_mem_degreeLE a
    · exact product_mem_degreeLE a b

theorem exists_coefficients [Fintype α] (p : FreeAlgebra R α)
    (h : p ∈ degreeLE R α 2) :
    ∃ (c : R) (l : α → R) (q : α → α → R), coefficientPolynomial R α c l q = p := by
  rw [degreeLE_two_eq_span] at h
  obtain ⟨f,hf⟩ := (Submodule.mem_span_range_iff_exists_fun R).mp h
  refine ⟨f (.inl ()), fun a => f (.inr (.inl a)),
    fun a b => f (.inr (.inr (a,b))), ?_⟩
  simpa [coefficientPolynomial, Fintype.sum_sum_type, Fintype.sum_prod_type,
    term, Algebra.smul_def, add_assoc] using hf

end LittleFinitistic.QuadraticPresentation

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Localization_QuotientAction
attribute [-instance] _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated
attribute [-simp] _root_.OAI.ExternalTensor.Section4.sum_hom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace LittleFinitistic.QuotientAction
open CategoryTheory CategoryTheory.Category CategoryTheory.Limits CategoryTheory.Preadditive
open QuadraticEncoding

variable {k : Type*} [Field k] {C : Type*} [Category C] [Preadditive C] [Linear k C]
variable {X₀ X₁ X₂ : C} {d t : ℕ} (P : Relations k d t)
  (s : X₀ ⟶ X₁) (s' : X₁ ⟶ X₂) [IsIso s] [IsIso s']
  (a : Fin d → (X₀ ⟶ X₁)) (b : Fin d → (X₁ ⟶ X₂))
  (hc : ∀ h, s ≫ b h = a h ≫ s')

variable (hr : ∀ j,
    (∑ h, ∑ l, P.quadratic j h l • (a l ≫ b h)) +
    (∑ h, P.linear j h • (a h ≫ s')) + P.constant j • (s ≫ s') = 0)

/-- The genuine quotient action theta, obtained by descending the free action. -/
noncomputable def quotientAction :
    QuadraticPresentation.Original k (Fin d) (polynomial P) →ₐ[k] End X₀ :=
  (QuadraticPresentation.original k (Fin d) (polynomial P)).liftₐ (freeAction s a)
    (RingCon.ringConGen_le.mpr (by
      rintro x y ⟨j,rfl,rfl⟩
      change freeAction s a (polynomial P j) = freeAction s a 0
      rw [map_zero,freeAction_polynomial P s s' a b hc hr]))

@[simp] theorem quotientAction_generator (h : Fin d) :
    quotientAction P s s' a b hc hr
      (QuadraticPresentation.originalMap k (Fin d) (polynomial P) (FreeAlgebra.ι k h)) =
      normalized s a h := by
  simp [quotientAction,QuadraticPresentation.originalMap,freeAction]

/-- Transport the descended action through the actual presentation equivalence. -/
noncomputable def presentedAction {R : Type*} [Ring R] [Algebra k R]
    (E : QuadraticPresentation.Original k (Fin d) (polynomial P) ≃ₐ[k] R) :
    R →ₐ[k] End X₀ := (quotientAction P s s' a b hc hr).comp E.symm.toAlgHom

omit [Preadditive C] in
/-- Evaluation of normalized generators, with the natural vertex identifications. -/
theorem normalized_evaluation {D : Type*} [Category D] (F : C ⥤ D)
    {Y : D} (e₀ : F.obj X₀ ≅ Y) (e₁ : F.obj X₁ ≅ Y)
    (x : Fin d → (Y ⟶ Y))
    (hs : F.map s ≫ e₁.hom = e₀.hom)
    (ha : ∀ h, F.map (a h) ≫ e₁.hom = e₀.hom ≫ x h) (h : Fin d) :
    F.map (normalized s a h) ≫ e₀.hom = e₀.hom ≫ x h := by
  have hsi : F.map (inv s) ≫ e₀.hom = e₁.hom := by
    apply (cancel_epi (F.map s)).mp
    rw [← assoc,← F.map_comp,IsIso.hom_inv_id,F.map_id,id_comp,hs]
  change F.map (a h ≫ inv s) ≫ e₀.hom = _
  rw [F.map_comp,assoc,hsi,ha]
end LittleFinitistic.QuotientAction

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Encoding_PresentationReindex
attribute [-instance] _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated
attribute [-simp] _root_.OAI.ExternalTensor.Section4.sum_hom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace LittleFinitistic.PresentationReindex
open QuadraticPresentation

variable {k : Type*} [Field k] {α β κ ι : Type*}

lemma rename_degree (e : α ≃ β) {p : FreeAlgebra k α} {n : ℕ}
    (hp : p ∈ degreeLE k α n) : rename e p ∈ degreeLE k β n := by
  induction hp using Submodule.span_induction with
  | mem x hx =>
    rcases hx with ⟨w,hw,rfl⟩
    simpa using word_mem_degreeLE (R := k) (w.map e) n (by simpa using hw)
  | zero => simp
  | add x y hx hy ihx ihy => simpa using (degreeLE k β n).add_mem ihx ihy
  | smul r x hx ih => simpa using (degreeLE k β n).smul_mem r ih

variable (e : α ≃ β) (j : κ ≃ ι) (p : κ → FreeAlgebra k α)

noncomputable def forward : Original k α p →ₐ[k] Original k β (renamedRelation e j p) :=
  (original k α p).liftₐ ((originalMap k β (renamedRelation e j p)).comp (rename e).toAlgHom)
    (RingCon.ringConGen_le.mpr (by
      rintro x y ⟨i,rfl,rfl⟩
      change originalMap k β (renamedRelation e j p) (rename e (p i)) = _
      have h := original_relation k β (renamedRelation e j p) (j i)
      simpa [renamedRelation] using h))

noncomputable def backward : Original k β (renamedRelation e j p) →ₐ[k] Original k α p :=
  (original k β (renamedRelation e j p)).liftₐ
    ((originalMap k α p).comp (rename e).symm.toAlgHom)
    (RingCon.ringConGen_le.mpr (by
      rintro x y ⟨i,rfl,rfl⟩
      change originalMap k α p ((rename e).symm (rename e (p (j.symm i)))) = _
      simpa only [AlgEquiv.symm_apply_apply,map_zero,AlgHom.comp_apply] using original_relation k α p (j.symm i)))

@[simp] theorem forward_mk (f : FreeAlgebra k α) :
    forward e j p (originalMap k α p f) =
      originalMap k β (renamedRelation e j p) (rename e f) := rfl

@[simp] theorem backward_mk (f : FreeAlgebra k β) :
    backward e j p (originalMap k β (renamedRelation e j p) f) =
      originalMap k α p ((rename e).symm f) := rfl

/-- Relabeling finite generators and relations preserves the actual presented algebra. -/
noncomputable def presentationEquiv : Original k α p ≃ₐ[k] Original k β (renamedRelation e j p) :=
  AlgEquiv.ofAlgHom (forward e j p) (backward e j p)
    (by
      apply AlgHom.ext
      intro x
      obtain ⟨f,rfl⟩ := (original k β (renamedRelation e j p)).mkₐ_surjective (α := k) x
      change forward e j p (backward e j p
        (originalMap k β (renamedRelation e j p) f)) = originalMap k β (renamedRelation e j p) f
      rw [backward_mk,forward_mk,AlgEquiv.apply_symm_apply])
    (by
      apply AlgHom.ext
      intro x
      obtain ⟨f,rfl⟩ := (original k α p).mkₐ_surjective (α := k) x
      change backward e j p (forward e j p (originalMap k α p f)) = originalMap k α p f
      rw [forward_mk,backward_mk,AlgEquiv.symm_apply_apply])

/-- Every finite list of quadratic polynomials has the concrete coefficient interface
used by the three-vertex algebra. -/
theorem exists_relations {d t : ℕ} (p : Fin t → FreeAlgebra k (Fin d))
    (hp : ∀ i, p i ∈ degreeLE k (Fin d) 2) :
    ∃ P : QuadraticEncoding.Relations k d t, ∀ i, QuotientAction.polynomial P i = p i := by
  classical
  choose c l q h using fun i => exists_coefficients k (Fin d) (p i) (hp i)
  refine ⟨⟨c,l,q⟩,?_⟩
  intro i
  rw [← h i]
  simp only [QuotientAction.polynomial,coefficientPolynomial,Algebra.algebraMap_eq_smul_one]
  abel

/-- Finite generator and equation types may both be replaced by Fin, and all
coefficient choices preserve the exact quotient algebra. -/
theorem finite_quadratic_encoding [Finite α] [Finite κ]
    (p : κ → FreeAlgebra k α) (hp : ∀ i, p i ∈ degreeLE k α 2) :
    ∃ (d t : ℕ) (P : QuadraticEncoding.Relations k d t),
      Nonempty (Original k (Fin d) (QuotientAction.polynomial P) ≃ₐ[k] Original k α p) := by
  classical
  let := Fintype.ofFinite α
  let := Fintype.ofFinite κ
  let e := Fintype.equivFin α
  let j := Fintype.equivFin κ
  let p' := renamedRelation e j p
  have hp' (i) : p' i ∈ degreeLE k (Fin (Fintype.card α)) 2 := rename_degree e (hp (j.symm i))
  obtain ⟨P,hP⟩ := exists_relations p' hp'
  refine ⟨Fintype.card α,Fintype.card κ,P,?_⟩
  have heq : QuotientAction.polynomial P = p' := funext hP
  rw [heq]
  exact ⟨(presentationEquiv e j p).symm⟩

/-- The entire actual complex group algebra feeds the finite directed encoding. -/
theorem auxiliaryGroupAlgebra_has_encoding :
    ∃ (d t : ℕ) (P : QuadraticEncoding.Relations ℂ d t),
      Nonempty (Original ℂ (Fin d) (QuotientAction.polynomial P) ≃ₐ[ℂ]
        MonoidAlgebra ℂ Presentation.AuxiliaryGroup) := by
  obtain ⟨d,t,P,⟨E⟩⟩ := finite_quadratic_encoding auxiliaryRelation auxiliaryRelation_degree
  exact ⟨d,t,P,⟨E.trans auxiliaryQuadraticEquiv⟩⟩

end LittleFinitistic.PresentationReindex

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Localization_BoundedQuotientEvaluation
attribute [-instance] _root_.OAI.DerivedBar.Multibar.patternModule _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.DerivedBar.termModule _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.BimoduleCoefficients.instAddCommGroupCarrierTensorProductMulOpposite _root_.OAI.LittleFinitistic.BimoduleCoefficients.instModuleCarrierTensorProductMulOpposite_1 _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open CategoryTheory CategoryTheory.Limits
namespace LittleFinitistic
open BalancedTensor FiniteProjectiveHomotopy IdempotentTensor
universe u v

namespace FiniteProjectiveHomotopy
variable {R : Type u} [Ring R]

lemma single_property (M : ModuleCat.{v} R) [Module.Finite R M] [Projective M] (n : ℤ) :
    ComplexProperty R ((HomologicalComplex.single _ (.up ℤ) n).obj M) := by
  constructor
  · exact ⟨n,n,fun i hi => HomologicalComplex.isZero_single_obj_X (.up ℤ) n M i (by omega)⟩
  · intro i
    by_cases h : i=n
    · subst i
      let e := HomologicalComplex.singleObjXSelf (.up ℤ) n M
      exact ⟨finite_of_iso R e.symm,Projective.of_iso e.symm inferInstance⟩
    · exact finite_projective_of_isZero R _
        (HomologicalComplex.isZero_single_obj_X (.up ℤ) n M i h)
end FiniteProjectiveHomotopy

end LittleFinitistic

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Localization_FormalSummandAction
attribute [-instance] _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open CategoryTheory CategoryTheory.Category CategoryTheory.Preadditive
open CategoryTheory.Idempotents CategoryTheory.Limits

namespace LittleFinitistic.FormalSummandAction

universe u v w
variable {k : Type w} [CommRing k]
variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear k C]

instance toKaroubiLinear : (toKaroubi C).Linear k where
  map_smul := by intros; rfl

end LittleFinitistic.FormalSummandAction

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Localization_TwoConeVerdier
attribute [-instance] _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open CategoryTheory Limits Pretriangulated Category
namespace LittleFinitistic.TwoConeVerdier

variable {C : Type*} [Category* C] [HasZeroObject C] [Preadditive C]
  [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive]
  [Pretriangulated C]

namespace ConePair
variable (T : ConePair C)

theorem first_cone_mem : T.S T.first.obj₃ := T.generators.le_triangEnvelope _ (Or.inl rfl)
theorem second_cone_mem : T.S T.second.obj₃ := T.generators.le_triangEnvelope _ (Or.inr rfl)

theorem first_mem : T.Sigma T.first.mor₁ :=
  ObjectProperty.trW.mk _ T.first_distinguished T.first_cone_mem

theorem second_mem : T.Sigma T.second.mor₁ :=
  ObjectProperty.trW.mk _ T.second_distinguished T.second_cone_mem

instance instIsIsoQMapQMor₁First : IsIso (T.q.map T.first.mor₁) := Localization.inverts _ _ _ T.first_mem
instance instIsIsoQMapQMor₁Second : IsIso (T.q.map T.second.mor₁) := Localization.inverts _ _ _ T.second_mem

/-- Exact minimality, including closure under retracts. -/
theorem thick_minimal (P : ObjectProperty C) [P.IsTriangulated] [P.IsStableUnderRetracts]
    (h₁ : P T.first.obj₃) (h₂ : P T.second.obj₃) : T.S ≤ P := by
  change T.generators.triangEnvelope ≤ P
  apply (ObjectProperty.triangEnvelope_le_iff T.generators (Q := P)).mpr
  intro X hX
  rcases hX with rfl | rfl <;> assumption

variable {D : Type*} [Category* D] [HasZeroObject D] [Preadditive D]
  [HasShift D ℤ] [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]

variable (F : C ⥤ D) [F.CommShift ℤ] [F.IsTriangulated]
  [IsIso (F.map T.first.mor₁)] [IsIso (F.map T.second.mor₁)]

/-- An exact functor inverting the two displayed arrows kills both
required generating cones, hence their entire thick closure. -/
theorem evaluation_kills : T.S ≤ F.kernel := by
  apply T.thick_minimal F.kernel
  · exact (F.mapTriangle.obj T.first).isZero₃_of_isIso₁
      (F.map_distinguished _ T.first_distinguished)
      (inferInstanceAs (IsIso (F.map T.first.mor₁)))
  · exact (F.mapTriangle.obj T.second).isZero₃_of_isIso₁
      (F.map_distinguished _ T.second_distinguished)
      (inferInstanceAs (IsIso (F.map T.second.mor₁)))

theorem evaluation_inverts : T.Sigma.IsInvertedBy F := by
  intro X Y f hf
  obtain ⟨Z,g,h,hU,hZ⟩ := hf
  exact ((F.mapTriangle.obj (Triangle.mk f g h)).isZero₃_iff_isIso₁
    (F.map_distinguished _ hU)).mp (T.evaluation_kills F _ hZ)

/-- The induced functor from the actual quotient. -/
def evaluation : T.Q ⥤ D := Localization.lift F (T.evaluation_inverts F) T.q

def evaluation_fac : T.q ⋙ T.evaluation F ≅ F :=
  Localization.fac F (T.evaluation_inverts F) T.q

end ConePair
end LittleFinitistic.TwoConeVerdier

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Selection_SelectionAlgebra
attribute [-instance] _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated
attribute [-simp] _root_.OAI.ExternalTensor.Section4.sum_hom _root_.OAI.LittleFinitistic.FinitePresentation.fromModel_T _root_.OAI.LittleFinitistic.FinitePresentation.fromModel_u _root_.OAI.LittleFinitistic.FinitePresentation.fromModel_v _root_.OAI.LittleFinitistic.FinitePresentation.fromModel_w _root_.OAI.LittleFinitistic.FinitePresentation.toModel_T _root_.OAI.LittleFinitistic.FinitePresentation.toModel_U _root_.OAI.LittleFinitistic.FinitePresentation.toModel_V _root_.OAI.LittleFinitistic.FinitePresentation.toModel_W
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
namespace LittleFinitistic

open MonoidAlgebra

abbrev SelectionRing := MonoidAlgebra ℂ Presentation.AuxiliaryGroup

noncomputable def algebraZ (q : ℤ) : SelectionRing := single (Presentation.z q) 1

@[simp] theorem algebraZ_square (q : ℤ) : algebraZ q * algebraZ q = 1 := by
  simp [algebraZ,single_mul_single,Presentation.z_involution]
  rfl

theorem algebraZ_central (q : ℤ) (a : SelectionRing) : Commute (algebraZ q) a :=
  MonoidAlgebra.single_commute (Presentation.z_central q) Commute.one_left a

noncomputable def selectionIdempotent (q : ℤ) : SelectionRing :=
  (1/2 : ℂ) • (1 + algebraZ q)

theorem selectionIdempotent_square (q : ℤ) :
    selectionIdempotent q * selectionIdempotent q = selectionIdempotent q := by
  have hz : (1 + algebraZ q)*(1 + algebraZ q) = (1+algebraZ q)+(1+algebraZ q) := by
    simp only [mul_add,add_mul,one_mul,mul_one,algebraZ_square]
    abel
  unfold selectionIdempotent
  rw [smul_mul_smul,hz,smul_add,← add_smul]
  norm_num

theorem selectionIdempotent_central (q : ℤ) (a : SelectionRing) :
    Commute (selectionIdempotent q) a := by
  show selectionIdempotent q * a = a * selectionIdempotent q
  unfold selectionIdempotent
  rw [smul_mul_assoc,mul_smul_comm]
  congr 1
  simp only [add_mul,mul_add,one_mul,mul_one,(algebraZ_central q a).eq]

noncomputable def selectionAutomorphism (k : ℤ) : SelectionRing ≃ₐ[ℂ] SelectionRing :=
  MonoidAlgebra.domCongr ℂ ℂ (Presentation.shiftAut k)

end LittleFinitistic

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

/-- Concrete finite coefficient data, with an exact presentation equivalence. -/
structure Encoding (k R : Type*) [Field k] [Ring R] [Algebra k R] where
  generators : ℕ
  equations : ℕ
  relations : Relations k generators equations
  equiv : Original k (Fin generators) (QuotientAction.polynomial relations) ≃ₐ[k] R

universe u v w
variable {k : Type u} {R : Type v} [Field k] [Ring R] [Algebra k R] (E : Encoding k R)

noncomputable def generator (h : Fin E.generators) : R :=
  E.equiv (originalMap k (Fin E.generators) (QuotientAction.polynomial E.relations)
    (FreeAlgebra.ι k h))

/-- These concrete elements of R satisfy every coefficient equation. -/
theorem generator_relations (j : Fin E.equations) :
    (∑ h, ∑ l, E.relations.quadratic j h l • (generator E h * generator E l)) +
    (∑ h, E.relations.linear j h • generator E h) + E.relations.constant j • (1 : R) = 0 := by
  have h := congrArg E.equiv (original_relation k (Fin E.generators)
    (QuotientAction.polynomial E.relations) j)
  simpa only [QuotientAction.polynomial,map_add,map_sum,map_smul,map_mul,map_one,map_zero,generator]
    using h

/-- The actual Section 2 selecting algebra has one fixed concrete finite encoding. -/
noncomputable def auxiliaryEncoding : Encoding ℂ SelectionRing :=
  Classical.choice (by
    obtain ⟨d,t,P,⟨E⟩⟩ := PresentationReindex.auxiliaryGroupAlgebra_has_encoding
    exact ⟨⟨d,t,P,E⟩⟩)
end LittleFinitistic.SelectionEncoding

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Localization_VerdierEvaluationExact
attribute [-instance] _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open CategoryTheory Limits
namespace LittleFinitistic.TwoConeVerdier.ConePair
variable {C : Type*} [Category* C] [HasZeroObject C] [Preadditive C]
  [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive]
  [Pretriangulated C] [IsTriangulated C]
variable (T : ConePair C)
variable {D : Type*} [Category* D] [HasZeroObject D] [Preadditive D]
  [HasShift D ℤ] [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]
variable (F : C ⥤ D) [F.CommShift ℤ] [F.IsTriangulated]
  [IsIso (F.map T.first.mor₁)] [IsIso (F.map T.second.mor₁)]

instance evaluationLift : Localization.Lifting T.q T.Sigma F (T.evaluation F) := by
  unfold evaluation
  infer_instance

instance evaluationShift : (T.evaluation F).CommShift ℤ :=
  Functor.commShiftOfLocalization T.q T.Sigma ℤ F (T.evaluation F)

end LittleFinitistic.TwoConeVerdier.ConePair

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Localization_SourceActionEvaluation
attribute [-instance] _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open CategoryTheory
attribute [local instance] HasDerivedCategory.standard
namespace LittleFinitistic.SourceActionEvaluation
open QuadraticEncoding SelectionEncoding QuadraticPresentation
universe u v w
variable {k : Type u} [Field k] {R : Type w} [Ring R] [Algebra k R]
variable (E : Encoding k R)
variable {Y : Type v} [AddCommGroup Y] [Module k Y] [FiniteDimensional k Y]
  [Module R Y] [IsScalarTower k R Y]

def given (_E : Encoding k R) : R →ₐ[k] End ((vectorStalk (k := k)).obj (ModuleCat.of k (ULift.{u} Y))) :=
  (identifiedEndHom (vectorStalk (k := k)) _ (Iso.refl _)).comp
    ((liftedEndHom (k := k) (Y := Y)).comp (Algebra.lsmul k k Y))

end LittleFinitistic.SourceActionEvaluation

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Localization_SourceImageEvaluation
attribute [-instance] _root_.OAI.DerivedBar.Multibar.patternModule _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.DerivedBar.termModule _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.BimoduleCoefficients.instModuleCarrierTensorProductMulOpposite_1 _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.SelectedTargetHomology.instAdditiveFullSubcategoryDerivedCategoryModuleCatComplexEssImageKDerivedEmbeddingCCohomology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open CategoryTheory CategoryTheory.Idempotents
attribute [local instance] HasDerivedCategory.standard
namespace LittleFinitistic.SourceImageEvaluation

open QuadraticEncoding FiniteProjectiveHomotopy
universe u v w
variable {k : Type u} [Field k] {R : Type w} [Ring R] [Algebra k R]
variable (E : SelectionEncoding.Encoding k R)
variable {Y : Type v} [AddCommGroup Y] [Module k Y] [FiniteDimensional k Y]
  [Module R Y] [IsScalarTower k R Y]

def imageK (e : R) : K.{u,max u v} k :=
  ⟨(vectorStalk (k := k)).obj (ModuleCat.of k (imageSpace (k := k) (Y := Y) e)),
    single_property _ 0⟩
def imageDerived (e : R) : FiniteVectorDerived.{u,v} (k := k) :=
  (derivedEmbedding k).toEssImage.obj (imageK (k := k) (Y := Y) e)

end LittleFinitistic.SourceImageEvaluation

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Localization_SourceCornerEvaluation
attribute [-instance] _root_.OAI.DerivedBar.Multibar.patternModule _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.DerivedBar.termModule _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.BimoduleCoefficients.instModuleCarrierTensorProductMulOpposite_1 _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.SelectedTargetHomology.instAdditiveFullSubcategoryDerivedCategoryModuleCatComplexEssImageKDerivedEmbeddingCCohomology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open CategoryTheory CategoryTheory.Idempotents
attribute [local instance] HasDerivedCategory.standard
namespace LittleFinitistic.SourceImageEvaluation

open QuadraticEncoding
universe u v w
variable {k : Type u} [Field k] {R : Type w} [Ring R] [Algebra k R]
variable (E : SelectionEncoding.Encoding k R)
variable {Y : Type v} [AddCommGroup Y] [Module k Y] [FiniteDimensional k Y]
  [Module R Y] [IsScalarTower k R Y]

def imageCorner (e a : R) : imageDerived (k := k) (Y := Y) e ⟶ imageDerived (k := k) (Y := Y) e :=
  (derivedTargetInclusion (k := k)).preimage (DerivedCategory.Qh.map
    ((vectorStalk (k := k)).map (imageCornerEnd (action (k := k) (Y := Y) e).hom (action (k := k) (Y := Y) a).hom)))

end LittleFinitistic.SourceImageEvaluation

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Ordinary_OrdinarySupportedExtension
attribute [-instance] _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated
attribute [-simp] _root_.OAI.ExternalTensor.Section4.sum_hom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
attribute [local instance] Classical.propDecidable
open CategoryTheory Limits
namespace LittleFinitistic.OrdinarySimulation.SupportedExtension
universe u v w w'
variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C] [HasZeroObject C]
variable {I : Type w} {J : Type w'} {c : ComplexShape I} {c' : ComplexShape J}
variable (K : HomologicalComplex C c') (e : c.Embedding c') [e.IsRelIff] [K.IsStrictlySupported e]

theorem component_at (i : I) : component K e (e.f i) = K.stupidTruncXIso e rfl := by
  unfold component
  rw [dite_eq_left (show ∃ j, e.f j = e.f i from ⟨i,rfl⟩)]
  exact component_iso_unique K e _ _

/-- An actual chain isomorphism, with support supplied by proved zero objects. -/
def iso : K.stupidTrunc e ≅ K :=
  HomologicalComplex.Hom.isoOfComponents (component K e) (by
    intro i' j' _
    by_cases hi : ∃ i, e.f i = i'
    · obtain ⟨i,rfl⟩ := hi
      by_cases hj : ∃ j, e.f j = j'
      · obtain ⟨j,rfl⟩ := hj
        rw [component_at,component_at]
        change (((K.restriction e).extendXIso e rfl).hom ≫ 𝟙 _) ≫ K.d (e.f i) (e.f j) =
          ((K.restriction e).extend e).d (e.f i) (e.f j) ≫
            (((K.restriction e).extendXIso e rfl).hom ≫ 𝟙 _)
        rw [Category.comp_id, Category.comp_id]
        rw [HomologicalComplex.extend_d_eq _ _ rfl rfl]
        simp only [Category.assoc,Iso.inv_hom_id,Category.comp_id]
        rfl
      · exact IsZero.eq_of_tgt (K.isZero_X_of_isStrictlySupported e j' (by simpa using hj)) _ _
    · exact IsZero.eq_of_src (K.isZero_stupidTrunc_X e i' (by simpa using hi)) _ _)
end LittleFinitistic.OrdinarySimulation.SupportedExtension

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Ordinary_OrdinaryFunctorExtension
attribute [-instance] _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open CategoryTheory Limits
namespace LittleFinitistic.FunctorExtension
universe u v u' v' w w'
variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C] [HasZeroObject C]
variable {D : Type u'} [Category.{v'} D] [HasZeroMorphisms D] [HasZeroObject D]
variable (F : C ⥤ D) [F.PreservesZeroMorphisms]
variable {I : Type w} {J : Type w'} {c : ComplexShape I} {c' : ComplexShape J}
variable (K : HomologicalComplex C c) (e : c.Embedding c') [e.IsRelIff]

/-- An actual chain isomorphism commuting a zero-preserving functor with extension by zero. -/
def iso : (F.mapHomologicalComplex c').obj (K.extend e) ≅
    ((F.mapHomologicalComplex c).obj K).extend e := by
  letI := mappedSupport F K e
  exact (OrdinarySimulation.SupportedExtension.iso ((F.mapHomologicalComplex c').obj (K.extend e)) e).symm ≪≫
    (e.extendFunctor D).mapIso (restrictionIso F K e)
end LittleFinitistic.FunctorExtension

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Ordinary_OrdinaryOffDiagonalComplex
attribute [-instance] _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instRing _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open CategoryTheory
open scoped TensorProduct
namespace LittleFinitistic.OrdinarySimulation.OffDiagonal
universe u
variable (k L R : Type u) [Field k] [Ring L] [Ring R] [Algebra k L] [Algebra k R]
variable (O : CochainComplex (ModuleCat.{u} (R ⊗[k] Lᵐᵒᵖ)) ℤ)
variable (T : CochainComplex (ModuleCat.{u} (L ⊗[k] Rᵐᵒᵖ)) ℤ)

abbrev complexTerm (n : ℤ) := RetainedBimodule k (L × R) (L × R)
  (OffDiagonal (BimoduleCoefficients k R L (O.X n)) (BimoduleCoefficients k L R (T.X n)))

end LittleFinitistic.OrdinarySimulation.OffDiagonal

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Ordinary_OrdinaryOffDiagonalObjects
attribute [-instance] _root_.OAI.DerivedBar.Multibar.patternModule _root_.OAI.DerivedBar.Multibar.patternTower _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.DerivedBar.termModule _root_.OAI.DerivedBar.termTower _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.ExternalTensor.Section4.rightModuleTower _root_.OAI.LittleFinitistic.BalancedTensor.scalarLeftTower _root_.OAI.LittleFinitistic.BalancedTensor.scalarModuleTower _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.PDTensor.scalarModuleTower _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.TensorComplex.scalarTower _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instAddCommGroup _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instRing _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open CategoryTheory Limits
open scoped TensorProduct
namespace LittleFinitistic.OrdinarySimulation.OffDiagonal
universe u
variable (k L R : Type u) [Field k] [Ring L] [Ring R] [Algebra k L] [Algebra k R]
variable (O : ModuleCat.{u} (R ⊗[k] Lᵐᵒᵖ)) (T : ModuleCat.{u} (L ⊗[k] Rᵐᵒᵖ))

abbrev object : ModuleCat.{u} ((L × R) ⊗[k] (L × R)ᵐᵒᵖ) :=
  RetainedBimodule.object k (L × R) (L × R)
    (OffDiagonal (BimoduleCoefficients k R L O) (BimoduleCoefficients k L R T))

end LittleFinitistic.OrdinarySimulation.OffDiagonal

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Ordinary_OrdinaryProductDimension
attribute [-instance] _root_.OAI.DerivedBar.Multibar.patternModule _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.DerivedBar.termModule _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.BimoduleCoefficients.instAddCommGroupCarrierTensorProductMulOpposite _root_.OAI.LittleFinitistic.BimoduleCoefficients.instModuleCarrierTensorProductMulOpposite_1 _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.BlockModule.derivedFirstIso_hom_commShift _root_.OAI.LittleFinitistic.BlockModule.derivedFirstIso_inv_commShift _root_.OAI.LittleFinitistic.BlockModule.firstInflation_preservesFiniteColimits _root_.OAI.LittleFinitistic.BlockModule.firstInflation_preservesFiniteLimits _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instAddCommGroup _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instRing _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open CategoryTheory
namespace LittleFinitistic.ProductModules
universe u v
variable (L R : Type u) [Ring L] [Ring R] [Small.{v} L] [Small.{v} R]

omit [Small.{v} L] [Small.{v} R] in
/-- Exactness of actual inflation, with the module universe independent of the ring universe. -/
theorem firstInflation_preservesHomology :
    (firstInflation.{u,v} L R).PreservesHomology :=
  CategoryTheory.Functor.preservesHomology_of_map_exact _ (fun K hK => by
    rw [ShortComplex.moduleCat_exact_iff] at hK ⊢
    exact hK)

end LittleFinitistic.ProductModules

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Ordinary_OrdinaryProductSecondDimension
attribute [-instance] _root_.OAI.DerivedBar.Multibar.patternModule _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.DerivedBar.termModule _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.BimoduleCoefficients.instAddCommGroupCarrierTensorProductMulOpposite _root_.OAI.LittleFinitistic.BimoduleCoefficients.instModuleCarrierTensorProductMulOpposite_1 _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.BlockModule.derivedFirstIso_hom_commShift _root_.OAI.LittleFinitistic.BlockModule.derivedFirstIso_inv_commShift _root_.OAI.LittleFinitistic.BlockModule.firstInflation_preservesFiniteColimits _root_.OAI.LittleFinitistic.BlockModule.firstInflation_preservesFiniteLimits _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instAddCommGroup _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instRing _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open CategoryTheory
namespace LittleFinitistic.ProductModules
universe u v
variable (L R : Type u) [Ring L] [Ring R]

attribute [local instance] RingHomInvPair.of_ringEquiv

/-- Swapping product factors identifies the two actual inflation constructions. -/
def swapInflationEquiv (P : ModuleCat.{v} R) :
    (firstInflation R L).obj P ≃ₛₗ[RingHomClass.toRingHom (RingEquiv.prodComm : R × L ≃+* L × R)]
      (secondInflation L R).obj P where
  toFun x := x
  invFun x := x
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

end LittleFinitistic.ProductModules

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Ordinary_OrdinaryOffDiagonalProjective
attribute [-instance] _root_.OAI.DerivedBar.Multibar.patternModule _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.DerivedBar.termModule _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.BlockModule.derivedFirstIso_hom_commShift _root_.OAI.LittleFinitistic.BlockModule.derivedFirstIso_inv_commShift _root_.OAI.LittleFinitistic.BlockModule.firstInflation_preservesFiniteColimits _root_.OAI.LittleFinitistic.BlockModule.firstInflation_preservesFiniteLimits _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instAddCommGroup _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instRing _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open CategoryTheory
namespace LittleFinitistic.OrdinarySimulation.OffDiagonal
universe u
variable (L R O T : Type u) [Ring L] [Ring R]
variable [AddCommGroup O] [AddCommGroup T] [Module Lᵐᵒᵖ O] [Module Rᵐᵒᵖ T]
open ProductModules

abbrev inflatedPair : ModuleCat.{u} (Lᵐᵒᵖ × Rᵐᵒᵖ) := ModuleCat.of _
  (((firstInflation Lᵐᵒᵖ Rᵐᵒᵖ).obj (ModuleCat.of Lᵐᵒᵖ O)) ×
    ((secondInflation Lᵐᵒᵖ Rᵐᵒᵖ).obj (ModuleCat.of Rᵐᵒᵖ T)))

attribute [local instance] RingHomInvPair.of_ringEquiv

def rightPairEquiv : OffDiagonal O T ≃ₛₗ[RingHomClass.toRingHom (oppositeEquiv L R)]
    inflatedPair L R O T where
  toFun x := x
  invFun x := x
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

end LittleFinitistic.OrdinarySimulation.OffDiagonal

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Ordinary_OrdinaryTensorDirected
attribute [-instance] _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open scoped TensorProduct
namespace LittleFinitistic.OrdinarySimulation.TensorDirected
universe u
variable {k B C : Type u} [Field k] [Ring B] [Ring C] [Algebra k B] [Algebra k C]
variable {n : ℕ} (DB : DirectedBound.DirectedSystem k B 3) (DC : DirectedBound.DirectedSystem k C n)

def vertex (i : Fin (n*3)) : B ⊗[k] C := DB.e (bIndex i) ⊗ₜ[k] DC.e (cIndex i)

end LittleFinitistic.OrdinarySimulation.TensorDirected

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Rectification_VertexHomology
attribute [-instance] _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instAddCommGroup _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instRing _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated
attribute [-simp] _root_.OAI.ExternalTensor.Section4.sum_hom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open CategoryTheory HomologicalComplex
namespace LittleFinitistic.VertexHomology
universe u
variable {A B : Type u} [Ring A] [Ring B]
variable (β : B →+* A) (e : A) (he : e*e=e) (hc : ∀ b, e*β b=β b*e)

include he

/-- Actual vertex projection preserves homology, because it preserves the
short exact sequences already proved in VertexFunctor. -/
theorem preservesHomology : (VertexFunctor.functor β e hc).PreservesHomology :=
  ((Functor.exact_tfae (VertexFunctor.functor β e hc)).out (1-1) (3-1)).1
    (VertexFunctor.map_shortExact β e he hc)

/-- Homology of the actual vertex complex is the actual vertex of module homology. -/
def iso (X : CochainComplex (ModuleCat.{u} A) ℤ) (n : ℤ) :
    (((VertexFunctor.functor β e hc).mapHomologicalComplex (.up ℤ)).obj X).homology n ≅
      (VertexFunctor.functor β e hc).obj (X.homology n) := by
  letI := preservesHomology β e he hc
  exact (X.sc n).mapHomologyIso (VertexFunctor.functor β e hc)

/-- This comparison respects every natural transformation of the vertex functors,
so it retains the algebra arrow actions as well as the vertex vector spaces. -/
theorem natural (e' : A) (he' : e'*e'=e') (hc' : ∀ b, e'*β b=β b*e')
    (τ : VertexFunctor.functor β e hc ⟶ VertexFunctor.functor β e' hc')
    (X : CochainComplex (ModuleCat.{u} A) ℤ) (n : ℤ) :
    homologyMap ((NatTrans.mapHomologicalComplex τ (.up ℤ)).app X) n ≫
      (iso β e' he' hc' X n).hom =
    (iso β e he hc X n).hom ≫ τ.app (X.homology n) := by
  let := preservesHomology β e he hc
  let := preservesHomology β e' he' hc'
  have h := ShortComplex.homologyMap_mapNatTrans (X.sc n) τ
  change homologyMap ((NatTrans.mapHomologicalComplex τ (.up ℤ)).app X) n =
    (iso β e he hc X n).hom ≫ τ.app (X.homology n) ≫
      (iso β e' he' hc' X n).inv at h
  rw [h]
  simp
end LittleFinitistic.VertexHomology

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Rectification_LeftVertexHomology
attribute [-instance] _root_.OAI.DerivedBar.Multibar.patternModule _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.DerivedBar.termModule _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.BimoduleCoefficients.instAddCommGroupCarrierTensorProductMulOpposite _root_.OAI.LittleFinitistic.BimoduleCoefficients.instModuleCarrierTensorProductMulOpposite_1 _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.ProductModules.firstModule _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instAddCommGroup _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instRing _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open CategoryTheory HomologicalComplex
namespace LittleFinitistic.LeftVertexHomology
universe u
variable (k B : Type u) [Field k] [Ring B] [Algebra k B]

/-- The actual left vertex functor from B-modules to k-vector spaces. -/
abbrev vertex (e : B) : ModuleCat.{u} B ⥤ ModuleCat.{u} k :=
  VertexFunctor.functor (algebraMap k B) e (scalar_commute k B e)

/-- Arrow action is a natural transformation between the actual vertex functors. -/
def arrow (ei ej a : B) (ha : ej*a=a) : vertex k B ei ⟶ vertex k B ej where
  app M := ModuleCat.ofHom {
    toFun := fun x => ⟨a • (x.val : M), by
      rw [VertexFunctor.mem_fixed]
      rw [← mul_smul, ha]⟩
    map_add' := fun x y => Subtype.ext (smul_add _ _ _)
    map_smul' := fun c x => by
      apply Subtype.ext
      change a • (algebraMap k B c • (x.val : M)) =
        algebraMap k B c • (a • (x.val : M))
      rw [← mul_smul, ← mul_smul, scalar_commute] }
  naturality M M' f := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    exact (f.hom.map_smul a x.val).symm

/-- Cohomology comparison retains the original arrow action, not only dimensions. -/
theorem arrow_homology (ei ej a : B) (hi : ei*ei=ei) (hj : ej*ej=ej) (ha : ej*a=a)
    (X : CochainComplex (ModuleCat.{u} B) ℤ) (n : ℤ) :
    homologyMap ((NatTrans.mapHomologicalComplex (arrow k B ei ej a ha) (.up ℤ)).app X) n ≫
      (VertexHomology.iso (algebraMap k B) ej hj (scalar_commute k B ej) X n).hom =
    (VertexHomology.iso (algebraMap k B) ei hi (scalar_commute k B ei) X n).hom ≫
      (arrow k B ei ej a ha).app (X.homology n) :=
  VertexHomology.natural (algebraMap k B) ei hi (scalar_commute k B ei)
    ej hj (scalar_commute k B ej) _ X n
end LittleFinitistic.LeftVertexHomology

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Rectification_TotalInterchange
attribute [-instance] _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instAddCommGroup _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instRing _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated
attribute [-simp] _root_.OAI.ExternalTensor.Section4.sum_hom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

set_option backward.isDefEq.respectTransparency false

namespace OAI
open CategoryTheory CategoryTheory.Limits HomologicalComplex CochainComplex
open CochainComplex.HomComplex
noncomputable section
namespace LittleFinitistic.RectificationTotal
variable {C D : Type*} [Category C] [Preadditive C] [HasBinaryBiproducts C]
  [Category D] [Preadditive D] [HasBinaryBiproducts D]
variable (F : C ⥤ D) [F.Additive]

variable {A B A' B' : CochainComplex C ℤ}

variable {L₀ L₁ L₂ : CochainComplex C ℤ}
variable (p : L₁ ⟶ L₀) (q : L₂ ⟶ L₁) (h : Homotopy (q ≫ p) 0)

/-- Mapping the rectifying map agrees with rectifying the mapped data. -/
theorem rectifyingMap_interchange_inv :
    (coneInterchange F q).inv ≫ (mapComplex F).map (rectifyingMap p q h) =
      rectifyingMap ((mapComplex F).map p) ((mapComplex F).map q)
        (mapNullHomotopy F p q h) := by
  ext n
  apply mappingCone.ext_from ((mapComplex F).map q) (n+1) n rfl
  · simp only [comp_f, coneInterchange_inv_inl_assoc]
    dsimp only [mapComplex, Functor.mapHomologicalComplex_map_f]
    erw [← F.map_comp]
    simp [rectifyingMap, Cochain.ofHomotopy]
  · simp only [comp_f, coneInterchange_inv_inr_assoc]
    dsimp only [mapComplex, Functor.mapHomologicalComplex_map_f]
    erw [← F.map_comp]
    simp [rectifyingMap]

theorem rectifyingMap_interchange :
    (coneInterchange F q).hom ≫
      rectifyingMap ((mapComplex F).map p) ((mapComplex F).map q)
        (mapNullHomotopy F p q h) = (mapComplex F).map (rectifyingMap p q h) := by
  rw [← rectifyingMap_interchange_inv F p q h, ← Category.assoc]
  simp

/-- Arbitrary additive functors commute with the actual iterated-cone total. -/
def totalInterchange : (mapComplex F).obj (total p q h) ≅
    total ((mapComplex F).map p) ((mapComplex F).map q) (mapNullHomotopy F p q h) :=
  coneInterchange F (rectifyingMap p q h) ≪≫
    homotopyCofiber.mapArrowIso _ _ (fun j => ⟨j-1, by simp⟩)
      (Arrow.isoMk (coneInterchange F q) (Iso.refl _)
        (by simpa using rectifyingMap_interchange F p q h))

/-- The original zero-column inclusion is carried to the original inclusion. -/
@[reassoc]
theorem inclusion_totalInterchange :
    (mapComplex F).map (inclusion p q h) ≫ (totalInterchange F p q h).hom =
      inclusion ((mapComplex F).map p) ((mapComplex F).map q) (mapNullHomotopy F p q h) := by
  ext n
  change F.map ((mappingCone.inr (rectifyingMap p q h)).f n) ≫
    ((coneInterchange F (rectifyingMap p q h)).hom.f n ≫ _) = _
  rw [coneInterchange_hom_inr_assoc]
  change (mappingCone.inr _).f n ≫ (coneMap _ _ _ _ _).f n = _
  rw [coneMap_inr]
  simp [inclusion]
end LittleFinitistic.RectificationTotal

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Rectification_ZeroColumnTotal
attribute [-instance] _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instAddCommGroup _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instRing _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open CategoryTheory CategoryTheory.Limits CochainComplex HomologicalComplex
namespace LittleFinitistic.ZeroColumnTotal
variable {C D : Type*} [Category C] [Category D] [Preadditive C] [Preadditive D]
  [HasBinaryBiproducts C] [HasBinaryBiproducts D]

/-- Vanishing higher columns make the original zero-column inclusion an isomorphism. -/
theorem mapped_inclusion_isIso {L₀ L₁ L₂ : CochainComplex C ℤ}
    (p : L₁ ⟶ L₀) (q : L₂ ⟶ L₁) (h : Homotopy (q ≫ p) 0)
    (F : C ⥤ D) [F.Additive]
    (h₁ : ∀ i, IsZero (F.obj (L₁.X i))) (h₂ : ∀ i, IsZero (F.obj (L₂.X i))) :
    IsIso ((F.mapHomologicalComplex (.up ℤ)).map (RectificationTotal.inclusion p q h)) := by
  let t := RectificationTotal.rectifyingMap p q h
  change IsIso ((F.mapHomologicalComplex (.up ℤ)).map (mappingCone.inr t))
  rw [← isIso_comp_right_iff _ (mappingCone.mapHomologicalComplexIso t F).hom,
    mappingCone.map_inr]
  exact cone_inr_isIso _ (mappedCone_zero q F h₂ h₁)
end LittleFinitistic.ZeroColumnTotal

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Rectification_ZeroLastColumn
attribute [-instance] _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instAddCommGroup _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instRing _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated
attribute [-simp] _root_.OAI.ExternalTensor.Section4.sum_hom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open CategoryTheory CategoryTheory.Limits HomologicalComplex CochainComplex
namespace LittleFinitistic.ZeroLastColumn
open RectificationTotal
variable {C D : Type*} [Category C] [Category D] [Preadditive C] [Preadditive D]
  [HasBinaryBiproducts C] [HasBinaryBiproducts D]

def coneIso {X Y X' Y' : CochainComplex D ℤ} (p : X ⟶ Y) (p' : X' ⟶ Y')
    (a : X ≅ X') (b : Y ≅ Y') (w : a.hom ≫ p' = p ≫ b.hom) :
    mappingCone p ≅ mappingCone p' where
  hom := coneMap p p' a.hom b.hom w
  inv := coneMap p' p a.inv b.inv (by
    apply (cancel_epi a.hom).1
    simp only [← Category.assoc, Iso.hom_inv_id, Category.id_comp]
    rw [w, Category.assoc, Iso.hom_inv_id, Category.comp_id])
  hom_inv_id := by rw [← coneMap_comp]; simp
  inv_hom_id := by rw [← coneMap_comp]; simp

variable {L₀ L₁ L₂ : CochainComplex C ℤ}
variable (p : L₁ ⟶ L₀) (q : L₂ ⟶ L₁) (h : Homotopy (q ≫ p) 0)
variable (F : C ⥤ D) [F.Additive]

/-- Taking an additive image that kills the relation column leaves precisely the ordinary cone. -/
def mappedTotalIso (h₂ : IsZero ((F.mapHomologicalComplex (.up ℤ)).obj L₂)) :
    (F.mapHomologicalComplex (.up ℤ)).obj (total p q h) ≅
      mappingCone ((F.mapHomologicalComplex (.up ℤ)).map p) := by
  let G := F.mapHomologicalComplex (.up ℤ)
  have hi : IsIso (G.map (mappingCone.inr q)) := by
    rw [← isIso_comp_right_iff _ (mappingCone.mapHomologicalComplexIso q F).hom,
      mappingCone.map_inr]
    exact ZeroColumnTotal.cone_inr_isIso _ h₂
  letI := hi
  refine mappingCone.mapHomologicalComplexIso (rectifyingMap p q h) F ≪≫
    (coneIso (G.map p) (G.map (rectifyingMap p q h))
      (asIso (G.map (mappingCone.inr q))) (Iso.refl _) ?_).symm
  simp only [asIso_hom,Iso.refl_hom,Category.comp_id,← Functor.map_comp]
  congr 1
  simp [rectifyingMap]
end LittleFinitistic.ZeroLastColumn

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Selected_SelectedFixedDiagram
attribute [-instance] _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open CategoryTheory CategoryTheory.Limits CategoryTheory.Idempotents
namespace LittleFinitistic.SelectedFixedDiagram
open SelectionEncoding RelationBasisAction FormalSummandAction

abbrev encoding := auxiliaryEncoding
abbrev e := selectionIdempotent 0
abbrev alpha := (selectionAutomorphism 1).toAlgHom
lemma idem : e*e=e := selectionIdempotent_square 0
lemma central (r : SelectionRing) : e*r=r*e := (selectionIdempotent_central 0 r).eq

end LittleFinitistic.SelectedFixedDiagram

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Selection_FiniteQuotient
attribute [-instance] _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticPresentation.instFiniteAuxiliaryEquation _root_.OAI.LittleFinitistic.QuadraticPresentation.instFiniteAuxiliaryLetter _root_.OAI.LittleFinitistic.QuadraticPresentation.step_finite _root_.OAI.LittleFinitistic.QuadraticPresentation.word_finite _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instAddCommGroup _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instRing _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated
attribute [-simp] _root_.OAI.ExternalTensor.Section4.sum_hom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
/-!
Exact prerequisites for Section 2 of v5s9.15.

These are the variable-coefficient elementary-matrix calculations in the
finite-quotient construction, over the actual rings F₂[t]/(t^m - 1).
They do not establish the paper's main homological theorem.
-/

open Matrix Polynomial

namespace LittleFinitistic

theorem cyclicPolynomial_monic (m : ℕ) (hm : m ≠ 0) :
    (cyclicPolynomial m).Monic := Polynomial.monic_X_pow_sub_C 1 hm

theorem cyclicPolynomial_degree (m : ℕ) :
    (cyclicPolynomial m).natDegree = m := Polynomial.natDegree_X_pow_sub_C

noncomputable def cyclicBasis (m : ℕ) (hm : m ≠ 0) :
    Module.Basis (Fin m) (ZMod 2) (CyclicRing m) :=
  ((AdjoinRoot.powerBasis' (cyclicPolynomial_monic m hm)).basis).reindex
    (finCongr (cyclicPolynomial_degree m))

theorem cyclicRing_finite (m : ℕ) (hm : m ≠ 0) : Finite (CyclicRing m) := by
  exact Finite.of_injective (cyclicBasis m hm).repr (cyclicBasis m hm).repr.injective

theorem cyclic_root_pow (m : ℕ) :
    AdjoinRoot.root (cyclicPolynomial m) ^ m = (1 : CyclicRing m) := by
  have h : AdjoinRoot.mk (cyclicPolynomial m) (X^m - C 1) = 0 :=
    AdjoinRoot.mk_eq_zero.mpr (dvd_refl _)
  rw [map_sub, map_pow, AdjoinRoot.mk_X, Polynomial.C_1, map_one] at h
  exact sub_eq_zero.mp h

theorem cyclic_root_isUnit (m : ℕ) (hm : 0 < m) :
    IsUnit (AdjoinRoot.root (cyclicPolynomial m)) := by
  exact IsUnit.of_pow_eq_one (cyclic_root_pow m) (Nat.ne_of_gt hm)

/-- The central coefficient embedding in the displayed 5-by-5 matrix model. -/
noncomputable def centralMatrix (m : ℕ) (c : Fin m → ZMod 2) :
    Matrix (Fin 5) (Fin 5) (CyclicRing m) :=
  transvection 0 4 (∑ i, c i • AdjoinRoot.root (cyclicPolynomial m) ^ (i : ℕ))

theorem centralMatrix_zero (m : ℕ) : centralMatrix m 0 = 1 := by
  simp [centralMatrix, transvection]

theorem centralMatrix_add (m : ℕ) (c d : Fin m → ZMod 2) :
    centralMatrix m (c + d) = centralMatrix m c * centralMatrix m d := by
  rw [centralMatrix, centralMatrix, centralMatrix,
    transvection_same 0 4 (by decide)]
  congr 1
  simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]

theorem centralMatrix_involution (m : ℕ) (c : Fin m → ZMod 2) :
    centralMatrix m c * centralMatrix m c = 1 := by
  rw [← centralMatrix_add]
  have h : c + c = 0 := by
    funext i
    exact CharTwo.add_self_eq_zero (c i)
  rw [h, centralMatrix_zero]

/-- This is the concrete copy of the elementary abelian 2-group used by the
paper's finite matrix quotient. Its realization as a quotient of the presented
group remains separate from the verified embedding below. -/
noncomputable def centralEmbedding (m : ℕ) :
    Multiplicative (Fin m → ZMod 2) →* (Matrix (Fin 5) (Fin 5) (CyclicRing m))ˣ where
  toFun c :=
    { val := centralMatrix m c.toAdd
      inv := centralMatrix m c.toAdd
      val_inv := centralMatrix_involution m c.toAdd
      inv_val := centralMatrix_involution m c.toAdd }
  map_one' := by
    apply Units.ext
    exact centralMatrix_zero m
  map_mul' c d := by
    apply Units.ext
    exact centralMatrix_add m c.toAdd d.toAdd

end LittleFinitistic

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Selection_MatrixModel
attribute [-instance] _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticPresentation.instFiniteAuxiliaryEquation _root_.OAI.LittleFinitistic.QuadraticPresentation.instFiniteAuxiliaryLetter _root_.OAI.LittleFinitistic.QuadraticPresentation.step_finite _root_.OAI.LittleFinitistic.QuadraticPresentation.word_finite _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instRing _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated
attribute [-simp] _root_.OAI.ExternalTensor.Section4.sum_hom _root_.OAI.LittleFinitistic.FinitePresentation.fromModel_T _root_.OAI.LittleFinitistic.FinitePresentation.fromModel_u _root_.OAI.LittleFinitistic.FinitePresentation.fromModel_v _root_.OAI.LittleFinitistic.FinitePresentation.fromModel_w _root_.OAI.LittleFinitistic.FinitePresentation.toModel_T _root_.OAI.LittleFinitistic.FinitePresentation.toModel_U _root_.OAI.LittleFinitistic.FinitePresentation.toModel_V _root_.OAI.LittleFinitistic.FinitePresentation.toModel_W _root_.OAI.LittleFinitistic.algebraZ_square
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
open scoped commutatorElement

namespace LittleFinitistic

section MatrixRepresentation

variable {R : Type*} [CommRing R]


theorem matrix_UW_commutator (r : Rˣ) (i j : Fin 3) (a b : ℤ) (hij : i≠j) :
    ⁅matrixU r i a,matrixW r i j b⁆ = matrixU r j (a+b) := by
  unfold matrixW matrixU
  rw [dite_eq_right hij]
  simpa only [zpow_add,Units.val_mul] using
    transvectionUnit_commutator (R := R) 0 (internalIndex i) (internalIndex j)
      (Ne.symm (internalIndex_ne_zero i)) (by simpa using hij)
      (Ne.symm (internalIndex_ne_zero j)) (↑(r^a) : R) (↑(r^b) : R)

theorem matrix_WV_commutator (r : Rˣ) (i j : Fin 3) (a b : ℤ) (hij : i≠j) :
    ⁅matrixW r i j a,matrixV r j b⁆ = matrixV r i (a+b) := by
  unfold matrixW matrixV
  rw [dite_eq_right hij]
  simpa only [zpow_add,Units.val_mul] using
    transvectionUnit_commutator (R := R) (internalIndex i) (internalIndex j) 4
      (by simpa using hij) (internalIndex_ne_four j)
      (internalIndex_ne_four i) (↑(r^a) : R) (↑(r^b) : R)

theorem matrix_TW_conjugation (r : Rˣ) (l i j : Fin 3) (a : ℤ) :
    matrixT r l * matrixW r i j a * (matrixT r l)⁻¹ =
      matrixW r i j (a+(if l=i then 1 else 0)-if l=j then 1 else 0) := by
  by_cases hij : i=j
  · subst j
    simp [matrix_W_diagonal]
  · simp only [matrixW,dite_eq_right hij,matrixT]
    rw [transvectionUnit_conjugation]
    by_cases hli : l=i <;> by_cases hlj : l=j
    · exact False.elim (hij (hli.symm.trans hlj))
    · subst l
      have hji : internalIndex j ≠ internalIndex i := by simpa using Ne.symm hij
      simp [hji,hlj,zpow_add,mul_comm]
    · subst l
      have hij' : internalIndex i ≠ internalIndex j := by simpa using hij
      simp [hij',hli,zpow_sub]
    · have hi : internalIndex i ≠ internalIndex l := by simpa using Ne.symm hli
      have hj : internalIndex j ≠ internalIndex l := by simpa using Ne.symm hlj
      simp [hi,hj,hli,hlj]

def matrixData [CharP R 2] (r : Rˣ) : SelectionGroupData (Matrix (Fin 5) (Fin 5) R)ˣ where
  T := matrixT r
  U := matrixU r
  V := matrixV r
  W := matrixW r
  square_U := matrixU_square r
  commute_UU i j a b _ := matrix_UU_commute r i j a b
  commute_VV i j a b _ := matrix_VV_commute r i j a b
  commute_UV := matrix_UV_commute r
  commute_WU := matrix_WU_commute r
  commute_WV := matrix_WV_commute r
  commutator_UW := matrix_UW_commutator r
  commutator_WV := matrix_WV_commutator r
  commute_TT := matrix_TT_commute r
  conj_TU := matrix_TU_conjugation r
  conj_TV := matrix_TV_conjugation r
  conj_TW := matrix_TW_conjugation r
  diagonal_W := matrix_W_diagonal r

def matrixRepresentation [CharP R 2] (r : Rˣ) : Presentation.AuxiliaryGroup →*
    (Matrix (Fin 5) (Fin 5) R)ˣ := Presentation.ofData (matrixData r)

theorem matrixRepresentation_z [CharP R 2] (r : Rˣ) (N : ℤ) :
    matrixRepresentation r (Presentation.z N) = transvectionUnit 0 4 (by decide) (↑(r^N) : R) := by
  change Presentation.ofData (matrixData r)
    ⁅PresentedGroup.of (Presentation.Generator.U 0 0),PresentedGroup.of (Presentation.Generator.V 0 N)⁆ = _
  rw [map_commutatorElement,Presentation.ofData_of,Presentation.ofData_of]
  change ⁅matrixU r 0 0,matrixV r 0 N⁆ = _
  unfold matrixU matrixV
  rw [transvectionUnit_commutator 0 (internalIndex 0) 4 _ _ (by decide)]
  simp only [zpow_zero,Units.val_one,one_mul]


end MatrixRepresentation

instance cyclicRing_nontrivial (m : ℕ) [NeZero m] : Nontrivial (CyclicRing m) := by
  let i : Fin m := ⟨0,Nat.pos_of_ne_zero (NeZero.ne m)⟩
  exact ⟨⟨cyclicBasis m (NeZero.ne m) i,0,(cyclicBasis m (NeZero.ne m)).ne_zero i⟩⟩

instance cyclicRing_finiteInst (m : ℕ) [NeZero m] : Finite (CyclicRing m) :=
  cyclicRing_finite m (NeZero.ne m)

instance cyclicRing_charTwo (m : ℕ) [NeZero m] : CharP (CyclicRing m) 2 :=
  charP_of_injective_algebraMap (algebraMap (ZMod 2) (CyclicRing m)).injective 2

noncomputable def cyclicUnit (m : ℕ) [NeZero m] : (CyclicRing m)ˣ :=
  (cyclic_root_isUnit m (Nat.pos_of_ne_zero (NeZero.ne m))).unit

@[simp] theorem cyclicUnit_val (m : ℕ) [NeZero m] :
    (cyclicUnit m : CyclicRing m) = AdjoinRoot.root (cyclicPolynomial m) :=
  IsUnit.unit_spec _

noncomputable def cyclicRepresentation (m : ℕ) [NeZero m] : Presentation.AuxiliaryGroup →*
    (Matrix (Fin 5) (Fin 5) (CyclicRing m))ˣ := matrixRepresentation (cyclicUnit m)

theorem cyclicRepresentation_z (m : ℕ) [NeZero m] (i : ℕ) :
    cyclicRepresentation m (Presentation.z i) = transvectionUnit 0 4 (by decide)
      (AdjoinRoot.root (cyclicPolynomial m)^i) := by
  unfold cyclicRepresentation
  rw [matrixRepresentation_z]
  simp only [zpow_natCast,Units.val_pow_eq_pow_val,cyclicUnit_val]

theorem centralEmbedding_basis (m : ℕ) [NeZero m] (i : Fin m) :
    centralEmbedding m (Multiplicative.ofAdd (Pi.single i 1)) =
      cyclicRepresentation m (Presentation.z i.val) := by
  rw [cyclicRepresentation_z]
  apply Units.ext
  change transvection (R := CyclicRing m) (0 : Fin 5) 4 (∑ j : Fin m, (Pi.single i (1 : ZMod 2) : Fin m → ZMod 2) j •
      AdjoinRoot.root (cyclicPolynomial m) ^ (j : ℕ)) = _
  simp [Pi.single_apply, transvectionUnit]

noncomputable abbrev FiniteQuotientGroup (m : ℕ) [NeZero m] := (cyclicRepresentation m).range

instance finiteQuotientGroup_finite (m : ℕ) [NeZero m] : Finite (FiniteQuotientGroup m) :=
  inferInstance

noncomputable def finiteQuotientMap (m : ℕ) [NeZero m] :
    Presentation.AuxiliaryGroup →* FiniteQuotientGroup m := (cyclicRepresentation m).rangeRestrict

theorem finiteQuotientMap_surjective (m : ℕ) [NeZero m] :
    Function.Surjective (finiteQuotientMap m) := (cyclicRepresentation m).rangeRestrict_surjective

theorem centralEmbedding_mem_center_map (m : ℕ) [NeZero m]
    (c : Fin m → ZMod 2) : centralEmbedding m (Multiplicative.ofAdd c) ∈
      (Subgroup.center Presentation.AuxiliaryGroup).map (cyclicRepresentation m) := by
  classical
  let S := (Subgroup.center Presentation.AuxiliaryGroup).map (cyclicRepresentation m)
  apply Pi.single_induction (fun c => centralEmbedding m (Multiplicative.ofAdd c) ∈ S) c
  · simp
  · intro f g hf hg
    change centralEmbedding m (Multiplicative.ofAdd f * Multiplicative.ofAdd g) ∈ S
    rw [map_mul]
    exact S.mul_mem hf hg
  · intro i a
    fin_cases a
    · change centralEmbedding m (Multiplicative.ofAdd (Pi.single i (0 : ZMod 2))) ∈ S
      simpa only [Pi.single_zero,ofAdd_zero,map_one] using S.one_mem
    · change centralEmbedding m (Multiplicative.ofAdd (Pi.single i (1 : ZMod 2))) ∈ S
      rw [centralEmbedding_basis]
      apply Subgroup.mem_map_of_mem
      exact Subgroup.mem_center_iff.mpr (fun g => (Presentation.z_central i.val g).eq.symm)

theorem centralEmbedding_mem_range (m : ℕ) [NeZero m]
    (c : Multiplicative (Fin m → ZMod 2)) :
    centralEmbedding m c ∈ (cyclicRepresentation m).range := by
  obtain ⟨g, _, hg⟩ := centralEmbedding_mem_center_map m c.toAdd
  exact ⟨g,hg⟩

noncomputable def quotientCentralEmbedding (m : ℕ) [NeZero m] :
    Multiplicative (Fin m → ZMod 2) →* FiniteQuotientGroup m where
  toFun c := ⟨centralEmbedding m c, centralEmbedding_mem_range m c⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' a b := Subtype.ext (map_mul _ a b)

theorem quotientCentralEmbedding_central (m : ℕ) [NeZero m]
    (c : Multiplicative (Fin m → ZMod 2)) (g : FiniteQuotientGroup m) :
    Commute (quotientCentralEmbedding m c) g := by
  obtain ⟨x, hx, hxval⟩ := centralEmbedding_mem_center_map m c.toAdd
  obtain ⟨y, hy⟩ := finiteQuotientMap_surjective m g
  subst g
  apply Subtype.ext
  change centralEmbedding m c * cyclicRepresentation m y =
    cyclicRepresentation m y * centralEmbedding m c
  change cyclicRepresentation m x = centralEmbedding m c at hxval
  rw [← hxval, ← map_mul, ← map_mul]
  exact congrArg (cyclicRepresentation m) (Subgroup.mem_center_iff.mp hx y).symm

end LittleFinitistic

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Selection_TestModules
attribute [-instance] _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.DirectedBound.DirectedSystem.cover_addCommGroup _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticPresentation.instFiniteAuxiliaryEquation _root_.OAI.LittleFinitistic.QuadraticPresentation.instFiniteAuxiliaryLetter _root_.OAI.LittleFinitistic.QuadraticPresentation.step_finite _root_.OAI.LittleFinitistic.QuadraticPresentation.word_finite _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instAddCommGroup _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instRing _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated
attribute [-simp] _root_.OAI.ExternalTensor.Section4.sum_hom _root_.OAI.LittleFinitistic.FinitePresentation.fromModel_T _root_.OAI.LittleFinitistic.FinitePresentation.fromModel_u _root_.OAI.LittleFinitistic.FinitePresentation.fromModel_v _root_.OAI.LittleFinitistic.FinitePresentation.fromModel_w _root_.OAI.LittleFinitistic.FinitePresentation.toModel_T _root_.OAI.LittleFinitistic.FinitePresentation.toModel_U _root_.OAI.LittleFinitistic.FinitePresentation.toModel_V _root_.OAI.LittleFinitistic.FinitePresentation.toModel_W
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
namespace LittleFinitistic
open MonoidAlgebra

noncomputable abbrev TestModule (m : ℕ) [NeZero m] :=
  CharacterModule.eigenspace (quotientCentralEmbedding m) (selectionCharacter m)
    (quotientCentralEmbedding_central m)

noncomputable instance testModule_finiteDimensional (m : ℕ) [NeZero m] :
    FiniteDimensional ℂ (TestModule m) :=
  CharacterModule.eigenspace_finiteDimensional _ _ _

noncomputable def testRingMap (m : ℕ) [NeZero m] :
    SelectionRing →ₐ[ℂ] MonoidAlgebra ℂ (FiniteQuotientGroup m) :=
  MonoidAlgebra.mapDomainAlgHom ℂ ℂ (finiteQuotientMap m)

noncomputable instance testModule_module (m : ℕ) [NeZero m] :
    Module SelectionRing (TestModule m) :=
  Module.compHom (TestModule m) (testRingMap m).toRingHom

@[simp] theorem testModule_smul_val (m : ℕ) [NeZero m]
    (r : SelectionRing) (x : TestModule m) :
    ((r • x : TestModule m) : MonoidAlgebra ℂ (FiniteQuotientGroup m)) = testRingMap m r * x := rfl

instance testModule_scalarTower (m : ℕ) [NeZero m] : IsScalarTower ℂ SelectionRing (TestModule m) where
  smul_assoc c r x := by
    apply Subtype.ext
    change testRingMap m (c • r) * x.val = c • (testRingMap m r * x.val)
    rw [map_smul,smul_mul_assoc]

@[simp] theorem testRingMap_algebraZ (m : ℕ) [NeZero m] (q : ℤ) :
    testRingMap m (algebraZ q) = single (finiteQuotientMap m (Presentation.z q)) 1 := by
  simp [testRingMap,algebraZ]

end LittleFinitistic

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Selection_SelectionIteration
attribute [-instance] _root_.OAI.DerivedBar.Multibar.patternModule _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.DerivedBar.termModule _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.BimoduleCoefficients.instAddCommGroupCarrierTensorProductMulOpposite _root_.OAI.LittleFinitistic.BimoduleCoefficients.instModuleCarrierTensorProductMulOpposite_1 _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.DirectedBound.DirectedSystem.cover_addCommGroup _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instAddCommGroup _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instRing _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated
attribute [-simp] _root_.OAI.ExternalTensor.Section4.sum_hom _root_.OAI.LittleFinitistic.FinitePresentation.fromModel_T _root_.OAI.LittleFinitistic.FinitePresentation.fromModel_u _root_.OAI.LittleFinitistic.FinitePresentation.fromModel_v _root_.OAI.LittleFinitistic.FinitePresentation.fromModel_w _root_.OAI.LittleFinitistic.FinitePresentation.toModel_T _root_.OAI.LittleFinitistic.FinitePresentation.toModel_U _root_.OAI.LittleFinitistic.FinitePresentation.toModel_V _root_.OAI.LittleFinitistic.FinitePresentation.toModel_W
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
namespace LittleFinitistic
open CategoryTheory

/-- The image of the central idempotent, expressed by its fixed vectors. -/
noncomputable def selectedSubmodule (M : ModuleCat SelectionRing) : Submodule SelectionRing M where
  carrier := {x | selectionIdempotent 0 • x = x}
  zero_mem' := by simp
  add_mem' := by
    intro x y hx hy
    change selectionIdempotent 0 • x = x at hx
    change selectionIdempotent 0 • y = y at hy
    change selectionIdempotent 0 • (x+y) = x+y
    rw [smul_add,hx,hy]
  smul_mem' := by
    intro r x hx
    change selectionIdempotent 0 • (r • x) = r • x
    rw [← mul_smul,(selectionIdempotent_central 0 r).eq,mul_smul,hx]

/-- Exactly H(Y) = restriction along alpha of eY from the manuscript. -/
noncomputable def selectionStep (M : ModuleCat SelectionRing) : ModuleCat SelectionRing :=
  (ModuleCat.restrictScalars (selectionAutomorphism 1).toRingHom).obj
    (ModuleCat.of SelectionRing (selectedSubmodule M))

def IdentityAt (M : ModuleCat SelectionRing) (q : ℕ) : Prop :=
  ∀ x : M, selectionIdempotent q • x = x

noncomputable def testObject (m : ℕ) [NeZero m] : ModuleCat SelectionRing :=
  ModuleCat.of SelectionRing (TestModule m)

noncomputable def complexObject (M : ModuleCat SelectionRing) : ModuleCat ℂ :=
  (ModuleCat.restrictScalars (algebraMap ℂ SelectionRing)).obj M

noncomputable def selectionStep_inclusion (M : ModuleCat SelectionRing) :
    complexObject (selectionStep M) →ₗ[ℂ] complexObject M where
  toFun x := x.val
  map_add' _ _ := rfl
  map_smul' c x := by
    change selectionAutomorphism 1 (algebraMap ℂ SelectionRing c) • x.val =
      algebraMap ℂ SelectionRing c • x.val
    rw [AlgEquiv.commutes]

theorem selectionStep_finiteDimensional (M : ModuleCat SelectionRing)
    [FiniteDimensional ℂ (complexObject M)] :
    FiniteDimensional ℂ (complexObject (selectionStep M)) :=
  FiniteDimensional.of_injective (selectionStep_inclusion M) Subtype.val_injective

theorem testObject_finiteDimensional (m : ℕ) [NeZero m] :
    FiniteDimensional ℂ (complexObject (testObject m)) := by
  let f : complexObject (testObject m) →ₗ[ℂ] TestModule m :=
    { toFun := fun x => x
      map_add' := fun _ _ => rfl
      map_smul' := fun c x => by
        have h : ∀ y : TestModule m, algebraMap ℂ SelectionRing c • y = c • y :=
          fun y => algebraMap_smul SelectionRing c y
        exact h x }
  exact FiniteDimensional.of_injective f (fun _ _ h => h)

end LittleFinitistic

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Selected_SelectedImageComparison
attribute [-instance] _root_.OAI.DerivedBar.Multibar.patternModule _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.DerivedBar.termModule _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.BimoduleCoefficients.instAddCommGroupCarrierTensorProductMulOpposite _root_.OAI.LittleFinitistic.BimoduleCoefficients.instModuleCarrierTensorProductMulOpposite_1 _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open CategoryTheory
namespace LittleFinitistic.SelectedImageComparison
open QuadraticEncoding SourceImageEvaluation
universe v
variable {Y : Type v} [AddCommGroup Y] [Module ℂ Y]
  [Module SelectionRing Y] [IsScalarTower ℂ SelectionRing Y]

/-- The evaluator's range is canonically the primary's actual H(Y), as a complex vector space. -/
def equiv : imageSpace (k := ℂ) (Y := Y) (selectionIdempotent 0) ≃ₗ[ℂ]
    complexObject (selectionStep (ModuleCat.of SelectionRing Y)) where
  toFun x := ⟨x.val.down, by
    obtain ⟨z,hz⟩ := x.property
    have hz' : selectionIdempotent 0 • z.down = x.val.down := congrArg ULift.down hz
    change selectionIdempotent 0 • x.val.down = x.val.down
    rw [← hz',← mul_smul,selectionIdempotent_square]⟩
  invFun x := ⟨ULift.up x.val, ⟨ULift.up x.val, by
    change ULift.up (selectionIdempotent 0 • x.val) = ULift.up x.val
    exact congrArg ULift.up x.property⟩⟩
  left_inv x := by apply Subtype.ext; rfl
  right_inv x := by rfl
  map_add' x y := rfl
  map_smul' c x := by
    apply Subtype.ext
    change c • x.val.down = selectionAutomorphism 1 (algebraMap ℂ SelectionRing c) • x.val.down
    rw [AlgEquiv.commutes,algebraMap_smul]

abbrev moduleAction (r : SelectionRing) (x : selectionStep (ModuleCat.of SelectionRing Y)) :
    selectionStep (ModuleCat.of SelectionRing Y) := r • x

/-- The evaluator's compressed alpha action is precisely the action on the primary's H(Y). -/
theorem equiv_action (r : SelectionRing)
    (x : imageSpace (k := ℂ) (Y := Y) (selectionIdempotent 0)) :
    equiv (Y := Y) ((imageCornerEnd (action (k := ℂ) (Y := Y) (selectionIdempotent 0)).hom
      (action (k := ℂ) (Y := Y) (selectionAutomorphism 1 r)).hom) x) =
    moduleAction (Y := Y) r (equiv (Y := Y) x) := by
  apply Subtype.ext
  have h := imageCorner_restriction (k := ℂ) (Y := Y) (selectionIdempotent 0)
    (selectionAutomorphism 1 r) (selectionIdempotent_square 0)
    (selectionIdempotent_central 0 (selectionAutomorphism 1 r)).eq x
  exact congrArg ULift.down h

end LittleFinitistic.SelectedImageComparison

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Selected_SelectedNativeEvaluation
attribute [-instance] _root_.OAI.DerivedBar.Multibar.patternModule _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.DerivedBar.termModule _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.BimoduleCoefficients.instAddCommGroupCarrierTensorProductMulOpposite _root_.OAI.LittleFinitistic.BimoduleCoefficients.instModuleCarrierTensorProductMulOpposite_1 _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.SelectedTargetHomology.instAdditiveFullSubcategoryDerivedCategoryModuleCatComplexEssImageKDerivedEmbeddingCCohomology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open CategoryTheory CategoryTheory.Limits
attribute [local instance] HasDerivedCategory.standard
namespace LittleFinitistic.SelectedNativeEvaluation
open QuadraticEncoding SourceImageEvaluation FiniteProjectiveHomotopy SelectedFixedDiagram
universe v
variable {Y : Type v} [AddCommGroup Y] [Module ℂ Y] [FiniteDimensional ℂ Y]
  [Module SelectionRing Y] [IsScalarTower ℂ SelectionRing Y]

abbrev H := complexObject (selectionStep (ModuleCat.of SelectionRing Y))
instance instFiniteDimensionalComplexCarrierH : FiniteDimensional ℂ (H (Y := Y)) :=
  Module.Finite.of_surjective (SelectedImageComparison.equiv (Y := Y)).toLinearMap
    (SelectedImageComparison.equiv (Y := Y)).surjective

def HK : K.{0,v} ℂ := ⟨(vectorStalk (k := ℂ)).obj (H (Y := Y)), single_property _ 0⟩
def HDerived : FiniteVectorDerived.{0,v} (k := ℂ) :=
  (derivedEmbedding ℂ).toEssImage.obj (HK (Y := Y))
def imageIsoK : imageK (k := ℂ) (Y := Y) e ≅ HK (Y := Y) :=
  (inclusion ℂ).preimageIso ((vectorStalk (k := ℂ)).mapIso
    (SelectedImageComparison.equiv (Y := Y)).toModuleIso)
def imageIso : imageDerived (k := ℂ) (Y := Y) e ≅ HDerived (Y := Y) :=
  (derivedEmbedding ℂ).toEssImage.mapIso (imageIsoK (Y := Y))

end LittleFinitistic.SelectedNativeEvaluation

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Selected_SelectedNativeAction
attribute [-instance] _root_.OAI.DerivedBar.Multibar.patternModule _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.DerivedBar.termModule _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.BimoduleCoefficients.instAddCommGroupCarrierTensorProductMulOpposite _root_.OAI.LittleFinitistic.BimoduleCoefficients.instModuleCarrierTensorProductMulOpposite_1 _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.SelectedTargetHomology.instAdditiveFullSubcategoryDerivedCategoryModuleCatComplexEssImageKDerivedEmbeddingCCohomology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open CategoryTheory CategoryTheory.Limits
attribute [local instance] HasDerivedCategory.standard
namespace LittleFinitistic.SelectedNativeEvaluation
open QuadraticEncoding SourceImageEvaluation FiniteProjectiveHomotopy SelectedFixedDiagram
universe v
variable {Y : Type v} [AddCommGroup Y] [Module ℂ Y]
  [Module SelectionRing Y] [IsScalarTower ℂ SelectionRing Y]

abbrev imageEnd (r : SelectionRing) := imageCornerEnd
  (action (k := ℂ) (Y := Y) e).hom (action (k := ℂ) (Y := Y) (alpha r)).hom
abbrev moduleIso := (SelectedImageComparison.equiv (Y := Y)).toModuleIso

def HAction (r : SelectionRing) : End (H (Y := Y)) :=
  (moduleIso (Y := Y)).inv ≫ imageEnd (Y := Y) r ≫ (moduleIso (Y := Y)).hom

/-- The conjugated map is the primary selectionStep module action, on every vector. -/
theorem HAction_apply (r : SelectionRing) (x : H (Y := Y)) :
    (HAction (Y := Y) r).hom x = SelectedImageComparison.moduleAction (Y := Y) r x := by
  have h := SelectedImageComparison.equiv_action (Y := Y) r
    ((SelectedImageComparison.equiv (Y := Y)).symm x)
  dsimp only [HAction,moduleIso,LinearEquiv.toModuleIso] at *
  simp only [LinearEquiv.apply_symm_apply] at h
  exact h

lemma module_square (r : SelectionRing) :
    imageEnd (Y := Y) r ≫ (moduleIso (Y := Y)).hom =
      (moduleIso (Y := Y)).hom ≫ HAction (Y := Y) r := by
  simp only [HAction,Iso.hom_inv_id_assoc]

variable [FiniteDimensional ℂ Y]

def HKAction (r : SelectionRing) : End (HK (Y := Y)) :=
  (inclusion ℂ).preimage ((vectorStalk (k := ℂ)).map (HAction (Y := Y) r))
def HDerivedAction (r : SelectionRing) : End (HDerived (Y := Y)) :=
  (derivedEmbedding ℂ).toEssImage.map (HKAction (Y := Y) r)

lemma imageIsoK_hom : (inclusion ℂ).map (imageIsoK (Y := Y)).hom =
    (vectorStalk (k := ℂ)).map (moduleIso (Y := Y)).hom := by
  simp only [imageIsoK,Functor.preimageIso,Functor.mapIso_hom]
  erw [Functor.map_preimage]

lemma image_square (r : SelectionRing) :
    imageCorner (k := ℂ) (Y := Y) e (alpha r) ≫ (imageIso (Y := Y)).hom =
      (imageIso (Y := Y)).hom ≫ HDerivedAction (Y := Y) r := by
  apply (derivedTargetInclusion (k := ℂ)).map_injective
  rw [Functor.map_comp,Functor.map_comp]
  dsimp only [imageCorner]
  erw [Functor.map_preimage]
  change DerivedCategory.Qh.map ((vectorStalk (k := ℂ)).map (imageEnd (Y := Y) r)) ≫
    DerivedCategory.Qh.map ((inclusion ℂ).map (imageIsoK (Y := Y)).hom) =
    DerivedCategory.Qh.map ((inclusion ℂ).map (imageIsoK (Y := Y)).hom) ≫
    DerivedCategory.Qh.map ((inclusion ℂ).map (HKAction (Y := Y) r))
  rw [imageIsoK_hom]
  dsimp only [HKAction]
  erw [Functor.map_preimage]
  erw [← Functor.map_comp,← Functor.map_comp,← Functor.map_comp,← Functor.map_comp,module_square]
  rfl

end LittleFinitistic.SelectedNativeEvaluation

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Selected_SelectedTargetHomology
attribute [-instance] _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open CategoryTheory CategoryTheory.Limits
attribute [local instance] HasDerivedCategory.standard
namespace LittleFinitistic.SelectedTargetHomology
open QuadraticEncoding SelectedNativeEvaluation FiniteProjectiveHomotopy
universe v
variable {Y : Type v} [AddCommGroup Y] [Module ℂ Y] [FiniteDimensional ℂ Y]
  [Module SelectionRing Y] [IsScalarTower ℂ SelectionRing Y]

def stalkIso : I.obj (HDerived (Y := Y)) ≅
    (DerivedCategory.singleFunctor C 0).obj (H (Y := Y)) := Iso.refl _

def stalkHomologyIso : (cohomology 0).obj (HDerived (Y := Y)) ≅ H (Y := Y) :=
  (DerivedCategory.homologyFunctor C 0).mapIso stalkIso ≪≫
    (DerivedCategory.singleFunctorCompHomologyFunctorIso C 0).app _
lemma stalk_zero (n : ℤ) (hn : n ≠ 0) :
    IsZero ((cohomology n).obj (HDerived (Y := Y))) :=
  ((DerivedCategory.homologyFunctor C n).mapIso (stalkIso (Y := Y))).isZero_iff.mpr
    (single_zero _ _ _ hn)

lemma stalkHomologyIso_hom : (stalkHomologyIso (Y := Y)).hom =
    ((DerivedCategory.singleFunctorCompHomologyFunctorIso C 0).app (H (Y := Y))).hom := by
  change (DerivedCategory.homologyFunctor C 0).map
    (𝟙 ((DerivedCategory.singleFunctor C 0).obj (H (Y := Y)))) ≫ _ = _
  rw [CategoryTheory.Functor.map_id,Category.id_comp]

lemma stalk_action (r : SelectionRing) :
    (cohomology 0).map (HDerivedAction (Y := Y) r) ≫ (stalkHomologyIso (Y := Y)).hom =
      (stalkHomologyIso (Y := Y)).hom ≫ HAction (Y := Y) r := by
  rw [stalkHomologyIso_hom]
  change (DerivedCategory.homologyFunctor C 0).map
    (DerivedCategory.Qh.map ((inclusion ℂ).map (HKAction (Y := Y) r))) ≫ _ = _
  dsimp only [HKAction]
  erw [Functor.map_preimage]
  change (DerivedCategory.homologyFunctor C 0).map
    ((DerivedCategory.singleFunctor C 0).map (HAction (Y := Y) r)) ≫ _ = _
  exact (DerivedCategory.singleFunctorCompHomologyFunctorIso C 0).hom.naturality
    (HAction (Y := Y) r)

end LittleFinitistic.SelectedTargetHomology

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Selected_SelectedRealization
attribute [-instance] _root_.OAI.DerivedBar.Multibar.patternModule _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.DerivedBar.termModule _root_.OAI.LittleFinitistic.BimoduleCoefficients.instAddCommGroupCarrierTensorProductMulOpposite _root_.OAI.LittleFinitistic.BimoduleCoefficients.instModuleCarrierTensorProductMulOpposite_1 _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open CategoryTheory CategoryTheory.Limits HomologicalComplex
attribute [local instance] HasDerivedCategory.standard HasExt.standard
namespace LittleFinitistic.SelectedRealization
open SelectedFixedDiagram QuadraticEncoding SelectedNativeEvaluation
variable {Y : Type} [AddCommGroup Y] [Module ℂ Y] [FiniteDimensional ℂ Y]
  [Module SelectionRing Y] [IsScalarTower ℂ SelectionRing Y]

local instance selectedModule : Module SelectionRing (H (Y := Y)) :=
  inferInstanceAs (Module SelectionRing (selectionStep (ModuleCat.of SelectionRing Y)))
local instance selectedTower : IsScalarTower ℂ SelectionRing (H (Y := Y)) :=
  IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)

end LittleFinitistic.SelectedRealization

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Selection_FiniteSelectionFamily
attribute [-instance] _root_.OAI.DerivedBar.Multibar.patternModule _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.DerivedBar.termModule _root_.OAI.LittleFinitistic.BimoduleCoefficients.instAddCommGroupCarrierTensorProductMulOpposite _root_.OAI.LittleFinitistic.BimoduleCoefficients.instModuleCarrierTensorProductMulOpposite_1 _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open CategoryTheory CategoryTheory.Limits
attribute [local instance] HasDerivedCategory.standard HasExt.standard
namespace LittleFinitistic.FiniteSelectionFamily
open SelectedFixedDiagram QuadraticEncoding

/-- Actual finite-dimensional modules over the fixed selecting algebra. -/
def S := {M : ModuleCat SelectionRing // FiniteDimensional ℂ (complexObject M)}
abbrev vector (Y : S) := complexObject Y.val
instance instFiniteDimensionalComplexCarrierVector (Y : S) : FiniteDimensional ℂ (vector Y) := Y.property
instance ringModule (Y : S) : Module SelectionRing (vector Y) :=
  inferInstanceAs (Module SelectionRing Y.val)
instance tower (Y : S) : IsScalarTower ℂ SelectionRing (vector Y) :=
  IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)

/-- H preserves this actual finite-dimensional family. -/
def H (Y : S) : S := ⟨selectionStep Y.val, by
  let : FiniteDimensional ℂ (complexObject Y.val) := Y.property
  exact selectionStep_finiteDimensional Y.val⟩

def test (m : ℕ) [NeZero m] : S := ⟨testObject m, testObject_finiteDimensional m⟩

end LittleFinitistic.FiniteSelectionFamily

end

end OAI
end



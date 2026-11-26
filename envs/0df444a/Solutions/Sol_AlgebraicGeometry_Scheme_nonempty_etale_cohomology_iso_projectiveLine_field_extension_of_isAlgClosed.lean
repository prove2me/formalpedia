-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.nonempty_etale_cohomology_iso_projectiveLine_field_extension_of_isAlgClosed
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-11-26T08:45:25.545566+00:00
-- url     : https://prove2.me/submissions/1b9a3957-8836-4c60-bb65-f7072d02de81
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_AlgebraicGeometry_EtaleCohomologyRestriction
import Definitions.Def_AlgebraicGeometry_EtaleFilteredCoefficientRestriction
import Definitions.Def_AlgebraicGeometry_EtaleFiniteCohomologyBaseChange
import Definitions.Def_AlgebraicGeometry_EtaleFiniteDirectImageBaseChange
import Definitions.Def_AlgebraicGeometry_EtaleFiniteLiftEvaluation
import Definitions.Def_AlgebraicGeometry_EtaleOpenCoefficientComparison
import Definitions.Def_AlgebraicGeometry_EtaleOverlapBoundary
import Definitions.Def_AlgebraicGeometry_EtalePullbackGermNaturality
import Definitions.Def_AlgebraicGeometry_EtaleStrictLocalSectionGerms
import Definitions.Def_AlgebraicGeometry_EtaleTwoAffineFilteredCohomology
import Definitions.Def_AlgebraicGeometry_FilteredColimitExtDetection
import Definitions.Def_AlgebraicGeometry_FreeEtaleChartSheaves
import Definitions.Def_AlgebraicGeometry_ProjSpace
import Definitions.Def_AlgebraicGeometry_ProjectiveLineFiniteOverlap
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.FiveLemma
import Mathlib.Algebra.Homology.DerivedCategory.Ext.EnoughInjectives
import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences
import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExtClass
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Map
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.CategoryTheory.Abelian.FunctorCategory
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.ColimCoyoneda
import Mathlib.CategoryTheory.Limits.Preserves.Filtered
import Mathlib.CategoryTheory.Limits.Types.Filtered
import Mathlib.CategoryTheory.ObjectProperty.Ind
import Mathlib.CategoryTheory.Preadditive.Injective.Preserves
import Mathlib.CategoryTheory.Presentable.Finite
import Mathlib.CategoryTheory.Sites.SheafCohomology.MayerVietoris
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.FieldTheory.PurelyInseparable.Basic
import Mathlib.RingTheory.LocalRing.ResidueField.Instances
import Mathlib.Tactic.FinCases
import Theorems.Thm_AlgebraicGeometry_Scheme_bijective_etale_constant_cohomology_on_finite_projectiveLine_cover
import Theorems.Thm_AlgebraicGeometry_Scheme_exists_etale_H_zero_preimage_of_filtered_coefficients
import Theorems.Thm_AlgebraicGeometry_Scheme_exists_finite_coproduct_strictlyHenselian_of_finite
import Theorems.Thm_AlgebraicGeometry_Scheme_filtered_colimit_of_injectives_etale_H_succ_subsingleton
import Theorems.Thm_AlgebraicGeometry_Scheme_ind_bounded_finite_constant_models_of_projectiveLine
import Theorems.Thm_AlgebraicGeometry_Scheme_isIso_etale_restrictGlobalSections_of_separably_closed_field_extension

noncomputable section

section

open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian

universe siteU

local instance (priority := 2000) projectiveConstantModularHasSheafify (X : Scheme.{siteU}) :
    HasSheafify X.smallEtaleTopology AddCommGrpCat.{siteU} := inferInstance

local instance (priority := 2000) projectiveConstantModularHasExt (X : Scheme.{siteU}) :
    HasExt.{siteU} (Sheaf X.smallEtaleTopology AddCommGrpCat.{siteU}) := inferInstance

local instance (priority := 2000) projectiveConstantModularEnoughInjectives (X : Scheme.{siteU}) :
    EnoughInjectives (Sheaf X.smallEtaleTopology AddCommGrpCat.{siteU}) := inferInstance

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1400000

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open PhilipponEtaleBoundedFiniteModelReduction (boundedFiniteModel)
open PhilipponEtaleClosedPushforward (pushforward)
open PhilipponEtaleFilteredRestriction (restrict_injective_of_ind restrict_surjective_of_ind)
open PhilipponEtalePrimeTorsionComparison (restrict bijective_restrict_of_test_embeddings)
open PhilipponEtaleSmallSite (pullbackAdjunction pullbackSheaves)
open PhilipponEtaleTwoAffineFilteredSections (AffineLifting preservesFilteredColimits_functorH)


namespace PhilipponEtaleFiniteConstantReduction

universe u

private abbrev Ab (X : Scheme.{u}) := Sheaf X.smallEtaleTopology AddCommGrpCat.{u}
private abbrev constant (X : Scheme.{u}) (M : AddCommGrpCat.{u}) :=
  (constantSheaf X.smallEtaleTopology AddCommGrpCat.{u}).obj M

/-- The positive-degree restriction maps to be checked on finite covers. -/
def FiniteConstantComparison {X T : Scheme.{u}} (a : T ⟶ X) (N : ℕ) : Prop :=
  ∀ {Y : Scheme.{u}} (p : Y ⟶ X) [IsFinite p] (M : AddCommGrpCat.{u}) [Finite M],
    N • 𝟙 M = 0 → ∀ q : ℕ,
    Function.Bijective (restrict (pullback.snd a p) (constant Y M) (q + 1))

private theorem finiteConstantDirectImage_killed {X Y : Scheme.{u}} (p : Y ⟶ X)
    (M : AddCommGrpCat.{u}) (N : ℕ) (hM : N • 𝟙 M = 0) :
    N • 𝟙 ((pushforward p).obj (constant Y M)) = 0 := by
  let C := constantSheaf Y.smallEtaleTopology AddCommGrpCat.{u}
  let hT : IsTerminal (Scheme.Etale.mk (𝟙 Y)) :=
    IsTerminal.isTerminalOfObj (Scheme.Etale.forget Y) _ Over.mkIdTerminal
  let : C.Additive := (constantSheafAdj Y.smallEtaleTopology AddCommGrpCat.{u} hT).left_adjoint_additive
  let P := pushforward p
  let : P.Additive := (pullbackAdjunction p).right_adjoint_additive
  let D := C ⋙ P
  change N • 𝟙 (D.obj M) = 0
  simpa only [D.map_nsmul, D.map_id, D.map_zero] using congrArg (fun m => D.map m) hM

/-- If coefficients are filtered colimits of sheaves admitting bounded
finite constant models, canonical comparison reduces to those finite covers. -/
theorem restrict_bijective_of_finiteConstantModels {X T : Scheme.{u}} (a : T ⟶ X) (N : ℕ)
    (hX : ∀ q, PreservesFilteredColimitsOfSize.{u, u} (Sheaf.functorH X.smallEtaleTopology q))
    (hT : ∀ q, PreservesFilteredColimitsOfSize.{u, u} (Sheaf.functorH T.smallEtaleTopology q))
    (h₀ : ∀ G : Ab X, Function.Bijective (restrict a G 0))
    (hModel : ∀ G : Ab X, N • 𝟙 G = 0 → ObjectProperty.ind.{u} (boundedFiniteModel X N) G)
    (hCompare : FiniteConstantComparison a N)
    (F : Ab X) (hF : N • 𝟙 F = 0) (n : ℕ) : Function.Bijective (restrict a F n) := by
  refine bijective_restrict_of_test_embeddings a N (boundedFiniteModel X N)
    (fun G _ => h₀ G) ?_ ?_ ?_ F hF n
  · intro G hG
    obtain ⟨Y, p, hp, _, M, hM, hz, m, hm⟩ := hG
    let : IsFinite p := hp
    let : Finite M := hM
    let J := (pushforward p).obj (constant Y M)
    refine ⟨J, m, hm, finiteConstantDirectImage_killed p M N hz, fun q => ?_⟩
    cases q with
    | zero => exact h₀ J
    | succ q =>
      exact (PhilipponEtaleFiniteCohomologyBaseChange.bijective_restrict_directImage_iff
        a p (pullback.fst a p) (pullback.snd a p) (IsPullback.of_hasPullback a p) (constant Y M)
        (q + 1)).mpr (hCompare p M hz q)
  · intro q hStage G hG
    let : PreservesFilteredColimitsOfSize.{u, u} (Sheaf.functorH X.smallEtaleTopology q) := hX q
    let : PreservesFilteredColimitsOfSize.{u, u} (Sheaf.functorH T.smallEtaleTopology q) := hT q
    exact restrict_injective_of_ind a q _ hStage G (hModel G hG)
  · intro q hStage G hG
    let : PreservesFilteredColimitsOfSize.{u, u} (Sheaf.functorH T.smallEtaleTopology q) := hT q
    exact restrict_surjective_of_ind a q _ hStage G (hModel G hG)

attribute [local instance] MvPolynomial.gradedAlgebra

/-- The field-extension comparison for a projective line reduces to
positive-degree comparison on finite covers with finite constant coefficients. -/
theorem projectiveLine_comparison_of_finiteConstant (hLift : AffineLifting.{u})
    (R K E : Type u) [CommRing R] [Field K] [Field E]
    (φ : K →+* E) (v : Spec (.of K) ⟶ Spec (.of R)) {P T : Scheme.{u}}
    (r : P ⟶ Spec (.of K)) (d : P ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin 2) R))
    (hP : IsPullback r d v (ProjSpace.π R 1)) (j : T ⟶ Spec (.of E)) (a : T ⟶ P)
    (hT : IsPullback j a (Spec.map (CommRingCat.ofHom φ)) r) (N : ℕ) (hN : N ≠ 0)
    (h₀ : ∀ G : Ab P, Function.Bijective (restrict a G 0))
    (hCompare : FiniteConstantComparison a N) (F : Ab P) (hF : N • 𝟙 F = 0) (n : ℕ) :
    Function.Bijective (restrict a F n) := by
  let g := Spec.map (CommRingCat.ofHom φ)
  have hLine : IsPullback j (a ≫ d) (g ≫ v) (ProjSpace.π R 1) := hT.paste_vert hP
  let : IsProper r := MorphismProperty.of_isPullback hP.flip inferInstance
  let : IsProper j := MorphismProperty.of_isPullback hLine.flip inferInstance
  have hp : terminal.from P = r ≫ terminal.from (Spec (.of K)) := terminal.hom_ext _ _
  have ht : terminal.from T = j ≫ terminal.from (Spec (.of E)) := terminal.hom_ext _ _
  let : P.IsSeparated := ⟨hp.symm ▸ inferInstanceAs (IsSeparated (r ≫ terminal.from (Spec (.of K))))⟩
  let : T.IsSeparated := ⟨ht.symm ▸ inferInstanceAs (IsSeparated (j ≫ terminal.from (Spec (.of E))))⟩
  obtain ⟨U, V, hU, hV, hX⟩ := PhilipponEtaleProjectiveLineTwoAffine.exists_two_affine_opens v r d hP
  obtain ⟨W, Z, hW, hZ, hY⟩ := PhilipponEtaleProjectiveLineTwoAffine.exists_two_affine_opens
    (g ≫ v) j (a ≫ d) hLine
  exact restrict_bijective_of_finiteConstantModels a N
    (preservesFilteredColimits_functorH hLift U V hU hV hX)
    (preservesFilteredColimits_functorH hLift W Z hW hZ hY) h₀
    (AlgebraicGeometry.Scheme.ind_bounded_finite_constant_models_of_projectiveLine R K v r d hP N hN)
    hCompare F hF n

end PhilipponEtaleFiniteConstantReduction

attribute [local instance] MvPolynomial.gradedAlgebra
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u

theorem solution
    (R L E : Type u) [CommRing R] [Field L] [IsAlgClosed L] [Field E] [IsAlgClosed E]
    (φ : L →+* E) (v : Spec (.of L) ⟶ Spec (.of R)) {P T : Scheme.{u}}
    (r : P ⟶ Spec (.of L)) (d : P ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin 2) R)) (hP : IsPullback r d v (ProjSpace.π R 1))
    (j : T ⟶ Spec (.of E)) (a : T ⟶ P) (hT : IsPullback j a (Spec.map (CommRingCat.ofHom φ)) r)
    (N : ℕ) (hN : N.Prime) (F : Sheaf P.smallEtaleTopology AddCommGrpCat.{u}) (hF : N • 𝟙 F = 0) (q : ℕ) :
    Nonempty (AddCommGrpCat.of (F.H (q + 1)) ≅
      AddCommGrpCat.of (((PhilipponEtaleSmallSite.pullbackSheaves a).obj F).H (q + 1))) := by
  let : IsProper r := MorphismProperty.of_isPullback hP.flip
    (inferInstance : IsProper (ProjSpace.π R 1))
  have hLift : PhilipponEtaleTwoAffineFilteredSections.AffineLifting.{u} := by
    intro J _ _ X _ G c hc x
    exact AlgebraicGeometry.Scheme.exists_etale_H_zero_preimage_of_filtered_coefficients X G c hc x
  have h₀ (G : Sheaf P.smallEtaleTopology AddCommGrpCat.{u}) :
      Function.Bijective (PhilipponEtalePrimeTorsionComparison.restrict a G 0) :=
    PhilipponEtalePrimeTorsionComparison.bijective_restrict_zero a G
      (AlgebraicGeometry.Scheme.isIso_etale_restrictGlobalSections_of_separably_closed_field_extension L E φ r j a hT G)
  have hC : PhilipponEtaleFiniteConstantReduction.FiniteConstantComparison a N := by
    intro Y p _ M _ hM n
    exact AlgebraicGeometry.Scheme.bijective_etale_constant_cohomology_on_finite_projectiveLine_cover R L E φ v r d hP j a hT p N hN M hM n
  let h := PhilipponEtaleFiniteConstantReduction.projectiveLine_comparison_of_finiteConstant
    hLift R L E φ v r d hP j a hT N hN.ne_zero h₀ hC F hF (q + 1)
  exact ⟨(AddEquiv.ofBijective _ h).toAddCommGrpIso⟩

end

end

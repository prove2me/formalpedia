-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.exists_finite_surjective_effacing_constant_closed_fiber
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-11-25T01:15:46.365863+00:00
-- url     : https://prove2.me/submissions/cba92d4d-0dbd-48be-ac5b-8c57569bad9e

import Definitions.Def_AlgebraicGeometry_EtaleCohomologyRestriction
import Definitions.Def_AlgebraicGeometry_EtaleFiniteSectionLifts
import Definitions.Def_AlgebraicGeometry_EtalePullbackAcyclicResolution
import Definitions.Def_AlgebraicGeometry_IntegralFiniteSurjectiveDiagram
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.AlgebraicGeometry.Morphisms.Integral
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Theorems.Thm_AlgebraicGeometry_Scheme_etale_pushforward_preservesFiniteColimits_of_isFinite
import Theorems.Thm_AlgebraicGeometry_Scheme_exists_etale_cohomology_restrict_eq_zero_at_finite_stage
import Theorems.Thm_AlgebraicGeometry_Scheme_subsingleton_etale_cohomology_constant_closed_of_isAlgClosed_fractionRing

noncomputable section

section

open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian

universe siteU

local instance (priority := 2000) etaleConstantCoverHasSheafify (X : Scheme.{siteU}) :
    HasSheafify X.smallEtaleTopology AddCommGrpCat.{siteU} := inferInstance

local instance (priority := 2000) etaleConstantCoverHasExt (X : Scheme.{siteU}) :
    HasExt.{siteU} (Sheaf X.smallEtaleTopology AddCommGrpCat.{siteU}) := inferInstance

local instance (priority := 2000) etaleConstantCoverEnoughInjectives (X : Scheme.{siteU}) :
    EnoughInjectives (Sheaf X.smallEtaleTopology AddCommGrpCat.{siteU}) := inferInstance

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits


namespace PhilipponEtaleIntegralEffacementCover

universe u

set_option maxHeartbeats 900000 in
/-- Any affine scheme admits an integral surjective cover that is a closed
subscheme of the spectrum of a normal domain with algebraically closed fraction field. -/
theorem exists_integral_surjective_closed_model (Y : Scheme.{u}) [IsAffine Y] :
    ∃ (R : Type u) (_ : CommRing R) (_ : IsDomain R) (_ : IsIntegrallyClosed R),
      IsAlgClosed (FractionRing R) ∧
        ∃ (V : Scheme.{u}) (f : V ⟶ Y) (e : V ⟶ Spec (.of R)),
          IsIntegralHom f ∧ Surjective f ∧ IsClosedImmersion e := by
  let A := Γ(Y, ⊤)
  let P := MvPolynomial A ℤ
  let K := FractionRing P
  let L := AlgebraicClosure K
  let f : P →+* A := MvPolynomial.eval₂Hom (Int.castRingHom A) id
  have hf : Function.Surjective f := by
    intro a
    exact ⟨MvPolynomial.X a, MvPolynomial.eval₂Hom_X' _ _ a⟩
  let : Algebra.IsAlgebraic P L := IsFractionRing.comap_isAlgebraic_iff.mpr
    (inferInstance : Algebra.IsAlgebraic K L)
  have hPL : Function.Injective (algebraMap P L) := by
    rw [IsScalarTower.algebraMap_eq P K L]
    exact (algebraMap K L).injective.comp (IsFractionRing.injective P K)
  let R := integralClosure P L
  let : IsFractionRing R L := integralClosure.isFractionRing_of_algebraic
    (fun _ hx => hPL (hx.trans (map_zero _).symm))
  have hNormal : IsIntegrallyClosed R :=
    (IsIntegrallyClosed.integralClosure_eq_bot_iff L).mp integralClosure_idem
  let fieldIso := IsLocalization.algEquiv (nonZeroDivisors R) L (FractionRing R)
  have hAlgClosed : IsAlgClosed (FractionRing R) := IsAlgClosed.of_ringEquiv L _ fieldIso.toRingEquiv
  let v : Y ⟶ Spec (.of P) := Y.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom f)
  let : IsClosedImmersion (Spec.map (CommRingCat.ofHom f)) :=
    IsClosedImmersion.spec_of_surjective _ hf
  let : IsClosedImmersion v := inferInstanceAs (IsClosedImmersion (Y.isoSpec.hom ≫ _))
  let a : Spec (.of R) ⟶ Spec (.of P) := Spec.map (CommRingCat.ofHom (algebraMap P R))
  have hPR : Function.Injective (algebraMap P R) := by
    intro x y hxy
    apply hPL
    exact congrArg Subtype.val hxy
  let : IsIntegralHom a := IsIntegralHom.SpecMap_iff.mpr
    (algebraMap_isIntegral_iff.mpr (inferInstance : Algebra.IsIntegral P R))
  let : Surjective a := ⟨(algebraMap_isIntegral_iff.mpr
    (inferInstance : Algebra.IsIntegral P R)).comap_surjective hPR⟩
  exact ⟨R, inferInstance, inferInstance, hNormal, hAlgClosed, pullback v a, pullback.fst v a,
    pullback.snd v a, inferInstance, inferInstance, inferInstance⟩

end PhilipponEtaleIntegralEffacementCover

end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open PhilipponEtaleClosedPushforward (pushforward)
open PhilipponEtaleCohomologyRestrictionUnit (toDirectImage_restrict_eq_unitMap)
open PhilipponEtaleCohomologyUnits (toDirectImage unitMap)
open PhilipponEtalePrimeTorsionComparison (restrict)


namespace PhilipponEtaleFiniteStageEffacement

universe u

private abbrev Ab (X : Scheme.{u}) := Sheaf X.smallEtaleTopology AddCommGrpCat.{u}

set_option maxHeartbeats 1400000 in
/-- Descent of a zero class along affine limits gives a finite surjective
cover that kills a class known to vanish on an integral surjective cover. -/
theorem exists_finite_surjective_effacing_unit_of_continuity
    (hExact : ∀ {X Y : Scheme.{u}} (p : Y ⟶ X) [IsFinite p],
      PreservesFiniteColimits (pushforward p))
    (hContinuity : ∀ {I : Type u} [Category.{u} I] [IsCofiltered I]
      (D : I ⥤ Scheme.{u}) (c : Cone D) (_ : IsLimit c)
      {Y W : Scheme.{u}} [IsAffine Y] (j : W ⟶ Y) [IsClosedImmersion j]
      (t : D ⟶ (Functor.const I).obj Y) (f : c.pt ⟶ Y)
      (_ : ∀ i, c.π.app i ≫ t.app i = f) (_ : ∀ i, IsFinite (t.app i))
      (F : Ab W) (q : ℕ) (x : F.H q),
      restrict (pullback.fst j f) F q x = 0 →
        ∃ i, restrict (pullback.fst j (t.app i)) F q x = 0)
    {Y V W : Scheme.{u}} [IsAffine Y] (j : W ⟶ Y) [IsClosedImmersion j]
    (f : V ⟶ Y) [IsIntegralHom f] [Surjective f] (F : Ab W) (q : ℕ)
    (x : F.H q) (hx : restrict (pullback.fst j f) F q x = 0) :
    ∃ (Y' : Scheme.{u}) (a : Y' ⟶ Y), IsFinite a ∧ Surjective a ∧
      unitMap (pullback.fst j a) F q x = 0 := by
  obtain ⟨I, hI, hCof, D, π, t, ⟨hc⟩, ht, hStages⟩ :=
    PhilipponEtaleIntegralFiniteDiagram.exists_finite_surjective_limit_of_integral f
  let _ : Category.{u} I := hI
  let _ : IsCofiltered I := hCof
  obtain ⟨i, hi⟩ := hContinuity D (Cone.mk V π) hc j t f ht (fun i => (hStages i).1) F q x hx
  let a := t.app i
  obtain ⟨ha, hs⟩ := hStages i
  let : IsFinite a := ha
  let a₀ := pullback.fst j a
  let : IsFinite a₀ := inferInstanceAs (IsFinite (pullback.fst j a))
  let : PreservesFiniteColimits (pushforward a₀) := hExact a₀
  refine ⟨D.obj i, a, ha, hs, ?_⟩
  calc
    _ = toDirectImage a₀ _ q (restrict a₀ F q x) := (toDirectImage_restrict_eq_unitMap a₀ F q x).symm
    _ = 0 := (congrArg (toDirectImage a₀ _ q) hi).trans (map_zero _)

end PhilipponEtaleFiniteStageEffacement

end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open PhilipponEtaleAcyclicCohomology (pullbackConstantIso)
open PhilipponEtalePrimeTorsionComparison (restrict)
open PhilipponEtaleSmallSite (pullbackAdjunction pullbackSheaves)


namespace PhilipponEtaleConstantCoverEffacement

universe u

private abbrev constant (Y : Scheme.{u}) (M : AddCommGrpCat.{u}) :=
  (constantSheaf Y.smallEtaleTopology AddCommGrpCat.{u}).obj M

private abbrev unitOnClosedFiber {Y V W : Scheme.{u}} (j : W ⟶ Y) (f : V ⟶ Y)
    (M : AddCommGrpCat.{u}) (q : ℕ) :=
  Sheaf.H.map ((pullbackAdjunction (pullback.fst j f)).unit.app
    ((pullbackSheaves j).obj (constant Y M))) q

set_option maxHeartbeats 1200000 in
/-- An integral cover with acyclic closed subschemes kills the class.
Descent of this vanishing provides the required finite cover. -/
theorem exists_finite_cover_effacing_constant_of_integral_vanishing
    (hVanishing : ∀ (R : Type u) [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
      [IsAlgClosed (FractionRing R)] {T : Scheme.{u}} (e : T ⟶ Spec (.of R)) [IsClosedImmersion e]
      (M : AddCommGrpCat.{u}) (_ : Finite M) (q : ℕ), Subsingleton ((constant T M).H (q + 1)))
    (hFiniteStage : ∀ {Y V W : Scheme.{u}} [IsAffine Y] (j : W ⟶ Y) [IsClosedImmersion j]
      (f : V ⟶ Y) [IsIntegralHom f] [Surjective f] (M : AddCommGrpCat.{u}) (_ : Finite M)
      (q : ℕ) (x : ((pullbackSheaves j).obj (constant Y M)).H (q + 1)),
      restrict (pullback.fst j f) ((pullbackSheaves j).obj (constant Y M)) (q + 1) x = 0 →
        ∃ (Y' : Scheme.{u}) (a : Y' ⟶ Y), IsFinite a ∧ Surjective a ∧
          unitOnClosedFiber j a M (q + 1) x = 0)
    {Y W : Scheme.{u}} [IsAffine Y] (j : W ⟶ Y) [IsClosedImmersion j]
    (M : AddCommGrpCat.{u}) (hM : Finite M) (q : ℕ)
    (x : ((pullbackSheaves j).obj (constant Y M)).H (q + 1)) :
    ∃ (Y' : Scheme.{u}) (a : Y' ⟶ Y), IsFinite a ∧ Surjective a ∧
      unitOnClosedFiber j a M (q + 1) x = 0 := by
  obtain ⟨R, hR, hDomain, hNormal, hAlgClosed, V, f, e, hf, hSurj, he⟩ :=
    PhilipponEtaleIntegralEffacementCover.exists_integral_surjective_closed_model Y
  let : CommRing R := hR
  let : IsDomain R := hDomain
  let : IsIntegrallyClosed R := hNormal
  let : IsAlgClosed (FractionRing R) := hAlgClosed
  let : IsIntegralHom f := hf
  let : Surjective f := hSurj
  let : IsClosedImmersion e := he
  let a := pullback.fst j f
  let b := pullback.snd j f
  let t := b ≫ e
  let : IsClosedImmersion b := inferInstanceAs (IsClosedImmersion (pullback.snd j f))
  let : IsClosedImmersion t := inferInstanceAs (IsClosedImmersion (b ≫ e))
  have hH := hVanishing R t M hM q
  let η := (pullbackSheaves a).mapIso ((pullbackConstantIso j).app M) ≪≫
    (pullbackConstantIso a).app M
  let H := Sheaf.functorH (pullback j f).smallEtaleTopology (q + 1)
  apply hFiniteStage j f M hM q x
  apply (ConcreteCategory.bijective_of_isIso (H.map η.hom)).injective
  exact hH.elim _ _

end PhilipponEtaleConstantCoverEffacement

end

section

open PhilipponEtaleSmallSite (pullbackAdjunction pullbackSheaves)

set_option autoImplicit false
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u

theorem solution
    {Y W : Scheme.{u}} [IsAffine Y] (j : W ⟶ Y) [IsClosedImmersion j]
    (M : AddCommGrpCat.{u}) (hM : Finite M) (q : ℕ)
    (x : ((pullbackSheaves j).obj ((constantSheaf Y.smallEtaleTopology AddCommGrpCat.{u}).obj M)).H (q + 1)) :
    ∃ (Y' : Scheme.{u}) (a : Y' ⟶ Y), IsFinite a ∧ Surjective a ∧
      Sheaf.H.map ((pullbackAdjunction (pullback.fst j a)).unit.app
        ((pullbackSheaves j).obj ((constantSheaf Y.smallEtaleTopology AddCommGrpCat.{u}).obj M)))
        (q + 1) x = 0 := by
  exact PhilipponEtaleConstantCoverEffacement.exists_finite_cover_effacing_constant_of_integral_vanishing
    (by
      intro R _ _ _ _ T e _ M hM q
      exact AlgebraicGeometry.Scheme.subsingleton_etale_cohomology_constant_closed_of_isAlgClosed_fractionRing R e M hM q)
    (by
      intro Y V W _ j _ f _ _ M hM q x hx
      exact PhilipponEtaleFiniteStageEffacement.exists_finite_surjective_effacing_unit_of_continuity
        (fun p => AlgebraicGeometry.Scheme.etale_pushforward_preservesFiniteColimits_of_isFinite p) (@AlgebraicGeometry.Scheme.exists_etale_cohomology_restrict_eq_zero_at_finite_stage) j f _ (q + 1) x hx)
    j M hM q x

end

end

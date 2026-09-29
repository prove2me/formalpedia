-- Prove2me | solution 1 for AlgebraicGeometry.RelEffCartierDiv.nonempty_lineBundle_pullbackAlong_iso_invModule_pow_ker_mul_pow_prod_ker
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/65060bad-010e-55f6-a676-8b7d80db7eb8

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RelEffCartierDiv
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivSupportedIn
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivSum
import Definitions.Def_AlgebraicGeometry_RelPicardThetaBundle
import Definitions.Def_AlgebraicGeometry_RelPicardChartSections
import Definitions.Def_AlgebraicGeometry_IdealSheafModule
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveBase
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_AlgebraicCurve_RelCartier
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_comap_mul
import Theorems.Thm_AlgebraicGeometry_isReduced_of_etale
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_RelEffCartierDiv_nonempty_lineBundle_pullbackAlong_iso_invModule_pow_ker_mul_pow_prod_ker

set_option autoImplicit false

universe u

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry P2MW.S_AlgebraicGeometry_RelEffCartierDiv_nonempty_lineBundle_pullbackAlong_iso_invModule_pow_ker_mul_pow_prod_ker.AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra CategoryTheory.MonoidalCategory AlgebraicGeometry.SmoothProperCurve TensorProduct"

noncomputable section

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Scheme.Hom.ker_comp_of_isIso Surjective IsClosedImmersion.of_comp Scheme.Hom pointOfClosedPoint_apply pointOfClosedPoint IsFinite LocallyOfFiniteType Spec Scheme LocallyOfFiniteType.jacobsonSpace pointOfClosedPoint_comp Flat IsClosedImmersion IsReduced IsSeparated Etale isIso_of_isClosedImmersion_of_surjective Scheme.IdealSheafData isClosedImmersion_of_comp_eq_id RelEffCartierDiv mapOnProdOver mapOnProdOver_fst mapOnProdOver_snd isPullback_mapOnProdOver isReduced_of_etale"
namespace N10Impl
p2m_open "AlgebraicGeometry"

p2m_open "AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.IdealSheafData TopologicalSpace"

theorem ker_eq_vanishingIdeal_of_isReduced {X Y : Scheme.{u}} (f : X ⟶ Y) [IsReduced X] :
    f.ker = vanishingIdeal (Closeds.closure (Set.range f.base)) := by
  rw [← map_bot, ← nilradical_eq_bot (X := X), ← vanishingIdeal_top, map_vanishingIdeal]
  congr 1
  simp [Set.image_univ]

theorem ker_point_eq {k : Type u} [Field k] {X : Scheme.{u}} (p : Spec (CommRingCat.of k) ⟶ X)
    (hp : IsClosed ({p.base (IsLocalRing.closedPoint k)} : Set X)) :
    p.ker = vanishingIdeal ⟨{p.base (IsLocalRing.closedPoint k)}, hp⟩ := by
  rw [ker_eq_vanishingIdeal_of_isReduced]
  congr 1
  apply Closeds.ext
  show closure (Set.range p.base) = {p.base (IsLocalRing.closedPoint k)}
  have : Set.range p.base = {p.base (IsLocalRing.closedPoint k)} := by
    ext y
    constructor
    · rintro ⟨a, rfl⟩; obtain rfl : a = IsLocalRing.closedPoint k := Subsingleton.elim _ _; rfl
    · rintro rfl; exact ⟨_, rfl⟩
  rw [this, hp.closure_eq]

theorem support_vanishingIdeal_of_singleton {X : Scheme.{u}} (x : X) (hx : IsClosed ({x} : Set X)) :
    ((vanishingIdeal ⟨{x}, hx⟩).support : Set X) = {x} := by
  rw [coe_support_vanishingIdeal]
  rfl

theorem mul_eq_inf_of_disjoint_support {X : Scheme.{u}} (I J : X.IdealSheafData)
    (h : Disjoint (I.support : Set X) (J.support : Set X)) : I * J = I ⊓ J := by
  have hsup : I ⊔ J = ⊤ := by
    rw [← support_eq_bot_iff, support_sup]
    apply Closeds.ext
    show (I.support : Set X) ∩ (J.support : Set X) = ∅
    exact h.inter_eq
  apply IdealSheafData.ext
  funext U
  rw [ideal_mul, Pi.mul_apply, ideal_inf, Pi.inf_apply]
  apply Ideal.mul_eq_inf_of_isCoprime
  rw [Ideal.isCoprime_iff_sup_eq]
  have := congrArg (fun K : X.IdealSheafData => K.ideal U) hsup
  simpa [ideal_sup] using this

theorem comap_pow {X Y : Scheme.{u}} (I : Y.IdealSheafData) (f : X ⟶ Y) (n : ℕ) :
    (I ^ n).comap f = (I.comap f) ^ n := by
  induction n with
  | zero => rw [pow_zero, pow_zero, one_eq_top, one_eq_top, comap_top]
  | succ n ih => rw [pow_succ, comap_mul, ih, pow_succ]

theorem eq_of_base_eq {k : Type u} [Field k] {X : Scheme.{u}} (x : X ⟶ Spec (CommRingCat.of k))
    (p p' : Spec (CommRingCat.of k) ⟶ X) (hp : p ≫ x = 𝟙 _) (hp' : p' ≫ x = 𝟙 _)
    (h : p.base (IsLocalRing.closedPoint k) = p'.base (IsLocalRing.closedPoint k)) : p = p' := by
  haveI : IsClosedImmersion p' := isClosedImmersion_of_comp_eq_id _ _ hp'
  haveI : IsClosedImmersion (pullback.fst p p') := MorphismProperty.pullback_fst _ _ inferInstance
  haveI : Surjective (pullback.fst p p') := ⟨by
    intro a
    obtain rfl : a = IsLocalRing.closedPoint k := Subsingleton.elim _ _
    have : IsLocalRing.closedPoint k ∈ Set.range (pullback.fst p p').base := by
      rw [Pullback.range_fst]; exact ⟨IsLocalRing.closedPoint k, h.symm⟩
    exact this⟩
  haveI : IsIso (pullback.fst p p') := isIso_of_isClosedImmersion_of_surjective _
  have he : inv (pullback.fst p p') ≫ pullback.snd p p' = 𝟙 _ := by
    have h1 : (inv (pullback.fst p p') ≫ pullback.snd p p') ≫ (p' ≫ x) = 𝟙 _ := by
      rw [Category.assoc, ← pullback.condition_assoc, IsIso.inv_hom_id_assoc, hp]
    rwa [hp', Category.comp_id] at h1
  calc p = inv (pullback.fst p p') ≫ pullback.fst p p' ≫ p := by rw [IsIso.inv_hom_id_assoc]
    _ = inv (pullback.fst p p') ≫ pullback.snd p p' ≫ p' := by rw [pullback.condition]
    _ = p' := by rw [← Category.assoc, he, Category.id_comp]

end AlgebraicGeometry.N10Impl

end

open AlgebraicGeometry.N10Impl _root_.AlgebraicGeometry.Scheme.IdealSheafData TopologicalSpace in
theorem solution
    (R : Type u) [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R)) [IsSeparated c]
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c)
    {ρ : ℕ} (E : RelEffCartierDiv c ρ (𝟙 (Spec (CommRingCat.of R))))
    (r r' d : ℕ) {W : Scheme.{u}} (w : W ⟶ pullback c (𝟙 (Spec (CommRingCat.of R)))) [IsClosedImmersion w]
    [IsFinite (w ≫ pullback.snd c (𝟙 _))] [Flat (w ≫ pullback.snd c (𝟙 _))] [Etale (w ≫ pullback.snd c (𝟙 _))]
    (hEI : E.I = (sectionIdeal c ε (𝟙 _)) ^ r * w.ker ^ r')
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (s : Spec (CommRingCat.of Ω) ⟶ Spec (CommRingCat.of R))
    (q : Fin d → {p : Spec (CommRingCat.of Ω) ⟶ pullback c s // p ≫ pullback.snd c s = 𝟙 _})
    (hqinj : Function.Injective (fun m => (q m).1))
    (hqW : ∀ m, ∃ y : Spec (CommRingCat.of Ω) ⟶ W, (q m).1 ≫ mapOnProdOver c s (Category.comp_id s) = y ≫ w)
    (hqall : ∀ y : Spec (CommRingCat.of Ω) ⟶ W, y ≫ w ≫ pullback.snd c (𝟙 _) = s →
      ∃ m, (q m).1 ≫ mapOnProdOver c s (Category.comp_id s) = y ≫ w)
    (pε : {p : Spec (CommRingCat.of Ω) ⟶ pullback c s // p ≫ pullback.snd c s = 𝟙 _})
    (hpε : pε.1 ≫ pullback.fst c s = s ≫ ε.1) :
    Nonempty ((E.pullbackAlong s (Category.comp_id s)).lineBundle ≅
      ((pε.1.ker) ^ r * (∏ m, (q m).1.ker) ^ r').invModule) := by
  classical
  let φ := mapOnProdOver c s (Category.comp_id s)

  haveI : IsSeparated (pullback.snd c (𝟙 (Spec (CommRingCat.of R)))) :=
    MorphismProperty.pullback_snd (P := @IsSeparated) _ _ inferInstance
  haveI : IsClosedImmersion (rigSection c (𝟙 _) ε ≫ pullback.snd c (𝟙 (Spec (CommRingCat.of R)))) := by
    rw [show rigSection c (𝟙 _) ε ≫ pullback.snd c (𝟙 (Spec (CommRingCat.of R))) = 𝟙 _ from pullback.lift_snd _ _ _]
    infer_instance
  haveI : IsClosedImmersion (rigSection c (𝟙 _) ε) := IsClosedImmersion.of_comp (rigSection c (𝟙 _) ε)
    (pullback.snd c (𝟙 (Spec (CommRingCat.of R))))

  have hsq : IsPullback pε.1 s φ (rigSection c (𝟙 _) ε) := by
    refine IsPullback.of_right (h₁₂ := pullback.snd c s) (v₁₃ := s) (h₂₂ := pullback.snd c (𝟙 _)) ?_ ?_
      (isPullback_mapOnProdOver c s (Category.comp_id s)).flip
    · rw [pε.2, show rigSection c (𝟙 _) ε ≫ pullback.snd c (𝟙 (Spec (CommRingCat.of R))) = 𝟙 _ from
        pullback.lift_snd _ _ _]
      exact IsPullback.of_horiz_isIso ⟨by simp⟩
    · apply pullback.hom_ext
      · rw [Category.assoc, mapOnProdOver_fst, hpε, Category.assoc]
        show _ = s ≫ pullback.lift _ _ _ ≫ pullback.fst _ _
        rw [pullback.lift_fst, Category.id_comp]
      · rw [Category.assoc, mapOnProdOver_snd, ← Category.assoc, pε.2, Category.id_comp, Category.assoc]
        show _ = s ≫ pullback.lift _ _ _ ≫ pullback.snd _ _
        rw [pullback.lift_snd, Category.comp_id]
  have h1 : (sectionIdeal c ε (𝟙 _)).comap φ = pε.1.ker := by
    show (rigSection c (𝟙 _) ε).ker.comap φ = pε.1.ker
    rw [← ker_fst_of_isClosedImmersion (rigSection c (𝟙 _) ε) φ,
      show pε.1 = hsq.isoPullback.hom ≫ pullback.fst φ (rigSection c (𝟙 _) ε) from (hsq.isoPullback_hom_fst).symm,
      Scheme.Hom.ker_comp_of_isIso]

  have h2 : w.ker.comap φ = ∏ m, (q m).1.ker := by
    rw [← ker_fst_of_isClosedImmersion w φ]
    set g := pullback.fst φ w with hg
    haveI : IsClosedImmersion g := MorphismProperty.pullback_fst (P := @IsClosedImmersion) _ _ inferInstance

    have sqW : IsPullback (pullback.snd φ w) (g ≫ pullback.snd c s) (w ≫ pullback.snd c (𝟙 _)) s :=
      (IsPullback.of_hasPullback φ w).flip.paste_vert (isPullback_mapOnProdOver c s (Category.comp_id s))
    haveI : Etale (g ≫ pullback.snd c s) := MorphismProperty.of_isPullback (P := @Etale) sqW inferInstance
    haveI : IsReduced (pullback φ w) := AlgebraicGeometry.isReduced_of_etale (g ≫ pullback.snd c s)

    have hsec_closed : ∀ (p : Spec (CommRingCat.of Ω) ⟶ pullback c s), p ≫ pullback.snd c s = 𝟙 _ →
        IsClosed ({p.base (IsLocalRing.closedPoint Ω)} : Set ↥(pullback c s)) := by
      intro p hp
      haveI : IsClosedImmersion p := isClosedImmersion_of_comp_eq_id _ _ hp
      have : Set.range p.base = {p.base (IsLocalRing.closedPoint Ω)} := by
        ext y; constructor
        · rintro ⟨a, rfl⟩; obtain rfl : a = IsLocalRing.closedPoint Ω := Subsingleton.elim _ _; rfl
        · rintro rfl; exact ⟨_, rfl⟩
      rw [← this]; exact p.isClosedEmbedding.isClosed_range

    have hrange : Set.range g.base = ⋃ m, {(q m).1.base (IsLocalRing.closedPoint Ω)} := by
      apply le_antisymm
      · rintro _ ⟨z, rfl⟩

        haveI : IsFinite (g ≫ pullback.snd c s) := MorphismProperty.of_isPullback (P := @IsFinite) sqW inferInstance
        haveI : JacobsonSpace ↥(pullback φ w) := LocallyOfFiniteType.jacobsonSpace (g ≫ pullback.snd c s)
        have hPfin : (Set.univ : Set ↥(pullback φ w)).Finite := by
          have := (g ≫ pullback.snd c s).finite_preimage_singleton (IsLocalRing.closedPoint Ω)
          refine this.subset fun x _ => ?_
          show (g ≫ pullback.snd c s).base x ∈ ({IsLocalRing.closedPoint Ω} : Set _)
          exact Subsingleton.elim (α := ↥(Spec (CommRingCat.of Ω))) _ _
        have hzc : IsClosed ({z} : Set ↥(pullback φ w)) := by
          have hcl : IsClosed (closedPoints ↥(pullback φ w)) := by
            rw [← Set.biUnion_of_singleton (closedPoints ↥(pullback φ w))]
            exact (hPfin.subset (Set.subset_univ _)).isClosed_biUnion fun x hx => hx
          have hall : closedPoints ↥(pullback φ w) = Set.univ := by
            rw [← hcl.closure_eq]; exact closure_closedPoints
          have : z ∈ closedPoints ↥(pullback φ w) := hall ▸ Set.mem_univ z
          exact this
        let yP : Spec (CommRingCat.of Ω) ⟶ pullback φ w := pointOfClosedPoint (g ≫ pullback.snd c s) z hzc
        have hyP : yP ≫ g ≫ pullback.snd c s = 𝟙 _ := pointOfClosedPoint_comp _ _ _
        have hyPz : ∀ a, yP.base a = z := fun a => pointOfClosedPoint_apply _ _ _ a

        obtain ⟨m, hm⟩ := hqall (yP ≫ pullback.snd φ w) (by
          rw [Category.assoc, ← pullback.condition_assoc]
          show yP ≫ g ≫ mapOnProdOver c s (Category.comp_id s) ≫ pullback.snd c (𝟙 _) = s
          rw [mapOnProdOver_snd, reassoc_of% hyP])
        have hqm : (q m).1 = yP ≫ g := by
          apply (isPullback_mapOnProdOver c s (Category.comp_id s)).hom_ext
          · show (q m).1 ≫ φ = (yP ≫ g) ≫ φ
            rw [hm, Category.assoc, Category.assoc, hg, pullback.condition]
          · rw [(q m).2, Category.assoc, hyP]
        refine Set.mem_iUnion.mpr ⟨m, ?_⟩
        show g.base z ∈ ({(q m).1.base (IsLocalRing.closedPoint Ω)} : Set _)
        rw [hqm]
        show g.base z = (yP ≫ g).base (IsLocalRing.closedPoint Ω)
        show g.base z = g.base (yP.base (IsLocalRing.closedPoint Ω))
        rw [hyPz]
      · rintro _ ⟨_, ⟨m, rfl⟩, hx⟩
        rw [Set.mem_singleton_iff] at hx; subst hx
        obtain ⟨y, hy⟩ := hqW m
        exact ⟨(pullback.lift (q m).1 y hy).base (IsLocalRing.closedPoint Ω), by
          show (pullback.lift (q m).1 y hy ≫ g).base _ = _; rw [pullback.lift_fst]⟩

    have hqc : ∀ m, IsClosed ({(q m).1.base (IsLocalRing.closedPoint Ω)} : Set ↥(pullback c s)) :=
      fun m => hsec_closed _ (q m).2
    have hker : ∀ m, (q m).1.ker = vanishingIdeal ⟨{(q m).1.base (IsLocalRing.closedPoint Ω)}, hqc m⟩ :=
      fun m => ker_point_eq (q m).1 (hqc m)
    have hsupp : ∀ m, (((q m).1.ker).support : Set ↥(pullback c s)) = {(q m).1.base (IsLocalRing.closedPoint Ω)} :=
      fun m => by rw [hker]; exact support_vanishingIdeal_of_singleton _ _
    have hpt_inj : Function.Injective fun m => (q m).1.base (IsLocalRing.closedPoint Ω) := by
      intro m m' h
      exact hqinj (eq_of_base_eq (pullback.snd c s) _ _ (q m).2 (q m').2 h)
    have key : ∀ sset : Finset (Fin d),
        (∏ m ∈ sset, (q m).1.ker) = ⨅ m ∈ sset, (q m).1.ker ∧
          ((∏ m ∈ sset, (q m).1.ker).support : Set ↥(pullback c s)) =
            ⋃ m ∈ sset, {(q m).1.base (IsLocalRing.closedPoint Ω)} := by
      intro sset
      induction sset using Finset.induction_on with
      | empty => simp [support_top]
      | insert a sset ha ih =>
        obtain ⟨ih1, ih2⟩ := ih
        rw [Finset.prod_insert ha]
        have hdisj : Disjoint (((q a).1.ker).support : Set ↥(pullback c s))
            (((∏ m ∈ sset, (q m).1.ker).support : Set ↥(pullback c s))) := by
          rw [hsupp, ih2, Set.disjoint_singleton_left]
          simp only [Set.mem_iUnion, Set.mem_singleton_iff, not_exists]
          intro m hm h
          exact ha (hpt_inj h ▸ hm)
        refine ⟨?_, ?_⟩
        · rw [mul_eq_inf_of_disjoint_support _ _ hdisj, ih1, Finset.iInf_insert]
        · rw [support_mul]
          show (((q a).1.ker).support : Set ↥(pullback c s)) ∪ ((∏ m ∈ sset, (q m).1.ker).support : Set _) = _
          rw [hsupp, ih2, Finset.set_biUnion_insert]
    obtain ⟨k1, -⟩ := key Finset.univ
    rw [k1, ker_eq_vanishingIdeal_of_isReduced g]
    simp only [Finset.mem_univ, iInf_true, hker]
    rw [← vanishingIdeal_iSup]
    congr 1
    apply Closeds.ext
    show closure (Set.range g.base) = (↑(⨆ m, (⟨{(q m).1.base (IsLocalRing.closedPoint Ω)}, hqc m⟩ : Closeds ↥(pullback c s))) : Set _)
    rw [g.isClosedEmbedding.isClosed_range.closure_eq, hrange, ← Finset.sup_univ_eq_iSup, Closeds.coe_finset_sup]
    ext y
    simp only [Finset.sup_set_eq_biUnion, Set.mem_iUnion]
    constructor
    · rintro ⟨m, hm⟩; exact ⟨m, Finset.mem_univ m, hm⟩
    · rintro ⟨m, -, hm⟩; exact ⟨m, hm⟩

  have hI : E.I.comap φ = (pε.1.ker) ^ r * (∏ m, (q m).1.ker) ^ r' := by
    rw [hEI, comap_mul, comap_pow, comap_pow, h1, h2]
  exact ⟨eqToIso (by show (E.I.comap φ).invModule = _; rw [hI])⟩

end S_AlgebraicGeometry_RelEffCartierDiv_nonempty_lineBundle_pullbackAlong_iso_invModule_pow_ker_mul_pow_prod_ker
end P2MW
export P2MW.S_AlgebraicGeometry_RelEffCartierDiv_nonempty_lineBundle_pullbackAlong_iso_invModule_pow_ker_mul_pow_prod_ker (solution)

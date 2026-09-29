-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.exists_forall_app_eq_app_of_isCompact_of_isDirectLimit_of_isPullback
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/6abd2416-6539-586b-b8a2-1e87bb4afd30

import Mathlib
import Definitions.Def_Mathlib_Algebra_IsDirectLimit
import Theorems.Thm_AlgebraicGeometry_Scheme_exists_app_eq_app_of_isCompact_of_isDirectLimit
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_exists_forall_app_eq_app_of_isCompact_of_isDirectLimit_of_isPullback
p2m_attr_erase "instance" "TwoChartCech.Sections.M0_moduleA TwoChartCech.Sections.M1_module TwoChartCech.Cover.A01_algebra TwoChartCech.Cover.A0_algebra TwoChartCech.Cover.A1_commRing TwoChartCech.Cover.A1_algebra TwoChartCech.Sections.M01_module TwoChartCech.Sections.M0_addCommGroup TwoChartCech.Sections.M0_tower TwoChartCech.Sections.M01_addCommGroup TwoChartCech.Cover.A0_commRing TwoChartCech.Sections.M1_tower TwoChartCech.Sections.M01_moduleA TwoChartCech.Sections.M0_module TwoChartCech.Sections.M1_moduleA TwoChartCech.Sections.M1_addCommGroup TwoChartCech.Cover.A01_commRing TwoChartCech.Sections.M01_tower CoherentBaseChange.TwoTermComplex.C0_module CoherentBaseChange.TwoTermComplex.C0_addCommGroup CoherentBaseChange.TwoTermComplex.C1_module CoherentBaseChange.TwoTermComplex.C1_addCommGroup CoherentBaseChange.TwoTermComplex.C0_free CoherentBaseChange.TwoTermComplex.C1_finite CoherentBaseChange.TwoTermComplex.C0_finite CoherentBaseChange.TwoTermComplex.C1_free"
p2m_attr_erase "simp" "AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.sizeOf_spec AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U1 AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U0 TwoChartCech.Sections.mk.injEq TwoChartCech.Cover.mk.injEq TwoChartCech.GrothendieckComplex.mk.injEq TwoChartCech.Sections.mk.sizeOf_spec TwoChartCech.Cover.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r0_apply TwoChartCech.GrothendieckComplex.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r1_apply CoherentBaseChange.TwoTermComplex.mk.sizeOf_spec CoherentBaseChange.TwoTermComplex.mk.injEq"

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite

universe u

namespace FunFamilyAgree

theorem exists_ge_forall {ι : Type u} [Preorder ι] [Nonempty ι] [IsDirected ι (· ≤ ·)] {κ : Type u} [Finite κ]
    (j : ι) (f : κ → ι) : ∃ m, j ≤ m ∧ ∀ k, f k ≤ m := by
  classical
  haveI := Fintype.ofFinite κ
  obtain ⟨m, hm⟩ := Finset.exists_le (insert j (Finset.univ.image f))
  exact ⟨m, hm _ (Finset.mem_insert_self _ _), fun k => hm _ (Finset.mem_insert_of_mem (Finset.mem_image_of_mem f (Finset.mem_univ k)))⟩

end FunFamilyAgree

open FunFamilyAgree in
theorem solution
    {ι : Type u} [Preorder ι] [Nonempty ι] [IsDirected ι (· ≤ ·)]
    {G : ι → Type u} [∀ i, CommRing (G i)] (φ : ∀ i j : ι, i ≤ j → G i →+* G j)
    [DirectedSystem G fun i j h => ⇑(φ i j h)]
    {R : Type u} [CommRing R] (g : ∀ i, G i →+* R)
    (hR : IsDirectLimit (fun i j h => ⇑(φ i j h)) fun i => ⇑(g i))
    (i : ι) {X : Scheme.{u}} (fX : X ⟶ Spec (CommRingCat.of (G i))) [QuasiCompact fX] [QuasiSeparated fX]
    {XR : Scheme.{u}} (p : XR ⟶ X) (q : XR ⟶ Spec (CommRingCat.of R))
    (hp : IsPullback p q fX (Spec.map (CommRingCat.ofHom (g i))))
    (j : ι) (hij : i ≤ j)
    {κ : Type u} [Finite κ] (W : κ → X.Opens) (hW : ∀ k, IsCompact (W k : Set X))
    (t t' : ∀ k, Γ(Limits.pullback fX (Spec.map (CommRingCat.ofHom (φ i j hij))),
      (Limits.pullback.fst fX (Spec.map (CommRingCat.ofHom (φ i j hij)))) ⁻¹ᵁ W k))
    (h : ∀ (c : XR ⟶ Limits.pullback fX (Spec.map (CommRingCat.ofHom (φ i j hij)))),
      c ≫ Limits.pullback.fst fX (Spec.map (CommRingCat.ofHom (φ i j hij))) = p →
      c ≫ Limits.pullback.snd fX (Spec.map (CommRingCat.ofHom (φ i j hij))) = q ≫ Spec.map (CommRingCat.ofHom (g j)) →
      ∀ k, c.app ((Limits.pullback.fst fX (Spec.map (CommRingCat.ofHom (φ i j hij)))) ⁻¹ᵁ W k) (t k) =
        c.app ((Limits.pullback.fst fX (Spec.map (CommRingCat.ofHom (φ i j hij)))) ⁻¹ᵁ W k) (t' k)) :
    ∃ (j' : ι) (hjj' : j ≤ j'),
      ∀ (c' : Limits.pullback fX (Spec.map (CommRingCat.ofHom (φ i j' (hij.trans hjj')))) ⟶
          Limits.pullback fX (Spec.map (CommRingCat.ofHom (φ i j hij)))),
        c' ≫ Limits.pullback.fst fX (Spec.map (CommRingCat.ofHom (φ i j hij))) =
          Limits.pullback.fst fX (Spec.map (CommRingCat.ofHom (φ i j' (hij.trans hjj')))) →
        c' ≫ Limits.pullback.snd fX (Spec.map (CommRingCat.ofHom (φ i j hij))) =
          Limits.pullback.snd fX (Spec.map (CommRingCat.ofHom (φ i j' (hij.trans hjj')))) ≫ Spec.map (CommRingCat.ofHom (φ j j' hjj')) →
        ∀ k, c'.app ((Limits.pullback.fst fX (Spec.map (CommRingCat.ofHom (φ i j hij)))) ⁻¹ᵁ W k) (t k) =
          c'.app ((Limits.pullback.fst fX (Spec.map (CommRingCat.ofHom (φ i j hij)))) ⁻¹ᵁ W k) (t' k) := by
  classical

  have h₀ : ∀ k, ∀ (c : Limits.pullback fX (Spec.map (CommRingCat.ofHom (g i))) ⟶ (Limits.pullback fX (Spec.map (CommRingCat.ofHom (φ i j hij))))),
      c ≫ (Limits.pullback.fst fX (Spec.map (CommRingCat.ofHom (φ i j hij)))) = Limits.pullback.fst fX (Spec.map (CommRingCat.ofHom (g i))) →
      c ≫ Limits.pullback.snd fX (Spec.map (CommRingCat.ofHom (φ i j hij))) =
        Limits.pullback.snd fX (Spec.map (CommRingCat.ofHom (g i))) ≫ Spec.map (CommRingCat.ofHom (g j)) →
      c.app ((Limits.pullback.fst fX (Spec.map (CommRingCat.ofHom (φ i j hij)))) ⁻¹ᵁ W k) (t k) = c.app ((Limits.pullback.fst fX (Spec.map (CommRingCat.ofHom (φ i j hij)))) ⁻¹ᵁ W k) (t' k) := by
    intro k c hc1 hc2
    have E := h (hp.isoPullback.hom ≫ c) (by rw [Category.assoc, hc1, hp.isoPullback_hom_fst])
      (by rw [Category.assoc, hc2, ← Category.assoc, hp.isoPullback_hom_snd]) k
    rw [Scheme.Hom.comp_app] at E
    change hp.isoPullback.hom.app _ (c.app _ (t k)) = hp.isoPullback.hom.app _ (c.app _ (t' k)) at E
    exact (ConcreteCategory.bijective_of_isIso (hp.isoPullback.hom.app _)).1 E

  have step := fun k => AlgebraicGeometry.Scheme.exists_app_eq_app_of_isCompact_of_isDirectLimit φ g hR i fX (W k) (hW k) j hij
    (t k) (t' k) (h₀ k)
  choose jk hjk hk using step
  obtain ⟨j', hjj', hk'⟩ := exists_ge_forall j jk
  refine ⟨j', hjj', fun c' hc'1 hc'2 k => ?_⟩

  have ecomp : (φ (jk k) j' (hk' k)).comp (φ j (jk k) (hjk k)) = φ j j' hjj' :=
    RingHom.ext fun x => DirectedSystem.map_map (f := fun i j h => ⇑(φ i j h)) (hjk k) (hk' k) x
  have ecomp' : (φ (jk k) j' (hk' k)).comp (φ i (jk k) (hij.trans (hjk k))) = φ i j' (hij.trans hjj') :=
    RingHom.ext fun x => DirectedSystem.map_map (f := fun i j h => ⇑(φ i j h)) (hij.trans (hjk k)) (hk' k) x
  let d : Limits.pullback fX (Spec.map (CommRingCat.ofHom (φ i j' (hij.trans hjj')))) ⟶
      Limits.pullback fX (Spec.map (CommRingCat.ofHom (φ i (jk k) (hij.trans (hjk k))))) :=
    Limits.pullback.lift (Limits.pullback.fst fX _)
      (Limits.pullback.snd fX _ ≫ Spec.map (CommRingCat.ofHom (φ (jk k) j' (hk' k))))
      (by rw [Limits.pullback.condition, Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ecomp'])
  let ck : Limits.pullback fX (Spec.map (CommRingCat.ofHom (φ i (jk k) (hij.trans (hjk k))))) ⟶ (Limits.pullback fX (Spec.map (CommRingCat.ofHom (φ i j hij)))) :=
    Limits.pullback.lift (Limits.pullback.fst fX _)
      (Limits.pullback.snd fX _ ≫ Spec.map (CommRingCat.ofHom (φ j (jk k) (hjk k))))
      (by
        rw [Limits.pullback.condition, Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
        exact congrArg (fun r => Limits.pullback.snd fX _ ≫ Spec.map (CommRingCat.ofHom r))
          (RingHom.ext fun x => (DirectedSystem.map_map (f := fun i j h => ⇑(φ i j h)) hij (hjk k) x).symm))
  have hc' : c' = d ≫ ck := by
    apply Limits.pullback.hom_ext
    · rw [hc'1, Category.assoc, Limits.pullback.lift_fst, Limits.pullback.lift_fst]
    · rw [hc'2, Category.assoc, Limits.pullback.lift_snd, ← Category.assoc, Limits.pullback.lift_snd, Category.assoc,
        ← Spec.map_comp, ← CommRingCat.ofHom_comp, ecomp]
  subst hc'
  rw [Scheme.Hom.comp_app]
  change d.app _ (ck.app _ (t k)) = d.app _ (ck.app _ (t' k))
  rw [hk k ck (Limits.pullback.lift_fst _ _ _) (Limits.pullback.lift_snd _ _ _)]

end S_AlgebraicGeometry_Scheme_exists_forall_app_eq_app_of_isCompact_of_isDirectLimit_of_isPullback
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_exists_forall_app_eq_app_of_isCompact_of_isDirectLimit_of_isPullback (solution)

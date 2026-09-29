-- Prove2me | solution 1 for AlgebraicGeometry.geometricallyConnected_of_bijective_algebraMap_sections
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/3c40583a-ec9e-5f4f-8908-d9ecebe7f3ab

import Mathlib
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_geometricallyConnected_of_bijective_algebraMap_sections

set_option autoImplicit false

universe u

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry P2MW.S_AlgebraicGeometry_geometricallyConnected_of_bijective_algebraMap_sections.AlgebraicGeometry Opposite TopologicalSpace"

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Spec IsIntegral Scheme geometrically_iff_of_commRing_of_isClosedUnderIsomorphisms GeometricallyConnected IsIntegral.of_isIso Scheme.TwoAffineOpenCover Scheme.TwoAffineOpenCover.specMap Scheme.TwoAffineOpenCover.algebraOfHom"
namespace Ws35Q1
p2m_open "AlgebraicGeometry"

theorem connectedSpace_of_forall_isIdempotentElem {X : Scheme.{u}} [Nontrivial Γ(X, ⊤)]
    (h : ∀ e : Γ(X, ⊤), IsIdempotentElem e → e = 0 ∨ e = 1) : ConnectedSpace X := by
  classical
  rw [connectedSpace_iff_clopen]
  refine ⟨?_, fun s hs => ?_⟩
  · by_contra hX
    haveI : IsEmpty X := not_nonempty_iff.mp hX
    have htop : (⊤ : X.Opens) = ⊥ := le_bot_iff.mp fun x _ => (IsEmpty.false x).elim
    haveI : Subsingleton Γ(X, ⊤) :=
      CommRingCat.subsingleton_of_isTerminal (X.sheaf.isTerminalOfEqEmpty htop)
    exact false_of_nontrivial_of_subsingleton Γ(X, ⊤)
  · let U : X.Opens := ⟨s, hs.isOpen⟩
    let V : X.Opens := ⟨sᶜ, hs.compl.isOpen⟩
    have hUV : U ⊓ V = ⊥ := TopologicalSpace.Opens.ext (Set.inter_compl_self s)
    have htop : U ⊔ V = ⊤ := by
      ext x
      simp only [Opens.coe_sup, Set.mem_union, Opens.coe_top, Set.mem_univ, iff_true]
      exact em (x ∈ s)
    have hsub : Subsingleton (X.sheaf.1.obj (op (U ⊓ V))) :=
      CommRingCat.subsingleton_of_isTerminal (X.sheaf.isTerminalOfEqEmpty hUV)

    let e' : Γ(X, U ⊔ V) := (X.sheaf.objSupIsoProdEqLocus U V).inv ⟨(1, 0), hsub.elim _ _⟩
    have he'U : X.presheaf.map (homOfLE le_sup_left).op e' = 1 :=
      X.sheaf.objSupIsoProdEqLocus_inv_fst U V _
    have he'V : X.presheaf.map (homOfLE le_sup_right).op e' = 0 :=
      X.sheaf.objSupIsoProdEqLocus_inv_snd U V _

    let ι : Γ(X, U ⊔ V) →+* Γ(X, ⊤) := (X.presheaf.map (eqToHom htop.symm).op).hom
    let π : Γ(X, ⊤) →+* Γ(X, U ⊔ V) := (X.presheaf.map (eqToHom htop).op).hom
    have hπι : ∀ z, π (ι z) = z := by
      intro z
      show (X.presheaf.map (eqToHom htop.symm).op ≫ X.presheaf.map (eqToHom htop).op) z = z
      rw [← X.presheaf.map_comp, ← op_comp, eqToHom_trans, eqToHom_refl, op_id, X.presheaf.map_id]
      rfl
    have hidem : IsIdempotentElem e' := by

      apply X.sheaf.eq_of_locally_eq₂ (homOfLE (le_sup_left : U ≤ U ⊔ V)) (homOfLE (le_sup_right : V ≤ U ⊔ V)) le_rfl
      · have := RingHom.map_mul (X.presheaf.map (homOfLE (le_sup_left : U ≤ U ⊔ V)).op).hom e' e'
        refine this.trans ?_
        change X.presheaf.map (homOfLE le_sup_left).op e' * X.presheaf.map (homOfLE le_sup_left).op e' =
          X.presheaf.map (homOfLE le_sup_left).op e'
        rw [he'U, mul_one]
      · have := RingHom.map_mul (X.presheaf.map (homOfLE (le_sup_right : V ≤ U ⊔ V)).op).hom e' e'
        refine this.trans ?_
        change X.presheaf.map (homOfLE le_sup_right).op e' * X.presheaf.map (homOfLE le_sup_right).op e' =
          X.presheaf.map (homOfLE le_sup_right).op e'
        rw [he'V, mul_zero]
    have hcases : e' = 0 ∨ e' = 1 := by
      rcases h (ι e') (hidem.map ι) with h0 | h1
      · left; rw [← hπι e', h0, map_zero]
      · right; rw [← hπι e', h1, map_one]
    rcases hcases with h0 | h1
    ·
      left
      by_contra hne
      obtain ⟨x, hx⟩ := Set.nonempty_iff_ne_empty.mpr hne
      haveI : Nonempty U := ⟨⟨x, hx⟩⟩
      have : (1 : Γ(X, U)) = 0 := by rw [← he'U, h0, map_zero]
      exact one_ne_zero this
    ·
      right
      by_contra hne
      obtain ⟨x, hx⟩ := (Set.ne_univ_iff_exists_notMem s).mp hne
      haveI : Nonempty V := ⟨⟨x, hx⟩⟩
      have : (0 : Γ(X, V)) = 1 := by rw [← he'V, h1, map_one]
      exact zero_ne_one this

theorem connectedSpace_of_bijective {K : Type u} [Field K] {X : Scheme.{u}} (φ : K →+* Γ(X, ⊤))
    (hφ : Function.Bijective φ) : ConnectedSpace X := by
  haveI : Nontrivial Γ(X, ⊤) := hφ.1.nontrivial
  refine connectedSpace_of_forall_isIdempotentElem fun e he => ?_
  obtain ⟨l, rfl⟩ := hφ.2 e
  have hl : IsIdempotentElem l := by
    apply hφ.1
    rw [map_mul]; exact he
  rcases IsIdempotentElem.iff_eq_zero_or_one.mp hl with rfl | rfl
  · left; exact map_zero φ
  · right; exact map_one φ

scoped instance isClosedUnderIsomorphisms_isIntegral :
    ObjectProperty.IsClosedUnderIsomorphisms (C := Scheme.{u}) (fun X : Scheme.{u} => IsIntegral X) :=
  ⟨fun e h => by haveI := h; exact IsIntegral.of_isIso e.hom⟩

end AlgebraicGeometry.Ws35Q1
p2m_reactivate "P2MW.S_AlgebraicGeometry_geometricallyConnected_of_bijective_algebraMap_sections.AlgebraicGeometry P2MW.S_AlgebraicGeometry_geometricallyConnected_of_bijective_algebraMap_sections.AlgebraicGeometry.Ws35Q1"
p2m_reactivate "P2MW.S_AlgebraicGeometry_geometricallyConnected_of_bijective_algebraMap_sections.AlgebraicGeometry"

open AlgebraicGeometry.Ws35Q1 in
theorem solution
    {R : Type u} [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
    (hH0 : ∀ (A : Type u) [CommRing A] [Algebra R A],
      letI := Scheme.TwoAffineOpenCover.algebraOfHom
        (Limits.pullback.snd c (Scheme.TwoAffineOpenCover.specMap R A)) ⊤
      Function.Bijective (algebraMap A Γ(Limits.pullback c (Scheme.TwoAffineOpenCover.specMap R A), ⊤))) :
    GeometricallyConnected c := by
  refine ⟨(geometrically_iff_of_commRing_of_isClosedUnderIsomorphisms (P := (ConnectedSpace ·))).mpr ?_⟩
  intro K _ _
  letI := Scheme.TwoAffineOpenCover.algebraOfHom
    (Limits.pullback.snd c (Scheme.TwoAffineOpenCover.specMap R K)) ⊤
  exact connectedSpace_of_bijective (algebraMap K Γ(Limits.pullback c (Scheme.TwoAffineOpenCover.specMap R K), ⊤)) (hH0 K)

end S_AlgebraicGeometry_geometricallyConnected_of_bijective_algebraMap_sections
end P2MW
export P2MW.S_AlgebraicGeometry_geometricallyConnected_of_bijective_algebraMap_sections (solution)

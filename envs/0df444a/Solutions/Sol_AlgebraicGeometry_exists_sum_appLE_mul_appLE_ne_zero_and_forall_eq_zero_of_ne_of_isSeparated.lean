-- Prove2me | solution 1 for AlgebraicGeometry.exists_sum_appLE_mul_appLE_ne_zero_and_forall_eq_zero_of_ne_of_isSeparated
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/b7e59885-19c7-52e3-ad6b-994493c4defa

import Mathlib
import Definitions.Def_CerednikDrinfeld_QMModuli
import Theorems.Thm_AlgebraicGeometry_IsSeparated_isAffineOpen_inf_and_exists_eq_sum_mul_of_isAffineOpen
import Theorems.Thm_AlgebraicGeometry_IsAffineOpen_eq_of_appLE_eq_and_exists_appLE_eq_of_ringHom
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_exists_sum_appLE_mul_appLE_ne_zero_and_forall_eq_zero_of_ne_of_isSeparated

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian CerednikDrinfeld.QM Topology

open scoped TensorProduct

namespace SepAlg29

variable {G : Scheme.{0}} {f : G ⟶ Spec (CommRingCat.of ℂ)}

noncomputable def ev (p : Spec (CommRingCat.of ℂ) ⟶ G) (W : G.Opens) (h : ⊤ ≤ p ⁻¹ᵁ W) : Γ(G, W) →+* ℂ :=
  (p.appLE W ⊤ h ≫ (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom).hom

theorem ev_apply (p : Spec (CommRingCat.of ℂ) ⟶ G) (W : G.Opens) (h : ⊤ ≤ p ⁻¹ᵁ W) (c : Γ(G, W)) :
    ev p W h c = (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom ((p.appLE W ⊤ h) c) := rfl

theorem ev_map (p : Spec (CommRingCat.of ℂ) ⟶ G) {W W' : G.Opens} (e : W ≤ W') (h : ⊤ ≤ p ⁻¹ᵁ W)
    (h' : ⊤ ≤ p ⁻¹ᵁ W') (c : Γ(G, W')) :
    ev p W h (G.presheaf.map (homOfLE e).op c) = ev p W' h' c := by
  simp only [ev_apply]
  congr 1
  change (G.presheaf.map (homOfLE e).op ≫ p.appLE W ⊤ h) c = (p.appLE W' ⊤ h') c
  rw [Scheme.Hom.map_appLE]

theorem ev_comp_const (p : Spec (CommRingCat.of ℂ) ⟶ G) (hp : p ≫ f = 𝟙 _) (W : G.Opens) (h : ⊤ ≤ p ⁻¹ᵁ W) :
    (ev p W h).comp ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv ≫ f.appLE ⊤ W le_top).hom = RingHom.id ℂ := by
  ext a
  change ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv ≫ f.appLE ⊤ W le_top ≫ p.appLE W ⊤ h ≫
    (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom) a = a
  rw [Scheme.Hom.appLE_comp_appLE_assoc]
  have key : ∀ (g : Spec (CommRingCat.of ℂ) ⟶ Spec (CommRingCat.of ℂ)) (hg : g = 𝟙 _)
      (e : (⊤ : (Spec (CommRingCat.of ℂ)).Opens) ≤ g ⁻¹ᵁ ⊤), g.appLE ⊤ ⊤ e = 𝟙 _ := by
    rintro g rfl e
    simp [Scheme.Hom.appLE]
  rw [key (p ≫ f) hp]
  simp

end SepAlg29

open SepAlg29

theorem solution
    {G : Scheme.{0}} {f : G ⟶ Spec (CommRingCat.of ℂ)} [IsSeparated f]
    (x y : SchemeHomOver (𝟙 (Spec (CommRingCat.of ℂ))) f) (hxy : x ≠ y) :
    ∃ (U V : G.Opens) (hx : ⊤ ≤ x.1 ⁻¹ᵁ U) (hy : ⊤ ≤ y.1 ⁻¹ᵁ V) (n : ℕ) (a : Fin n → Γ(G, U)) (b : Fin n → Γ(G, V)),
      (∑ i : Fin n, (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom ((x.1.appLE U ⊤ hx) (a i)) * (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom ((y.1.appLE V ⊤ hy) (b i)) ≠ 0) ∧
      ∀ (P : SchemeHomOver (𝟙 (Spec (CommRingCat.of ℂ))) f) (hPU : ⊤ ≤ P.1 ⁻¹ᵁ U) (hPV : ⊤ ≤ P.1 ⁻¹ᵁ V),
        ∑ i : Fin n, (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom ((P.1.appLE U ⊤ hPU) (a i)) * (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom ((P.1.appLE V ⊤ hPV) (b i)) = 0 := by
  classical

  let pt : ↥(Spec (CommRingCat.of ℂ)) := Classical.arbitrary _
  have hpt : ∀ q : ↥(Spec (CommRingCat.of ℂ)), q = pt := fun q => Subsingleton.elim q pt

  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
    G.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (x.1.base pt)) isOpen_univ
  obtain ⟨_, ⟨V, hV, rfl⟩, hyV, -⟩ :=
    G.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (y.1.base pt)) isOpen_univ
  have hx : ⊤ ≤ x.1 ⁻¹ᵁ U := by rintro q -; show x.1.base q ∈ U; rw [hpt q]; exact hxU
  have hy : ⊤ ≤ y.1 ⁻¹ᵁ V := by rintro q -; show y.1.base q ∈ V; rw [hpt q]; exact hyV

  obtain ⟨hUV, hgen⟩ := AlgebraicGeometry.IsSeparated.isAffineOpen_inf_and_exists_eq_sum_mul_of_isAffineOpen f U V hU hV
  obtain ⟨huniq, hexist⟩ := AlgebraicGeometry.IsAffineOpen.eq_of_appLE_eq_and_exists_appLE_eq_of_ringHom f (U ⊓ V) hUV

  let ρU : Γ(G, U) →+* Γ(G, U ⊓ V) := (G.presheaf.map (homOfLE inf_le_left).op).hom
  let ρV : Γ(G, V) →+* Γ(G, U ⊓ V) := (G.presheaf.map (homOfLE inf_le_right).op).hom
  let δ : Γ(G, U) ⊗[ℤ] Γ(G, V) →ₐ[ℤ] Γ(G, U ⊓ V) :=
    Algebra.TensorProduct.lift ρU.toIntAlgHom ρV.toIntAlgHom (fun _ _ => Commute.all _ _)
  let μ : Γ(G, U) ⊗[ℤ] Γ(G, V) →ₐ[ℤ] ℂ :=
    Algebra.TensorProduct.lift (ev x.1 U hx).toIntAlgHom (ev y.1 V hy).toIntAlgHom (fun _ _ => Commute.all _ _)
  have hδ : ∀ (a : Γ(G, U)) (b : Γ(G, V)), δ (a ⊗ₜ b) = ρU a * ρV b := fun a b =>
    Algebra.TensorProduct.lift_tmul _ _ _ a b
  have hμ : ∀ (a : Γ(G, U)) (b : Γ(G, V)), μ (a ⊗ₜ b) = ev x.1 U hx a * ev y.1 V hy b := fun a b =>
    Algebra.TensorProduct.lift_tmul _ _ _ a b
  have hδsurj : Function.Surjective δ := by
    intro c
    obtain ⟨n, a, b, rfl⟩ := hgen c
    exact ⟨∑ i, a i ⊗ₜ b i, by rw [map_sum]; exact Finset.sum_congr rfl fun i _ => hδ (a i) (b i)⟩

  have key : ∃ t : Γ(G, U) ⊗[ℤ] Γ(G, V), δ t = 0 ∧ μ t ≠ 0 := by
    by_contra hcon
    push_neg at hcon

    have hker : RingHom.ker δ.toRingHom ≤ RingHom.ker μ.toRingHom := fun t ht => hcon t ht
    let ν : Γ(G, U ⊓ V) →+* ℂ :=
      (Ideal.Quotient.lift (RingHom.ker δ.toRingHom) μ.toRingHom hker).comp
        (RingHom.quotientKerEquivOfSurjective hδsurj).symm.toRingHom
    have hνδ : ∀ t, ν (δ t) = μ t := by
      intro t
      show (Ideal.Quotient.lift (RingHom.ker δ.toRingHom) μ.toRingHom hker)
        ((RingHom.quotientKerEquivOfSurjective hδsurj).symm (δ.toRingHom t)) = μ t
      rw [show (RingHom.quotientKerEquivOfSurjective hδsurj).symm (δ.toRingHom t) = Ideal.Quotient.mk _ t from
        (RingHom.quotientKerEquivOfSurjective hδsurj).symm_apply_eq.mpr rfl]
      rfl
    have hνU : ∀ a, ν (ρU a) = ev x.1 U hx a := by
      intro a
      have : ρU a = δ (a ⊗ₜ 1) := by rw [hδ, map_one, mul_one]
      rw [this, hνδ, hμ, map_one, mul_one]
    have hνV : ∀ b, ν (ρV b) = ev y.1 V hy b := by
      intro b
      have : ρV b = δ (1 ⊗ₜ b) := by rw [hδ, map_one, one_mul]
      rw [this, hνδ, hμ, map_one, one_mul]

    have hνconst : ν.comp ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv ≫ f.appLE ⊤ (U ⊓ V) le_top).hom = RingHom.id ℂ := by
      have h1 : ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv ≫ f.appLE ⊤ (U ⊓ V) le_top).hom =
          ρU.comp ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv ≫ f.appLE ⊤ U le_top).hom := by
        change _ = ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv ≫ f.appLE ⊤ U le_top ≫ G.presheaf.map (homOfLE inf_le_left).op).hom
        rw [Scheme.Hom.appLE_map]
      rw [h1, ← RingHom.comp_assoc, show ν.comp ρU = ev x.1 U hx from RingHom.ext hνU]
      exact ev_comp_const x.1 x.2 U hx
    obtain ⟨q, hqf, hq, hqev⟩ := hexist ν hνconst

    have hqU : ⊤ ≤ q ⁻¹ᵁ U := fun z hz => (hq hz).1
    have hqV : ⊤ ≤ q ⁻¹ᵁ V := fun z hz => (hq hz).2
    have hqev' : ev q (U ⊓ V) hq = ν := hqev
    have hqx : q = x.1 := by
      obtain ⟨huU, -⟩ := AlgebraicGeometry.IsAffineOpen.eq_of_appLE_eq_and_exists_appLE_eq_of_ringHom f U hU
      refine huU q x.1 hqf x.2 hqU hx (CommRingCat.hom_ext (RingHom.ext fun a => ?_))
      change ev q U hqU a = ev x.1 U hx a
      rw [← ev_map q inf_le_left hq hqU a, hqev', hνU]
    have hqy : q = y.1 := by
      obtain ⟨huV, -⟩ := AlgebraicGeometry.IsAffineOpen.eq_of_appLE_eq_and_exists_appLE_eq_of_ringHom f V hV
      refine huV q y.1 hqf y.2 hqV hy (CommRingCat.hom_ext (RingHom.ext fun b => ?_))
      change ev q V hqV b = ev y.1 V hy b
      rw [← ev_map q inf_le_right hq hqV b, hqev', hνV]
    exact hxy (Subtype.ext (hqx.symm.trans hqy))

  obtain ⟨t, hδt, hμt⟩ := key
  obtain ⟨S, hS⟩ := TensorProduct.exists_finset t
  have hsumt : ∑ i : Fin S.card, (S.equivFin.symm i).1.1 ⊗ₜ[ℤ] (S.equivFin.symm i).1.2 = t := by
    rw [hS, ← Finset.sum_coe_sort S]
    exact Equiv.sum_comp S.equivFin.symm (fun p : ↥S => p.1.1 ⊗ₜ[ℤ] p.1.2)
  refine ⟨U, V, hx, hy, S.card, fun i => (S.equivFin.symm i).1.1, fun i => (S.equivFin.symm i).1.2, ?_, ?_⟩
  · change ∑ i : Fin S.card, ev x.1 U hx (S.equivFin.symm i).1.1 * ev y.1 V hy (S.equivFin.symm i).1.2 ≠ 0
    have : ∑ i : Fin S.card, ev x.1 U hx (S.equivFin.symm i).1.1 * ev y.1 V hy (S.equivFin.symm i).1.2 = μ t := by
      rw [← hsumt, map_sum]
      exact Finset.sum_congr rfl fun i _ => (hμ _ _).symm
    rw [this]; exact hμt
  · intro P hPU hPV
    have hPUV : ⊤ ≤ P.1 ⁻¹ᵁ (U ⊓ V) := fun z hz => ⟨hPU hz, hPV hz⟩
    change ∑ i : Fin S.card, ev P.1 U hPU (S.equivFin.symm i).1.1 * ev P.1 V hPV (S.equivFin.symm i).1.2 = 0
    have : ∀ (a : Γ(G, U)) (b : Γ(G, V)), ev P.1 U hPU a * ev P.1 V hPV b = ev P.1 (U ⊓ V) hPUV (δ (a ⊗ₜ b)) := by
      intro a b
      rw [hδ, map_mul, ev_map P.1 inf_le_left hPUV hPU, ev_map P.1 inf_le_right hPUV hPV]
    rw [Finset.sum_congr rfl fun i _ => this _ _, ← map_sum, ← map_sum, hsumt, hδt, map_zero]

end S_AlgebraicGeometry_exists_sum_appLE_mul_appLE_ne_zero_and_forall_eq_zero_of_ne_of_isSeparated
end P2MW
export P2MW.S_AlgebraicGeometry_exists_sum_appLE_mul_appLE_ne_zero_and_forall_eq_zero_of_ne_of_isSeparated (solution)

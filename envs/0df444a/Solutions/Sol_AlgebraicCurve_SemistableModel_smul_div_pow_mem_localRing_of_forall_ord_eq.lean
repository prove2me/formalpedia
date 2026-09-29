-- Prove2me | solution 1 for AlgebraicCurve.SemistableModel.smul_div_pow_mem_localRing_of_forall_ord_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/8079477d-1eb7-5526-92a0-2631aca3b32f

import Definitions.Def_AlgebraicCurve_SemistableCharts
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_Repartitions
import Definitions.Def_AlgebraicCurve_SemistableModel
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_SemistableModel_smul_div_pow_mem_localRing_of_forall_ord_eq

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve

universe u u'

set_option maxHeartbeats 3200000 in
theorem solution
    {L : Type u} [Field L] [IsAlgClosed L] {A : ValuationSubring L}
    {F : Type u'} [Field F] [Algebra L F]
    {ιV ιE : Type*} {Fbar : ιV → Type*} [∀ i, Field (Fbar i)] [∀ i, Algebra (IsLocalRing.ResidueField A) (Fbar i)]
    {C : ∀ i, ComponentChart A F (Fbar i)} {An : ιE → Annulus A F} {src tgt : ιE → ιV}
    {xs : ∀ e, Place (IsLocalRing.ResidueField A) (Fbar (src e))}
    {xt : ∀ e, Place (IsLocalRing.ResidueField A) (Fbar (tgt e))}
    (M : SemistableModel A F Fbar C An src tgt xs xt)
    (k : ℕ) (G : Place L F → ℤ) (g : F) (hg : g ≠ 0)
    (hkG : ∀ P : Place L F, P.ord g = (k : ℤ) * G P)
    (r : ℕ) (U : Fin r → M.X.Opens) (h : Fin r → F) (hh : ∀ a, h a ≠ 0)
    (hdiv : ∀ a (P : Place L F), M.pt P ∈ U a → P.ord (h a) = G P)
    (c₀ : L) (hc₀ : c₀ ≠ 0)
    (hunit : ∀ i a, M.gen i ∈ U a →
      c₀ • (g / h a ^ k) ∈ (C i).integers ∧ (c₀ • (g / h a ^ k))⁻¹ ∈ (C i).integers)
    (a : Fin r) (x : M.X) (hx : x ∈ U a) :
    c₀ • (g / h a ^ k) ∈ SemistableModel.localRing M.X M.ffEquiv x ∧
      (c₀ • (g / h a ^ k))⁻¹ ∈ SemistableModel.localRing M.X M.ffEquiv x := by
  classical
  set f : F := c₀ • (g / h a ^ k) with hfdef
  have hha0 : h a ≠ 0 := hh a
  have hc₀F : algebraMap L F c₀ ≠ 0 := (map_ne_zero _).mpr hc₀
  have hf0 : f ≠ 0 := by
    rw [hfdef, Algebra.smul_def]
    exact mul_ne_zero hc₀F (div_ne_zero hg (pow_ne_zero _ hha0))

  have hordc : ∀ P : Place L F, P.ord (algebraMap L F c₀) = 0 := by
    intro P
    have hu : IsUnit (algebraMap L P.toValuationSubring c₀) := (IsUnit.mk0 c₀ hc₀).map _
    have := P.ord_coe_unit hu.unit
    rwa [IsUnit.unit_spec, Place.coe_algebraMap] at this
  have hordf : ∀ P : Place L F, M.pt P ∈ U a → P.ord f = 0 := by
    intro P hP
    have h1 : P.ord (h a ^ k) = (k : ℤ) * G P := by
      rw [← zpow_natCast, P.ord_zpow, hdiv a P hP]
    rw [hfdef, Algebra.smul_def, P.ord_mul hc₀F (div_ne_zero hg (pow_ne_zero _ hha0)), hordc, div_eq_mul_inv,
      P.ord_mul hg (inv_ne_zero (pow_ne_zero _ hha0)), P.ord_inv, h1, hkG P]
    ring

  have hmemP : ∀ P : Place L F, M.pt P ∈ U a → f ∈ P.toValuationSubring ∧ f⁻¹ ∈ P.toValuationSubring := by
    intro P hP
    obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible ↥P.toValuationSubring
    obtain ⟨u, hu⟩ := P.exists_unit_mul_zpow hf0 hπ
    rw [hordf P hP, zpow_zero, mul_one] at hu
    rw [hu]
    refine ⟨(u : ↥P.toValuationSubring).2, ?_⟩
    have : (((u : ↥P.toValuationSubring)) : F)⁻¹ = (((u⁻¹ : (↥P.toValuationSubring)ˣ) : ↥P.toValuationSubring) : F) := by
      rw [eq_comm]
      exact eq_inv_of_mul_eq_one_left (congrArg Subtype.val u.inv_mul)
    rw [this]; exact ((u⁻¹ : (↥P.toValuationSubring)ˣ) : ↥P.toValuationSubring).2

  have hgenU : ∀ {y z : M.X}, y ⤳ z → z ∈ U a → y ∈ U a := fun h hz => h.mem_open (U a).isOpen hz

  obtain ⟨s, hs⟩ := M.classify_bijective.2 x
  rcases s with ⟨⟩ | P | i | ⟨i, Q⟩ | e
  ·
    simp only [Sum.elim_inl] at hs
    subst hs
    have htop : SemistableModel.localRing M.X M.ffEquiv (genericPoint M.X) = ⊤ := by
      rw [eq_top_iff]
      intro y _
      refine ⟨M.ffEquiv y, ?_⟩
      rw [RingHom.comp_apply]
      change M.ffEquiv.symm.toRingHom ((M.X.presheaf.stalkSpecializes _).hom (M.ffEquiv y)) = y
      rw [TopCat.Presheaf.stalkSpecializes_refl]
      simp
    rw [htop]; exact ⟨trivial, trivial⟩
  ·
    simp only [Sum.elim_inl, Sum.elim_inr] at hs
    subst hs
    rw [M.localRing_pt]
    exact ⟨(hmemP P hx).1, (hmemP P hx).2⟩
  ·
    simp only [Sum.elim_inl, Sum.elim_inr] at hs
    subst hs
    rw [M.localRing_gen]
    exact ⟨(hunit i a hx).1, (hunit i a hx).2⟩
  ·
    simp only [Sum.elim_inl, Sum.elim_inr] at hs
    subst hs
    have hgi : M.gen i ∈ U a := hgenU (M.gen_specializes_sm i Q) hx
    have hUi := hunit i a hgi
    have key : ∀ P ∈ (C i).dom, (C i).placeMap P = Q.1 → M.pt P ∈ U a := by
      intro P hPd hPQ
      apply hgenU _ hx
      have e : Q = ⟨(C i).placeMap P, (C i).placeMap_not_mem_nodes P hPd⟩ := Subtype.ext hPQ.symm
      rw [e]; exact M.pt_specializes_sm i P hPd
    rw [M.localRing_sm, M.localRing_sm]
    exact ⟨⟨hUi.1, fun P hPd hPQ => (hmemP P (key P hPd hPQ)).1⟩, ⟨hUi.2, fun P hPd hPQ => (hmemP P (key P hPd hPQ)).2⟩⟩
  ·
    simp only [Sum.elim_inl, Sum.elim_inr] at hs
    subst hs
    have hgs : M.gen (src e) ∈ U a := hgenU (M.gen_specializes_nd e).1 hx
    have hgt : M.gen (tgt e) ∈ U a := hgenU (M.gen_specializes_nd e).2 hx
    have key : ∀ P ∈ (An e).dom, M.pt P ∈ U a := fun P hP => hgenU (M.pt_specializes_nd e P hP) hx
    rw [M.localRing_nd, M.localRing_nd]
    exact ⟨⟨(hunit _ a hgs).1, (hunit _ a hgt).1, fun P hP => (hmemP P (key P hP)).1⟩,
      ⟨(hunit _ a hgs).2, (hunit _ a hgt).2, fun P hP => (hmemP P (key P hP)).2⟩⟩

end S_AlgebraicCurve_SemistableModel_smul_div_pow_mem_localRing_of_forall_ord_eq
end P2MW
export P2MW.S_AlgebraicCurve_SemistableModel_smul_div_pow_mem_localRing_of_forall_ord_eq (solution)

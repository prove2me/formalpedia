-- Prove2me | solution 1 for AlgebraicCurve.SemistableModel.isReduced_stalk_quotient_maximalIdeal_of_base_eq_closedPoint
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/64f50b0b-7293-5570-afac-2e0ffbb8143c

import Mathlib
import Definitions.Def_AlgebraicCurve_SemistableCharts
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_Repartitions
import Definitions.Def_AlgebraicCurve_SemistableModel
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_SemistableModel_isReduced_stalk_quotient_maximalIdeal_of_base_eq_closedPoint

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve

universe u u'

theorem solution
    {L : Type u} [Field L] [IsAlgClosed L] {A : ValuationSubring L}
    {F : Type u'} [Field F] [Algebra L F]
    {ιV ιE : Type*} {Fbar : ιV → Type*} [∀ i, Field (Fbar i)] [∀ i, Algebra (IsLocalRing.ResidueField A) (Fbar i)]
    {C : ∀ i, ComponentChart A F (Fbar i)} {An : ιE → Annulus A F} {src tgt : ιE → ιV}
    {xs : ∀ e, Place (IsLocalRing.ResidueField A) (Fbar (src e))}
    {xt : ∀ e, Place (IsLocalRing.ResidueField A) (Fbar (tgt e))}
    (M : SemistableModel A F Fbar C An src tgt xs xt)
    (x : M.X) (hx : M.toBase.base x = IsLocalRing.closedPoint ↥A) :
    _root_.IsReduced (M.X.presheaf.stalk x ⧸
      Ideal.map ((M.X.presheaf.germ ⊤ x trivial).hom.comp
        (M.toBase.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of ↥A)).inv.hom))
        (IsLocalRing.maximalIdeal ↥A)) := by
  classical

  set 𝒪 := M.X.presheaf.stalk x with h𝒪
  set jA : ↥A →+* M.X.presheaf.stalk x :=
    (M.X.presheaf.germ ⊤ x trivial).hom.comp (M.toBase.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of ↥A)).inv.hom)
    with hjA
  set I : Ideal (M.X.presheaf.stalk x) := Ideal.map jA (IsLocalRing.maximalIdeal ↥A) with hI

  set ρ : M.X.presheaf.stalk x →+* F :=
    (M.ffEquiv.symm : M.X.functionField ≃+* F).toRingHom.comp (algebraMap (M.X.presheaf.stalk x) M.X.functionField)
    with hρ
  have hρinj : Function.Injective ρ := by
    rw [hρ]
    exact M.ffEquiv.symm.injective.comp (IsFractionRing.injective (M.X.presheaf.stalk x) M.X.functionField)
  have hρmem : ∀ s, ρ s ∈ SemistableModel.localRing M.X M.ffEquiv x := fun s => ⟨s, rfl⟩
  have hρsurj : ∀ f ∈ SemistableModel.localRing M.X M.ffEquiv x, ∃ s, ρ s = f := fun f hf => hf

  have hρj : ∀ a : ↥A, ρ (jA a) = algebraMap L F (a : L) := by
    intro a
    apply M.ffEquiv.injective
    rw [M.ffEquiv_algebraMap]
    show M.ffEquiv (M.ffEquiv.symm (algebraMap (M.X.presheaf.stalk x) M.X.functionField
      ((M.X.presheaf.germ ⊤ x trivial).hom (M.toBase.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of ↥A)).inv.hom a))))) = _
    rw [RingEquiv.apply_symm_apply]
    show (M.X.presheaf.stalkSpecializes ((genericPoint_spec M.X).specializes trivial)).hom
      ((M.X.presheaf.germ ⊤ x trivial).hom _) = _
    rw [TopCat.Presheaf.germ_stalkSpecializes_apply]
    rfl
  have hconst : ∀ a : ↥A, algebraMap L F (a : L) ∈ SemistableModel.localRing M.X M.ffEquiv x :=
    fun a => hρj a ▸ hρmem (jA a)

  have hIρ : ∀ t ∈ I, ∃ a ∈ IsLocalRing.maximalIdeal ↥A, ∃ g ∈ SemistableModel.localRing M.X M.ffEquiv x,
      ρ t = algebraMap L F (a : L) * g := by
    intro t ht
    rw [hI, Ideal.map] at ht
    refine Submodule.span_induction (p := fun t _ => ∃ a ∈ IsLocalRing.maximalIdeal ↥A,
      ∃ g ∈ SemistableModel.localRing M.X M.ffEquiv x, ρ t = algebraMap L F (a : L) * g) ?_ ?_ ?_ ?_ ht
    · rintro t ⟨a, ha, rfl⟩
      exact ⟨a, ha, 1, Subring.one_mem _, by rw [hρj, mul_one]⟩
    · exact ⟨0, Ideal.zero_mem _, 0, Subring.zero_mem _, by simp⟩
    · rintro t₁ t₂ _ _ ⟨a₁, ha₁, g₁, hg₁, h₁⟩ ⟨a₂, ha₂, g₂, hg₂, h₂⟩
      rcases ValuationRing.dvd_total a₁ a₂ with ⟨c, hc⟩ | ⟨c, hc⟩
      · refine ⟨a₁, ha₁, g₁ + algebraMap L F (c : L) * g₂, Subring.add_mem _ hg₁ (Subring.mul_mem _ (hconst c) hg₂), ?_⟩
        rw [map_add, h₁, h₂, hc]
        simp only [MulMemClass.coe_mul, map_mul]
        ring
      · refine ⟨a₂, ha₂, algebraMap L F (c : L) * g₁ + g₂, Subring.add_mem _ (Subring.mul_mem _ (hconst c) hg₁) hg₂, ?_⟩
        rw [map_add, h₁, h₂, hc]
        simp only [MulMemClass.coe_mul, map_mul]
        ring
    · rintro r t _ ⟨a, ha, g, hg, h⟩
      refine ⟨a, ha, ρ r * g, Subring.mul_mem _ (hρmem r) hg, ?_⟩
      rw [smul_eq_mul, map_mul, h]
      ring
  have hρI : ∀ s, (∃ a ∈ IsLocalRing.maximalIdeal ↥A, ∃ g ∈ SemistableModel.localRing M.X M.ffEquiv x,
      ρ s = algebraMap L F (a : L) * g) → s ∈ I := by
    rintro s ⟨a, ha, g, hg, h⟩
    obtain ⟨s', rfl⟩ := hρsurj g hg
    have : s = jA a * s' := hρinj (by rw [map_mul, hρj, h])
    rw [this, hI]
    exact Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ ha)

  rw [← Ideal.isRadical_iff_quotient_reduced]
  intro s hs
  obtain ⟨n, hn⟩ := (Ideal.mem_radical_iff.mp hs)
  apply hρI
  obtain ⟨a, ha, g, hg, hfn⟩ := hIρ _ hn
  rw [map_pow] at hfn

  have hf : ρ s ∈ SemistableModel.localRing M.X M.ffEquiv x := hρmem s

  have hnonunit : ∀ (O : ValuationSubring F) (hO : ∀ y : L, algebraMap L F y ∈ O ↔ y ∈ A) (b : ↥A),
      b ∈ IsLocalRing.maximalIdeal ↥A →
        (⟨algebraMap L F (b : L), (hO _).mpr b.2⟩ : O) ∈ IsLocalRing.maximalIdeal O := by
    intro O hO b hb
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    intro hu
    apply (IsLocalRing.mem_maximalIdeal _).mp hb
    by_cases hb0 : (b : L) = 0
    · exfalso
      apply not_isUnit_zero (M₀ := O)
      have : (⟨algebraMap L F (b : L), (hO _).mpr b.2⟩ : O) = 0 := Subtype.ext (by simp [hb0])
      rwa [this] at hu
    · have hinv : ((algebraMap L F (b : L))⁻¹) ∈ O := Submonoid.inv_mem_of_isUnit hu
      rw [← map_inv₀] at hinv
      have hbinv : (b : L)⁻¹ ∈ A := (hO _).mp hinv
      refine isUnit_iff_exists_inv.mpr ⟨⟨(b : L)⁻¹, hbinv⟩, ?_⟩
      apply Subtype.ext
      show (b : L) * (b : L)⁻¹ = 1
      exact mul_inv_cancel₀ hb0

  obtain ⟨w, hw⟩ := M.classify_bijective.2 x
  rcases w with u | P | i | iQ | e
  ·
    simp only [Sum.elim_inl] at hw
    subst hw
    have hρall : ∀ y : F, ∃ s, ρ s = y := by
      intro y
      refine ⟨M.ffEquiv y, ?_⟩
      rw [hρ, RingHom.comp_apply]
      show M.ffEquiv.symm ((M.X.presheaf.stalkSpecializes ((genericPoint_spec M.X).specializes trivial)).hom
        (M.ffEquiv y)) = y
      rw [TopCat.Presheaf.stalkSpecializes_refl]
      simp
    by_cases ha0 : (a : L) = 0
    · refine ⟨0, Ideal.zero_mem _, 0, Subring.zero_mem _, ?_⟩
      have : ρ s ^ n = 0 := by rw [hfn, ha0]; simp
      simp [pow_eq_zero_iff'.mp this |>.1]
    · refine ⟨a, ha, (algebraMap L F (a : L))⁻¹ * ρ s, ?_, ?_⟩
      · obtain ⟨s', hs'⟩ := hρall ((algebraMap L F (a : L))⁻¹ * ρ s)
        exact hs' ▸ hρmem s'
      · have : algebraMap L F (a : L) ≠ 0 := by rwa [map_ne_zero]
        rw [← mul_assoc, mul_inv_cancel₀ this, one_mul]
  ·
    simp only [Sum.elim_inr, Sum.elim_inl] at hw
    subst hw
    have hbot : IsLocalRing.maximalIdeal ↥A = ⊥ := by
      have h1 := M.toBase_pt P
      rw [hx] at h1
      exact h1
    have ha0 : a = 0 := by rw [hbot] at ha; exact ha
    refine ⟨0, Ideal.zero_mem _, 0, Subring.zero_mem _, ?_⟩
    have : ρ s ^ n = 0 := by rw [hfn, ha0]; simp
    simp [pow_eq_zero_iff'.mp this |>.1]
  ·
    simp only [Sum.elim_inr, Sum.elim_inl] at hw
    subst hw
    have hR : SemistableModel.localRing M.X M.ffEquiv (M.gen i) = (C i).integers.toSubring := M.localRing_gen i
    have hfO : ρ s ∈ (C i).integers := by have h := hf; rw [hR] at h; exact h
    have hgO : g ∈ (C i).integers := by have h := hg; rw [hR] at h; exact h
    by_cases hf0 : ρ s = 0
    · exact ⟨0, Ideal.zero_mem _, 0, Subring.zero_mem _, by simp [hf0]⟩

    have hfm : (⟨ρ s, hfO⟩ : (C i).integers) ∈ IsLocalRing.maximalIdeal (C i).integers := by
      have hpow : (⟨ρ s, hfO⟩ : (C i).integers) ^ n ∈ IsLocalRing.maximalIdeal (C i).integers := by
        have : (⟨ρ s, hfO⟩ : (C i).integers) ^ n =
            ⟨algebraMap L F (a : L), ((C i).algebraMap_mem_iff _).mpr a.2⟩ * ⟨g, hgO⟩ := by
          apply Subtype.ext
          rw [SubmonoidClass.coe_pow, MulMemClass.coe_mul]
          exact hfn
        rw [this]
        exact Ideal.mul_mem_right _ _ (hnonunit (C i).integers (C i).algebraMap_mem_iff a ha)
      exact (Ideal.IsPrime.mem_of_pow_mem inferInstance n hpow)

    obtain ⟨c, hcf, hcres⟩ := (C i).exists_smul_mem (ρ s) hf0
    have hcunit : IsUnit (⟨c • ρ s, hcf⟩ : (C i).integers) := by
      by_contra hnu
      apply hcres
      have : (⟨c • ρ s, hcf⟩ : (C i).integers) ∈ RingHom.ker (C i).residue := by
        rw [(C i).ker_residue]
        exact (IsLocalRing.mem_maximalIdeal _).mpr hnu
      exact (RingHom.mem_ker).mp this
    have hc0 : c ≠ 0 := by
      intro h0
      apply hcres
      have : (⟨c • ρ s, hcf⟩ : (C i).integers) = 0 := Subtype.ext (by simp [h0])
      rw [this, map_zero]

    have hcinvO : algebraMap L F c⁻¹ ∈ (C i).integers := by
      have h1 : ((c • ρ s)⁻¹) ∈ (C i).integers := Submonoid.inv_mem_of_isUnit hcunit
      have : algebraMap L F c⁻¹ = ρ s * (c • ρ s)⁻¹ := by
        rw [Algebra.smul_def, mul_inv, ← mul_assoc, mul_comm (ρ s), mul_assoc, mul_inv_cancel₀ hf0, mul_one,
          map_inv₀]
      rw [this]
      exact Subring.mul_mem _ hfO h1
    have hcinvA : c⁻¹ ∈ A := ((C i).algebraMap_mem_iff _).mp hcinvO
    have hcinvm : (⟨c⁻¹, hcinvA⟩ : ↥A) ∈ IsLocalRing.maximalIdeal ↥A := by
      rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
      intro hu
      apply (IsLocalRing.mem_maximalIdeal _).mp hfm

      have hsplit : (⟨ρ s, hfO⟩ : (C i).integers) = ⟨algebraMap L F c⁻¹, hcinvO⟩ * ⟨c • ρ s, hcf⟩ := by
        apply Subtype.ext
        show ρ s = algebraMap L F c⁻¹ * (c • ρ s)
        rw [Algebra.smul_def, ← mul_assoc, ← map_mul, inv_mul_cancel₀ hc0, map_one, one_mul]
      rw [hsplit]
      refine IsUnit.mul ?_ hcunit
      obtain ⟨v, hv⟩ := isUnit_iff_exists_inv.mp hu
      refine isUnit_iff_exists_inv.mpr ⟨⟨algebraMap L F ((v : ↥A) : L), ((C i).algebraMap_mem_iff _).mpr v.2⟩, ?_⟩
      apply Subtype.ext
      show algebraMap L F c⁻¹ * algebraMap L F ((v : ↥A) : L) = 1
      rw [← map_mul]
      have : c⁻¹ * ((v : ↥A) : L) = 1 := by
        have := congrArg (fun z : ↥A => (z : L)) hv
        simpa using this
      rw [this, map_one]
    refine ⟨⟨c⁻¹, hcinvA⟩, hcinvm, c • ρ s, ?_, ?_⟩
    · rw [hR]; exact hcf
    · show ρ s = algebraMap L F c⁻¹ * (c • ρ s)
      rw [Algebra.smul_def, ← mul_assoc, ← map_mul, inv_mul_cancel₀ hc0, map_one, one_mul]
  ·
    simp only [Sum.elim_inr, Sum.elim_inl] at hw
    subst hw
    obtain ⟨i, Q⟩ := iQ
    have hfR := (M.localRing_sm i Q (ρ s)).mp hf
    have hgR := (M.localRing_sm i Q g).mp hg
    have hres0 : (C i).residue ⟨ρ s, hfR.1⟩ = 0 := by
      have h1 : (⟨ρ s, hfR.1⟩ : (C i).integers) ^ n =
          ⟨algebraMap L F (a : L), ((C i).algebraMap_mem_iff _).mpr a.2⟩ * ⟨g, hgR.1⟩ := by
        apply Subtype.ext
        rw [SubmonoidClass.coe_pow, MulMemClass.coe_mul]
        exact hfn
      have hpow : ((C i).residue ⟨ρ s, hfR.1⟩) ^ n = 0 := by
        rw [← map_pow, h1, map_mul, (C i).residue_algebraMap, (IsLocalRing.residue_eq_zero_iff _).mpr ha,
          map_zero, zero_mul]
      exact (pow_eq_zero_iff'.mp hpow).1
    obtain ⟨a', ha', g', hg', hfg⟩ := M.exists_eq_mul_sm i Q (ρ s) hfR.1 hf hres0
    exact ⟨a', ha', g', hg', hfg⟩
  ·
    simp only [Sum.elim_inr] at hw
    subst hw
    have hfR := (M.localRing_nd e (ρ s)).mp hf
    have hgR := (M.localRing_nd e g).mp hg
    have hres : ∀ (j : ιV) (Cj : ComponentChart A F (Fbar j)) (hfj : ρ s ∈ Cj.integers) (hgj : g ∈ Cj.integers),
        Cj.residue ⟨ρ s, hfj⟩ = 0 := by
      intro j Cj hfj hgj
      have h1 : (⟨ρ s, hfj⟩ : Cj.integers) ^ n =
          ⟨algebraMap L F (a : L), (Cj.algebraMap_mem_iff _).mpr a.2⟩ * ⟨g, hgj⟩ := by
        apply Subtype.ext
        rw [SubmonoidClass.coe_pow, MulMemClass.coe_mul]
        exact hfn
      have hpow : (Cj.residue ⟨ρ s, hfj⟩) ^ n = 0 := by
        rw [← map_pow, h1, map_mul, Cj.residue_algebraMap, (IsLocalRing.residue_eq_zero_iff _).mpr ha,
          map_zero, zero_mul]
      exact (pow_eq_zero_iff'.mp hpow).1
    obtain ⟨a', ha', g', hg', hfg⟩ := M.exists_eq_mul_nd e (ρ s) hfR.1 hfR.2.1 hf
      (hres _ (C (src e)) hfR.1 hgR.1) (hres _ (C (tgt e)) hfR.2.1 hgR.2.1)
    exact ⟨a', ha', g', hg', hfg⟩

end S_AlgebraicCurve_SemistableModel_isReduced_stalk_quotient_maximalIdeal_of_base_eq_closedPoint
end P2MW
export P2MW.S_AlgebraicCurve_SemistableModel_isReduced_stalk_quotient_maximalIdeal_of_base_eq_closedPoint (solution)

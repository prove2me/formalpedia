-- Prove2me | solution 1 for AlgebraicCurve.ell_le_degree_add_ellZero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/059b8425-82fa-5852-ba77-c57ce13c3788

import Mathlib
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_AlgebraicCurve_Repartitions
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_AdelicIndex
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_ell_le_degree_add_ellZero

set_option autoImplicit false
set_option maxHeartbeats 3200000

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "Place Place.coe_algebraMap Divisor Divisor.degree Divisor.degree_single HasPrincipalDivisors HasPrincipalDivisors.exists_divisor IsCurveOver IsCurveOver.finite_residueField LSpace ell mem_lSpace_iff_ord lSpace_mono ConstantsAreBase ell_zero_eq_one_of_constantsAreBase WeilDifferentialRankOne StichtenothGenusExists"
p2m_open "AlgebraicCurve"
namespace Place
p2m_export "AlgebraicCurve.Place" "ext coe_algebraMap ResidueField deg adicValuation adicValuation_coe_eq_one_iff ord ord_mul ord_inv ord_coe_unit ord_coe_irreducible ord_zpow ord_unit_smul_zpow exists_unit_mul_zpow toValuationSubring adicValuation_eq_exp_neg_ord"
p2m_open "AlgebraicCurve.Place"
variable {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F)
private theorem _root_.AlgebraicCurve.Place.ord_nonneg_of_mem {f : F} (hf : f ∈ v.toValuationSubring) : 0 ≤ v.ord f := by
  rcases eq_or_ne f 0 with rfl | hf0
  · simp
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible v.toValuationSubring
  obtain ⟨n, u, hu⟩ :=
    IsDiscreteValuationRing.eq_unit_mul_pow_irreducible
      (x := (⟨f, hf⟩ : v.toValuationSubring)) (by simpa [Subtype.ext_iff] using hf0) hπ
  have hcoe : f = ((u : v.toValuationSubring) : F) * ((π : F) ^ (n : ℤ)) := by
    have h := congrArg (Subtype.val) hu
    push_cast at h
    rw [zpow_natCast]
    exact h
  rw [hcoe, v.ord_unit_smul_zpow u hπ (n : ℤ)]
  exact Int.natCast_nonneg n
p2m_export "AlgebraicCurve.Place" "ord_nonneg_of_mem"
private theorem _root_.AlgebraicCurve.Place.mem_of_ord_nonneg {f : F} (hf : f ≠ 0) (h : 0 ≤ v.ord f) :
    f ∈ v.toValuationSubring := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible v.toValuationSubring
  obtain ⟨u, hu⟩ := v.exists_unit_mul_zpow hf hπ
  rw [hu, show v.ord f = (((v.ord f).toNat : ℕ) : ℤ) from (Int.toNat_of_nonneg h).symm,
    zpow_natCast]
  exact mul_mem (u : v.toValuationSubring).2 (pow_mem (π : v.toValuationSubring).2 _)
p2m_export "AlgebraicCurve.Place" "mem_of_ord_nonneg"
theorem mem_iff_ord_nonneg {f : F} (hf : f ≠ 0) :
    f ∈ v.toValuationSubring ↔ 0 ≤ v.ord f :=
  ⟨v.ord_nonneg_of_mem, v.mem_of_ord_nonneg hf⟩
end Place
end AlgebraicCurve

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "Place Place.coe_algebraMap Divisor Divisor.degree Divisor.degree_single HasPrincipalDivisors HasPrincipalDivisors.exists_divisor IsCurveOver IsCurveOver.finite_residueField LSpace ell mem_lSpace_iff_ord lSpace_mono ConstantsAreBase ell_zero_eq_one_of_constantsAreBase WeilDifferentialRankOne StichtenothGenusExists"
p2m_open "AlgebraicCurve"
variable {K F : Type*} [Field K] [Field F] [Algebra K F]
namespace Divisor p2m_export "AlgebraicCurve.Divisor" "degree degree_single principal smul_def" end Divisor
p2m_open_scoped "AlgebraicCurve.Divisor" in
theorem Divisor.degree_eq_sum_support (D : Divisor K F) :
    Divisor.degree D = ∑ v ∈ D.support, D v * (v.deg : ℤ) := by
  rw [Divisor.degree, Finsupp.liftAddHom_apply, Finsupp.sum]
  rfl
variable {D : Divisor K F}
p2m_open_scoped "AlgebraicCurve.Divisor" in

theorem Divisor.degree_nonneg_of_nonneg [IsCurveOver K F]
    {D : Divisor K F} (hD : ∀ v, 0 ≤ D v) : 0 ≤ Divisor.degree D := by
  rw [Divisor.degree_eq_sum_support]
  exact Finset.sum_nonneg fun v _ => mul_nonneg (hD v) (Int.natCast_nonneg _)
theorem lSpace_eq_bot_of_degree_neg [IsCurveOver K F]
    (hD : Divisor.degree D < 0) : LSpace D = ⊥ := by
  rw [eq_bot_iff]
  intro f hf
  rw [Submodule.mem_bot]
  by_contra hf0
  obtain ⟨P, hPord, hPdeg⟩ := HasPrincipalDivisors.exists_divisor (K := K) f hf0
  have heff : ∀ v : Place K F, 0 ≤ (P + D) v := by
    intro v
    rw [Finsupp.add_apply, hPord]
    rcases mem_lSpace_iff_ord.mp hf with rfl | h
    · exact absurd rfl hf0
    · linarith [h v]
  have hdegPD : 0 ≤ Divisor.degree (P + D) := Divisor.degree_nonneg_of_nonneg heff
  rw [map_add, hPdeg, zero_add] at hdegPD
  exact absurd hdegPD (not_le.mpr hD)
theorem ell_eq_zero_of_degree_neg [IsCurveOver K F] (hD : Divisor.degree D < 0) :
    ell D = 0 := by
  rw [ell, lSpace_eq_bot_of_degree_neg hD, finrank_bot]
end AlgebraicCurve

set_option autoImplicit false

noncomputable section

p2m_open "Module IsLocalRing Module.IsLocalRing IsDedekindDomain WithZero"

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "Place Place.coe_algebraMap Divisor Divisor.degree Divisor.degree_single HasPrincipalDivisors HasPrincipalDivisors.exists_divisor IsCurveOver IsCurveOver.finite_residueField LSpace ell mem_lSpace_iff_ord lSpace_mono ConstantsAreBase ell_zero_eq_one_of_constantsAreBase WeilDifferentialRankOne StichtenothGenusExists"
p2m_open "AlgebraicCurve"

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

namespace Place
p2m_export "AlgebraicCurve.Place" "ext coe_algebraMap ResidueField deg adicValuation adicValuation_coe_eq_one_iff ord ord_mul ord_inv ord_coe_unit ord_coe_irreducible ord_zpow ord_unit_smul_zpow exists_unit_mul_zpow toValuationSubring adicValuation_eq_exp_neg_ord"
p2m_open "AlgebraicCurve.Place"

variable (v : Place K F)

private theorem _root_.AlgebraicCurve.Place.mk_mem_maximalIdeal_iff {f : F} (hf : f ∈ v.toValuationSubring) :
    (⟨f, hf⟩ : v.toValuationSubring) ∈ IsLocalRing.maximalIdeal v.toValuationSubring
      ↔ f = 0 ∨ 0 < v.ord f := by
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  constructor
  · intro hu
    rcases eq_or_ne f 0 with rfl | hf0
    · exact Or.inl rfl
    · refine Or.inr ?_
      rcases lt_or_eq_of_le (v.ord_nonneg_of_mem hf) with h | h
      · exact h
      ·
        exfalso
        apply hu
        rw [← v.adicValuation_coe_eq_one_iff ⟨f, hf⟩]
        show v.adicValuation f = 1
        rw [v.adicValuation_eq_exp_neg_ord hf0, ← h, neg_zero, WithZero.exp_zero]
  · intro h hu
    have hne : f ≠ 0 := fun h0 => hu.ne_zero (Subtype.ext h0)
    have h0 : v.ord f = 0 := by
      obtain ⟨u, hu'⟩ := hu
      have hcoe : f = ((u : v.toValuationSubring) : F) := by rw [hu']
      rw [hcoe]; exact v.ord_coe_unit u
    rcases h with rfl | hpos
    · exact hne rfl
    · omega

p2m_export "AlgebraicCurve.Place" "mk_mem_maximalIdeal_iff"
end Place

theorem ell_le_ell_sub_single_add_deg [IsCurveOver K F] (D : Divisor K F) (P : Place K F) :
    ell D ≤ ell (D - Finsupp.single P 1) + P.deg := by
  classical
  haveI : Module.Finite K P.ResidueField := IsCurveOver.finite_residueField P
  set E : Divisor K F := D - Finsupp.single P 1 with hE
  have hEP : E P = D P - 1 := by rw [hE, Finsupp.sub_apply, Finsupp.single_eq_same]
  have hEv : ∀ v, v ≠ P → E v = D v := by
    intro v hv; rw [hE, Finsupp.sub_apply, Finsupp.single_eq_of_ne hv, sub_zero]

  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible P.toValuationSubring
  set t : F := (π : F) with ht
  have ht0 : t ≠ 0 := by
    simpa [ht, ne_eq, ZeroMemClass.coe_eq_zero] using hπ.ne_zero
  have ht1 : P.ord t = 1 := P.ord_coe_irreducible hπ
  have htn0 : t ^ (D P) ≠ 0 := zpow_ne_zero _ ht0

  have hordmul : ∀ {g : F}, g ≠ 0 → P.ord (t ^ (D P) * g) = D P + P.ord g := by
    intro g hg
    rw [P.ord_mul htn0 hg, P.ord_zpow, ht1, mul_one]

  have hmem : ∀ g : F, g ∈ LSpace D → t ^ (D P) * g ∈ P.toValuationSubring := by
    intro g hg
    rcases eq_or_ne g 0 with rfl | hg0
    · simp
    · refine P.mem_of_ord_nonneg (mul_ne_zero htn0 hg0) ?_
      rw [hordmul hg0]
      have := (mem_lSpace_iff_ord.mp hg).resolve_left hg0 P
      linarith

  let ψ : LSpace D →ₗ[K] P.toValuationSubring :=
    { toFun := fun f => ⟨t ^ (D P) * (f : F), hmem _ f.2⟩
      map_add' := by intro f g; apply Subtype.ext; push_cast; ring
      map_smul' := by
        intro c f; apply Subtype.ext
        simp only [RingHom.id_apply, SetLike.val_smul, Algebra.smul_def, MulMemClass.coe_mul,
          Place.coe_algebraMap]
        ring }

  let res : P.toValuationSubring →ₗ[K] P.ResidueField :=
    (Algebra.linearMap P.toValuationSubring P.ResidueField).restrictScalars K
  have hres : ∀ x : P.toValuationSubring, res x = IsLocalRing.residue _ x := by
    intro x
    show (Algebra.linearMap P.toValuationSubring P.ResidueField).restrictScalars K x = _
    rw [LinearMap.restrictScalars_apply, Algebra.linearMap_apply,
      IsLocalRing.ResidueField.algebraMap_eq]
  let φ : LSpace D →ₗ[K] P.ResidueField := res ∘ₗ ψ

  have hphi : ∀ f : LSpace D, φ f = 0 ↔
      (⟨t ^ (D P) * (f : F), hmem _ f.2⟩ : P.toValuationSubring)
        ∈ IsLocalRing.maximalIdeal P.toValuationSubring := by
    intro f
    rw [show φ f = IsLocalRing.residue P.toValuationSubring ⟨t ^ (D P) * (f : F), hmem _ f.2⟩
          from hres (ψ f),
      IsLocalRing.residue_eq_zero_iff]

  have hED : E ≤ D := by
    rw [Finsupp.le_def]; intro v; rw [hE, Finsupp.sub_apply]
    have : (0 : ℤ) ≤ Finsupp.single P 1 v := by
      rcases eq_or_ne v P with rfl | hv
      · simp
      · simp [Finsupp.single_eq_of_ne hv]
    linarith
  have hsub : LSpace E ≤ LSpace D := lSpace_mono hED
  have hker : LinearMap.ker φ = (LSpace E).comap (LSpace D).subtype := by
    ext f
    simp only [LinearMap.mem_ker, Submodule.mem_comap, Submodule.coe_subtype]
    rw [hphi f, P.mk_mem_maximalIdeal_iff]
    rcases eq_or_ne (f : F) 0 with hf0 | hf0
    ·
      simp only [hf0, mul_zero, true_or, true_iff]
      exact (LSpace E).zero_mem
    ·
      rw [mem_lSpace_iff_ord]
      have hfD := (mem_lSpace_iff_ord.mp f.2).resolve_left hf0
      constructor
      · rintro (h | h)
        · exact absurd h (mul_ne_zero htn0 hf0)
        · refine Or.inr (fun v => ?_)
          rcases eq_or_ne v P with rfl | hv
          · rw [hEP]; rw [hordmul hf0] at h; omega
          · rw [hEv v hv]; exact hfD v
      · rintro (h | h)
        · exact absurd h hf0
        · refine Or.inr ?_
          have hP := h P
          rw [hEP] at hP
          rw [hordmul hf0]; omega

  have hkerfin : finrank K (LinearMap.ker φ) = ell E := by
    rw [hker, LinearEquiv.finrank_eq (Submodule.comapSubtypeEquivOfLe hsub)]

  have hquot : finrank K (LSpace D ⧸ LinearMap.ker φ) ≤ P.deg := by
    rw [LinearEquiv.finrank_eq φ.quotKerEquivRange]
    exact Submodule.finrank_le (LinearMap.range φ)

  by_cases hfin : FiniteDimensional K (LSpace D)
  · haveI := hfin
    have hrn := Submodule.finrank_quotient_add_finrank (LinearMap.ker φ)
    rw [hkerfin] at hrn
    have hb : ell D = finrank K (LSpace D) := rfl
    omega
  · have h0 : ell D = 0 := by rw [ell]; exact finrank_of_infinite_dimensional hfin
    omega

theorem one_le_deg [IsCurveOver K F] (P : Place K F) : 1 ≤ P.deg := by
  haveI : Module.Finite K P.ResidueField := IsCurveOver.finite_residueField P
  exact Module.finrank_pos

theorem ell_le_degree_add_ellZero_port [IsCurveOver K F] {D : Divisor K F}
    (hD : ∀ v, 0 ≤ D v) :
    (ell D : ℤ) ≤ Divisor.degree D + ell (0 : Divisor K F) := by
  classical
  suffices H : ∀ m : ℕ, ∀ D : Divisor K F, (∀ v, 0 ≤ D v) →
      (Divisor.degree D).toNat = m →
      (ell D : ℤ) ≤ Divisor.degree D + ell (0 : Divisor K F) by
    exact H (Divisor.degree D).toNat D hD rfl
  intro m
  induction m using Nat.strong_induction_on with
  | _ m IH =>
    intro D hD hm
    by_cases hD0 : D = 0
    · subst hD0; simp
    ·
      obtain ⟨P, hP⟩ := Finsupp.support_nonempty_iff.mpr hD0
      have hPpos : 1 ≤ D P := by
        have hne : D P ≠ 0 := Finsupp.mem_support_iff.mp hP
        have := hD P; omega
      set E : Divisor K F := D - Finsupp.single P 1 with hE
      have hEeff : ∀ v, 0 ≤ E v := by
        intro v; rw [hE, Finsupp.sub_apply]
        rcases eq_or_ne v P with rfl | hv
        · rw [Finsupp.single_eq_same]; omega
        · rw [Finsupp.single_eq_of_ne hv, sub_zero]; exact hD v

      have hdegE : Divisor.degree E = Divisor.degree D - P.deg := by
        rw [hE, map_sub, Divisor.degree_single, one_mul]
      have hPdeg1 : 1 ≤ (P.deg : ℤ) := by exact_mod_cast one_le_deg P
      have hDnn : 0 ≤ Divisor.degree D := Divisor.degree_nonneg_of_nonneg hD
      have hEnn : 0 ≤ Divisor.degree E := Divisor.degree_nonneg_of_nonneg hEeff

      have hmlt : (Divisor.degree E).toNat < m := by rw [← hm]; omega
      have hIH := IH _ hmlt E hEeff rfl

      have hstep := ell_le_ell_sub_single_add_deg D P
      rw [← hE] at hstep
      have hstep' : (ell D : ℤ) ≤ (ell E : ℤ) + P.deg := by exact_mod_cast hstep
      rw [hdegE] at hIH
      linarith

theorem ell_le_degree_add_one_of_effective [IsCurveOver K F]
    (hC : ConstantsAreBase K F) {D : Divisor K F} (hD : ∀ v, 0 ≤ D v) :
    (ell D : ℤ) ≤ Divisor.degree D + 1 := by
  have h := ell_le_degree_add_ellZero_port hD
  rw [ell_zero_eq_one_of_constantsAreBase hC] at h
  exact_mod_cast h

def lSpaceShiftEquiv (D : Divisor K F) {g : F} (hg : g ≠ 0)
    {Dg : Divisor K F} (hDg : ∀ v, Dg v = v.ord g) :
    LSpace D ≃ₗ[K] LSpace (D + Dg) where
  toFun h := ⟨(h : F) * g⁻¹, by
    rw [mem_lSpace_iff_ord]
    rcases eq_or_ne (h : F) 0 with hh0 | hh0
    · left; rw [hh0, zero_mul]
    · right; intro v
      rw [Finsupp.add_apply, hDg, v.ord_mul hh0 (inv_ne_zero hg), v.ord_inv]
      have := (mem_lSpace_iff_ord.mp h.2).resolve_left hh0 v
      linarith⟩
  invFun k := ⟨(k : F) * g, by
    rw [mem_lSpace_iff_ord]
    rcases eq_or_ne (k : F) 0 with hk0 | hk0
    · left; rw [hk0, zero_mul]
    · right; intro v
      have := (mem_lSpace_iff_ord.mp k.2).resolve_left hk0 v
      rw [Finsupp.add_apply, hDg] at this
      rw [v.ord_mul hk0 hg]
      linarith⟩
  map_add' h₁ h₂ := by apply Subtype.ext; push_cast; ring
  map_smul' c h := by
    apply Subtype.ext
    simp only [RingHom.id_apply, SetLike.val_smul, Algebra.smul_def]
    ring
  left_inv h := by
    apply Subtype.ext
    show (h : F) * g⁻¹ * g = (h : F)
    rw [mul_assoc, inv_mul_cancel₀ hg, mul_one]
  right_inv k := by
    apply Subtype.ext
    show (k : F) * g * g⁻¹ = (k : F)
    rw [mul_assoc, mul_inv_cancel₀ hg, mul_one]

theorem ell_le_degree_add_one [IsCurveOver K F] (hC : ConstantsAreBase K F)
    {D : Divisor K F} (hD : 0 ≤ Divisor.degree D) :
    (ell D : ℤ) ≤ Divisor.degree D + 1 := by
  rcases eq_or_ne (ell D) 0 with h0 | h0
  · rw [h0]; push_cast; linarith
  ·
    have hbot : LSpace D ≠ ⊥ := fun h => h0 (by rw [ell, h, finrank_bot])
    obtain ⟨g, hgL, hg0⟩ := (Submodule.ne_bot_iff _).mp hbot
    obtain ⟨Dg, hDgord, hDgdeg⟩ := HasPrincipalDivisors.exists_divisor (K := K) g hg0

    have heff : ∀ v, 0 ≤ (D + Dg) v := by
      intro v; rw [Finsupp.add_apply, hDgord]
      have := (mem_lSpace_iff_ord.mp hgL).resolve_left hg0 v
      linarith
    have hdeg : Divisor.degree (D + Dg) = Divisor.degree D := by
      rw [map_add, hDgdeg, add_zero]
    have hell : ell D = ell (D + Dg) :=
      LinearEquiv.finrank_eq (lSpaceShiftEquiv D hg0 hDgord)
    have hfin := ell_le_degree_add_one_of_effective hC heff
    rw [hdeg] at hfin
    rw [hell]; exact hfin

end AlgebraicCurve

end

open _root_.AlgebraicCurve _root_.P2MW.S_AlgebraicCurve_ell_le_degree_add_ellZero.AlgebraicCurve in
theorem solution {K F : Type*} [Field K] [Field F] [Algebra K F] [IsCurveOver K F] {D : Divisor K F}
    (hD : 0 ≤ D) [FiniteDimensional K ↥(LSpace (0 : Divisor K F))] :
    (ell D : ℤ) ≤ Divisor.degree D + ell (0 : Divisor K F) :=
  AlgebraicCurve.ell_le_degree_add_ellZero_port (K := K) (F := F) (D := D) (hD := hD)

end S_AlgebraicCurve_ell_le_degree_add_ellZero
end P2MW
export P2MW.S_AlgebraicCurve_ell_le_degree_add_ellZero (solution)

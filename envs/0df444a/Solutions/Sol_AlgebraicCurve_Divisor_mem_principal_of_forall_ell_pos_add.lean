-- Prove2me | solution 1 for AlgebraicCurve.Divisor.mem_principal_of_forall_ell_pos_add
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/ee1bfdf4-a74b-534e-bfc8-e417a0472015

import Mathlib
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_AlgebraicCurve_Repartitions
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_AdelicIndex
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_Divisor_mem_principal_of_forall_ell_pos_add

set_option autoImplicit false

universe u v

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "Place Place.coe_algebraMap Divisor Divisor.degree Divisor.degree_single Divisor.principal HasPrincipalDivisors HasPrincipalDivisors.exists_divisor IsCurveOver IsCurveOver.finite_residueField IsCurveOver.deg_eq_one_of_isAlgClosed LSpace ell mem_lSpace_iff_ord lSpace_mono one_mem_lSpace_zero ConstantsAreBase ell_zero_eq_one_of_constantsAreBase"
p2m_open "AlgebraicCurve"
namespace Place
p2m_export "AlgebraicCurve.Place" "ext coe_algebraMap ResidueField deg adicValuation adicValuation_coe_eq_one_iff ord ord_mul ord_inv ord_coe_unit ord_coe_irreducible ord_zpow ord_unit_smul_zpow exists_unit_mul_zpow algebraMap_mem' toValuationSubring adicValuation_eq_exp_neg_ord"
p2m_open "AlgebraicCurve.Place"

section SinglePlacePriv
variable {K : Type u} {F : Type v} [Field K] [Field F] [Algebra K F] (v : Place K F)

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
end SinglePlacePriv
end Place
end AlgebraicCurve

noncomputable section

open IsDedekindDomain WithZero IsLocalRing Module

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "Place Place.coe_algebraMap Divisor Divisor.degree Divisor.degree_single Divisor.principal HasPrincipalDivisors HasPrincipalDivisors.exists_divisor IsCurveOver IsCurveOver.finite_residueField IsCurveOver.deg_eq_one_of_isAlgClosed LSpace ell mem_lSpace_iff_ord lSpace_mono one_mem_lSpace_zero ConstantsAreBase ell_zero_eq_one_of_constantsAreBase"
p2m_open "AlgebraicCurve"

namespace RROpensImpl

variable {K : Type u} {F : Type v} [Field K] [Field F] [Algebra K F]

private theorem mk_mem_maximalIdeal_iff (v : Place K F) {f : F} (hf : f ∈ v.toValuationSubring) :
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
      · exfalso
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

private theorem ell_le_ell_sub_single_add_deg [IsCurveOver K F] (D : Divisor K F)
    (P : Place K F) : ell D ≤ ell (D - Finsupp.single P 1) + P.deg := by
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
    rw [hphi f, mk_mem_maximalIdeal_iff P]
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

private theorem one_le_deg [IsCurveOver K F] (P : Place K F) : 1 ≤ P.deg := by
  haveI : Module.Finite K P.ResidueField := IsCurveOver.finite_residueField P
  exact Module.finrank_pos

private theorem degree_eq_sum_support (D : Divisor K F) :
    Divisor.degree D = ∑ v ∈ D.support, D v * (v.deg : ℤ) := by
  classical
  conv_lhs => rw [← Finsupp.sum_single D, Finsupp.sum, map_sum]
  exact Finset.sum_congr rfl fun v _ => Divisor.degree_single v (D v)

section WithPack

variable {Kc : Divisor K F} {g : ℕ}

private theorem ell_canonical_eq
    (hRR : ∀ D : Divisor K F, (ell D : ℤ) - ell (Kc - D) = Divisor.degree D + 1 - g)
    (hC : ConstantsAreBase K F) : ell Kc = g := by
  have h := hRR 0
  rw [sub_zero, ell_zero_eq_one_of_constantsAreBase hC, map_zero] at h
  push_cast at h
  omega

private theorem degree_add_one_sub_le_ell
    (hRR : ∀ D : Divisor K F, (ell D : ℤ) - ell (Kc - D) = Divisor.degree D + 1 - g)
    (E : Divisor K F) : Divisor.degree E + 1 - (g : ℤ) ≤ (ell E : ℤ) := by
  have h := hRR E
  have h0 : (0 : ℤ) ≤ (ell (Kc - E) : ℤ) := Int.natCast_nonneg _
  linarith

private theorem finite_lSpace [IsCurveOver K F]
    (hRR : ∀ D : Divisor K F, (ell D : ℤ) - ell (Kc - D) = Divisor.degree D + 1 - g)
    (P : Place K F) (D : Divisor K F) : Module.Finite K (LSpace D) := by
  set n : ℕ := ((g : ℤ) - Divisor.degree D).toNat with hn
  set D' : Divisor K F := D + (n : ℤ) • Finsupp.single P 1 with hD'
  have hdeg : (g : ℤ) ≤ Divisor.degree D' := by
    have h1 : (1 : ℤ) ≤ (P.deg : ℤ) := by exact_mod_cast one_le_deg P
    have hn0 : (g : ℤ) - Divisor.degree D ≤ (n : ℤ) := by
      rw [hn]; exact Int.self_le_toNat _
    rw [hD', map_add, map_zsmul, Divisor.degree_single, one_mul, smul_eq_mul]
    nlinarith [Int.natCast_nonneg n]
  have hpos : 0 < finrank K (LSpace D') := by
    have h := degree_add_one_sub_le_ell hRR D'
    have : (1 : ℤ) ≤ (ell D' : ℤ) := by linarith
    have h' : 1 ≤ ell D' := by exact_mod_cast this
    exact h'
  haveI : Module.Finite K (LSpace D') := Module.finite_of_finrank_pos hpos
  have hle : D ≤ D' := by
    rw [Finsupp.le_def]; intro v
    rw [hD', Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul]
    have : (0 : ℤ) ≤ Finsupp.single P 1 v := by
      rcases eq_or_ne v P with rfl | hv
      · simp
      · simp [Finsupp.single_eq_of_ne hv]
    nlinarith [Int.natCast_nonneg n]
  exact Submodule.finiteDimensional_of_le (lSpace_mono hle)

end WithPack

private theorem exists_ord_pos_of_ord_neg [IsCurveOver K F] {x : F} (hx : x ≠ 0)
    (v₀ : Place K F) (hpole : v₀.ord x < 0) : ∃ P : Place K F, 0 < P.ord x := by
  classical
  obtain ⟨D, hD, hdeg⟩ := HasPrincipalDivisors.exists_divisor (K := K) x hx
  by_contra hall
  simp only [not_exists, not_lt] at hall
  have hall' : ∀ v, 0 ≤ (-D) v := fun v => by
    rw [Finsupp.neg_apply, neg_nonneg, hD v]; exact hall v
  have hv₀ : 0 < (-D) v₀ := by
    rw [Finsupp.neg_apply, neg_pos, hD v₀]; exact hpole
  have hmem : v₀ ∈ (-D).support := Finsupp.mem_support_iff.mpr hv₀.ne'
  have hdegpos : 0 < Divisor.degree (-D) := by
    rw [degree_eq_sum_support]
    calc (0 : ℤ) < (-D) v₀ * (v₀.deg : ℤ) :=
          mul_pos hv₀ (by exact_mod_cast one_le_deg v₀)
      _ ≤ ∑ v ∈ (-D).support, (-D) v * (v.deg : ℤ) :=
          Finset.single_le_sum
            (fun v _ => mul_nonneg (hall' v) (Int.natCast_nonneg _)) hmem
  rw [map_neg, hdeg, neg_zero] at hdegpos
  exact lt_irrefl 0 hdegpos

private theorem infinite_place_of_pole [IsCurveOver K F] [Infinite K] {x : F}
    (v₀ : Place K F) (hpole : v₀.ord x < 0) : Infinite (Place K F) := by
  have hnotmem : x ∉ v₀.toValuationSubring := fun hmem =>
    not_lt.mpr (v₀.ord_nonneg_of_mem hmem) hpole
  have hxa_ne : ∀ a : K, x - algebraMap K F a ≠ 0 := fun a h => by
    rw [sub_eq_zero] at h
    exact hnotmem (h ▸ v₀.algebraMap_mem' a)
  have hxa_pole : ∀ a : K, x - algebraMap K F a ∉ v₀.toValuationSubring := fun a hmem =>
    hnotmem (by have := add_mem hmem (v₀.algebraMap_mem' a); rwa [sub_add_cancel] at this)
  have hxa_ord : ∀ a : K, v₀.ord (x - algebraMap K F a) < 0 := fun a => by
    by_contra hge
    exact hxa_pole a (v₀.mem_of_ord_nonneg (hxa_ne a) (not_lt.mp hge))
  have hzero : ∀ a : K, ∃ w : Place K F, 0 < w.ord (x - algebraMap K F a) := fun a =>
    exists_ord_pos_of_ord_neg (hxa_ne a) v₀ (hxa_ord a)
  choose z hz using hzero

  have hzinj : Function.Injective z := by
    intro c c' hcc'
    by_contra hne
    have h1 : 0 < (z c).ord (x - algebraMap K F c) := hz c
    have h2 : 0 < (z c).ord (x - algebraMap K F c') := by rw [hcc']; exact hz c'
    generalize z c = w at h1 h2
    have hm : ∀ {y : F}, 0 < w.ord y → ∃ hy : y ∈ w.toValuationSubring,
        (⟨y, hy⟩ : w.toValuationSubring) ∈ IsLocalRing.maximalIdeal w.toValuationSubring := by
      intro y hy
      have hy0 : y ≠ 0 := by rintro rfl; simp at hy
      exact ⟨w.mem_of_ord_nonneg hy0 hy.le, (mk_mem_maximalIdeal_iff w _).mpr (Or.inr hy)⟩
    obtain ⟨hx1, hm1⟩ := hm h1
    obtain ⟨hx2, hm2⟩ := hm h2
    have hdiff := Ideal.sub_mem _ hm2 hm1
    have hval : ((⟨x - algebraMap K F c', hx2⟩ : w.toValuationSubring)
        - ⟨x - algebraMap K F c, hx1⟩) = algebraMap K w.toValuationSubring (c - c') := by
      apply Subtype.ext
      simp only [AddSubgroupClass.coe_sub, Place.coe_algebraMap, map_sub]
      ring
    rw [hval] at hdiff
    have hunit : IsUnit (algebraMap K w.toValuationSubring (c - c')) :=
      (IsUnit.mk0 _ (sub_ne_zero.mpr hne)).map _
    exact (IsLocalRing.mem_maximalIdeal _).mp hdiff hunit
  exact Infinite.of_injective z hzinj

private theorem infinite_place [IsAlgClosed K] [IsCurveOver K F] (P : Place K F) :
    Infinite (Place K F) := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible P.toValuationSubring
  have hordx : P.ord ((π : F)⁻¹) < 0 := by
    rw [P.ord_inv, P.ord_coe_irreducible hπ]; decide
  exact infinite_place_of_pole P hordx

section WithPack

variable {Kc : Divisor K F} {g : ℕ}

private theorem ell_sub_single_add_one_eq [IsCurveOver K F]
    (hRR : ∀ D : Divisor K F, (ell D : ℤ) - ell (Kc - D) = Divisor.degree D + 1 - g)
    (P : Place K F) {G : Divisor K F} {f : F} (hfG : f ∈ LSpace G)
    (hf0 : f ≠ 0) {Q : Place K F} (hQ : Q.deg = 1) (hGQ : G Q = 0) (hfQ : Q.ord f = 0) :
    ell (G - Finsupp.single Q 1) + 1 = ell G := by

  have hfnot : f ∉ LSpace (G - Finsupp.single Q 1) := by
    intro h
    have h' := (mem_lSpace_iff_ord.mp h).resolve_left hf0 Q
    rw [Finsupp.sub_apply, Finsupp.single_eq_same, hGQ, hfQ] at h'
    omega
  have hle : LSpace (G - Finsupp.single Q 1) ≤ LSpace G := by
    refine lSpace_mono ?_
    rw [Finsupp.le_def]; intro v; rw [Finsupp.sub_apply]
    have : (0 : ℤ) ≤ Finsupp.single Q 1 v := by
      rcases eq_or_ne v Q with rfl | hv
      · simp
      · simp [Finsupp.single_eq_of_ne hv]
    linarith
  have hlt : LSpace (G - Finsupp.single Q 1) < LSpace G :=
    lt_of_le_of_ne hle fun h => hfnot (h ▸ hfG)
  haveI : Module.Finite K (LSpace G) := finite_lSpace hRR P G
  have h1 : ell (G - Finsupp.single Q 1) < ell G := Submodule.finrank_lt_finrank_of_lt hlt
  have h2 : ell G ≤ ell (G - Finsupp.single Q 1) + Q.deg := ell_le_ell_sub_single_add_deg G Q
  rw [hQ] at h2
  omega

private theorem exists_finset_forall_ell_sub_single_add_one_eq [IsAlgClosed K] [IsCurveOver K F]
    (hRR : ∀ D : Divisor K F, (ell D : ℤ) - ell (Kc - D) = Divisor.degree D + 1 - g)
    (P : Place K F) {G : Divisor K F} (hG : 0 < ell G) :
    ∃ S : Finset (Place K F), ∀ Q ∉ S, ell (G - Finsupp.single Q 1) + 1 = ell G := by
  classical

  have hbot : LSpace G ≠ ⊥ := fun h => by
    have : ell G = 0 := by rw [ell, h, finrank_bot]
    omega
  obtain ⟨f, hfG, hf0⟩ := (Submodule.ne_bot_iff _).mp hbot
  obtain ⟨Δ, hΔord, -⟩ := HasPrincipalDivisors.exists_divisor (K := K) f hf0
  refine ⟨G.support ∪ Δ.support, fun Q hQ => ?_⟩
  rw [Finset.mem_union, not_or, Finsupp.notMem_support_iff, Finsupp.notMem_support_iff] at hQ
  obtain ⟨hGQ, hΔQ⟩ := hQ
  exact ell_sub_single_add_one_eq hRR P hfG hf0 (IsCurveOver.deg_eq_one_of_isAlgClosed Q)
    hGQ (by rw [← hΔord Q, hΔQ])

end WithPack

end RROpensImpl

namespace WStabImpl

variable {K : Type u} {F : Type v} [Field K] [Field F] [Algebra K F]

private theorem eq_zero_of_effective_of_degree_eq_zero [IsCurveOver K F] {D : Divisor K F}
    (hD : ∀ v, 0 ≤ D v) (hdeg : Divisor.degree D = 0) : D = 0 := by
  classical
  rw [RROpensImpl.degree_eq_sum_support] at hdeg
  have hterm : ∀ v ∈ D.support, 0 ≤ D v * (v.deg : ℤ) := fun v _ =>
    mul_nonneg (hD v) (Int.natCast_nonneg _)
  have hzero := (Finset.sum_eq_zero_iff_of_nonneg hterm).mp hdeg
  ext v
  by_contra hv
  have hvs : v ∈ D.support := Finsupp.mem_support_iff.mpr hv
  have h1 : (1 : ℤ) ≤ (v.deg : ℤ) := by exact_mod_cast RROpensImpl.one_le_deg v
  have := hzero v hvs
  have hDv : 0 < D v := lt_of_le_of_ne (hD v) (Ne.symm hv)
  nlinarith

private theorem ell_pos_of_effective [IsCurveOver K F] {Kc : Divisor K F} {g : ℕ}
    (hRR : ∀ D : Divisor K F, (ell D : ℤ) - ell (Kc - D) = Divisor.degree D + 1 - g)
    (P : Place K F) {E : Divisor K F} (hE : ∀ v, 0 ≤ E v) : 0 < ell E := by
  haveI : Module.Finite K (LSpace E) := RROpensImpl.finite_lSpace hRR P E
  have h1 : (1 : F) ∈ LSpace E := lSpace_mono (Finsupp.le_def.mpr fun v => by simpa using hE v) one_mem_lSpace_zero
  exact Module.finrank_pos_iff_exists_ne_zero.mpr ⟨⟨1, h1⟩, by simp⟩

private theorem mem_principal_of_ell_pos [IsCurveOver K F] {ξ : Divisor K F}
    (hξ : Divisor.degree ξ = 0) (hpos : 0 < ell ξ) :
    ξ ∈ Divisor.principal (K := K) (F := F) := by
  have hbot : LSpace ξ ≠ ⊥ := fun hb => by
    have : ell ξ = 0 := by rw [ell, hb, finrank_bot]
    omega
  obtain ⟨f, hfξ, hf0⟩ := (Submodule.ne_bot_iff _).mp hbot
  obtain ⟨Δ, hΔord, hΔdeg⟩ := HasPrincipalDivisors.exists_divisor (K := K) f hf0
  have hford := (mem_lSpace_iff_ord.mp hfξ).resolve_left hf0

  have heff : ∀ v, 0 ≤ (Δ + ξ) v := fun v => by
    rw [Finsupp.add_apply, hΔord v]; have := hford v; omega
  have hsum : Δ + ξ = 0 :=
    eq_zero_of_effective_of_degree_eq_zero heff (by rw [map_add, hΔdeg, hξ, add_zero])
  have hξeq : ξ = -Δ := eq_neg_of_add_eq_zero_right hsum
  rw [hξeq]
  exact neg_mem ⟨f, hf0, hΔord⟩

theorem mem_principal_of_forall_ell_pos_add_impl [IsAlgClosed K] [IsCurveOver K F]
    (Kc : Divisor K F) (g : ℕ)
    (hRR : ∀ D : Divisor K F, (ell D : ℤ) - ell (Kc - D) = Divisor.degree D + 1 - g)
    (ξ : Divisor K F) (hξ : Divisor.degree ξ = 0)
    (h : ∀ D : Divisor K F, Divisor.degree D = (g : ℤ) - 1 → 0 < ell D → 0 < ell (D + ξ)) :
    ξ ∈ Divisor.principal (K := K) (F := F) := by
  classical

  rcases isEmpty_or_nonempty (Place K F) with hempty | ⟨⟨P⟩⟩
  · have : ξ = 0 := Finsupp.ext fun v => hempty.elim v
    rw [this]; exact zero_mem _
  refine mem_principal_of_ell_pos hξ ?_

  rcases Nat.eq_zero_or_pos g with hg | hg
  · subst hg
    have := hRR ξ
    have h0 : (0 : ℤ) ≤ (ell (Kc - ξ) : ℤ) := Int.natCast_nonneg _
    rw [hξ] at this
    have : (1 : ℤ) ≤ (ell ξ : ℤ) := by push_cast at this; linarith
    exact_mod_cast this

  haveI := RROpensImpl.infinite_place (K := K) P
  have Q : ∀ j : ℕ, j + 1 ≤ g → ∀ E : Divisor K F, (∀ v, 0 ≤ E v) →
      Divisor.degree E = (g : ℤ) - 1 - j → 0 < ell (E + ξ) := by
    intro j
    induction j with
    | zero =>
      intro _ E hE hdeg
      exact h E (by rw [hdeg]; push_cast; ring) (ell_pos_of_effective hRR P hE)
    | succ j ih =>
      intro hj E hE hdeg
      by_contra hcon
      have hEξ : ell (E + ξ) = 0 := by omega

      set G : Divisor K F := Kc - (E + ξ) with hG
      have hRR1 := hRR (E + ξ)
      rw [hEξ, map_add, hdeg, hξ] at hRR1
      have hGpos : 0 < ell G := by
        have : (1 : ℤ) ≤ (ell G : ℤ) := by push_cast at hRR1 ⊢; linarith
        exact_mod_cast this

      obtain ⟨S, hS⟩ := RROpensImpl.exists_finset_forall_ell_sub_single_add_one_eq hRR P hGpos
      obtain ⟨Qp, hQp⟩ := Infinite.exists_notMem_finset S
      have hdrop := hS Qp hQp

      have hE' : ∀ v, 0 ≤ (E + Finsupp.single Qp 1 : Divisor K F) v := fun v => by
        rw [Finsupp.add_apply]
        have : (0 : ℤ) ≤ Finsupp.single Qp 1 v := by
          rcases eq_or_ne v Qp with rfl | hv
          · simp
          · simp [Finsupp.single_eq_of_ne hv]
        linarith [hE v]
      have hdeg' : Divisor.degree (E + Finsupp.single Qp 1) = (g : ℤ) - 1 - j := by
        rw [map_add, Divisor.degree_single, IsCurveOver.deg_eq_one_of_isAlgClosed Qp, hdeg]
        push_cast; ring
      have hpos := ih (by omega) (E + Finsupp.single Qp 1) hE' hdeg'

      have hRR2 := hRR (E + Finsupp.single Qp 1 + ξ)
      have hKc : Kc - (E + Finsupp.single Qp 1 + ξ) = G - Finsupp.single Qp 1 := by
        rw [hG]; abel
      rw [hKc, map_add, map_add, hdeg, hξ, Divisor.degree_single,
        IsCurveOver.deg_eq_one_of_isAlgClosed Qp] at hRR2
      have hcomm : E + Finsupp.single Qp 1 + ξ = E + ξ + Finsupp.single Qp 1 := by abel
      have hzero : ell (E + Finsupp.single Qp 1 + ξ) = 0 := by
        have e1 : (ell (G - Finsupp.single Qp 1) : ℤ) + 1 = ell G := by exact_mod_cast hdrop
        push_cast at hRR1 hRR2 e1 ⊢
        have : (ell (E + Finsupp.single Qp 1 + ξ) : ℤ) = 0 := by linarith
        exact_mod_cast this
      rw [hzero] at hpos
      exact lt_irrefl _ hpos

  have hcast : ((g - 1 : ℕ) : ℤ) = (g : ℤ) - 1 := by omega
  have := Q (g - 1) (by omega) 0 (fun _ => le_rfl) (by rw [map_zero, hcast]; ring)
  simpa using this

end WStabImpl
end AlgebraicCurve

end

p2m_open "AlgebraicCurve P2MW.S_AlgebraicCurve_Divisor_mem_principal_of_forall_ell_pos_add.AlgebraicCurve"

theorem solution
    {K : Type u} {F : Type v} [Field K] [Field F] [Algebra K F] [IsAlgClosed K]
    [IsCurveOver K F] [Algebra.EssFiniteType K F] (Kc : Divisor K F) (g : ℕ)
    (hRR : ∀ D : Divisor K F, (ell D : ℤ) - ell (Kc - D) = Divisor.degree D + 1 - g)
    (ξ : Divisor K F) (hξ : Divisor.degree ξ = 0)
    (h : ∀ D : Divisor K F, Divisor.degree D = (g : ℤ) - 1 → 0 < ell D → 0 < ell (D + ξ)) :
    ξ ∈ Divisor.principal (K := K) (F := F) :=
  AlgebraicCurve.WStabImpl.mem_principal_of_forall_ell_pos_add_impl Kc g hRR ξ hξ h

end S_AlgebraicCurve_Divisor_mem_principal_of_forall_ell_pos_add
end P2MW
export P2MW.S_AlgebraicCurve_Divisor_mem_principal_of_forall_ell_pos_add (solution)

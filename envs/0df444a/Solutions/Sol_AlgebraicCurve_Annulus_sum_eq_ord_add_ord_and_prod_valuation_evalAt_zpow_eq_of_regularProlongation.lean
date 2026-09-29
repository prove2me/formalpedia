-- Prove2me | solution 1 for AlgebraicCurve.Annulus.sum_eq_ord_add_ord_and_prod_valuation_evalAt_zpow_eq_of_regularProlongation
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/2e760209-ae79-594f-bfe6-dca80f732994

import Mathlib
import Definitions.Def_AlgebraicCurve_SemistableCharts
import Definitions.Def_AlgebraicCurve_RegularProlongation
import Definitions.Def_AlgebraicCurve_PlaceEvaluationAlgebra
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_Annulus_sum_eq_ord_add_ord_and_prod_valuation_evalAt_zpow_eq_of_regularProlongation

set_option autoImplicit false

open AlgebraicCurve IsLocalRing

namespace AnnulusTwoEndVal

section PlaceLemmas

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem evalAt_sub' (v : Place K F) (hv : v.IsRational) {f g : F} (hf : f ∈ v.toValuationSubring)
    (hg : g ∈ v.toValuationSubring) : v.evalAt (f - g) = v.evalAt f - v.evalAt g := by
  apply v.algebraMap_residueField_injective
  rw [v.algebraMap_evalAt hv (sub_mem hf hg), map_sub, v.algebraMap_evalAt hv hf,
    v.algebraMap_evalAt hv hg, ← map_sub]
  rfl

theorem ord_nonneg_of_mem' (v : Place K F) {f : F} (hf : f ∈ v.toValuationSubring) : 0 ≤ v.ord f := by
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

theorem ord_eq_zero_of_evalAt_ne_zero' (v : Place K F) {f : F} (hf : f ∈ v.toValuationSubring)
    (h : v.evalAt f ≠ 0) : v.ord f = 0 := by
  by_contra hne
  have hpos : 0 < v.ord f := lt_of_le_of_ne (ord_nonneg_of_mem' v hf) (Ne.symm hne)
  apply h
  have hnu : ¬ IsUnit (⟨f, hf⟩ : v.toValuationSubring) := by
    intro hu
    obtain ⟨u, hu⟩ := hu
    have : v.ord f = 0 := by
      have := v.ord_coe_unit u
      rwa [hu] at this
    omega
  have hmax : (⟨f, hf⟩ : v.toValuationSubring) ∈ IsLocalRing.maximalIdeal _ :=
    (IsLocalRing.mem_maximalIdeal _).2 hnu
  rw [v.evalAt_of_mem hf, (IsLocalRing.residue_eq_zero_iff _).2 hmax, ← map_zero (algebraMap K _),
    v.residueInv_algebraMap]

theorem isUnit_of_evalAt_ne_zero' (v : Place K F) {f : F} (hf : f ∈ v.toValuationSubring)
    (h : v.evalAt f ≠ 0) : IsUnit (⟨f, hf⟩ : v.toValuationSubring) := by
  by_contra hnu
  apply h
  have hmax : (⟨f, hf⟩ : v.toValuationSubring) ∈ IsLocalRing.maximalIdeal _ :=
    (IsLocalRing.mem_maximalIdeal _).2 hnu
  rw [v.evalAt_of_mem hf, (IsLocalRing.residue_eq_zero_iff _).2 hmax, ← map_zero (algebraMap K _),
    v.residueInv_algebraMap]

theorem inv_mem_and_evalAt_inv' (v : Place K F) (hv : v.IsRational) {f : F} (hf : f ∈ v.toValuationSubring)
    (h : v.evalAt f ≠ 0) : ∃ hfi : f⁻¹ ∈ v.toValuationSubring, v.evalAt f⁻¹ = (v.evalAt f)⁻¹ := by
  obtain ⟨u, hu⟩ := isUnit_of_evalAt_ne_zero' v hf h
  have hf0 : f ≠ 0 := by
    rintro rfl
    apply h
    rw [show (0 : F) = algebraMap K F 0 from (map_zero _).symm, v.evalAt_algebraMap_eq]
  have hval : ((u⁻¹ : v.toValuationSubringˣ) : v.toValuationSubring).1 = f⁻¹ := by
    have h1 := congrArg (fun t : v.toValuationSubring => (t : F)) u.mul_inv
    simp only [MulMemClass.coe_mul, OneMemClass.coe_one] at h1
    rw [hu] at h1
    exact (eq_inv_of_mul_eq_one_right h1)
  have hmem : f⁻¹ ∈ v.toValuationSubring := hval ▸ ((u⁻¹ : v.toValuationSubringˣ) : v.toValuationSubring).2
  refine ⟨hmem, ?_⟩
  have hmul := v.evalAt_mul_of_mem hv hf hmem
  rw [mul_inv_cancel₀ hf0, v.evalAt_one] at hmul
  exact eq_inv_of_mul_eq_one_right hmul.symm

theorem ord_prod' (v : Place K F) {ι : Type*} (S : Finset ι) (f : ι → F) (hf : ∀ i ∈ S, f i ≠ 0) :
    v.ord (∏ i ∈ S, f i) = ∑ i ∈ S, v.ord (f i) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | @insert i S hi ih =>
    rw [Finset.prod_insert hi, Finset.sum_insert hi,
      v.ord_mul (hf i (Finset.mem_insert_self _ _))
        (Finset.prod_ne_zero_iff.2 fun j hj => hf j (Finset.mem_insert_of_mem hj)),
      ih fun j hj => hf j (Finset.mem_insert_of_mem hj)]

theorem ord_algebraMap' (v : Place K F) {c : K} (hc : c ≠ 0) : v.ord (algebraMap K F c) = 0 := by
  have h1 : 0 ≤ v.ord (algebraMap K F c) := ord_nonneg_of_mem' v (v.algebraMap_mem' c)
  have h2 : 0 ≤ v.ord (algebraMap K F c)⁻¹ := by
    have hmem' : (algebraMap K F c)⁻¹ ∈ v.toValuationSubring := by
      rw [← map_inv₀]; exact v.algebraMap_mem' _
    exact ord_nonneg_of_mem' v hmem'
  rw [v.ord_inv] at h2
  omega

end PlaceLemmas

section Prolongation

variable {L : Type*} [Field L] {A : ValuationSubring L} {F : Type*} [Field F] [Algebra L F]
  {Fbar : Type*} [Field Fbar] [Algebra (ResidueField A) Fbar]

theorem algebraMap_mem (R : RegularProlongation A F Fbar) (a : A) : algebraMap L F a ∈ R.integers :=
  (R.algebraMap_mem_iff a).mpr a.2

theorem residue_algebraMap' (R : RegularProlongation A F Fbar) (a : A) (h : algebraMap L F a ∈ R.integers) :
    R.residue ⟨algebraMap L F a, h⟩ = algebraMap (ResidueField A) Fbar (IsLocalRing.residue A a) :=
  R.residue_algebraMap a

theorem coe_units_inv (S : ValuationSubring F) (u : (↥S)ˣ) : (((u⁻¹ : (↥S)ˣ) : ↥S) : F) = ((u : ↥S) : F)⁻¹ := by
  have h1 : ((u : ↥S) : F) * (((u⁻¹ : (↥S)ˣ) : ↥S) : F) = 1 := by
    rw [← MulMemClass.coe_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, OneMemClass.coe_one]
  exact (eq_inv_of_mul_eq_one_right h1)

theorem inv_mem_of_residue_ne_zero (R : RegularProlongation A F Fbar) {f : F} (hf : f ∈ R.integers)
    (h : R.residue ⟨f, hf⟩ ≠ 0) :
    ∃ hf' : f⁻¹ ∈ R.integers, R.residue ⟨f⁻¹, hf'⟩ = (R.residue ⟨f, hf⟩)⁻¹ := by
  obtain ⟨u, hu⟩ := R.isUnit_of_residue_ne_zero h
  have hcoe : ((u : R.integers) : F) = f := by rw [hu]
  have hinv : (((u⁻¹ : (↥R.integers)ˣ) : R.integers) : F) = f⁻¹ := by rw [coe_units_inv, hcoe]
  have hmem : f⁻¹ ∈ R.integers := hinv ▸ SetLike.coe_mem _
  refine ⟨hmem, ?_⟩
  have hx : (⟨f⁻¹, hmem⟩ : R.integers) = ((u⁻¹ : (↥R.integers)ˣ) : R.integers) := Subtype.ext hinv.symm
  rw [hx, map_units_inv, hu]

theorem zpow_mem_of_residue_ne_zero (R : RegularProlongation A F Fbar) {f : F} (hf : f ∈ R.integers)
    (h : R.residue ⟨f, hf⟩ ≠ 0) (n : ℤ) :
    ∃ hf' : f ^ n ∈ R.integers, R.residue ⟨f ^ n, hf'⟩ = (R.residue ⟨f, hf⟩) ^ n := by
  obtain ⟨k, rfl | rfl⟩ := n.eq_nat_or_neg
  · refine ⟨by rw [zpow_natCast]; exact pow_mem hf k, ?_⟩
    have : (⟨f ^ (k : ℤ), by rw [zpow_natCast]; exact pow_mem hf k⟩ : R.integers) = ⟨f, hf⟩ ^ k :=
      Subtype.ext (by rw [SubmonoidClass.coe_pow]; exact zpow_natCast f k)
    rw [this, map_pow, zpow_natCast]
  · obtain ⟨hi, hri⟩ := inv_mem_of_residue_ne_zero R hf h
    refine ⟨by rw [zpow_neg, zpow_natCast, ← inv_pow]; exact pow_mem hi k, ?_⟩
    have : (⟨f ^ (-(k : ℤ)), by rw [zpow_neg, zpow_natCast, ← inv_pow]; exact pow_mem hi k⟩ : R.integers) = ⟨f⁻¹, hi⟩ ^ k :=
      Subtype.ext (by rw [SubmonoidClass.coe_pow]; show f ^ (-(k:ℤ)) = (f⁻¹) ^ k; rw [zpow_neg, zpow_natCast, inv_pow])
    rw [this, map_pow, hri, zpow_neg, zpow_natCast, inv_pow]

theorem factor_fst (R : RegularProlongation A F Fbar) {z : F} (hz : z ∈ R.integers) (a : A) (ha : a ∈ maximalIdeal A) :
    ∃ hu : z - algebraMap L F a ∈ R.integers, R.residue ⟨z - algebraMap L F a, hu⟩ = R.residue ⟨z, hz⟩ := by
  have haI : algebraMap L F a ∈ R.integers := algebraMap_mem R a
  refine ⟨sub_mem hz haI, ?_⟩
  have : (⟨z - algebraMap L F a, sub_mem hz haI⟩ : R.integers) = ⟨z, hz⟩ - ⟨algebraMap L F a, haI⟩ := rfl
  rw [this, map_sub, residue_algebraMap' R a haI, (IsLocalRing.residue_eq_zero_iff _).mpr ha, map_zero, sub_zero]

theorem factor_snd (R' : RegularProlongation A F Fbar) {z z' : F} (hz' : z' ∈ R'.integers) (hres' : R'.residue ⟨z', hz'⟩ ≠ 0)
    (π : A) (hπ0 : (π : L) ≠ 0) (htwo : z' * z = algebraMap L F (π : L))
    (a : L) (m : A) (hm : m ∈ maximalIdeal A) (hπam : (π : L) = a * m) :
    ∃ hv : (algebraMap L F (-a))⁻¹ * (z - algebraMap L F a) ∈ R'.integers,
      R'.residue ⟨(algebraMap L F (-a))⁻¹ * (z - algebraMap L F a), hv⟩ = 1 := by
  have hz'0 : z' ≠ 0 := by
    intro h; rw [h, zero_mul] at htwo; exact (map_ne_zero _).mpr hπ0 htwo.symm
  have ha0 : a ≠ 0 := by rintro rfl; rw [zero_mul] at hπam; exact hπ0 hπam
  have hzeq : z = algebraMap L F (π : L) * z'⁻¹ := by
    rw [← htwo, mul_comm z', mul_inv_cancel_right₀ hz'0]
  obtain ⟨hinv, hres_inv⟩ := inv_mem_of_residue_ne_zero R' hz' hres'
  have hmI : algebraMap L F (m : L) ∈ R'.integers := algebraMap_mem R' m
  have key : (algebraMap L F (-a))⁻¹ * (z - algebraMap L F a) = 1 - algebraMap L F (m : L) * z'⁻¹ := by
    rw [hzeq, hπam, map_mul, map_neg]
    have haF : algebraMap L F a ≠ 0 := (map_ne_zero _).mpr ha0
    field_simp
    ring
  have hmem : (1 : F) - algebraMap L F (m : L) * z'⁻¹ ∈ R'.integers := sub_mem (one_mem _) (mul_mem hmI hinv)
  refine ⟨key ▸ hmem, ?_⟩
  have hx : (⟨_, key ▸ hmem⟩ : R'.integers) = 1 - ⟨algebraMap L F (m : L), hmI⟩ * ⟨z'⁻¹, hinv⟩ := Subtype.ext key
  rw [hx, map_sub, map_one, map_mul, residue_algebraMap' R' m hmI, (IsLocalRing.residue_eq_zero_iff _).mpr hm, map_zero,
    zero_mul, sub_zero]

theorem ord_param_sub_of_ne (An : Annulus A F) {P V : Place L F} (hP : P ∈ An.dom) (hV : V ∈ An.dom) (hne : V ≠ P) :
    V.ord (An.param - algebraMap L F (P.evalAt An.param)) = 0 := by
  obtain ⟨-, -, ⟨hPA, hPmax⟩, hP0, hPdiv⟩ := An.mem_dom P hP
  obtain ⟨hVrat, hVz, -, -, -⟩ := An.mem_dom V hV
  have hmem : An.param - algebraMap L F (P.evalAt An.param) ∈ V.toValuationSubring :=
    sub_mem hVz (V.algebraMap_mem' _)
  have hval : V.evalAt (An.param - algebraMap L F (P.evalAt An.param)) = V.evalAt An.param - P.evalAt An.param := by
    rw [evalAt_sub' V hVrat hVz (V.algebraMap_mem' _), V.evalAt_algebraMap_eq]
  have hdiff : V.evalAt An.param ≠ P.evalAt An.param := by
    intro h
    apply hne
    have hu := An.existsUnique_evalAt_eq ⟨P.evalAt An.param, hPA⟩ hPmax hP0 hPdiv
    exact hu.unique ⟨hV, h⟩ ⟨hP, rfl⟩
  refine ord_eq_zero_of_evalAt_ne_zero' V hmem ?_
  rw [hval]; exact sub_ne_zero.mpr hdiff

theorem param_sub_ne_zero (An : Annulus A F) {P : Place L F} (hP : P ∈ An.dom) :
    An.param - algebraMap L F (P.evalAt An.param) ≠ 0 := by
  intro h
  have h1 := An.ord_param_sub P hP
  rw [h, Place.ord_zero] at h1
  exact zero_ne_one h1

theorem ord_prod_param_sub_zpow [DecidableEq (Place L F)] (An : Annulus A F) (s : Finset (Place L F)) (hs : ∀ P ∈ s, P ∈ An.dom)
    (n : Place L F → ℤ) {V : Place L F} (hV : V ∈ An.dom) :
    V.ord (∏ P ∈ s, (An.param - algebraMap L F (P.evalAt An.param)) ^ n P) = if V ∈ s then n V else 0 := by
  rw [ord_prod' V s _ fun P hP => zpow_ne_zero _ (param_sub_ne_zero An (hs P hP))]
  simp_rw [Place.ord_zpow]
  rw [← Finset.sum_filter_add_sum_filter_not s (fun P => P = V)]
  have h2 : ∑ P ∈ s.filter (fun P => ¬ P = V), n P * V.ord (An.param - algebraMap L F (P.evalAt An.param)) = 0 := by
    refine Finset.sum_eq_zero fun P hP => ?_
    rw [Finset.mem_filter] at hP
    rw [ord_param_sub_of_ne An (hs P hP.1) hV (Ne.symm hP.2), mul_zero]
  rw [h2, add_zero]
  by_cases hVs : V ∈ s
  · rw [if_pos hVs, Finset.filter_eq' s V, if_pos hVs, Finset.sum_singleton, An.ord_param_sub V hV, mul_one]
  · rw [if_neg hVs, Finset.filter_eq' s V, if_neg hVs, Finset.sum_empty]

theorem valuation_eq_zpow_of_isUnit {x w : L} {m : ℤ} (hw : w ≠ 0)
    (h : x * w ^ (-m) ∈ A) (hu : IsUnit (⟨x * w ^ (-m), h⟩ : A)) :
    A.valuation x = A.valuation w ^ m := by
  have h1 : A.valuation (x * w ^ (-m)) = 1 := (A.valuation_eq_one_iff _).mp hu
  rw [map_mul, map_zpow₀, zpow_neg] at h1
  have hw' : A.valuation w ^ m ≠ 0 := zpow_ne_zero _ ((map_ne_zero A.valuation).mpr hw)
  exact (mul_inv_eq_one₀ hw').mp h1

theorem eq_of_zpow_eq_zpow {Γ : Type*} [LinearOrderedCommGroupWithZero Γ] {a b : Γ} {n : ℤ} (hn : n ≠ 0)
    (h : a ^ n = b ^ n) : a = b :=
  (zpow_left_inj₀ zero_le' zero_le' hn).mp h

end Prolongation

section Main

variable {L : Type*} [Field L] {A : ValuationSubring L} {F : Type*} [Field F] [Algebra L F]
  {Fa : Type*} [Field Fa] [Algebra (ResidueField A) Fa]
  {Fb : Type*} [Field Fb] [Algebra (ResidueField A) Fb]

theorem twoEnd
    (An : Annulus A F) (hmod0 : (An.modulus : L) ≠ 0)
    (Ra : RegularProlongation A F Fa) (xa : Place (ResidueField A) Fa)
    (hza : An.param ∈ Ra.integers) (hxa : xa.ord (Ra.residue ⟨An.param, hza⟩) = 1)
    (hslope_a : ∀ (f : F) (hf : f ∈ Ra.integers), Ra.residue ⟨f, hf⟩ ≠ 0 →
      (∀ P ∈ An.dom, P.ord f = 0) → ∀ P ∈ An.dom,
        ∃ h : P.evalAt f * (P.evalAt An.param) ^ (-(xa.ord (Ra.residue ⟨f, hf⟩))) ∈ A, IsUnit (⟨_, h⟩ : A))
    (Rb : RegularProlongation A F Fb) (xb : Place (ResidueField A) Fb)
    (hzb : algebraMap L F (An.modulus : L) * An.param⁻¹ ∈ Rb.integers)
    (hxb : xb.ord (Rb.residue ⟨algebraMap L F (An.modulus : L) * An.param⁻¹, hzb⟩) = 1)
    (hslope_b : ∀ (f : F) (hf : f ∈ Rb.integers), Rb.residue ⟨f, hf⟩ ≠ 0 →
      (∀ P ∈ An.dom, P.ord f = 0) → ∀ P ∈ An.dom,
        ∃ h : P.evalAt f * (P.evalAt (algebraMap L F (An.modulus : L) * An.param⁻¹)) ^
          (-(xb.ord (Rb.residue ⟨f, hf⟩))) ∈ A, IsUnit (⟨_, h⟩ : A))
    (hwide : ∃ Q₁ ∈ An.dom, ∃ Q₂ ∈ An.dom, A.valuation (Q₁.evalAt An.param) ≠ A.valuation (Q₂.evalAt An.param))
    (h : F) (hh0 : h ≠ 0) (hha : h ∈ Ra.integers) (hresa : Ra.residue ⟨h, hha⟩ ≠ 0)
    (c' : L) (hc'0 : c' ≠ 0)
    (hhb : (algebraMap L F c')⁻¹ * h ∈ Rb.integers) (hresb : Rb.residue ⟨(algebraMap L F c')⁻¹ * h, hhb⟩ ≠ 0)
    (D : Place L F →₀ ℤ) (hDsupp : ∀ P ∈ D.support, P ∈ An.dom) (hD : ∀ P ∈ An.dom, D P = P.ord h) :
    (D.sum fun _ n => n) = xa.ord (Ra.residue ⟨h, hha⟩) + xb.ord (Rb.residue ⟨(algebraMap L F c')⁻¹ * h, hhb⟩) ∧
    (D.prod fun P n => A.valuation (P.evalAt An.param) ^ n) =
      A.valuation c' * A.valuation (An.modulus : L) ^ (xb.ord (Rb.residue ⟨(algebraMap L F c')⁻¹ * h, hhb⟩)) := by
  classical

  set s : Finset (Place L F) := D.support with hsdef
  have hs : ∀ P ∈ s, P ∈ An.dom := hDsupp
  have ha0 : ∀ P ∈ s, P.evalAt An.param ≠ 0 := fun P hP => (An.mem_dom P (hs P hP)).2.2.2.1

  have hzres0 : Ra.residue ⟨An.param, hza⟩ ≠ 0 := by
    intro h0; rw [h0, Place.ord_zero] at hxa; exact zero_ne_one hxa
  have hwres0 : Rb.residue ⟨algebraMap L F (An.modulus : L) * An.param⁻¹, hzb⟩ ≠ 0 := by
    intro h0; rw [h0, Place.ord_zero] at hxb; exact zero_ne_one hxb
  have hz0 : An.param ≠ 0 := by
    intro h0
    apply hwres0
    have : (⟨algebraMap L F (An.modulus : L) * An.param⁻¹, hzb⟩ : Rb.integers) = 0 :=
      Subtype.ext (by show algebraMap L F (An.modulus : L) * An.param⁻¹ = 0; rw [h0, inv_zero, mul_zero])
    rw [this, map_zero]
  have hwz : algebraMap L F (An.modulus : L) * An.param⁻¹ * An.param = algebraMap L F (An.modulus : L) := by
    rw [inv_mul_cancel_right₀ hz0]

  set U : F := ∏ P ∈ s, (An.param - algebraMap L F (P.evalAt An.param)) ^ D P with hU
  have hU0 : U ≠ 0 := Finset.prod_ne_zero_iff.mpr fun P hP => zpow_ne_zero _ (param_sub_ne_zero An (hs P hP))
  set g : F := h * U⁻¹ with hgdef
  have hg0 : g ≠ 0 := mul_ne_zero hh0 (inv_ne_zero hU0)
  have hgord : ∀ Q ∈ An.dom, Q.ord g = 0 := by
    intro Q hQ
    have hUQ : Q.ord U = D Q := by
      rw [hU, ord_prod_param_sub_zpow An s hs D hQ]
      by_cases hQs : Q ∈ s
      · rw [if_pos hQs]
      · rw [if_neg hQs]; exact (Finsupp.notMem_support_iff.mp hQs).symm
    rw [hgdef, Q.ord_mul hh0 (inv_ne_zero hU0), Q.ord_inv, hUQ, ← hD Q hQ, add_neg_cancel]

  have hfacA : ∀ P ∈ s, ∃ hP : (An.param - algebraMap L F (P.evalAt An.param)) ^ D P ∈ Ra.integers,
      Ra.residue ⟨_, hP⟩ = Ra.residue ⟨An.param, hza⟩ ^ D P := by
    intro P hP
    obtain ⟨-, -, ⟨haA, hamax⟩, -, -⟩ := An.mem_dom P (hs P hP)
    obtain ⟨hu, hures⟩ := factor_fst Ra hza ⟨_, haA⟩ hamax
    obtain ⟨hz, hzr⟩ := zpow_mem_of_residue_ne_zero Ra hu (by rw [hures]; exact hzres0) (D P)
    exact ⟨hz, by rw [hzr, hures]⟩
  choose hUmem hUres using hfacA
  have hUA : U ∈ Ra.integers := by
    rw [hU]; exact prod_mem fun P hP => hUmem P hP
  have hUres_eq : Ra.residue ⟨U, hUA⟩ = ∏ P ∈ s.attach, Ra.residue ⟨An.param, hza⟩ ^ D P := by
    have : (⟨U, hUA⟩ : Ra.integers) = ∏ P ∈ s.attach, ⟨_, hUmem P P.2⟩ := by
      apply Subtype.ext
      show U = _
      rw [SubmonoidClass.coe_finsetProd, hU]
      exact (Finset.prod_attach s (fun P => (An.param - algebraMap L F (P.evalAt An.param)) ^ D P)).symm
    rw [this, map_prod]
    exact Finset.prod_congr rfl fun P _ => hUres P P.2
  have hUres0 : Ra.residue ⟨U, hUA⟩ ≠ 0 := by
    rw [hUres_eq]; exact Finset.prod_ne_zero_iff.mpr fun P _ => zpow_ne_zero _ hzres0
  obtain ⟨hUinvA, hUinvres⟩ := inv_mem_of_residue_ne_zero Ra hUA hUres0
  have hgA : g ∈ Ra.integers := by rw [hgdef]; exact mul_mem hha hUinvA
  have hgres : Ra.residue ⟨g, hgA⟩ = Ra.residue ⟨h, hha⟩ * (Ra.residue ⟨U, hUA⟩)⁻¹ := by
    have : (⟨g, hgA⟩ : Ra.integers) = ⟨h, hha⟩ * ⟨U⁻¹, hUinvA⟩ := Subtype.ext hgdef
    rw [this, map_mul, hUinvres]
  have hgres0 : Ra.residue ⟨g, hgA⟩ ≠ 0 := by rw [hgres]; exact mul_ne_zero hresa (inv_ne_zero hUres0)
  have hordU : xa.ord (Ra.residue ⟨U, hUA⟩) = ∑ P ∈ s, D P := by
    rw [hUres_eq, ord_prod' xa _ _ (fun P _ => zpow_ne_zero _ hzres0)]
    have : ∀ P ∈ s.attach, xa.ord (Ra.residue ⟨An.param, hza⟩ ^ D (P : Place L F)) = D P := by
      intro P _
      rw [Place.ord_zpow, hxa, mul_one]
    rw [Finset.sum_congr rfl this]
    exact Finset.sum_attach s D

  set ma : ℤ := xa.ord (Ra.residue ⟨g, hgA⟩) with hma
  have hordg : ma = xa.ord (Ra.residue ⟨h, hha⟩) - ∑ P ∈ s, D P := by
    rw [hma, hgres, xa.ord_mul hresa (inv_ne_zero hUres0), xa.ord_inv, hordU]; ring

  have hslopeA : ∀ Q ∈ An.dom, A.valuation (Q.evalAt g) = A.valuation (Q.evalAt An.param) ^ ma := by
    intro Q hQ
    obtain ⟨hmem, hunit⟩ := hslope_a g hgA hgres0 hgord Q hQ
    exact valuation_eq_zpow_of_isUnit ((An.mem_dom Q hQ).2.2.2.1) hmem hunit

  have hfacB : ∀ P ∈ s, ∃ hP : ((algebraMap L F (-(P.evalAt An.param)))⁻¹ *
        (An.param - algebraMap L F (P.evalAt An.param))) ^ D P ∈ Rb.integers, Rb.residue ⟨_, hP⟩ = 1 := by
    intro P hP
    obtain ⟨-, -, -, ha0', m, hm, hπam⟩ := An.mem_dom P (hs P hP)
    obtain ⟨hv, hvres⟩ := factor_snd Rb hzb hwres0 An.modulus hmod0 hwz (P.evalAt An.param) m hm hπam
    obtain ⟨hz', hzr⟩ := zpow_mem_of_residue_ne_zero Rb hv (by rw [hvres]; exact one_ne_zero) (D P)
    exact ⟨hz', by rw [hzr, hvres, one_zpow]⟩
  choose hWmem hWres using hfacB
  set W : F := ∏ P ∈ s, ((algebraMap L F (-(P.evalAt An.param)))⁻¹ *
      (An.param - algebraMap L F (P.evalAt An.param))) ^ D P with hW
  have hWB : W ∈ Rb.integers := by rw [hW]; exact prod_mem fun P hP => hWmem P hP
  have hWres1 : Rb.residue ⟨W, hWB⟩ = 1 := by
    have : (⟨W, hWB⟩ : Rb.integers) = ∏ P ∈ s.attach, ⟨_, hWmem P P.2⟩ := by
      apply Subtype.ext
      show W = _
      rw [SubmonoidClass.coe_finsetProd, hW]
      exact (Finset.prod_attach s (fun P => ((algebraMap L F (-(P.evalAt An.param)))⁻¹ *
        (An.param - algebraMap L F (P.evalAt An.param))) ^ D P)).symm
    rw [this, map_prod]
    exact Finset.prod_eq_one fun P _ => hWres P P.2

  set κU : L := ∏ P ∈ s, (-(P.evalAt An.param)) ^ D P with hκU
  have hκU0 : κU ≠ 0 := Finset.prod_ne_zero_iff.mpr fun P hP => zpow_ne_zero _ (neg_ne_zero.mpr (ha0 P hP))
  have hUW : U = algebraMap L F κU * W := by
    rw [hU, hW, hκU, map_prod, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun P hP => ?_
    have hane : algebraMap L F (-(P.evalAt An.param)) ≠ 0 := (map_ne_zero _).mpr (neg_ne_zero.mpr (ha0 P hP))
    rw [map_zpow₀, ← mul_zpow, mul_inv_cancel_left₀ hane]
  have hW0 : W ≠ 0 := by
    intro h0; apply hU0; rw [hUW, h0, mul_zero]
  obtain ⟨hWinvB, hWinvres⟩ := inv_mem_of_residue_ne_zero Rb hWB (by rw [hWres1]; exact one_ne_zero)

  set cg : L := c' * κU⁻¹ with hcg
  have hcg0 : cg ≠ 0 := mul_ne_zero hc'0 (inv_ne_zero hκU0)
  set g' : F := (algebraMap L F cg)⁻¹ * g with hg'def
  have hcgg : g' = ((algebraMap L F c')⁻¹ * h) * W⁻¹ := by
    rw [hg'def, hgdef, hUW, hcg, map_mul, map_inv₀]
    have h1 : algebraMap L F c' ≠ 0 := (map_ne_zero _).mpr hc'0
    have h2 : algebraMap L F κU ≠ 0 := (map_ne_zero _).mpr hκU0
    field_simp
  have hg'B : g' ∈ Rb.integers := by rw [hcgg]; exact mul_mem hhb hWinvB
  have hg'res : Rb.residue ⟨g', hg'B⟩ = Rb.residue ⟨(algebraMap L F c')⁻¹ * h, hhb⟩ := by
    have : (⟨g', hg'B⟩ : Rb.integers) = ⟨(algebraMap L F c')⁻¹ * h, hhb⟩ * ⟨W⁻¹, hWinvB⟩ := Subtype.ext hcgg
    rw [this, map_mul, hWinvres, hWres1, inv_one, mul_one]
  have hg'res0 : Rb.residue ⟨g', hg'B⟩ ≠ 0 := by rw [hg'res]; exact hresb
  set mb : ℤ := xb.ord (Rb.residue ⟨(algebraMap L F c')⁻¹ * h, hhb⟩) with hmb
  have hg'ord : ∀ Q ∈ An.dom, Q.ord g' = 0 := by
    intro Q hQ
    have hc : (algebraMap L F cg)⁻¹ ≠ 0 := inv_ne_zero ((map_ne_zero _).mpr hcg0)
    rw [hg'def, Q.ord_mul hc hg0, hgord Q hQ, add_zero, ← map_inv₀, ord_algebraMap' Q (inv_ne_zero hcg0)]

  have hwval : ∀ Q ∈ An.dom, Q.evalAt (algebraMap L F (An.modulus : L) * An.param⁻¹) =
      (An.modulus : L) * (Q.evalAt An.param)⁻¹ := by
    intro Q hQ
    obtain ⟨hQrat, hQz, -, hQz0, -⟩ := An.mem_dom Q hQ
    obtain ⟨hzinv, hzinv_val⟩ := inv_mem_and_evalAt_inv' Q hQrat hQz hQz0
    rw [Q.evalAt_mul_of_mem hQrat (Q.algebraMap_mem' _) hzinv, Q.evalAt_algebraMap_eq, hzinv_val]
  have hg'val : ∀ Q ∈ An.dom, Q.evalAt g' = cg⁻¹ * Q.evalAt g := by
    intro Q hQ
    obtain ⟨hQrat, -, -, -, -⟩ := An.mem_dom Q hQ
    have hgQ : g ∈ Q.toValuationSubring := Q.mem_toValuationSubring_of_ord_nonneg_alt hg0 (hgord Q hQ).ge
    rw [hg'def, ← map_inv₀, Q.evalAt_mul_of_mem hQrat (Q.algebraMap_mem' _) hgQ, Q.evalAt_algebraMap_eq]

  have hslopeB : ∀ Q ∈ An.dom, A.valuation (Q.evalAt g') =
      A.valuation (Q.evalAt (algebraMap L F (An.modulus : L) * An.param⁻¹)) ^ mb := by
    intro Q hQ
    obtain ⟨hmem, hunit⟩ := hslope_b g' hg'B hg'res0 hg'ord Q hQ
    have hw0 : Q.evalAt (algebraMap L F (An.modulus : L) * An.param⁻¹) ≠ 0 := by
      rw [hwval Q hQ]; exact mul_ne_zero hmod0 (inv_ne_zero (An.mem_dom Q hQ).2.2.2.1)
    have := valuation_eq_zpow_of_isUnit hw0 hmem hunit
    rwa [hg'res] at this

  have hprofile : ∀ Q ∈ An.dom,
      A.valuation (Q.evalAt An.param) ^ (ma + mb) = A.valuation cg * A.valuation (An.modulus : L) ^ mb := by
    intro Q hQ
    have hQz0 : Q.evalAt An.param ≠ 0 := (An.mem_dom Q hQ).2.2.2.1
    have hA := hslopeA Q hQ
    have hB := hslopeB Q hQ
    rw [hg'val Q hQ, map_mul A.valuation cg⁻¹ (Q.evalAt g), map_inv₀ A.valuation cg, hA, hwval Q hQ,
      map_mul A.valuation (An.modulus : L) (Q.evalAt An.param)⁻¹, map_inv₀ A.valuation (Q.evalAt An.param)] at hB

    have hvz0 : A.valuation (Q.evalAt An.param) ≠ 0 := (map_ne_zero A.valuation).mpr hQz0
    have hvcg0 : A.valuation cg ≠ 0 := (map_ne_zero A.valuation).mpr hcg0
    rw [mul_zpow, inv_zpow, ← zpow_neg] at hB
    rw [zpow_add₀ hvz0]
    calc A.valuation (Q.evalAt An.param) ^ ma * A.valuation (Q.evalAt An.param) ^ mb
        = A.valuation cg * ((A.valuation cg)⁻¹ * A.valuation (Q.evalAt An.param) ^ ma) *
            A.valuation (Q.evalAt An.param) ^ mb := by
          rw [mul_inv_cancel_left₀ hvcg0]
      _ = A.valuation cg * (A.valuation (An.modulus : L) ^ mb * A.valuation (Q.evalAt An.param) ^ (-mb)) *
            A.valuation (Q.evalAt An.param) ^ mb := by
          rw [hB]
      _ = A.valuation cg * A.valuation (An.modulus : L) ^ mb := by
          rw [zpow_neg, mul_assoc, mul_assoc, inv_mul_cancel₀ (zpow_ne_zero _ hvz0), mul_one]

  have hsum0 : ma + mb = 0 := by
    by_contra hne
    obtain ⟨Q₁, hQ₁, Q₂, hQ₂, hneq⟩ := hwide
    apply hneq
    have h12 : A.valuation (Q₁.evalAt An.param) ^ (ma + mb) = A.valuation (Q₂.evalAt An.param) ^ (ma + mb) := by
      rw [hprofile Q₁ hQ₁, hprofile Q₂ hQ₂]
    exact eq_of_zpow_eq_zpow hne h12

  refine ⟨?_, ?_⟩
  ·
    show ∑ P ∈ D.support, D P = _
    rw [← hsdef]
    have : ∑ P ∈ s, D P = xa.ord (Ra.residue ⟨h, hha⟩) - ma := by rw [hordg]; ring
    rw [this]
    omega
  ·
    show ∏ P ∈ D.support, A.valuation (P.evalAt An.param) ^ D P = _
    rw [← hsdef]
    obtain ⟨Q₁, hQ₁, -⟩ := hwide
    have hkey := hprofile Q₁ hQ₁
    rw [hsum0, zpow_zero] at hkey

    have hvκ : A.valuation κU = ∏ P ∈ s, A.valuation (P.evalAt An.param) ^ D P := by
      rw [hκU, map_prod]
      refine Finset.prod_congr rfl fun P _ => ?_
      rw [map_zpow₀, Valuation.map_neg]
    have hprod0 : (∏ P ∈ s, A.valuation (P.evalAt An.param) ^ D P) ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr fun P hP => zpow_ne_zero _ ((map_ne_zero A.valuation).mpr (ha0 P hP))
    rw [hcg, map_mul, map_inv₀, hvκ] at hkey

    calc ∏ P ∈ s, A.valuation (P.evalAt An.param) ^ D P
        = (∏ P ∈ s, A.valuation (P.evalAt An.param) ^ D P) * 1 := (mul_one _).symm
      _ = (∏ P ∈ s, A.valuation (P.evalAt An.param) ^ D P) *
            (A.valuation c' * (∏ P ∈ s, A.valuation (P.evalAt An.param) ^ D P)⁻¹ *
              A.valuation (An.modulus : L) ^ mb) := by rw [← hkey]
      _ = A.valuation c' * A.valuation (An.modulus : L) ^ mb := by
          rw [mul_comm (A.valuation c') ((∏ P ∈ s, A.valuation (P.evalAt An.param) ^ D P)⁻¹), mul_assoc,
            mul_inv_cancel_left₀ hprod0]

end Main

end AnnulusTwoEndVal

theorem solution
    {L : Type*} [Field L] {A : ValuationSubring L} {F : Type*} [Field F] [Algebra L F]
    {Fa : Type*} [Field Fa] [Algebra (ResidueField A) Fa]
    {Fb : Type*} [Field Fb] [Algebra (ResidueField A) Fb]
    (An : Annulus A F) (hmod0 : (An.modulus : L) ≠ 0)

    (Ra : RegularProlongation A F Fa) (xa : Place (ResidueField A) Fa)
    (hza : An.param ∈ Ra.integers) (hxa : xa.ord (Ra.residue ⟨An.param, hza⟩) = 1)
    (hslope_a : ∀ (f : F) (hf : f ∈ Ra.integers), Ra.residue ⟨f, hf⟩ ≠ 0 →
      (∀ P ∈ An.dom, P.ord f = 0) → ∀ P ∈ An.dom,
        ∃ h : P.evalAt f * (P.evalAt An.param) ^ (-(xa.ord (Ra.residue ⟨f, hf⟩))) ∈ A, IsUnit (⟨_, h⟩ : A))

    (Rb : RegularProlongation A F Fb) (xb : Place (ResidueField A) Fb)
    (hzb : algebraMap L F (An.modulus : L) * An.param⁻¹ ∈ Rb.integers)
    (hxb : xb.ord (Rb.residue ⟨algebraMap L F (An.modulus : L) * An.param⁻¹, hzb⟩) = 1)
    (hslope_b : ∀ (f : F) (hf : f ∈ Rb.integers), Rb.residue ⟨f, hf⟩ ≠ 0 →
      (∀ P ∈ An.dom, P.ord f = 0) → ∀ P ∈ An.dom,
        ∃ h : P.evalAt f * (P.evalAt (algebraMap L F (An.modulus : L) * An.param⁻¹)) ^
          (-(xb.ord (Rb.residue ⟨f, hf⟩))) ∈ A, IsUnit (⟨_, h⟩ : A))

    (hwide : ∃ Q₁ ∈ An.dom, ∃ Q₂ ∈ An.dom, A.valuation (Q₁.evalAt An.param) ≠ A.valuation (Q₂.evalAt An.param))

    (h : F) (hh0 : h ≠ 0) (hha : h ∈ Ra.integers) (hresa : Ra.residue ⟨h, hha⟩ ≠ 0)
    (c' : L) (hc'0 : c' ≠ 0)
    (hhb : (algebraMap L F c')⁻¹ * h ∈ Rb.integers) (hresb : Rb.residue ⟨(algebraMap L F c')⁻¹ * h, hhb⟩ ≠ 0)

    (D : Divisor L F) (hDsupp : ∀ P ∈ D.support, P ∈ An.dom) (hD : ∀ P ∈ An.dom, D P = P.ord h) :
    (D.sum fun _ n => n) = xa.ord (Ra.residue ⟨h, hha⟩) + xb.ord (Rb.residue ⟨(algebraMap L F c')⁻¹ * h, hhb⟩) ∧
    (D.prod fun P n => A.valuation (P.evalAt An.param) ^ n) =
      A.valuation c' * A.valuation (An.modulus : L) ^ (xb.ord (Rb.residue ⟨(algebraMap L F c')⁻¹ * h, hhb⟩)) :=
  AnnulusTwoEndVal.twoEnd An hmod0 Ra xa hza hxa hslope_a Rb xb hzb hxb hslope_b hwide h hh0 hha hresa c' hc'0 hhb hresb
    D hDsupp hD

end S_AlgebraicCurve_Annulus_sum_eq_ord_add_ord_and_prod_valuation_evalAt_zpow_eq_of_regularProlongation
end P2MW
export P2MW.S_AlgebraicCurve_Annulus_sum_eq_ord_add_ord_and_prod_valuation_evalAt_zpow_eq_of_regularProlongation (solution)

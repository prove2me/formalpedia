-- Prove2me | solution 1 for AlgebraicCurve.Annulus.exists_valuationSubring_mem_iff_of_valuation_lt
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/5c94f9fa-1aa9-5706-a7f9-1bd8677d0acc

import Definitions.Def_AlgebraicCurve_SemistableCharts
import Definitions.Def_AlgebraicCurve_StandardAnnulus
import Theorems.Thm_AlgebraicCurve_Annulus_exists_eq_mul_prod_param_sub_zpow
import Theorems.Thm_AlgebraicCurve_Annulus_valuation_evalAt_param_sub_algebraMap
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_Annulus_exists_valuationSubring_mem_iff_of_valuation_lt

set_option autoImplicit false

p2m_open "AlgebraicCurve P2MW.S_AlgebraicCurve_Annulus_exists_valuationSubring_mem_iff_of_valuation_lt.AlgebraicCurve IsLocalRing AlgebraicCurve.RationalFunctionField"

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "Annulus Place Place.ord_zero Annulus.exists_eq_mul_prod_param_sub_zpow Annulus.valuation_evalAt_param_sub_algebraMap"
namespace Annulus
p2m_export "AlgebraicCurve.Annulus" "unit_principle existsUnique_evalAt_eq modulus dom mem_dom param ord_param_sub exists_eq_mul_prod_param_sub_zpow valuation_evalAt_param_sub_algebraMap"
namespace CircleRing
p2m_open "AlgebraicCurve.Annulus AlgebraicCurve"

open AlgebraicCurve.GaussReduction AlgebraicCurve.StandardAnnulus

variable {L : Type*} [Field L] {F : Type*} [Field F] [Algebra L F]

theorem evalAt_zero' (P : Place L F) (hP : P.IsRational) : P.evalAt (0 : F) = 0 := by
  have h := evalAt_sub_of_mem P hP (one_mem P.toValuationSubring) (one_mem P.toValuationSubring)
  rwa [sub_self, sub_self] at h

theorem evalAt_add_of_mem (P : Place L F) (hP : P.IsRational) {f g : F}
    (hf : f ∈ P.toValuationSubring) (hg : g ∈ P.toValuationSubring) :
    P.evalAt (f + g) = P.evalAt f + P.evalAt g := by
  have h1 : f + g = f - (0 - g) := by ring
  rw [h1, evalAt_sub_of_mem P hP hf (sub_mem (zero_mem _) hg),
    evalAt_sub_of_mem P hP (zero_mem _) hg, evalAt_zero' P hP]
  ring

theorem evalAt_neg_of_mem (P : Place L F) (hP : P.IsRational) {f : F}
    (hf : f ∈ P.toValuationSubring) : P.evalAt (-f) = -P.evalAt f := by
  have h1 : -f = 0 - f := by ring
  rw [h1, evalAt_sub_of_mem P hP (zero_mem _) hf, evalAt_zero' P hP, zero_sub]

theorem evalAt_prod_of_mem (P : Place L F) (hP : P.IsRational) {ι : Type*} (t : Finset ι) (u : ι → F)
    (hu : ∀ i ∈ t, u i ∈ P.toValuationSubring) :
    (∏ i ∈ t, u i) ∈ P.toValuationSubring ∧ P.evalAt (∏ i ∈ t, u i) = ∏ i ∈ t, P.evalAt (u i) := by
  classical
  induction t using Finset.induction_on with
  | empty => simp [P.evalAt_one]
  | insert i t hit ih =>
    rw [Finset.forall_mem_insert] at hu
    obtain ⟨hmem, hev⟩ := ih hu.2
    refine ⟨?_, ?_⟩
    · rw [Finset.prod_insert hit]; exact mul_mem hu.1 hmem
    · rw [Finset.prod_insert hit, Finset.prod_insert hit, evalAt_mul_of_mem P hP hu.1 hmem, hev]

theorem evalAt_pow_of_mem (P : Place L F) (hP : P.IsRational) {f : F} (hf : f ∈ P.toValuationSubring) (n : ℕ) :
    P.evalAt (f ^ n) = P.evalAt f ^ n := by
  induction n with
  | zero => simp [P.evalAt_one]
  | succ n ih => rw [pow_succ, pow_succ, evalAt_mul_of_mem P hP (pow_mem hf n) hf, ih]

theorem evalAt_zpow_of_ord_eq_zero (P : Place L F) (hP : P.IsRational) {f : F} (hf0 : f ≠ 0)
    (h : P.ord f = 0) (n : ℤ) :
    f ^ n ∈ P.toValuationSubring ∧ P.evalAt (f ^ n) = P.evalAt f ^ n := by
  have hmem : f ∈ P.toValuationSubring := mem_of_ord_nonneg_gen P hf0 h.ge
  have hmem' : f⁻¹ ∈ P.toValuationSubring :=
    mem_of_ord_nonneg_gen P (inv_ne_zero hf0) (by rw [P.ord_inv]; omega)
  rcases Int.eq_nat_or_neg n with ⟨m, rfl | rfl⟩
  · exact ⟨by rw [zpow_natCast]; exact pow_mem hmem m, by rw [zpow_natCast, zpow_natCast, evalAt_pow_of_mem P hP hmem]⟩
  · refine ⟨by rw [zpow_neg, zpow_natCast, ← inv_pow]; exact pow_mem hmem' m, ?_⟩
    rw [zpow_neg, zpow_natCast, zpow_neg, zpow_natCast, ← inv_pow, ← inv_pow,
      evalAt_pow_of_mem P hP hmem' m, evalAt_inv_of_ord_eq_zero P hP hf0 h]

end AlgebraicCurve.Annulus.CircleRing

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "Annulus Place Place.ord_zero Annulus.exists_eq_mul_prod_param_sub_zpow Annulus.valuation_evalAt_param_sub_algebraMap"
namespace Annulus
p2m_export "AlgebraicCurve.Annulus" "unit_principle existsUnique_evalAt_eq modulus dom mem_dom param ord_param_sub exists_eq_mul_prod_param_sub_zpow valuation_evalAt_param_sub_algebraMap"
namespace CircleRing
p2m_open "AlgebraicCurve.Annulus AlgebraicCurve"

open AlgebraicCurve.GaussReduction AlgebraicCurve.StandardAnnulus
open scoped Classical

variable {L : Type*} [Field L] {A : ValuationSubring L} {F : Type*} [Field F] [Algebra L F]

def Good (An : Annulus A F) (c : L) (t : Finset (IsLocalRing.ResidueField A)) (f : F) : Prop :=
  ∀ P ∈ An.dom, ∀ h : c⁻¹ * P.evalAt An.param ∈ A, A.valuation (P.evalAt An.param) = A.valuation c →
    IsLocalRing.residue A ⟨c⁻¹ * P.evalAt An.param, h⟩ ∉ t → f ∈ P.toValuationSubring ∧ P.evalAt f ∈ A

variable (An : Annulus A F) (c : L)

theorem Good.mono {t t' : Finset (IsLocalRing.ResidueField A)} (htt' : t ⊆ t') {f : F} (hf : Good An c t f) :
    Good An c t' f :=
  fun P hP h hv hnot => hf P hP h hv (fun hm => hnot (htt' hm))

theorem good_zero (t : Finset (IsLocalRing.ResidueField A)) : Good An c t (0 : F) := by
  intro P hP h hv hnot
  exact ⟨zero_mem _, by rw [evalAt_zero' P (An.mem_dom P hP).1]; exact zero_mem _⟩

theorem good_algebraMap (t : Finset (IsLocalRing.ResidueField A)) {x : L} (hx : x ∈ A) :
    Good An c t (algebraMap L F x) := by
  intro P hP h hv hnot
  exact ⟨P.algebraMap_mem' x, by rw [evalAt_algebraMap_const P (An.mem_dom P hP).1]; exact hx⟩

theorem good_one (t : Finset (IsLocalRing.ResidueField A)) : Good An c t (1 : F) := by
  simpa using good_algebraMap An c t A.one_mem

theorem Good.add {t t' : Finset (IsLocalRing.ResidueField A)} {f g : F} (hf : Good An c t f) (hg : Good An c t' g) :
    Good An c (t ∪ t') (f + g) := by
  intro P hP h hv hnot
  rw [Finset.mem_union, not_or] at hnot
  obtain ⟨hfm, hfv⟩ := hf P hP h hv hnot.1
  obtain ⟨hgm, hgv⟩ := hg P hP h hv hnot.2
  exact ⟨add_mem hfm hgm, by rw [evalAt_add_of_mem P (An.mem_dom P hP).1 hfm hgm]; exact add_mem hfv hgv⟩

theorem Good.mul {t t' : Finset (IsLocalRing.ResidueField A)} {f g : F} (hf : Good An c t f) (hg : Good An c t' g) :
    Good An c (t ∪ t') (f * g) := by
  intro P hP h hv hnot
  rw [Finset.mem_union, not_or] at hnot
  obtain ⟨hfm, hfv⟩ := hf P hP h hv hnot.1
  obtain ⟨hgm, hgv⟩ := hg P hP h hv hnot.2
  exact ⟨mul_mem hfm hgm, by rw [evalAt_mul_of_mem P (An.mem_dom P hP).1 hfm hgm]; exact mul_mem hfv hgv⟩

theorem Good.neg {t : Finset (IsLocalRing.ResidueField A)} {f : F} (hf : Good An c t f) : Good An c t (-f) := by
  intro P hP h hv hnot
  obtain ⟨hfm, hfv⟩ := hf P hP h hv hnot
  exact ⟨neg_mem hfm, by rw [evalAt_neg_of_mem P (An.mem_dom P hP).1 hfm]; exact neg_mem hfv⟩

variable {An c}

theorem exists_mem_dom_evalAt_eq (hc : A.valuation ((An.modulus : A) : L) < A.valuation c ∧ A.valuation c < 1)
    (u : A) (hu : IsUnit u) : ∃ P ∈ An.dom, P.evalAt An.param = c * u := by
  have hvu : A.valuation (u : L) = 1 := (A.valuation_eq_one_iff u).mp hu
  have hc0 : c ≠ 0 := by
    intro h0; rw [h0, Valuation.map_zero] at hc; exact (not_lt_of_ge zero_le' hc.1).elim
  have hu0 : (u : L) ≠ 0 := by
    intro h0; rw [h0, Valuation.map_zero] at hvu; exact zero_ne_one hvu
  have hcuA : c * u ∈ A := (A.valuation_le_one_iff _).mp (by rw [Valuation.map_mul, hvu, mul_one]; exact hc.2.le)
  have hcu_max : (⟨c * u, hcuA⟩ : A) ∈ IsLocalRing.maximalIdeal A := by
    rw [ValuationSubring.valuation_lt_one_iff]
    show A.valuation (c * u) < 1
    rw [Valuation.map_mul, hvu, mul_one]; exact hc.2
  have hcu0 : ((⟨c * u, hcuA⟩ : A) : L) ≠ 0 := mul_ne_zero hc0 hu0

  set m : L := (An.modulus : L) * (c * u)⁻¹ with hm
  have hvm : A.valuation m < 1 := by
    rw [hm, Valuation.map_mul, Valuation.map_inv, Valuation.map_mul, hvu, mul_one]
    exact mul_inv_lt_of_lt_mul₀ (show A.valuation ((An.modulus : A) : L) < 1 * A.valuation c by rw [one_mul]; exact hc.1)
  have hmA : m ∈ A := (A.valuation_le_one_iff _).mp hvm.le
  have hm_max : (⟨m, hmA⟩ : A) ∈ IsLocalRing.maximalIdeal A := by
    rw [ValuationSubring.valuation_lt_one_iff]; exact hvm
  have hmod : ∃ m' ∈ IsLocalRing.maximalIdeal A, ((An.modulus : A) : L) = ((⟨c * u, hcuA⟩ : A) : L) * m' :=
    ⟨⟨m, hmA⟩, hm_max, by show (An.modulus : L) = c * u * m; rw [hm, mul_left_comm, mul_inv_cancel₀ (mul_ne_zero hc0 hu0), mul_one]⟩
  obtain ⟨P, ⟨hPdom, hPev⟩, -⟩ := An.existsUnique_evalAt_eq ⟨c * u, hcuA⟩ hcu_max hcu0 hmod
  exact ⟨P, hPdom, hPev⟩

theorem exists_mem_dom_residue_notMem (hc : A.valuation ((An.modulus : A) : L) < A.valuation c ∧ A.valuation c < 1)
    [Infinite (IsLocalRing.ResidueField A)] (t : Finset (IsLocalRing.ResidueField A)) :
    ∃ P ∈ An.dom, ∃ h : c⁻¹ * P.evalAt An.param ∈ A, A.valuation (P.evalAt An.param) = A.valuation c ∧
      IsLocalRing.residue A ⟨c⁻¹ * P.evalAt An.param, h⟩ ∉ t := by
  classical
  obtain ⟨r, hr⟩ := Infinite.exists_notMem_finset (insert (0 : IsLocalRing.ResidueField A) t)
  rw [Finset.mem_insert, not_or] at hr
  obtain ⟨u, rfl⟩ := Ideal.Quotient.mk_surjective r
  have hu : IsUnit u := by
    rw [← IsLocalRing.notMem_maximalIdeal, ← IsLocalRing.residue_eq_zero_iff]; exact hr.1
  obtain ⟨P, hP, hev⟩ := exists_mem_dom_evalAt_eq hc u hu
  have hc0 : c ≠ 0 := by
    intro h0; rw [h0, Valuation.map_zero] at hc; exact (not_lt_of_ge zero_le' hc.1).elim
  have hkey : c⁻¹ * P.evalAt An.param = u := by rw [hev, ← mul_assoc, inv_mul_cancel₀ hc0, one_mul]
  have hvu : A.valuation (u : L) = 1 := (A.valuation_eq_one_iff u).mp hu
  refine ⟨P, hP, by rw [hkey]; exact u.2, by rw [hev, Valuation.map_mul, hvu, mul_one], ?_⟩
  have : (⟨c⁻¹ * P.evalAt An.param, by rw [hkey]; exact u.2⟩ : A) = u := Subtype.ext hkey
  rw [this]; exact hr.2

end AlgebraicCurve.Annulus.CircleRing

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "Annulus Place Place.ord_zero Annulus.exists_eq_mul_prod_param_sub_zpow Annulus.valuation_evalAt_param_sub_algebraMap"
namespace Annulus
p2m_export "AlgebraicCurve.Annulus" "unit_principle existsUnique_evalAt_eq modulus dom mem_dom param ord_param_sub exists_eq_mul_prod_param_sub_zpow valuation_evalAt_param_sub_algebraMap"
namespace CircleRing
p2m_open "AlgebraicCurve.Annulus AlgebraicCurve"

open AlgebraicCurve.GaussReduction AlgebraicCurve.StandardAnnulus
open scoped Classical

variable {L : Type*} [Field L] {A : ValuationSubring L} {F : Type*} [Field F] [Algebra L F]

noncomputable def cls (A : ValuationSubring L) (c x : L) : IsLocalRing.ResidueField A :=
  if h : c⁻¹ * x ∈ A then IsLocalRing.residue A ⟨c⁻¹ * x, h⟩ else 0

theorem cls_eq (c x : L) (h : c⁻¹ * x ∈ A) : cls A c x = IsLocalRing.residue A ⟨c⁻¹ * x, h⟩ := dif_pos h

theorem ord_prod_zpow (P : Place L F) {ι : Type*} (t : Finset ι) (u : ι → F) (e : ι → ℤ)
    (hu : ∀ i ∈ t, u i ≠ 0) :
    (∏ i ∈ t, u i ^ e i) ≠ 0 ∧ P.ord (∏ i ∈ t, u i ^ e i) = ∑ i ∈ t, e i * P.ord (u i) := by
  induction t using Finset.induction_on with
  | empty => simp
  | insert i t hit ih =>
    rw [Finset.forall_mem_insert] at hu
    obtain ⟨hne, hord⟩ := ih hu.2
    have hi0 : u i ^ e i ≠ 0 := zpow_ne_zero _ hu.1
    refine ⟨by rw [Finset.prod_insert hit]; exact mul_ne_zero hi0 hne, ?_⟩
    rw [Finset.prod_insert hit, Finset.sum_insert hit, P.ord_mul hi0 hne, hord, P.ord_zpow]

theorem ord_param_sub_eq_zero_of_ne (An : Annulus A F) {P Q : Place L F} (hP : P ∈ An.dom) (hQ : Q ∈ An.dom)
    (hPQ : P ≠ Q) : An.param - algebraMap L F (Q.evalAt An.param) ≠ 0 ∧
      P.ord (An.param - algebraMap L F (Q.evalAt An.param)) = 0 := by
  have hne : An.param - algebraMap L F (Q.evalAt An.param) ≠ 0 := by
    intro h0
    have h1 := An.ord_param_sub Q hQ
    rw [h0, Place.ord_zero] at h1
    exact zero_ne_one h1
  refine ⟨hne, ?_⟩
  obtain ⟨hPrat, hzP, -, -, -⟩ := An.mem_dom P hP
  have hmem : An.param - algebraMap L F (Q.evalAt An.param) ∈ P.toValuationSubring :=
    sub_mem hzP (P.algebraMap_mem' _)
  have hnn := ord_nonneg_of_mem_gen P hmem hne
  rcases hnn.lt_or_eq with hpos | h0
  · exfalso
    have hev := evalAt_eq_zero_of_ord_pos P hne hpos
    rw [evalAt_sub_of_mem P hPrat hzP (P.algebraMap_mem' _), evalAt_algebraMap_const P hPrat, sub_eq_zero] at hev
    obtain ⟨-, -, ⟨hcA, hcmax⟩, hc0, hmod⟩ := An.mem_dom Q hQ
    have huniq := An.existsUnique_evalAt_eq ⟨Q.evalAt An.param, hcA⟩ hcmax hc0 hmod
    exact hPQ (huniq.unique ⟨hP, hev⟩ ⟨hQ, rfl⟩)
  · exact h0.symm

theorem exists_profile (An : Annulus A F)
    (hfin : ∀ f : F, f ≠ 0 → {P : Place L F | P ∈ An.dom ∧ P.ord f ≠ 0}.Finite)
    (c : L) (hc0 : c ≠ 0) (f : F) (hf : f ≠ 0) :
    ∃ (t₀ : Finset (IsLocalRing.ResidueField A)) (γ : A.ValueGroup), γ ≠ 0 ∧
      ∀ P ∈ An.dom, ∀ h : c⁻¹ * P.evalAt An.param ∈ A, A.valuation (P.evalAt An.param) = A.valuation c →
        IsLocalRing.residue A ⟨c⁻¹ * P.evalAt An.param, h⟩ ∉ t₀ → P.ord f = 0 ∧ A.valuation (P.evalAt f) = γ := by
  obtain ⟨s, n, g, hs, hg0, hordg, hfac⟩ :=
    AlgebraicCurve.Annulus.exists_eq_mul_prod_param_sub_zpow An hfin f hf
  obtain ⟨m, c₀, hc₀, hunit⟩ := An.unit_principle g hg0 hordg
  have hvc : A.valuation c ≠ 0 := by rwa [ne_eq, Valuation.zero_iff]
  have hvc₀ : A.valuation c₀ ≠ 0 := by rwa [ne_eq, Valuation.zero_iff]

  let r : Place L F → A.ValueGroup := fun Q =>
    if A.valuation (Q.evalAt An.param) = A.valuation c then A.valuation c
    else max (A.valuation c) (A.valuation (Q.evalAt An.param))
  have hr0 : ∀ Q, r Q ≠ 0 := by
    intro Q
    simp only [r]
    split_ifs
    · exact hvc
    · exact ne_of_gt (lt_of_lt_of_le (zero_lt_iff.mpr hvc) (le_max_left _ _))
  refine ⟨s.image (fun Q => cls A c (Q.evalAt An.param)),
    A.valuation c₀ * A.valuation c ^ m * ∏ Q ∈ s, r Q ^ n Q, ?_, ?_⟩
  · exact mul_ne_zero (mul_ne_zero hvc₀ (zpow_ne_zero _ hvc))
      (Finset.prod_ne_zero_iff.mpr fun Q _ => zpow_ne_zero _ (hr0 Q))
  intro P hP h hvP hnot
  obtain ⟨hPrat, hzP, -, hzP0, -⟩ := An.mem_dom P hP

  have hPs : P ∉ s := by
    intro hPs
    apply hnot
    rw [← cls_eq c _ h]
    exact Finset.mem_image_of_mem _ hPs
  have hPQ : ∀ Q ∈ s, P ≠ Q := fun Q hQ hPQ => hPs (hPQ ▸ hQ)

  have hu : ∀ Q ∈ s, An.param - algebraMap L F (Q.evalAt An.param) ≠ 0 ∧
      P.ord (An.param - algebraMap L F (Q.evalAt An.param)) = 0 :=
    fun Q hQ => ord_param_sub_eq_zero_of_ne An hP (hs hQ) (hPQ Q hQ)
  obtain ⟨hprod0, hordprod⟩ := ord_prod_zpow P s (fun Q => An.param - algebraMap L F (Q.evalAt An.param)) n
    (fun Q hQ => (hu Q hQ).1)
  have hordprod0 : P.ord (∏ Q ∈ s, (An.param - algebraMap L F (Q.evalAt An.param)) ^ n Q) = 0 := by
    rw [hordprod]
    exact Finset.sum_eq_zero fun Q hQ => by rw [(hu Q hQ).2, mul_zero]

  have hordf : P.ord f = 0 := by
    rw [hfac, P.ord_mul hg0 hprod0, hordg P hP, hordprod0, add_zero]
  refine ⟨hordf, ?_⟩

  have hgmem : g ∈ P.toValuationSubring := mem_of_ord_nonneg_gen P hg0 (hordg P hP).ge
  have hfactor : ∀ Q ∈ s, (An.param - algebraMap L F (Q.evalAt An.param)) ^ n Q ∈ P.toValuationSubring ∧
      P.evalAt ((An.param - algebraMap L F (Q.evalAt An.param)) ^ n Q) =
        (P.evalAt An.param - Q.evalAt An.param) ^ n Q := by
    intro Q hQ
    obtain ⟨hmem, hev⟩ := evalAt_zpow_of_ord_eq_zero P hPrat (hu Q hQ).1 (hu Q hQ).2 (n Q)
    refine ⟨hmem, ?_⟩
    rw [hev, evalAt_sub_of_mem P hPrat hzP (P.algebraMap_mem' _), evalAt_algebraMap_const P hPrat]
  obtain ⟨hprodmem, hevprod⟩ := evalAt_prod_of_mem P hPrat s
    (fun Q => (An.param - algebraMap L F (Q.evalAt An.param)) ^ n Q) (fun Q hQ => (hfactor Q hQ).1)
  have hevf : P.evalAt f = P.evalAt g * ∏ Q ∈ s, (P.evalAt An.param - Q.evalAt An.param) ^ n Q := by
    conv_lhs => rw [hfac]
    rw [evalAt_mul_of_mem P hPrat hgmem hprodmem, hevprod]
    congr 1
    exact Finset.prod_congr rfl fun Q hQ => (hfactor Q hQ).2

  have hvg : A.valuation (P.evalAt g) = A.valuation c₀ * A.valuation c ^ m := by
    obtain ⟨hA, hU⟩ := hunit P hP
    have h1 : A.valuation (P.evalAt g * c₀⁻¹ * P.evalAt An.param ^ (-m)) = 1 :=
      (A.valuation_eq_one_iff _).mp hU
    rw [Valuation.map_mul, Valuation.map_mul, Valuation.map_inv, map_zpow₀, hvP] at h1
    rw [zpow_neg, mul_assoc] at h1
    rw [eq_inv_of_mul_eq_one_left h1, mul_inv, inv_inv, inv_inv]

  have hvfac : ∀ Q ∈ s, A.valuation (P.evalAt An.param - Q.evalAt An.param) = r Q := by
    intro Q hQ
    have hB := AlgebraicCurve.Annulus.valuation_evalAt_param_sub_algebraMap An P hP (Q.evalAt An.param)
    rw [evalAt_sub_of_mem P hPrat hzP (P.algebraMap_mem' _), evalAt_algebraMap_const P hPrat] at hB
    obtain ⟨hQrat, hzQ, ⟨hzQA, -⟩, hzQ0, -⟩ := An.mem_dom Q (hs hQ)
    by_cases hvQ : A.valuation (Q.evalAt An.param) = A.valuation c
    ·
      simp only [r, if_pos hvQ]
      have hPQv : A.valuation (P.evalAt An.param) = A.valuation (Q.evalAt An.param) := by rw [hvP, hvQ]
      obtain ⟨-, hiff⟩ := hB.2 hPQv
      have h' : (Q.evalAt An.param)⁻¹ * P.evalAt An.param ∈ A := by
        rw [← A.valuation_le_one_iff, Valuation.map_mul, Valuation.map_inv, hPQv, inv_mul_cancel₀ (by rwa [hvQ])]
      have hQ' : c⁻¹ * Q.evalAt An.param ∈ A := by
        rw [← A.valuation_le_one_iff, Valuation.map_mul, Valuation.map_inv, hvQ, inv_mul_cancel₀ hvc]
      rw [← hvQ]
      refine (hiff hzQ0 h').mpr ?_
      intro hres
      apply hnot

      have hmulA : (⟨(Q.evalAt An.param)⁻¹ * P.evalAt An.param, h'⟩ : A) * ⟨c⁻¹ * Q.evalAt An.param, hQ'⟩ =
          ⟨c⁻¹ * P.evalAt An.param, h⟩ := by
        apply Subtype.ext
        show (Q.evalAt An.param)⁻¹ * P.evalAt An.param * (c⁻¹ * Q.evalAt An.param) = c⁻¹ * P.evalAt An.param
        field_simp
      have hres' := congrArg (IsLocalRing.residue A) hmulA
      rw [map_mul, hres, one_mul] at hres'
      rw [← hres', ← cls_eq c _ hQ']
      exact Finset.mem_image_of_mem _ hQ
    ·
      simp only [r, if_neg hvQ]
      rw [hB.1 (by rw [hvP]; exact fun h' => hvQ h'.symm), hvP]

  rw [hevf, Valuation.map_mul, map_prod, hvg]
  congr 1
  exact Finset.prod_congr rfl fun Q hQ => by rw [map_zpow₀, hvfac Q hQ]

end AlgebraicCurve.Annulus.CircleRing

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "Annulus Place Place.ord_zero Annulus.exists_eq_mul_prod_param_sub_zpow Annulus.valuation_evalAt_param_sub_algebraMap"
namespace Annulus
p2m_export "AlgebraicCurve.Annulus" "unit_principle existsUnique_evalAt_eq modulus dom mem_dom param ord_param_sub exists_eq_mul_prod_param_sub_zpow valuation_evalAt_param_sub_algebraMap"
namespace CircleRing
p2m_open "AlgebraicCurve.Annulus AlgebraicCurve"

open AlgebraicCurve.GaussReduction AlgebraicCurve.StandardAnnulus
open scoped Classical

variable {L : Type*} [Field L] {A : ValuationSubring L} {F : Type*} [Field F] [Algebra L F]

theorem good_or_good_inv (An : Annulus A F)
    (hfin : ∀ f : F, f ≠ 0 → {P : Place L F | P ∈ An.dom ∧ P.ord f ≠ 0}.Finite)
    (c : L) (hc0 : c ≠ 0) (f : F) :
    (∃ t, Good An c t f) ∨ (∃ t, Good An c t f⁻¹) := by
  by_cases hf : f = 0
  · exact Or.inl ⟨∅, by rw [hf]; exact good_zero An c ∅⟩
  obtain ⟨t₀, γ, hγ, hprof⟩ := exists_profile An hfin c hc0 f hf
  rcases le_or_gt γ 1 with hle | hlt
  · refine Or.inl ⟨t₀, fun P hP h hv hnot => ?_⟩
    obtain ⟨hord, hval⟩ := hprof P hP h hv hnot
    exact ⟨mem_of_ord_nonneg_gen P hf hord.ge, (A.valuation_le_one_iff _).mp (by rw [hval]; exact hle)⟩
  · refine Or.inr ⟨t₀, fun P hP h hv hnot => ?_⟩
    obtain ⟨hord, hval⟩ := hprof P hP h hv hnot
    refine ⟨mem_of_ord_nonneg_gen P (inv_ne_zero hf) (by rw [P.ord_inv]; omega), ?_⟩
    rw [evalAt_inv_of_ord_eq_zero P (An.mem_dom P hP).1 hf hord, ← A.valuation_le_one_iff, Valuation.map_inv, hval]
    exact (inv_le_one₀ (zero_lt_iff.mpr hγ)).mpr hlt.le

noncomputable def circleRing (An : Annulus A F)
    (hfin : ∀ f : F, f ≠ 0 → {P : Place L F | P ∈ An.dom ∧ P.ord f ≠ 0}.Finite)
    (c : L) (hc0 : c ≠ 0) : ValuationSubring F where
  carrier := {f | ∃ t, Good An c t f}
  mul_mem' := by
    rintro f g ⟨t, ht⟩ ⟨t', ht'⟩
    exact ⟨t ∪ t', Good.mul An c ht ht'⟩
  one_mem' := ⟨∅, good_one An c ∅⟩
  add_mem' := by
    rintro f g ⟨t, ht⟩ ⟨t', ht'⟩
    exact ⟨t ∪ t', Good.add An c ht ht'⟩
  zero_mem' := ⟨∅, good_zero An c ∅⟩
  neg_mem' := by
    rintro f ⟨t, ht⟩
    exact ⟨t, Good.neg An c ht⟩
  mem_or_inv_mem' := good_or_good_inv An hfin c hc0

theorem mem_circleRing_iff (An : Annulus A F)
    (hfin : ∀ f : F, f ≠ 0 → {P : Place L F | P ∈ An.dom ∧ P.ord f ≠ 0}.Finite)
    (c : L) (hc0 : c ≠ 0) (f : F) : f ∈ circleRing An hfin c hc0 ↔ ∃ t, Good An c t f := Iff.rfl

end AlgebraicCurve.Annulus.CircleRing

open AlgebraicCurve.Annulus.CircleRing AlgebraicCurve.GaussReduction in

theorem solution
    {L : Type*} [Field L] {A : ValuationSubring L} {F : Type*} [Field F] [Algebra L F]
    (An : Annulus A F)
    (hfin : ∀ f : F, f ≠ 0 → {P : Place L F | P ∈ An.dom ∧ P.ord f ≠ 0}.Finite)
    (c : L) (hc : A.valuation ((An.modulus : A) : L) < A.valuation c ∧ A.valuation c < 1)
    (hinf : Infinite (IsLocalRing.ResidueField A)) :
    ∃ V : ValuationSubring F,
      (∀ f : F, f ∈ V ↔ ∃ t : Finset (IsLocalRing.ResidueField A), ∀ P ∈ An.dom, ∀ h : c⁻¹ * P.evalAt An.param ∈ A,
        A.valuation (P.evalAt An.param) = A.valuation c → IsLocalRing.residue A ⟨c⁻¹ * P.evalAt An.param, h⟩ ∉ t → f ∈ P.toValuationSubring ∧ P.evalAt f ∈ A) ∧
      (∀ x : L, algebraMap L F x ∈ V ↔ x ∈ A) := by
  classical
  haveI := hinf
  have hc0 : c ≠ 0 := by
    intro h0; rw [h0, Valuation.map_zero] at hc; exact (not_lt_of_ge zero_le' hc.1).elim
  refine ⟨circleRing An hfin c hc0, fun f => Iff.rfl, fun x => ⟨?_, fun hx => ⟨∅, good_algebraMap An c ∅ hx⟩⟩⟩
  rintro ⟨t, ht⟩
  obtain ⟨P, hP, h, hv, hnot⟩ := exists_mem_dom_residue_notMem hc t
  have h2 := (ht P hP h hv hnot).2
  rwa [evalAt_algebraMap_const P (An.mem_dom P hP).1] at h2

end S_AlgebraicCurve_Annulus_exists_valuationSubring_mem_iff_of_valuation_lt
end P2MW
export P2MW.S_AlgebraicCurve_Annulus_exists_valuationSubring_mem_iff_of_valuation_lt (solution)

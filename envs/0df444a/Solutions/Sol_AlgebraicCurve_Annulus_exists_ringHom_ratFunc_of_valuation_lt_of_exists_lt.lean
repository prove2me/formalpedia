-- Prove2me | solution 1 for AlgebraicCurve.Annulus.exists_ringHom_ratFunc_of_valuation_lt_of_exists_lt
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/8aad8479-1276-5cf6-bce7-bbf572de2686

import Definitions.Def_AlgebraicCurve_SemistableCharts
import Definitions.Def_AlgebraicCurve_StandardAnnulus
import Theorems.Thm_AlgebraicCurve_Annulus_exists_eq_mul_prod_param_sub_zpow
import Theorems.Thm_AlgebraicCurve_Annulus_residue_evalAt_eq_of_forall_isUnit_evalAt
import Mathlib.Algebra.Polynomial.Roots
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_Annulus_exists_ringHom_ratFunc_of_valuation_lt_of_exists_lt

set_option autoImplicit false

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "Annulus Place Place.ord_zero Place.algebraMap_mem' Place.algebraMap_evalAt Annulus.exists_eq_mul_prod_param_sub_zpow Annulus.residue_evalAt_eq_of_forall_isUnit_evalAt"
namespace Annulus
p2m_export "AlgebraicCurve.Annulus" "unit_principle existsUnique_evalAt_eq modulus dom mem_dom param ord_param_sub exists_eq_mul_prod_param_sub_zpow residue_evalAt_eq_of_forall_isUnit_evalAt"
namespace CircleChart
p2m_open "AlgebraicCurve.Annulus AlgebraicCurve"

p2m_open "AlgebraicCurve P2MW.S_AlgebraicCurve_Annulus_exists_ringHom_ratFunc_of_valuation_lt_of_exists_lt.AlgebraicCurve AlgebraicCurve.RationalFunctionField AlgebraicCurve.StandardAnnulus AlgebraicCurve.GaussReduction"
open Polynomial

section EvalHelpers
variable {K' F' : Type*} [Field K'] [Field F'] [Algebra K' F']

theorem isRational_of_deg_eq_one' (v : Place K' F') (h : v.deg = 1) : v.IsRational := by
  haveI : Module.Finite K' v.ResidueField := Module.finite_of_finrank_eq_succ (n := 0) h
  intro x
  obtain ⟨a, ha⟩ := (finrank_eq_one_iff_of_nonzero' (1 : v.ResidueField) one_ne_zero).mp h x
  exact ⟨a, by rw [Algebra.algebraMap_eq_smul_one]; exact ha⟩

theorem evalAt_zero' (P : Place K' F') (hP : P.IsRational) : P.evalAt (0 : F') = 0 := by
  have h := evalAt_sub_of_mem P hP (one_mem P.toValuationSubring) (one_mem P.toValuationSubring)
  rwa [sub_self, sub_self] at h

theorem evalAt_add_of_mem (P : Place K' F') (hP : P.IsRational) {f g : F'}
    (hf : f ∈ P.toValuationSubring) (hg : g ∈ P.toValuationSubring) :
    P.evalAt (f + g) = P.evalAt f + P.evalAt g := by
  have h1 : f + g = f - (0 - g) := by ring
  rw [h1, evalAt_sub_of_mem P hP hf (sub_mem (zero_mem _) hg),
    evalAt_sub_of_mem P hP (zero_mem _) hg, evalAt_zero' P hP]
  ring

theorem evalAt_pow_of_mem (P : Place K' F') (hP : P.IsRational) {f : F'} (hf : f ∈ P.toValuationSubring) (n : ℕ) :
    P.evalAt (f ^ n) = P.evalAt f ^ n := by
  induction n with
  | zero => simp [P.evalAt_one]
  | succ n ih => rw [pow_succ, pow_succ, evalAt_mul_of_mem P hP (pow_mem hf n) hf, ih]

theorem evalAt_prod_of_mem (P : Place K' F') (hP : P.IsRational) {ι : Type*} (t : Finset ι) (u : ι → F')
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

theorem ord_eq_zero_of_evalAt_ne_zero (P : Place K' F') {f : F'} (hf : f ∈ P.toValuationSubring)
    (hne : P.evalAt f ≠ 0) : P.ord f = 0 := by
  have hf0 : f ≠ 0 := by
    intro h0; apply hne; rw [h0]

    rw [P.evalAt_of_mem (zero_mem _)]
    rw [show (⟨(0 : F'), zero_mem _⟩ : P.toValuationSubring) = 0 from Subtype.ext rfl, map_zero,
      ← map_zero (algebraMap K' P.ResidueField), P.residueInv_algebraMap]
  have hnn := ord_nonneg_of_mem_gen P hf hf0
  rcases hnn.lt_or_eq with hpos | h0
  · exact absurd (evalAt_eq_zero_of_ord_pos P hf0 hpos) hne
  · exact h0.symm

theorem evalAt_zpow_of_ord_eq_zero (P : Place K' F') (hP : P.IsRational) {f : F'} (hf0 : f ≠ 0)
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

end EvalHelpers

variable {k : Type*} [Field k]

theorem isRational_placeOfPoint' (a : k) : (placeOfPoint k a).IsRational :=
  isRational_of_deg_eq_one' _ (deg_placeOfPoint k a)

theorem evalAt_placeOfPoint_X' (a : k) : (placeOfPoint k a).evalAt (RatFunc.X : RatFunc k) = a := by
  have hrat := isRational_placeOfPoint' (k := k) a
  have hX := X_mem_placeOfPoint (K := k) a
  have hC : algebraMap k (RatFunc k) a ∈ (placeOfPoint k a).toValuationSubring := (placeOfPoint k a).algebraMap_mem' a
  have hne : (RatFunc.X : RatFunc k) - algebraMap k (RatFunc k) a ≠ 0 := by
    rw [← RatFunc.algebraMap_X, RatFunc.algebraMap_eq_C, ← RatFunc.algebraMap_C, ← map_sub, ne_eq,
      map_eq_zero_iff _ (IsFractionRing.injective k[X] (RatFunc k))]
    exact X_sub_C_ne_zero a
  have hpos : 0 < (placeOfPoint k a).ord ((RatFunc.X : RatFunc k) - algebraMap k (RatFunc k) a) := by
    have h1 := ord_placeOfPoint_X_sub_C_self (K := k) a
    rw [show (RatFunc.X : RatFunc k) - algebraMap k (RatFunc k) a =
        algebraMap k[X] (RatFunc k) (Polynomial.X - Polynomial.C a) by
      rw [map_sub, RatFunc.algebraMap_X, RatFunc.algebraMap_C, RatFunc.algebraMap_eq_C]]
    omega
  have h0 := evalAt_eq_zero_of_ord_pos _ hne hpos
  rw [evalAt_sub_of_mem _ hrat hX hC, evalAt_algebraMap_const _ hrat, sub_eq_zero] at h0
  exact h0

theorem evalAt_placeOfPoint_algebraMap' (a : k) (p : k[X]) :
    (placeOfPoint k a).evalAt (algebraMap k[X] (RatFunc k) p) = p.eval a := by
  have hrat := isRational_placeOfPoint' (k := k) a
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    rw [map_add, evalAt_add_of_mem _ hrat (algebraMap_mem_placeOfPoint a p) (algebraMap_mem_placeOfPoint a q),
      hp, hq, eval_add]
  | monomial n b =>
    rw [← C_mul_X_pow_eq_monomial, map_mul, map_pow, RatFunc.algebraMap_C, RatFunc.algebraMap_X, eval_mul, eval_pow,
      eval_C, eval_X]
    have hCb : (RatFunc.C b : RatFunc k) ∈ (placeOfPoint k a).toValuationSubring := by
      rw [← RatFunc.algebraMap_eq_C]; exact (placeOfPoint k a).algebraMap_mem' b
    rw [evalAt_mul_of_mem _ hrat hCb (pow_mem (X_mem_placeOfPoint a) n),
      evalAt_pow_of_mem _ hrat (X_mem_placeOfPoint a), evalAt_placeOfPoint_X']
    congr 1
    rw [← RatFunc.algebraMap_eq_C]
    exact evalAt_algebraMap_const _ hrat b

theorem ord_placeOfPoint_algebraMap_eq_zero (a : k) {q : k[X]} (hq : q.eval a ≠ 0) :
    (placeOfPoint k a).ord (algebraMap k[X] (RatFunc k) q) = 0 :=
  ord_eq_zero_of_evalAt_ne_zero _ (algebraMap_mem_placeOfPoint a q) (by rw [evalAt_placeOfPoint_algebraMap']; exact hq)

theorem evalAt_placeOfPoint_div (a : k) (p q : k[X]) (hq : q.eval a ≠ 0) :
    algebraMap k[X] (RatFunc k) p / algebraMap k[X] (RatFunc k) q ∈ (placeOfPoint k a).toValuationSubring ∧
    (placeOfPoint k a).evalAt (algebraMap k[X] (RatFunc k) p / algebraMap k[X] (RatFunc k) q) = p.eval a / q.eval a := by
  have hrat := isRational_placeOfPoint' (k := k) a
  have hq0 : algebraMap k[X] (RatFunc k) q ≠ 0 := by
    rw [ne_eq, map_eq_zero_iff _ (IsFractionRing.injective k[X] (RatFunc k))]
    rintro rfl; exact hq (eval_zero)
  have hord := ord_placeOfPoint_algebraMap_eq_zero a hq
  obtain ⟨hinvmem, hinv⟩ := evalAt_zpow_of_ord_eq_zero _ hrat hq0 hord (-1)
  rw [zpow_neg_one] at hinvmem hinv
  rw [zpow_neg_one] at hinv
  refine ⟨by rw [div_eq_mul_inv]; exact mul_mem (algebraMap_mem_placeOfPoint a p) hinvmem, ?_⟩
  rw [div_eq_mul_inv, evalAt_mul_of_mem _ hrat (algebraMap_mem_placeOfPoint a p) hinvmem, hinv,
    evalAt_placeOfPoint_algebraMap', evalAt_placeOfPoint_algebraMap', div_eq_mul_inv]

theorem ratFunc_eq_of_evalAt_placeOfPoint_eq [Infinite k] (R₁ R₂ : RatFunc k) (t : Finset k)
    (h : ∀ x, x ∉ t → (placeOfPoint k x).evalAt R₁ = (placeOfPoint k x).evalAt R₂) : R₁ = R₂ := by
  classical
  set D : k[X] := R₁.num * R₂.denom - R₂.num * R₁.denom with hD
  have hroots : Set.Infinite {x : k | IsRoot D x} := by
    have hfin : (↑(t ∪ (R₁.denom * R₂.denom).roots.toFinset) : Set k).Finite := Finset.finite_toSet _
    refine (hfin.infinite_compl).mono ?_
    intro x hx
    simp only [Set.mem_compl_iff, Finset.coe_union, Set.mem_union, Finset.mem_coe, Multiset.mem_toFinset,
      mem_roots (mul_ne_zero (RatFunc.denom_ne_zero R₁) (RatFunc.denom_ne_zero R₂)), IsRoot.def, eval_mul,
      mul_eq_zero, not_or] at hx
    obtain ⟨hxt, hd₁, hd₂⟩ := hx
    have hv := h x hxt
    rw [← RatFunc.num_div_denom R₁, ← RatFunc.num_div_denom R₂, (evalAt_placeOfPoint_div x _ _ hd₁).2,
      (evalAt_placeOfPoint_div x _ _ hd₂).2, div_eq_div_iff hd₁ hd₂] at hv
    simp only [Set.mem_setOf_eq, IsRoot.def, hD, eval_sub, eval_mul]
    rw [hv, mul_comm (R₂.num.eval x), sub_self]
  have hD0 : D = 0 := Polynomial.eq_zero_of_infinite_isRoot D hroots
  have hq₁ : (algebraMap k[X] (RatFunc k) R₁.denom) ≠ 0 := by
    rw [ne_eq, map_eq_zero_iff _ (IsFractionRing.injective k[X] (RatFunc k))]; exact RatFunc.denom_ne_zero R₁
  have hq₂ : (algebraMap k[X] (RatFunc k) R₂.denom) ≠ 0 := by
    rw [ne_eq, map_eq_zero_iff _ (IsFractionRing.injective k[X] (RatFunc k))]; exact RatFunc.denom_ne_zero R₂
  rw [← RatFunc.num_div_denom R₁, ← RatFunc.num_div_denom R₂, div_eq_div_iff hq₁ hq₂, ← map_mul, ← map_mul]
  congr 1
  rw [hD, sub_eq_zero] at hD0
  exact hD0

end AlgebraicCurve.Annulus.CircleChart

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "Annulus Place Place.ord_zero Place.algebraMap_mem' Place.algebraMap_evalAt Annulus.exists_eq_mul_prod_param_sub_zpow Annulus.residue_evalAt_eq_of_forall_isUnit_evalAt"
namespace Annulus
p2m_export "AlgebraicCurve.Annulus" "unit_principle existsUnique_evalAt_eq modulus dom mem_dom param ord_param_sub exists_eq_mul_prod_param_sub_zpow residue_evalAt_eq_of_forall_isUnit_evalAt"
namespace CircleChart
p2m_open "AlgebraicCurve.Annulus AlgebraicCurve"

p2m_open "AlgebraicCurve P2MW.S_AlgebraicCurve_Annulus_exists_ringHom_ratFunc_of_valuation_lt_of_exists_lt.AlgebraicCurve AlgebraicCurve.RationalFunctionField AlgebraicCurve.StandardAnnulus AlgebraicCurve.GaussReduction"
open scoped Classical

variable {L : Type*} [Field L] {A : ValuationSubring L}

noncomputable def rcl (A : ValuationSubring L) (x : L) : IsLocalRing.ResidueField A :=
  if h : x ∈ A then IsLocalRing.residue A ⟨x, h⟩ else 0

theorem rcl_eq {x : L} (h : x ∈ A) : rcl A x = IsLocalRing.residue A ⟨x, h⟩ := dif_pos h

theorem rcl_mul {x y : L} (hx : x ∈ A) (hy : y ∈ A) : rcl A (x * y) = rcl A x * rcl A y := by
  rw [rcl_eq hx, rcl_eq hy, rcl_eq (mul_mem hx hy), ← map_mul]; rfl

theorem rcl_one : rcl A (1 : L) = 1 := by
  rw [rcl_eq A.one_mem]; exact map_one _

theorem mem_of_valuation_eq_one {x : L} (hx : A.valuation x = 1) :
    x ∈ A ∧ x⁻¹ ∈ A ∧ rcl A x ≠ 0 ∧ rcl A x⁻¹ = (rcl A x)⁻¹ := by
  have hA : x ∈ A := (A.valuation_le_one_iff x).mp hx.le
  have hinvA : x⁻¹ ∈ A := (A.valuation_le_one_iff _).mp (by rw [Valuation.map_inv, hx, inv_one])
  have hx0 : x ≠ 0 := by intro h0; rw [h0, Valuation.map_zero] at hx; exact zero_ne_one hx
  have hunit : IsUnit (⟨x, hA⟩ : A) := (A.valuation_eq_one_iff _).mpr hx
  have hres0 : rcl A x ≠ 0 := by
    rw [rcl_eq hA, ne_eq, IsLocalRing.residue_eq_zero_iff]; exact IsLocalRing.notMem_maximalIdeal.mpr hunit
  refine ⟨hA, hinvA, hres0, ?_⟩
  apply eq_inv_of_mul_eq_one_left
  rw [← rcl_mul hinvA hA, inv_mul_cancel₀ hx0, rcl_one]

theorem rcl_zpow {x : L} (hx : A.valuation x = 1) (n : ℤ) :
    x ^ n ∈ A ∧ A.valuation (x ^ n) = 1 ∧ rcl A (x ^ n) = rcl A x ^ n := by
  obtain ⟨hA, hinvA, -, hinv⟩ := mem_of_valuation_eq_one hx
  have hval : A.valuation (x ^ n) = 1 := by rw [map_zpow₀, hx, one_zpow]
  have hpow : ∀ (y : L) (hy : y ∈ A) (m : ℕ), rcl A (y ^ m) = rcl A y ^ m := by
    intro y hy m
    induction m with
    | zero => rw [pow_zero, pow_zero, rcl_one]
    | succ m ih => rw [pow_succ, pow_succ, rcl_mul (A.pow_mem hy m) hy, ih]
  rcases Int.eq_nat_or_neg n with ⟨m, rfl | rfl⟩
  · exact ⟨by rw [zpow_natCast]; exact A.pow_mem hA m, hval, by rw [zpow_natCast, zpow_natCast, hpow x hA m]⟩
  · refine ⟨by rw [zpow_neg, zpow_natCast, ← inv_pow]; exact A.pow_mem hinvA m, hval, ?_⟩
    rw [zpow_neg, zpow_natCast, ← inv_pow, hpow x⁻¹ hinvA m, hinv, inv_pow, zpow_neg, zpow_natCast]

theorem rcl_prod_zpow {ι : Type*} (t : Finset ι) (θ : ι → L) (n : ι → ℤ)
    (hθ : ∀ i ∈ t, A.valuation (θ i) = 1) :
    (∏ i ∈ t, θ i ^ n i) ∈ A ∧ A.valuation (∏ i ∈ t, θ i ^ n i) = 1 ∧
      rcl A (∏ i ∈ t, θ i ^ n i) = ∏ i ∈ t, rcl A (θ i) ^ n i := by
  induction t using Finset.induction_on with
  | empty => exact ⟨by rw [Finset.prod_empty]; exact A.one_mem, by rw [Finset.prod_empty, Valuation.map_one],
      by rw [Finset.prod_empty, Finset.prod_empty, rcl_one]⟩
  | insert i t hit ih =>
    rw [Finset.forall_mem_insert] at hθ
    obtain ⟨hmem, hval, hres⟩ := ih hθ.2
    obtain ⟨hmemi, hvali, hresi⟩ := rcl_zpow hθ.1 (n i)
    refine ⟨by rw [Finset.prod_insert hit]; exact mul_mem hmemi hmem,
      by rw [Finset.prod_insert hit, Valuation.map_mul, hvali, hval, one_mul], ?_⟩
    rw [Finset.prod_insert hit, Finset.prod_insert hit, rcl_mul hmemi hmem, hresi, hres]

end AlgebraicCurve.Annulus.CircleChart

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "Annulus Place Place.ord_zero Place.algebraMap_mem' Place.algebraMap_evalAt Annulus.exists_eq_mul_prod_param_sub_zpow Annulus.residue_evalAt_eq_of_forall_isUnit_evalAt"
namespace Annulus
p2m_export "AlgebraicCurve.Annulus" "unit_principle existsUnique_evalAt_eq modulus dom mem_dom param ord_param_sub exists_eq_mul_prod_param_sub_zpow residue_evalAt_eq_of_forall_isUnit_evalAt"
namespace CircleChart
p2m_open "AlgebraicCurve.Annulus AlgebraicCurve"

p2m_open "AlgebraicCurve P2MW.S_AlgebraicCurve_Annulus_exists_ringHom_ratFunc_of_valuation_lt_of_exists_lt.AlgebraicCurve AlgebraicCurve.RationalFunctionField AlgebraicCurve.StandardAnnulus AlgebraicCurve.GaussReduction"
open Polynomial
open scoped Classical

variable {L : Type*} [Field L] {A : ValuationSubring L} {F : Type*} [Field F] [Algebra L F]

theorem rcl_sub {x y : L} (hx : x ∈ A) (hy : y ∈ A) : rcl A (x - y) = rcl A x - rcl A y := by
  rw [rcl_eq hx, rcl_eq hy, rcl_eq (sub_mem hx hy), ← map_sub]; rfl

theorem rcl_eq_zero_of_valuation_lt_one {x : L} (hx : A.valuation x < 1) : rcl A x = 0 := by
  have hA : x ∈ A := (A.valuation_le_one_iff x).mp hx.le
  rw [rcl_eq hA, IsLocalRing.residue_eq_zero_iff, ValuationSubring.valuation_lt_one_iff]; exact hx

theorem valuation_eq_one_of_rcl_ne_zero {x : L} (hA : x ∈ A) (hx : rcl A x ≠ 0) : A.valuation x = 1 := by
  rw [rcl_eq hA, ne_eq, IsLocalRing.residue_eq_zero_iff, IsLocalRing.notMem_maximalIdeal] at hx
  exact (A.valuation_eq_one_iff _).mp hx

noncomputable def lam (A : ValuationSubring L) (c zQ : L) : L := if A.valuation zQ ≤ A.valuation c then c else -zQ

theorem lam_ne_zero {c zQ : L} (hc0 : c ≠ 0) (hz0 : zQ ≠ 0) : lam A c zQ ≠ 0 := by
  unfold lam; split_ifs; exacts [hc0, neg_ne_zero.mpr hz0]

theorem valuation_lam (c zQ : L) : A.valuation (lam A c zQ) = max (A.valuation c) (A.valuation zQ) := by
  unfold lam; split_ifs with h
  · rw [max_eq_left h]
  · rw [Valuation.map_neg, max_eq_right (le_of_not_ge h)]

noncomputable def redFactor (A : ValuationSubring L) (c zQ : L) (wbar : IsLocalRing.ResidueField A) :
    IsLocalRing.ResidueField A :=
  if A.valuation zQ = A.valuation c then wbar - rcl A (c⁻¹ * zQ)
  else if A.valuation zQ < A.valuation c then wbar else 1

theorem factor_analysis {c zP zQ : L} (hc0 : c ≠ 0) (hzQ0 : zQ ≠ 0)
    (h : c⁻¹ * zP ∈ A) (hv : A.valuation zP = A.valuation c)
    (hgen : A.valuation zQ = A.valuation c → rcl A (c⁻¹ * zP) ≠ rcl A (c⁻¹ * zQ)) :
    A.valuation ((lam A c zQ)⁻¹ * (zP - zQ)) = 1 ∧
      rcl A ((lam A c zQ)⁻¹ * (zP - zQ)) = redFactor A c zQ (rcl A (c⁻¹ * zP)) := by
  have hvc : A.valuation c ≠ 0 := by rwa [ne_eq, Valuation.zero_iff]
  have hw : A.valuation (c⁻¹ * zP) = 1 := by rw [Valuation.map_mul, Valuation.map_inv, hv, inv_mul_cancel₀ hvc]
  have hw0 : rcl A (c⁻¹ * zP) ≠ 0 := (mem_of_valuation_eq_one hw).2.2.1
  by_cases hon : A.valuation zQ = A.valuation c
  ·
    have hlam : lam A c zQ = c := by unfold lam; rw [if_pos hon.le]
    have hwQ : A.valuation (c⁻¹ * zQ) = 1 := by rw [Valuation.map_mul, Valuation.map_inv, hon, inv_mul_cancel₀ hvc]
    have hwQA : c⁻¹ * zQ ∈ A := (mem_of_valuation_eq_one hwQ).1
    have heq : (lam A c zQ)⁻¹ * (zP - zQ) = c⁻¹ * zP - c⁻¹ * zQ := by rw [hlam, mul_sub]
    have hred : redFactor A c zQ (rcl A (c⁻¹ * zP)) = rcl A (c⁻¹ * zP) - rcl A (c⁻¹ * zQ) := by
      unfold redFactor; rw [if_pos hon]
    rw [heq, hred, rcl_sub h hwQA]
    refine ⟨valuation_eq_one_of_rcl_ne_zero (sub_mem h hwQA) ?_, rfl⟩
    rw [rcl_sub h hwQA]; exact sub_ne_zero.mpr (hgen hon)
  by_cases hin : A.valuation zQ < A.valuation c
  ·
    have hlam : lam A c zQ = c := by unfold lam; rw [if_pos hin.le]
    have hsmall : A.valuation (c⁻¹ * zQ) < 1 := by
      rw [Valuation.map_mul, Valuation.map_inv, mul_comm]
      exact mul_inv_lt_of_lt_mul₀ (by rw [one_mul]; exact hin)
    have hwQA : c⁻¹ * zQ ∈ A := (A.valuation_le_one_iff _).mp hsmall.le
    have heq : (lam A c zQ)⁻¹ * (zP - zQ) = c⁻¹ * zP - c⁻¹ * zQ := by rw [hlam, mul_sub]
    have hred : redFactor A c zQ (rcl A (c⁻¹ * zP)) = rcl A (c⁻¹ * zP) := by
      unfold redFactor; rw [if_neg hon, if_pos hin]
    rw [heq, hred, rcl_sub h hwQA, rcl_eq_zero_of_valuation_lt_one hsmall, sub_zero]
    refine ⟨valuation_eq_one_of_rcl_ne_zero (sub_mem h hwQA) ?_, rfl⟩
    rwa [rcl_sub h hwQA, rcl_eq_zero_of_valuation_lt_one hsmall, sub_zero]
  ·
    have hout : A.valuation c < A.valuation zQ := lt_of_le_of_ne (le_of_not_gt hin) (Ne.symm hon)
    have hlam : lam A c zQ = -zQ := by unfold lam; rw [if_neg (not_le.mpr hout)]
    have heq : (lam A c zQ)⁻¹ * (zP - zQ) = 1 - zQ⁻¹ * zP := by
      rw [hlam]; field_simp; ring
    have hvz : A.valuation zQ ≠ 0 := by rwa [ne_eq, Valuation.zero_iff]
    have hsmall : A.valuation (zQ⁻¹ * zP) < 1 := by
      rw [Valuation.map_mul, Valuation.map_inv, hv, mul_comm]
      exact mul_inv_lt_of_lt_mul₀ (by rw [one_mul]; exact hout)
    have hsA : zQ⁻¹ * zP ∈ A := (A.valuation_le_one_iff _).mp hsmall.le
    have hred : redFactor A c zQ (rcl A (c⁻¹ * zP)) = 1 := by
      unfold redFactor; rw [if_neg hon, if_neg hin]
    rw [heq, hred, rcl_sub A.one_mem hsA, rcl_one, rcl_eq_zero_of_valuation_lt_one hsmall, sub_zero]
    refine ⟨valuation_eq_one_of_rcl_ne_zero (sub_mem A.one_mem hsA) ?_, rfl⟩
    rw [rcl_sub A.one_mem hsA, rcl_one, rcl_eq_zero_of_valuation_lt_one hsmall, sub_zero]; exact one_ne_zero

end AlgebraicCurve.Annulus.CircleChart

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "Annulus Place Place.ord_zero Place.algebraMap_mem' Place.algebraMap_evalAt Annulus.exists_eq_mul_prod_param_sub_zpow Annulus.residue_evalAt_eq_of_forall_isUnit_evalAt"
namespace Annulus
p2m_export "AlgebraicCurve.Annulus" "unit_principle existsUnique_evalAt_eq modulus dom mem_dom param ord_param_sub exists_eq_mul_prod_param_sub_zpow residue_evalAt_eq_of_forall_isUnit_evalAt"
namespace CircleChart
p2m_open "AlgebraicCurve.Annulus AlgebraicCurve"

p2m_open "AlgebraicCurve P2MW.S_AlgebraicCurve_Annulus_exists_ringHom_ratFunc_of_valuation_lt_of_exists_lt.AlgebraicCurve AlgebraicCurve.RationalFunctionField AlgebraicCurve.StandardAnnulus AlgebraicCurve.GaussReduction"
open Polynomial
open scoped Classical

variable {L : Type*} [Field L] {A : ValuationSubring L} {F : Type*} [Field F] [Algebra L F]

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

theorem exists_mem_dom_evalAt_eq (An : Annulus A F) {c : L}
    (hc : A.valuation ((An.modulus : A) : L) < A.valuation c ∧ A.valuation c < 1)
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

theorem prod_zpow_eq_zpow_sum {M : Type*} [CommGroupWithZero M] {ι : Type*} (t : Finset ι)
    (a : M) (ha : a ≠ 0) (f : ι → ℤ) : ∏ i ∈ t, a ^ f i = a ^ ∑ i ∈ t, f i := by
  induction t using Finset.induction_on with
  | empty => simp
  | insert i t hit ih => rw [Finset.prod_insert hit, Finset.sum_insert hit, ih, zpow_add₀ ha]

theorem exists_interpolant (An : Annulus A F)
    (hfin : ∀ f : F, f ≠ 0 → {P : Place L F | P ∈ An.dom ∧ P.ord f ≠ 0}.Finite)
    (c : L) (hc : A.valuation ((An.modulus : A) : L) < A.valuation c ∧ A.valuation c < 1)
    (hinf : Infinite (IsLocalRing.ResidueField A))
    (hR : (∃ b : L, A.valuation c < A.valuation b ∧ A.valuation b < 1) ∧
      (∃ b : L, A.valuation ((An.modulus : A) : L) < A.valuation b ∧ A.valuation b < A.valuation c))
    (f : F) (hf : f ≠ 0) :
    ∃ (t₀ : Finset (IsLocalRing.ResidueField A)) (Λ : L) (R₀ : RatFunc (IsLocalRing.ResidueField A)),
      Λ ≠ 0 ∧ R₀ ≠ 0 ∧
      ∀ P ∈ An.dom, ∀ h : c⁻¹ * P.evalAt An.param ∈ A, A.valuation (P.evalAt An.param) = A.valuation c →
        rcl A (c⁻¹ * P.evalAt An.param) ∉ t₀ →
          P.ord f = 0 ∧ A.valuation (Λ⁻¹ * P.evalAt f) = 1 ∧
            rcl A (Λ⁻¹ * P.evalAt f) =
              (placeOfPoint (IsLocalRing.ResidueField A) (rcl A (c⁻¹ * P.evalAt An.param))).evalAt R₀ := by

  set k := IsLocalRing.ResidueField A
  have hc0 : c ≠ 0 := by
    intro h0; rw [h0, Valuation.map_zero] at hc; exact (not_lt_of_ge zero_le' hc.1).elim
  have hvc : A.valuation c ≠ 0 := by rwa [ne_eq, Valuation.zero_iff]

  obtain ⟨s, n, g, hs, hg0, hordg, hfac⟩ :=
    AlgebraicCurve.Annulus.exists_eq_mul_prod_param_sub_zpow An hfin f hf
  obtain ⟨m, c₀, hc₀, hunit⟩ := An.unit_principle g hg0 hordg

  have hz : ∀ P ∈ An.dom, An.param ≠ 0 ∧ P.ord An.param = 0 := by
    intro P hP
    obtain ⟨hPrat, hzP, -, hzP0, -⟩ := An.mem_dom P hP
    have hz0 : An.param ≠ 0 := by
      intro h0; apply hzP0; rw [h0]; exact evalAt_zero' P hPrat
    exact ⟨hz0, ord_eq_zero_of_evalAt_ne_zero P hzP hzP0⟩

  set u : F := g * algebraMap L F c₀⁻¹ * An.param ^ (-m) with hu_def
  have hu : ∀ P ∈ An.dom, u ∈ P.toValuationSubring ∧
      P.evalAt u = P.evalAt g * c₀⁻¹ * P.evalAt An.param ^ (-m) := by
    intro P hP
    obtain ⟨hPrat, hzP, -, hzP0, -⟩ := An.mem_dom P hP
    have hgmem : g ∈ P.toValuationSubring := mem_of_ord_nonneg_gen P hg0 (hordg P hP).ge
    obtain ⟨hzm, hzev⟩ := evalAt_zpow_of_ord_eq_zero P hPrat (hz P hP).1 (hz P hP).2 (-m)
    have h1 : g * algebraMap L F c₀⁻¹ ∈ P.toValuationSubring := mul_mem hgmem (P.algebraMap_mem' _)
    refine ⟨mul_mem h1 hzm, ?_⟩
    rw [hu_def, evalAt_mul_of_mem P hPrat h1 hzm, evalAt_mul_of_mem P hPrat hgmem (P.algebraMap_mem' _),
      evalAt_algebraMap_const P hPrat, hzev]
  have hunitu : ∀ P ∈ An.dom, ∃ h : P.evalAt u ∈ A, IsUnit (⟨P.evalAt u, h⟩ : A) := by
    intro P hP
    rw [(hu P hP).2]
    exact hunit P hP
  have hvu : ∀ P ∈ An.dom, A.valuation (P.evalAt u) = 1 := by
    intro P hP
    obtain ⟨h, hU⟩ := hunitu P hP
    exact (A.valuation_eq_one_iff _).mp hU

  obtain ⟨P₁, hP₁, hzP₁⟩ := exists_mem_dom_evalAt_eq An hc (1 : A) isUnit_one
  have hvP₁ : A.valuation (P₁.evalAt An.param) = A.valuation c := by
    rw [hzP₁]; simp
  set ubar : k := rcl A (P₁.evalAt u) with hubar
  have hconst : ∀ P ∈ An.dom, A.valuation (P.evalAt An.param) = A.valuation c → rcl A (P.evalAt u) = ubar := by
    intro P hP hvP
    obtain ⟨hPu, -⟩ := hunitu P hP
    obtain ⟨hP₁u, -⟩ := hunitu P₁ hP₁
    rw [hubar, rcl_eq hPu, rcl_eq hP₁u]
    exact AlgebraicCurve.Annulus.residue_evalAt_eq_of_forall_isUnit_evalAt An hfin c hc hinf hR u
      (fun Q hQ => (hu Q hQ).1) hunitu P P₁ hP hP₁ hvP hvP₁ hPu hP₁u
  have hubar0 : ubar ≠ 0 := (mem_of_valuation_eq_one (hvu P₁ hP₁)).2.2.1

  let zq : Place L F → L := fun Q => Q.evalAt An.param
  let bq : Place L F → k := fun Q => rcl A (c⁻¹ * zq Q)
  let son := s.filter (fun Q => A.valuation (zq Q) = A.valuation c)
  let sin := s.filter (fun Q => A.valuation (zq Q) < A.valuation c)
  let e : ℤ := m + ∑ Q ∈ sin, n Q
  refine ⟨s.image bq, c₀ * c ^ m * ∏ Q ∈ s, lam A c (zq Q) ^ n Q,
    algebraMap k (RatFunc k) ubar * (RatFunc.X : RatFunc k) ^ e *
      ∏ Q ∈ son, (algebraMap k[X] (RatFunc k) (X - C (bq Q))) ^ n Q, ?_, ?_, ?_⟩
  ·
    refine mul_ne_zero (mul_ne_zero hc₀ (zpow_ne_zero _ hc0)) (Finset.prod_ne_zero_iff.mpr fun Q hQ => ?_)
    exact zpow_ne_zero _ (lam_ne_zero hc0 (An.mem_dom Q (hs hQ)).2.2.2.1)
  ·
    refine mul_ne_zero (mul_ne_zero ?_ (zpow_ne_zero _ RatFunc.X_ne_zero))
      (Finset.prod_ne_zero_iff.mpr fun Q _ => zpow_ne_zero _ ?_)
    · rwa [ne_eq, map_eq_zero_iff _ (algebraMap k (RatFunc k)).injective]
    · rw [ne_eq, map_eq_zero_iff _ (IsFractionRing.injective k[X] (RatFunc k))]; exact X_sub_C_ne_zero _

  intro P hP h hvP hnot
  obtain ⟨hPrat, hzP, -, hzP0, -⟩ := An.mem_dom P hP
  have hw : A.valuation (c⁻¹ * P.evalAt An.param) = 1 := by
    rw [Valuation.map_mul, Valuation.map_inv, hvP, inv_mul_cancel₀ hvc]
  set wbar : k := rcl A (c⁻¹ * P.evalAt An.param) with hwbar
  have hwbar0 : wbar ≠ 0 := (mem_of_valuation_eq_one hw).2.2.1
  have hPs : P ∉ s := fun hPs => hnot (Finset.mem_image_of_mem bq hPs)
  have hgen : ∀ Q ∈ s, A.valuation (zq Q) = A.valuation c → rcl A (c⁻¹ * P.evalAt An.param) ≠ rcl A (c⁻¹ * zq Q) :=
    fun Q hQ _ heq => hnot (by rw [hwbar, heq]; exact Finset.mem_image_of_mem bq hQ)
  have hfa : ∀ Q ∈ s, An.param - algebraMap L F (zq Q) ≠ 0 ∧ P.ord (An.param - algebraMap L F (zq Q)) = 0 :=
    fun Q hQ => ord_param_sub_eq_zero_of_ne An hP (hs hQ) (fun hPQ => hPs (hPQ ▸ hQ))

  obtain ⟨hprod0, hordprod⟩ := ord_prod_zpow P s (fun Q => An.param - algebraMap L F (zq Q)) n (fun Q hQ => (hfa Q hQ).1)
  have hordf : P.ord f = 0 := by
    rw [hfac, P.ord_mul hg0 hprod0, hordg P hP, hordprod, zero_add]
    exact Finset.sum_eq_zero fun Q hQ => by rw [(hfa Q hQ).2, mul_zero]
  refine ⟨hordf, ?_⟩

  have hgmem : g ∈ P.toValuationSubring := mem_of_ord_nonneg_gen P hg0 (hordg P hP).ge
  have hfactor : ∀ Q ∈ s, (An.param - algebraMap L F (zq Q)) ^ n Q ∈ P.toValuationSubring ∧
      P.evalAt ((An.param - algebraMap L F (zq Q)) ^ n Q) = (P.evalAt An.param - zq Q) ^ n Q := by
    intro Q hQ
    obtain ⟨hmem, hev⟩ := evalAt_zpow_of_ord_eq_zero P hPrat (hfa Q hQ).1 (hfa Q hQ).2 (n Q)
    refine ⟨hmem, ?_⟩
    rw [hev, evalAt_sub_of_mem P hPrat hzP (P.algebraMap_mem' _), evalAt_algebraMap_const P hPrat]
  obtain ⟨hprodmem, hevprod⟩ := evalAt_prod_of_mem P hPrat s
    (fun Q => (An.param - algebraMap L F (zq Q)) ^ n Q) (fun Q hQ => (hfactor Q hQ).1)
  have hevf : P.evalAt f = P.evalAt g * ∏ Q ∈ s, (P.evalAt An.param - zq Q) ^ n Q := by
    conv_lhs => rw [hfac]
    rw [evalAt_mul_of_mem P hPrat hgmem hprodmem, hevprod]
    congr 1
    exact Finset.prod_congr rfl fun Q hQ => (hfactor Q hQ).2

  have hgval : P.evalAt g = P.evalAt u * c₀ * P.evalAt An.param ^ m := by
    rw [(hu P hP).2, zpow_neg]
    field_simp

  let θ : Place L F → L := fun Q => (lam A c (zq Q))⁻¹ * (P.evalAt An.param - zq Q)
  have hθ : ∀ Q ∈ s, A.valuation (θ Q) = 1 ∧ rcl A (θ Q) = redFactor A c (zq Q) wbar :=
    fun Q hQ => factor_analysis hc0 (An.mem_dom Q (hs hQ)).2.2.2.1 h hvP (hgen Q hQ)
  have hfacθ : ∀ Q ∈ s, P.evalAt An.param - zq Q = lam A c (zq Q) * θ Q := by
    intro Q hQ
    simp only [θ]
    rw [← mul_assoc, mul_inv_cancel₀ (lam_ne_zero hc0 (An.mem_dom Q (hs hQ)).2.2.2.1), one_mul]

  obtain ⟨hTprodA, hTprodv, hTprodr⟩ := rcl_prod_zpow s θ n (fun Q hQ => (hθ Q hQ).1)
  obtain ⟨hwmA, hwmv, hwmr⟩ := rcl_zpow hw m
  have hT : P.evalAt f = (c₀ * c ^ m * ∏ Q ∈ s, lam A c (zq Q) ^ n Q) *
      (P.evalAt u * (c⁻¹ * P.evalAt An.param) ^ m * ∏ Q ∈ s, θ Q ^ n Q) := by
    rw [hevf, hgval, Finset.prod_congr rfl (fun Q hQ => by rw [hfacθ Q hQ, mul_zpow]), Finset.prod_mul_distrib,
      mul_zpow, inv_zpow]
    field_simp
  have hΛ0 : c₀ * c ^ m * ∏ Q ∈ s, lam A c (zq Q) ^ n Q ≠ 0 := by
    refine mul_ne_zero (mul_ne_zero hc₀ (zpow_ne_zero _ hc0)) (Finset.prod_ne_zero_iff.mpr fun Q hQ => ?_)
    exact zpow_ne_zero _ (lam_ne_zero hc0 (An.mem_dom Q (hs hQ)).2.2.2.1)
  have hTeq : (c₀ * c ^ m * ∏ Q ∈ s, lam A c (zq Q) ^ n Q)⁻¹ * P.evalAt f =
      P.evalAt u * (c⁻¹ * P.evalAt An.param) ^ m * ∏ Q ∈ s, θ Q ^ n Q := by
    rw [hT, ← mul_assoc, inv_mul_cancel₀ hΛ0, one_mul]
  rw [hTeq]
  obtain ⟨hPuA, -⟩ := hunitu P hP
  refine ⟨by rw [Valuation.map_mul, Valuation.map_mul, hvu P hP, hwmv, hTprodv, one_mul, one_mul], ?_⟩
  rw [rcl_mul (mul_mem hPuA hwmA) hTprodA, rcl_mul hPuA hwmA, hconst P hP hvP, hwmr, hTprodr, ← hwbar]

  have hrat := isRational_placeOfPoint' (k := k) wbar
  set Pw := placeOfPoint k wbar with hPw
  have hXu : (RatFunc.X : RatFunc k) ≠ 0 ∧ Pw.ord (RatFunc.X : RatFunc k) = 0 := by
    refine ⟨RatFunc.X_ne_zero, ?_⟩
    rw [← RatFunc.algebraMap_X]; exact ord_placeOfPoint_algebraMap_eq_zero wbar (by rw [eval_X]; exact hwbar0)
  obtain ⟨hXeA, hXev⟩ := evalAt_zpow_of_ord_eq_zero Pw hrat hXu.1 hXu.2 e
  have hlin : ∀ Q ∈ son, algebraMap k[X] (RatFunc k) (X - C (bq Q)) ≠ 0 ∧
      Pw.ord (algebraMap k[X] (RatFunc k) (X - C (bq Q))) = 0 := by
    intro Q hQ
    rw [Finset.mem_filter] at hQ
    refine ⟨by rw [ne_eq, map_eq_zero_iff _ (IsFractionRing.injective k[X] (RatFunc k))]; exact X_sub_C_ne_zero _, ?_⟩
    exact ord_placeOfPoint_algebraMap_eq_zero wbar (by rw [eval_sub, eval_X, eval_C]; exact sub_ne_zero.mpr (hgen Q hQ.1 hQ.2))
  have hlinev : ∀ Q ∈ son, (algebraMap k[X] (RatFunc k) (X - C (bq Q))) ^ n Q ∈ Pw.toValuationSubring ∧
      Pw.evalAt ((algebraMap k[X] (RatFunc k) (X - C (bq Q))) ^ n Q) = (wbar - bq Q) ^ n Q := by
    intro Q hQ
    obtain ⟨hmem, hev⟩ := evalAt_zpow_of_ord_eq_zero Pw hrat (hlin Q hQ).1 (hlin Q hQ).2 (n Q)
    refine ⟨hmem, ?_⟩
    rw [hev, evalAt_placeOfPoint_algebraMap', eval_sub, eval_X, eval_C]
  obtain ⟨hprodA', hprodev'⟩ := evalAt_prod_of_mem Pw hrat son _ (fun Q hQ => (hlinev Q hQ).1)
  have hconstmem : algebraMap k (RatFunc k) ubar ∈ Pw.toValuationSubring := Pw.algebraMap_mem' ubar
  rw [evalAt_mul_of_mem Pw hrat (mul_mem hconstmem hXeA) hprodA', evalAt_mul_of_mem Pw hrat hconstmem hXeA,
    evalAt_algebraMap_const Pw hrat, hXev, hprodev', Finset.prod_congr rfl (fun Q hQ => (hlinev Q hQ).2)]
  rw [show Pw.evalAt RatFunc.X = wbar from by rw [hPw]; exact evalAt_placeOfPoint_X' wbar]

  have hsplit : ∏ Q ∈ s, redFactor A c (zq Q) wbar ^ n Q =
      (∏ Q ∈ son, (wbar - bq Q) ^ n Q) * wbar ^ ∑ Q ∈ sin, n Q := by
    rw [← prod_zpow_eq_zpow_sum sin wbar hwbar0, Finset.prod_filter, Finset.prod_filter, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun Q hQ => ?_
    unfold redFactor
    by_cases hon : A.valuation (zq Q) = A.valuation c
    · rw [if_pos hon, if_pos hon, if_neg (by rw [hon]; exact lt_irrefl _), mul_one]
    · rw [if_neg hon, if_neg hon, one_mul]
      by_cases hin : A.valuation (zq Q) < A.valuation c
      · rw [if_pos hin, if_pos hin]
      · rw [if_neg hin, if_neg hin, one_zpow]
  rw [Finset.prod_congr rfl (fun Q hQ => by rw [(hθ Q hQ).2]), hsplit]
  simp only [e]
  rw [zpow_add₀ hwbar0]
  ring

end AlgebraicCurve.Annulus.CircleChart

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "Annulus Place Place.ord_zero Place.algebraMap_mem' Place.algebraMap_evalAt Annulus.exists_eq_mul_prod_param_sub_zpow Annulus.residue_evalAt_eq_of_forall_isUnit_evalAt"
namespace Annulus
p2m_export "AlgebraicCurve.Annulus" "unit_principle existsUnique_evalAt_eq modulus dom mem_dom param ord_param_sub exists_eq_mul_prod_param_sub_zpow residue_evalAt_eq_of_forall_isUnit_evalAt"
namespace CircleChart
p2m_open "AlgebraicCurve.Annulus AlgebraicCurve"

p2m_open "AlgebraicCurve P2MW.S_AlgebraicCurve_Annulus_exists_ringHom_ratFunc_of_valuation_lt_of_exists_lt.AlgebraicCurve AlgebraicCurve.RationalFunctionField AlgebraicCurve.StandardAnnulus AlgebraicCurve.GaussReduction"
open Polynomial
open scoped Classical

variable {L : Type*} [Field L] {A : ValuationSubring L} {F : Type*} [Field F] [Algebra L F]

theorem rcl_zpow' {x : L} (hx : x ∈ A) (n : ℤ) (h : A.valuation x = 1 ∨ 0 ≤ n) :
    x ^ n ∈ A ∧ rcl A (x ^ n) = rcl A x ^ n := by
  rcases h with h | h
  · exact ⟨(rcl_zpow h n).1, (rcl_zpow h n).2.2⟩
  · obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le h
    rw [zpow_natCast, zpow_natCast]
    refine ⟨A.pow_mem hx m, ?_⟩
    clear h
    induction m with
    | zero => rw [pow_zero, pow_zero, rcl_one]
    | succ m ih => rw [pow_succ, pow_succ, rcl_mul (A.pow_mem hx m) hx, ih]

theorem rcl_prod_zpow' {ι : Type*} (t : Finset ι) (θ : ι → L) (n : ι → ℤ)
    (hθ : ∀ i ∈ t, θ i ∈ A ∧ (A.valuation (θ i) = 1 ∨ 0 ≤ n i)) :
    (∏ i ∈ t, θ i ^ n i) ∈ A ∧ rcl A (∏ i ∈ t, θ i ^ n i) = ∏ i ∈ t, rcl A (θ i) ^ n i := by
  induction t using Finset.induction_on with
  | empty => exact ⟨by rw [Finset.prod_empty]; exact A.one_mem, by rw [Finset.prod_empty, Finset.prod_empty, rcl_one]⟩
  | insert i t hit ih =>
    rw [Finset.forall_mem_insert] at hθ
    obtain ⟨hmem, hres⟩ := ih hθ.2
    obtain ⟨hmemi, hresi⟩ := rcl_zpow' hθ.1.1 (n i) hθ.1.2
    refine ⟨by rw [Finset.prod_insert hit]; exact mul_mem hmemi hmem, ?_⟩
    rw [Finset.prod_insert hit, Finset.prod_insert hit, rcl_mul hmemi hmem, hresi, hres]

theorem factor_analysis' {c zP zQ : L} (hc0 : c ≠ 0) (hzQ0 : zQ ≠ 0)
    (h : c⁻¹ * zP ∈ A) (hv : A.valuation zP = A.valuation c) :
    (lam A c zQ)⁻¹ * (zP - zQ) ∈ A ∧
      rcl A ((lam A c zQ)⁻¹ * (zP - zQ)) = redFactor A c zQ (rcl A (c⁻¹ * zP)) ∧
      ((A.valuation zQ = A.valuation c → rcl A (c⁻¹ * zP) ≠ rcl A (c⁻¹ * zQ)) →
        A.valuation ((lam A c zQ)⁻¹ * (zP - zQ)) = 1) := by
  by_cases hgen : A.valuation zQ = A.valuation c → rcl A (c⁻¹ * zP) ≠ rcl A (c⁻¹ * zQ)
  · obtain ⟨hval, hres⟩ := factor_analysis hc0 hzQ0 h hv hgen
    exact ⟨(mem_of_valuation_eq_one hval).1, hres, fun _ => hval⟩
  ·
    push Not at hgen
    obtain ⟨hon, heq⟩ := hgen
    have hvc : A.valuation c ≠ 0 := by rwa [ne_eq, Valuation.zero_iff]
    have hlam : lam A c zQ = c := by unfold lam; rw [if_pos hon.le]
    have hwQ : A.valuation (c⁻¹ * zQ) = 1 := by rw [Valuation.map_mul, Valuation.map_inv, hon, inv_mul_cancel₀ hvc]
    have hwQA : c⁻¹ * zQ ∈ A := (mem_of_valuation_eq_one hwQ).1
    have heq' : (lam A c zQ)⁻¹ * (zP - zQ) = c⁻¹ * zP - c⁻¹ * zQ := by rw [hlam, mul_sub]
    have hred : redFactor A c zQ (rcl A (c⁻¹ * zP)) = rcl A (c⁻¹ * zP) - rcl A (c⁻¹ * zQ) := by
      unfold redFactor; rw [if_pos hon]
    rw [heq', hred, rcl_sub h hwQA]
    exact ⟨sub_mem h hwQA, rfl, fun hg => absurd heq (hg hon)⟩

end AlgebraicCurve.Annulus.CircleChart

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "Annulus Place Place.ord_zero Place.algebraMap_mem' Place.algebraMap_evalAt Annulus.exists_eq_mul_prod_param_sub_zpow Annulus.residue_evalAt_eq_of_forall_isUnit_evalAt"
namespace Annulus
p2m_export "AlgebraicCurve.Annulus" "unit_principle existsUnique_evalAt_eq modulus dom mem_dom param ord_param_sub exists_eq_mul_prod_param_sub_zpow residue_evalAt_eq_of_forall_isUnit_evalAt"
namespace CircleChart
p2m_open "AlgebraicCurve.Annulus AlgebraicCurve"

p2m_open "AlgebraicCurve P2MW.S_AlgebraicCurve_Annulus_exists_ringHom_ratFunc_of_valuation_lt_of_exists_lt.AlgebraicCurve AlgebraicCurve.RationalFunctionField AlgebraicCurve.StandardAnnulus AlgebraicCurve.GaussReduction"
open Polynomial
open scoped Classical

variable {L : Type*} [Field L] {A : ValuationSubring L} {F : Type*} [Field F] [Algebra L F]

section EvalHelpers2
variable {K' F' : Type*} [Field K'] [Field F'] [Algebra K' F']

theorem evalAt_zpow' (P : Place K' F') (hP : P.IsRational) {f : F'} (hf : f ∈ P.toValuationSubring) (n : ℤ)
    (h : (f ≠ 0 ∧ P.ord f = 0) ∨ 0 ≤ n) :
    f ^ n ∈ P.toValuationSubring ∧ P.evalAt (f ^ n) = P.evalAt f ^ n := by
  rcases h with ⟨hf0, h0⟩ | h
  · exact evalAt_zpow_of_ord_eq_zero P hP hf0 h0 n
  · obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le h
    rw [zpow_natCast, zpow_natCast]
    exact ⟨pow_mem hf m, evalAt_pow_of_mem P hP hf m⟩

end EvalHelpers2

theorem exists_interpolant' (An : Annulus A F)
    (hfin : ∀ f : F, f ≠ 0 → {P : Place L F | P ∈ An.dom ∧ P.ord f ≠ 0}.Finite)
    (c : L) (hc : A.valuation ((An.modulus : A) : L) < A.valuation c ∧ A.valuation c < 1)
    (hinf : Infinite (IsLocalRing.ResidueField A))
    (hR : (∃ b : L, A.valuation c < A.valuation b ∧ A.valuation b < 1) ∧
      (∃ b : L, A.valuation ((An.modulus : A) : L) < A.valuation b ∧ A.valuation b < A.valuation c))
    (f : F) (hf : f ≠ 0) :
    ∃ (t₀ : Finset (IsLocalRing.ResidueField A)) (Λ : L) (R₀ : RatFunc (IsLocalRing.ResidueField A)),
      Λ ≠ 0 ∧ R₀ ≠ 0 ∧
      (∀ P ∈ An.dom, ∀ h : c⁻¹ * P.evalAt An.param ∈ A, A.valuation (P.evalAt An.param) = A.valuation c →
        rcl A (c⁻¹ * P.evalAt An.param) ∉ t₀ →
          P.ord f = 0 ∧ A.valuation (Λ⁻¹ * P.evalAt f) = 1 ∧ Λ⁻¹ * P.evalAt f ∈ A ∧
          R₀ ∈ (placeOfPoint (IsLocalRing.ResidueField A) (rcl A (c⁻¹ * P.evalAt An.param))).toValuationSubring ∧
            rcl A (Λ⁻¹ * P.evalAt f) =
              (placeOfPoint (IsLocalRing.ResidueField A) (rcl A (c⁻¹ * P.evalAt An.param))).evalAt R₀) ∧
      (∀ P ∈ An.dom, ∀ h : c⁻¹ * P.evalAt An.param ∈ A, A.valuation (P.evalAt An.param) = A.valuation c →
        f ∈ P.toValuationSubring →
        (∀ w ∈ An.dom, ∀ h' : c⁻¹ * w.evalAt An.param ∈ A, A.valuation (w.evalAt An.param) = A.valuation c →
            rcl A (c⁻¹ * w.evalAt An.param) = rcl A (c⁻¹ * P.evalAt An.param) → f ∈ w.toValuationSubring) →
          Λ⁻¹ * P.evalAt f ∈ A ∧
          R₀ ∈ (placeOfPoint (IsLocalRing.ResidueField A) (rcl A (c⁻¹ * P.evalAt An.param))).toValuationSubring ∧
            rcl A (Λ⁻¹ * P.evalAt f) =
              (placeOfPoint (IsLocalRing.ResidueField A) (rcl A (c⁻¹ * P.evalAt An.param))).evalAt R₀) := by
  set k := IsLocalRing.ResidueField A
  have hc0 : c ≠ 0 := by
    intro h0; rw [h0, Valuation.map_zero] at hc; exact (not_lt_of_ge zero_le' hc.1).elim
  have hvc : A.valuation c ≠ 0 := by rwa [ne_eq, Valuation.zero_iff]
  obtain ⟨s, n, g, hs, hg0, hordg, hfac⟩ :=
    AlgebraicCurve.Annulus.exists_eq_mul_prod_param_sub_zpow An hfin f hf
  obtain ⟨m, c₀, hc₀, hunit⟩ := An.unit_principle g hg0 hordg
  have hz : ∀ P ∈ An.dom, An.param ≠ 0 ∧ P.ord An.param = 0 := by
    intro P hP
    obtain ⟨hPrat, hzP, -, hzP0, -⟩ := An.mem_dom P hP
    have hz0 : An.param ≠ 0 := by
      intro h0; apply hzP0; rw [h0]; exact evalAt_zero' P hPrat
    exact ⟨hz0, ord_eq_zero_of_evalAt_ne_zero P hzP hzP0⟩
  set u : F := g * algebraMap L F c₀⁻¹ * An.param ^ (-m) with hu_def
  have hu : ∀ P ∈ An.dom, u ∈ P.toValuationSubring ∧
      P.evalAt u = P.evalAt g * c₀⁻¹ * P.evalAt An.param ^ (-m) := by
    intro P hP
    obtain ⟨hPrat, hzP, -, hzP0, -⟩ := An.mem_dom P hP
    have hgmem : g ∈ P.toValuationSubring := mem_of_ord_nonneg_gen P hg0 (hordg P hP).ge
    obtain ⟨hzm, hzev⟩ := evalAt_zpow_of_ord_eq_zero P hPrat (hz P hP).1 (hz P hP).2 (-m)
    have h1 : g * algebraMap L F c₀⁻¹ ∈ P.toValuationSubring := mul_mem hgmem (P.algebraMap_mem' _)
    refine ⟨mul_mem h1 hzm, ?_⟩
    rw [hu_def, evalAt_mul_of_mem P hPrat h1 hzm, evalAt_mul_of_mem P hPrat hgmem (P.algebraMap_mem' _),
      evalAt_algebraMap_const P hPrat, hzev]
  have hunitu : ∀ P ∈ An.dom, ∃ h : P.evalAt u ∈ A, IsUnit (⟨P.evalAt u, h⟩ : A) := by
    intro P hP
    rw [(hu P hP).2]
    exact hunit P hP
  have hvu : ∀ P ∈ An.dom, A.valuation (P.evalAt u) = 1 := by
    intro P hP
    obtain ⟨h, hU⟩ := hunitu P hP
    exact (A.valuation_eq_one_iff _).mp hU
  obtain ⟨P₁, hP₁, hzP₁⟩ := exists_mem_dom_evalAt_eq An hc (1 : A) isUnit_one
  have hvP₁ : A.valuation (P₁.evalAt An.param) = A.valuation c := by
    rw [hzP₁]; simp
  set ubar : k := rcl A (P₁.evalAt u) with hubar
  have hconst : ∀ P ∈ An.dom, A.valuation (P.evalAt An.param) = A.valuation c → rcl A (P.evalAt u) = ubar := by
    intro P hP hvP
    obtain ⟨hPu, -⟩ := hunitu P hP
    obtain ⟨hP₁u, -⟩ := hunitu P₁ hP₁
    rw [hubar, rcl_eq hPu, rcl_eq hP₁u]
    exact AlgebraicCurve.Annulus.residue_evalAt_eq_of_forall_isUnit_evalAt An hfin c hc hinf hR u
      (fun Q hQ => (hu Q hQ).1) hunitu P P₁ hP hP₁ hvP hvP₁ hPu hP₁u
  have hubar0 : ubar ≠ 0 := (mem_of_valuation_eq_one (hvu P₁ hP₁)).2.2.1

  have hordQ : ∀ Q ∈ s, Q.ord f = n Q := by
    intro Q hQ
    have hfa : ∀ Q' ∈ s, An.param - algebraMap L F (Q'.evalAt An.param) ≠ 0 ∧
        Q.ord (An.param - algebraMap L F (Q'.evalAt An.param)) = if Q' = Q then 1 else 0 := by
      intro Q' hQ'
      by_cases hQQ : Q' = Q
      · subst hQQ
        refine ⟨fun h0 => ?_, by rw [if_pos rfl]; exact An.ord_param_sub Q' (hs hQ')⟩
        have h1 := An.ord_param_sub Q' (hs hQ'); rw [h0, Place.ord_zero] at h1; exact zero_ne_one h1
      · rw [if_neg hQQ]; exact ord_param_sub_eq_zero_of_ne An (hs hQ) (hs hQ') (Ne.symm hQQ)
    obtain ⟨hprod0, hordprod⟩ := ord_prod_zpow Q s (fun Q' => An.param - algebraMap L F (Q'.evalAt An.param)) n
      (fun Q' hQ' => (hfa Q' hQ').1)
    rw [hfac, Q.ord_mul hg0 hprod0, hordg Q (hs hQ), hordprod, zero_add,
      Finset.sum_congr rfl (fun Q' hQ' => by rw [(hfa Q' hQ').2]), ]
    simp [Finset.sum_ite_eq', hQ]

  let zq : Place L F → L := fun Q => Q.evalAt An.param
  let bq : Place L F → k := fun Q => rcl A (c⁻¹ * zq Q)
  let son := s.filter (fun Q => A.valuation (zq Q) = A.valuation c)
  let sin := s.filter (fun Q => A.valuation (zq Q) < A.valuation c)
  let e : ℤ := m + ∑ Q ∈ sin, n Q
  set Λ : L := c₀ * c ^ m * ∏ Q ∈ s, lam A c (zq Q) ^ n Q with hΛdef
  set R₀ : RatFunc k := algebraMap k (RatFunc k) ubar * (RatFunc.X : RatFunc k) ^ e *
      ∏ Q ∈ son, (algebraMap k[X] (RatFunc k) (X - C (bq Q))) ^ n Q with hR₀def
  have hΛ0 : Λ ≠ 0 := by
    refine mul_ne_zero (mul_ne_zero hc₀ (zpow_ne_zero _ hc0)) (Finset.prod_ne_zero_iff.mpr fun Q hQ => ?_)
    exact zpow_ne_zero _ (lam_ne_zero hc0 (An.mem_dom Q (hs hQ)).2.2.2.1)
  have hR₀0 : R₀ ≠ 0 := by
    refine mul_ne_zero (mul_ne_zero ?_ (zpow_ne_zero _ RatFunc.X_ne_zero))
      (Finset.prod_ne_zero_iff.mpr fun Q _ => zpow_ne_zero _ ?_)
    · rwa [ne_eq, map_eq_zero_iff _ (algebraMap k (RatFunc k)).injective]
    · rw [ne_eq, map_eq_zero_iff _ (IsFractionRing.injective k[X] (RatFunc k))]; exact X_sub_C_ne_zero _

  have key : ∀ P ∈ An.dom, ∀ h : c⁻¹ * P.evalAt An.param ∈ A, A.valuation (P.evalAt An.param) = A.valuation c →
      f ∈ P.toValuationSubring →
      (∀ Q ∈ s, A.valuation (zq Q) = A.valuation c → rcl A (c⁻¹ * P.evalAt An.param) = rcl A (c⁻¹ * zq Q) → 0 ≤ n Q) →
      (Λ⁻¹ * P.evalAt f ∈ A ∧ R₀ ∈ (placeOfPoint k (rcl A (c⁻¹ * P.evalAt An.param))).toValuationSubring ∧
        rcl A (Λ⁻¹ * P.evalAt f) = (placeOfPoint k (rcl A (c⁻¹ * P.evalAt An.param))).evalAt R₀) ∧
      ((∀ Q ∈ s, A.valuation (zq Q) = A.valuation c → rcl A (c⁻¹ * P.evalAt An.param) ≠ rcl A (c⁻¹ * zq Q)) →
        P.ord f = 0 ∧ A.valuation (Λ⁻¹ * P.evalAt f) = 1) := by
    intro P hP h hvP hfP hclass
    obtain ⟨hPrat, hzP, -, hzP0, -⟩ := An.mem_dom P hP
    have hw : A.valuation (c⁻¹ * P.evalAt An.param) = 1 := by
      rw [Valuation.map_mul, Valuation.map_inv, hvP, inv_mul_cancel₀ hvc]
    set wbar : k := rcl A (c⁻¹ * P.evalAt An.param) with hwbar
    have hwbar0 : wbar ≠ 0 := (mem_of_valuation_eq_one hw).2.2.1

    have hnP : P ∈ s → 0 ≤ n P := fun hPs => hclass P hPs hvP rfl

    have hfa : ∀ Q ∈ s, An.param - algebraMap L F (zq Q) ≠ 0 ∧ An.param - algebraMap L F (zq Q) ∈ P.toValuationSubring ∧
        ((An.param - algebraMap L F (zq Q) ≠ 0 ∧ P.ord (An.param - algebraMap L F (zq Q)) = 0) ∨ 0 ≤ n Q) := by
      intro Q hQ
      have hmem : An.param - algebraMap L F (zq Q) ∈ P.toValuationSubring := sub_mem hzP (P.algebraMap_mem' _)
      by_cases hPQ : P = Q
      · subst hPQ
        refine ⟨fun h0 => ?_, hmem, Or.inr (hnP hQ)⟩
        have h1 := An.ord_param_sub P hP; rw [show An.param - algebraMap L F (P.evalAt An.param) = 0 from h0,
          Place.ord_zero] at h1; exact zero_ne_one h1
      · have := ord_param_sub_eq_zero_of_ne An hP (hs hQ) hPQ
        exact ⟨this.1, hmem, Or.inl this⟩

    have hgmem : g ∈ P.toValuationSubring := mem_of_ord_nonneg_gen P hg0 (hordg P hP).ge
    have hfactor : ∀ Q ∈ s, (An.param - algebraMap L F (zq Q)) ^ n Q ∈ P.toValuationSubring ∧
        P.evalAt ((An.param - algebraMap L F (zq Q)) ^ n Q) = (P.evalAt An.param - zq Q) ^ n Q := by
      intro Q hQ
      obtain ⟨hmem, hev⟩ := evalAt_zpow' P hPrat (hfa Q hQ).2.1 (n Q) (hfa Q hQ).2.2
      refine ⟨hmem, ?_⟩
      rw [hev, evalAt_sub_of_mem P hPrat hzP (P.algebraMap_mem' _), evalAt_algebraMap_const P hPrat]
    obtain ⟨hprodmem, hevprod⟩ := evalAt_prod_of_mem P hPrat s
      (fun Q => (An.param - algebraMap L F (zq Q)) ^ n Q) (fun Q hQ => (hfactor Q hQ).1)
    have hevf : P.evalAt f = P.evalAt g * ∏ Q ∈ s, (P.evalAt An.param - zq Q) ^ n Q := by
      conv_lhs => rw [hfac]
      rw [evalAt_mul_of_mem P hPrat hgmem hprodmem, hevprod]
      congr 1
      exact Finset.prod_congr rfl fun Q hQ => (hfactor Q hQ).2
    have hgval : P.evalAt g = P.evalAt u * c₀ * P.evalAt An.param ^ m := by
      rw [(hu P hP).2, zpow_neg]
      field_simp

    let θ : Place L F → L := fun Q => (lam A c (zq Q))⁻¹ * (P.evalAt An.param - zq Q)
    have hθ : ∀ Q ∈ s, θ Q ∈ A ∧ rcl A (θ Q) = redFactor A c (zq Q) wbar ∧
        ((A.valuation (zq Q) = A.valuation c → rcl A (c⁻¹ * P.evalAt An.param) ≠ rcl A (c⁻¹ * zq Q)) →
          A.valuation (θ Q) = 1) :=
      fun Q hQ => factor_analysis' hc0 (An.mem_dom Q (hs hQ)).2.2.2.1 h hvP
    have hθ' : ∀ Q ∈ s, θ Q ∈ A ∧ (A.valuation (θ Q) = 1 ∨ 0 ≤ n Q) := by
      intro Q hQ
      refine ⟨(hθ Q hQ).1, ?_⟩
      by_cases hg : A.valuation (zq Q) = A.valuation c → rcl A (c⁻¹ * P.evalAt An.param) ≠ rcl A (c⁻¹ * zq Q)
      · exact Or.inl ((hθ Q hQ).2.2 hg)
      · push Not at hg
        exact Or.inr (hclass Q hQ hg.1 hg.2)
    have hfacθ : ∀ Q ∈ s, P.evalAt An.param - zq Q = lam A c (zq Q) * θ Q := by
      intro Q hQ
      simp only [θ]
      rw [← mul_assoc, mul_inv_cancel₀ (lam_ne_zero hc0 (An.mem_dom Q (hs hQ)).2.2.2.1), one_mul]
    obtain ⟨hTprodA, hTprodr⟩ := rcl_prod_zpow' s θ n hθ'
    obtain ⟨hwmA, hwmv, hwmr⟩ := rcl_zpow hw m
    have hT : P.evalAt f = Λ * (P.evalAt u * (c⁻¹ * P.evalAt An.param) ^ m * ∏ Q ∈ s, θ Q ^ n Q) := by
      rw [hevf, hgval, Finset.prod_congr rfl (fun Q hQ => by rw [hfacθ Q hQ, mul_zpow]), Finset.prod_mul_distrib,
        mul_zpow, inv_zpow, hΛdef]
      field_simp
    have hTeq : Λ⁻¹ * P.evalAt f = P.evalAt u * (c⁻¹ * P.evalAt An.param) ^ m * ∏ Q ∈ s, θ Q ^ n Q := by
      rw [hT, ← mul_assoc, inv_mul_cancel₀ hΛ0, one_mul]
    obtain ⟨hPuA, -⟩ := hunitu P hP
    have hTA : Λ⁻¹ * P.evalAt f ∈ A := by rw [hTeq]; exact mul_mem (mul_mem hPuA hwmA) hTprodA

    have hrat := isRational_placeOfPoint' (k := k) wbar
    set Pw := placeOfPoint k wbar with hPw
    have hXu : (RatFunc.X : RatFunc k) ≠ 0 ∧ Pw.ord (RatFunc.X : RatFunc k) = 0 := by
      refine ⟨RatFunc.X_ne_zero, ?_⟩
      rw [← RatFunc.algebraMap_X]; exact ord_placeOfPoint_algebraMap_eq_zero wbar (by rw [eval_X]; exact hwbar0)
    obtain ⟨hXeA, hXev⟩ := evalAt_zpow_of_ord_eq_zero Pw hrat hXu.1 hXu.2 e
    have hlinev : ∀ Q ∈ son, (algebraMap k[X] (RatFunc k) (X - C (bq Q))) ^ n Q ∈ Pw.toValuationSubring ∧
        Pw.evalAt ((algebraMap k[X] (RatFunc k) (X - C (bq Q))) ^ n Q) = (wbar - bq Q) ^ n Q := by
      intro Q hQ
      rw [Finset.mem_filter] at hQ
      have hmem := algebraMap_mem_placeOfPoint (K := k) wbar (X - C (bq Q))
      have hcond : ((algebraMap k[X] (RatFunc k) (X - C (bq Q)) ≠ 0 ∧
          Pw.ord (algebraMap k[X] (RatFunc k) (X - C (bq Q))) = 0) ∨ 0 ≤ n Q) := by
        by_cases hbw : wbar = bq Q
        · exact Or.inr (hclass Q hQ.1 hQ.2 hbw)
        · refine Or.inl ⟨by rw [ne_eq, map_eq_zero_iff _ (IsFractionRing.injective k[X] (RatFunc k))]; exact X_sub_C_ne_zero _, ?_⟩
          exact ord_placeOfPoint_algebraMap_eq_zero wbar (by rw [eval_sub, eval_X, eval_C]; exact sub_ne_zero.mpr hbw)
      obtain ⟨hm, hev⟩ := evalAt_zpow' Pw hrat hmem (n Q) hcond
      exact ⟨hm, by rw [hev, evalAt_placeOfPoint_algebraMap', eval_sub, eval_X, eval_C]⟩
    obtain ⟨hprodA', hprodev'⟩ := evalAt_prod_of_mem Pw hrat son _ (fun Q hQ => (hlinev Q hQ).1)
    have hconstmem : algebraMap k (RatFunc k) ubar ∈ Pw.toValuationSubring := Pw.algebraMap_mem' ubar
    have hR₀mem : R₀ ∈ Pw.toValuationSubring := by
      rw [hR₀def]; exact mul_mem (mul_mem hconstmem hXeA) hprodA'
    have hR₀ev : Pw.evalAt R₀ = ubar * wbar ^ e * ∏ Q ∈ son, (wbar - bq Q) ^ n Q := by
      rw [hR₀def, evalAt_mul_of_mem Pw hrat (mul_mem hconstmem hXeA) hprodA', evalAt_mul_of_mem Pw hrat hconstmem hXeA,
        evalAt_algebraMap_const Pw hrat, hXev, hprodev', Finset.prod_congr rfl (fun Q hQ => (hlinev Q hQ).2),
        show Pw.evalAt RatFunc.X = wbar from by rw [hPw]; exact evalAt_placeOfPoint_X' wbar]
    have hsplit : ∏ Q ∈ s, redFactor A c (zq Q) wbar ^ n Q =
        (∏ Q ∈ son, (wbar - bq Q) ^ n Q) * wbar ^ ∑ Q ∈ sin, n Q := by
      rw [← prod_zpow_eq_zpow_sum sin wbar hwbar0, Finset.prod_filter, Finset.prod_filter, ← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun Q hQ => ?_
      unfold redFactor
      by_cases hon : A.valuation (zq Q) = A.valuation c
      · rw [if_pos hon, if_pos hon, if_neg (by rw [hon]; exact lt_irrefl _), mul_one]
      · rw [if_neg hon, if_neg hon, one_mul]
        by_cases hin : A.valuation (zq Q) < A.valuation c
        · rw [if_pos hin, if_pos hin]
        · rw [if_neg hin, if_neg hin, one_zpow]
    refine ⟨⟨hTA, hR₀mem, ?_⟩, fun hgenP => ?_⟩
    · rw [hTeq, rcl_mul (mul_mem hPuA hwmA) hTprodA, rcl_mul hPuA hwmA, hconst P hP hvP, hwmr, hTprodr, ← hwbar,
        Finset.prod_congr rfl (fun Q hQ => by rw [(hθ Q hQ).2.1]), hsplit, hR₀ev]
      simp only [e]
      rw [zpow_add₀ hwbar0]
      ring
    ·
      have hPs : P ∉ s := fun hPs => hgenP P hPs hvP rfl
      have hfa0 : ∀ Q ∈ s, An.param - algebraMap L F (zq Q) ≠ 0 ∧ P.ord (An.param - algebraMap L F (zq Q)) = 0 :=
        fun Q hQ => ord_param_sub_eq_zero_of_ne An hP (hs hQ) (fun hPQ => hPs (hPQ ▸ hQ))
      obtain ⟨hprod0, hordprod⟩ := ord_prod_zpow P s (fun Q => An.param - algebraMap L F (zq Q)) n (fun Q hQ => (hfa0 Q hQ).1)
      refine ⟨?_, ?_⟩
      · rw [hfac, P.ord_mul hg0 hprod0, hordg P hP, hordprod, zero_add]
        exact Finset.sum_eq_zero fun Q hQ => by rw [(hfa0 Q hQ).2, mul_zero]
      · rw [hTeq, Valuation.map_mul, Valuation.map_mul, hvu P hP, hwmv, one_mul, one_mul, map_prod]
        exact Finset.prod_eq_one fun Q hQ => by rw [map_zpow₀, (hθ Q hQ).2.2 (hgenP Q hQ), one_zpow]

  refine ⟨s.image bq, Λ, R₀, hΛ0, hR₀0, ?_, ?_⟩
  · intro P hP h hvP hnot
    have hgenP : ∀ Q ∈ s, A.valuation (zq Q) = A.valuation c → rcl A (c⁻¹ * P.evalAt An.param) ≠ rcl A (c⁻¹ * zq Q) :=
      fun Q hQ _ heq => hnot (by rw [heq]; exact Finset.mem_image_of_mem bq hQ)
    have hPs : P ∉ s := fun hPs => hgenP P hPs hvP rfl

    have hclass : ∀ Q ∈ s, A.valuation (zq Q) = A.valuation c → rcl A (c⁻¹ * P.evalAt An.param) = rcl A (c⁻¹ * zq Q) → 0 ≤ n Q :=
      fun Q hQ hon heq => absurd heq (hgenP Q hQ hon)

    have hfa0 : ∀ Q ∈ s, An.param - algebraMap L F (zq Q) ≠ 0 ∧ P.ord (An.param - algebraMap L F (zq Q)) = 0 :=
      fun Q hQ => ord_param_sub_eq_zero_of_ne An hP (hs hQ) (fun hPQ => hPs (hPQ ▸ hQ))
    obtain ⟨hprod0, hordprod⟩ := ord_prod_zpow P s (fun Q => An.param - algebraMap L F (zq Q)) n (fun Q hQ => (hfa0 Q hQ).1)
    have hordf : P.ord f = 0 := by
      rw [hfac, P.ord_mul hg0 hprod0, hordg P hP, hordprod, zero_add]
      exact Finset.sum_eq_zero fun Q hQ => by rw [(hfa0 Q hQ).2, mul_zero]
    have hfP : f ∈ P.toValuationSubring := mem_of_ord_nonneg_gen P hf hordf.ge
    obtain ⟨⟨hTA, hR₀mem, hval⟩, hgen'⟩ := key P hP h hvP hfP hclass
    obtain ⟨-, hv1⟩ := hgen' hgenP
    exact ⟨hordf, hv1, hTA, hR₀mem, hval⟩
  · intro P hP h hvP hfP hreg
    refine (key P hP h hvP hfP fun Q hQ hon heq => ?_).1

    have hwQA : c⁻¹ * zq Q ∈ A :=
      (mem_of_valuation_eq_one (by rw [Valuation.map_mul, Valuation.map_inv, hon, inv_mul_cancel₀ hvc])).1
    have hfQ : f ∈ Q.toValuationSubring := hreg Q (hs hQ) hwQA hon heq.symm
    rw [← hordQ Q hQ]
    exact ord_nonneg_of_mem_gen Q hfQ hf

end AlgebraicCurve.Annulus.CircleChart

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "Annulus Place Place.ord_zero Place.algebraMap_mem' Place.algebraMap_evalAt Annulus.exists_eq_mul_prod_param_sub_zpow Annulus.residue_evalAt_eq_of_forall_isUnit_evalAt"
namespace Annulus
p2m_export "AlgebraicCurve.Annulus" "unit_principle existsUnique_evalAt_eq modulus dom mem_dom param ord_param_sub exists_eq_mul_prod_param_sub_zpow residue_evalAt_eq_of_forall_isUnit_evalAt"
namespace CircleChart
p2m_open "AlgebraicCurve.Annulus AlgebraicCurve"

p2m_open "AlgebraicCurve P2MW.S_AlgebraicCurve_Annulus_exists_ringHom_ratFunc_of_valuation_lt_of_exists_lt.AlgebraicCurve AlgebraicCurve.RationalFunctionField AlgebraicCurve.StandardAnnulus AlgebraicCurve.GaussReduction"
open Polynomial
open scoped Classical

variable {L : Type*} [Field L] {A : ValuationSubring L} {F : Type*} [Field F] [Algebra L F]

theorem rcl_add {x y : L} (hx : x ∈ A) (hy : y ∈ A) : rcl A (x + y) = rcl A x + rcl A y := by
  rw [rcl_eq hx, rcl_eq hy, rcl_eq (add_mem hx hy), ← map_add]; rfl

theorem rcl_zero : rcl A (0 : L) = 0 := by
  rw [rcl_eq A.zero_mem]; exact map_zero _

def Interp (An : Annulus A F) (c : L) (f : F) (R : RatFunc (IsLocalRing.ResidueField A)) : Prop :=
  ∃ t : Finset (IsLocalRing.ResidueField A), ∀ P ∈ An.dom, ∀ h : c⁻¹ * P.evalAt An.param ∈ A,
    A.valuation (P.evalAt An.param) = A.valuation c → rcl A (c⁻¹ * P.evalAt An.param) ∉ t →
      f ∈ P.toValuationSubring ∧ P.evalAt f ∈ A ∧
      R ∈ (placeOfPoint (IsLocalRing.ResidueField A) (rcl A (c⁻¹ * P.evalAt An.param))).toValuationSubring ∧
      rcl A (P.evalAt f) = (placeOfPoint (IsLocalRing.ResidueField A) (rcl A (c⁻¹ * P.evalAt An.param))).evalAt R

variable (An : Annulus A F) (c : L)

theorem interp_zero : Interp An c (0 : F) 0 := by
  refine ⟨∅, fun P hP h hv _ => ?_⟩
  have hPrat := (An.mem_dom P hP).1
  have hrat := isRational_placeOfPoint' (k := IsLocalRing.ResidueField A) (rcl A (c⁻¹ * P.evalAt An.param))
  refine ⟨zero_mem _, by rw [evalAt_zero' P hPrat]; exact A.zero_mem, zero_mem _, ?_⟩
  rw [evalAt_zero' P hPrat, rcl_zero, evalAt_zero' _ hrat]

theorem interp_const {a : L} (ha : a ∈ A) :
    Interp An c (algebraMap L F a) (algebraMap (IsLocalRing.ResidueField A) _ (rcl A a)) := by
  refine ⟨∅, fun P hP h hv _ => ?_⟩
  have hPrat := (An.mem_dom P hP).1
  have hrat := isRational_placeOfPoint' (k := IsLocalRing.ResidueField A) (rcl A (c⁻¹ * P.evalAt An.param))
  refine ⟨P.algebraMap_mem' a, by rw [evalAt_algebraMap_const P hPrat]; exact ha, Place.algebraMap_mem' _ _, ?_⟩
  rw [evalAt_algebraMap_const P hPrat, evalAt_algebraMap_const _ hrat]

theorem interp_one : Interp An c (1 : F) 1 := by
  have h := interp_const An c A.one_mem
  rwa [map_one, rcl_one, map_one] at h

theorem interp_X : Interp An c (algebraMap L F c⁻¹ * An.param) RatFunc.X := by
  refine ⟨∅, fun P hP h hv _ => ?_⟩
  obtain ⟨hPrat, hzP, -⟩ := An.mem_dom P hP
  have hmem : algebraMap L F c⁻¹ * An.param ∈ P.toValuationSubring := mul_mem (P.algebraMap_mem' _) hzP
  have hev : P.evalAt (algebraMap L F c⁻¹ * An.param) = c⁻¹ * P.evalAt An.param := by
    rw [evalAt_mul_of_mem P hPrat (P.algebraMap_mem' _) hzP, evalAt_algebraMap_const P hPrat]
  refine ⟨hmem, by rw [hev]; exact h, X_mem_placeOfPoint _, ?_⟩
  rw [hev, evalAt_placeOfPoint_X']

variable {An c}

theorem Interp.add {f g : F} {R S : RatFunc (IsLocalRing.ResidueField A)} (hf : Interp An c f R) (hg : Interp An c g S) :
    Interp An c (f + g) (R + S) := by
  obtain ⟨t, ht⟩ := hf
  obtain ⟨t', ht'⟩ := hg
  refine ⟨t ∪ t', fun P hP h hv hnot => ?_⟩
  rw [Finset.mem_union, not_or] at hnot
  obtain ⟨hfm, hfv, hRm, hfr⟩ := ht P hP h hv hnot.1
  obtain ⟨hgm, hgv, hSm, hgr⟩ := ht' P hP h hv hnot.2
  have hPrat := (An.mem_dom P hP).1
  have hrat := isRational_placeOfPoint' (k := IsLocalRing.ResidueField A) (rcl A (c⁻¹ * P.evalAt An.param))
  refine ⟨add_mem hfm hgm, by rw [evalAt_add_of_mem P hPrat hfm hgm]; exact add_mem hfv hgv, add_mem hRm hSm, ?_⟩
  rw [evalAt_add_of_mem P hPrat hfm hgm, rcl_add hfv hgv, hfr, hgr, evalAt_add_of_mem _ hrat hRm hSm]

theorem Interp.mul {f g : F} {R S : RatFunc (IsLocalRing.ResidueField A)} (hf : Interp An c f R) (hg : Interp An c g S) :
    Interp An c (f * g) (R * S) := by
  obtain ⟨t, ht⟩ := hf
  obtain ⟨t', ht'⟩ := hg
  refine ⟨t ∪ t', fun P hP h hv hnot => ?_⟩
  rw [Finset.mem_union, not_or] at hnot
  obtain ⟨hfm, hfv, hRm, hfr⟩ := ht P hP h hv hnot.1
  obtain ⟨hgm, hgv, hSm, hgr⟩ := ht' P hP h hv hnot.2
  have hPrat := (An.mem_dom P hP).1
  have hrat := isRational_placeOfPoint' (k := IsLocalRing.ResidueField A) (rcl A (c⁻¹ * P.evalAt An.param))
  refine ⟨mul_mem hfm hgm, by rw [evalAt_mul_of_mem P hPrat hfm hgm]; exact mul_mem hfv hgv, mul_mem hRm hSm, ?_⟩
  rw [evalAt_mul_of_mem P hPrat hfm hgm, rcl_mul hfv hgv, hfr, hgr, evalAt_mul_of_mem _ hrat hRm hSm]

theorem Interp.mono {f : F} {R : RatFunc (IsLocalRing.ResidueField A)} (hf : Interp An c f R) (t' : Finset (IsLocalRing.ResidueField A)) :
    ∃ t : Finset (IsLocalRing.ResidueField A), t' ⊆ t ∧ ∀ P ∈ An.dom, ∀ h : c⁻¹ * P.evalAt An.param ∈ A,
    A.valuation (P.evalAt An.param) = A.valuation c → rcl A (c⁻¹ * P.evalAt An.param) ∉ t →
      f ∈ P.toValuationSubring ∧ P.evalAt f ∈ A ∧
      R ∈ (placeOfPoint (IsLocalRing.ResidueField A) (rcl A (c⁻¹ * P.evalAt An.param))).toValuationSubring ∧
      rcl A (P.evalAt f) = (placeOfPoint (IsLocalRing.ResidueField A) (rcl A (c⁻¹ * P.evalAt An.param))).evalAt R := by
  obtain ⟨t, ht⟩ := hf
  exact ⟨t ∪ t', Finset.subset_union_right, fun P hP h hv hnot =>
    ht P hP h hv (fun hm => hnot (Finset.mem_union_left _ hm))⟩

theorem exists_mem_dom_rcl_eq (An : Annulus A F) {c : L}
    (hc : A.valuation ((An.modulus : A) : L) < A.valuation c ∧ A.valuation c < 1)
    (x : IsLocalRing.ResidueField A) (hx : x ≠ 0) :
    ∃ P ∈ An.dom, ∃ h : c⁻¹ * P.evalAt An.param ∈ A, A.valuation (P.evalAt An.param) = A.valuation c ∧
      rcl A (c⁻¹ * P.evalAt An.param) = x := by
  obtain ⟨u, rfl⟩ := Ideal.Quotient.mk_surjective x
  have hu : IsUnit u := by
    rw [← IsLocalRing.notMem_maximalIdeal, ← IsLocalRing.residue_eq_zero_iff]; exact hx
  obtain ⟨P, hP, hev⟩ := exists_mem_dom_evalAt_eq An hc u hu
  have hc0 : c ≠ 0 := by
    intro h0; rw [h0, Valuation.map_zero] at hc; exact (not_lt_of_ge zero_le' hc.1).elim
  have hkey : c⁻¹ * P.evalAt An.param = u := by rw [hev, ← mul_assoc, inv_mul_cancel₀ hc0, one_mul]
  have hvu : A.valuation (u : L) = 1 := (A.valuation_eq_one_iff u).mp hu
  refine ⟨P, hP, by rw [hkey]; exact u.2, by rw [hev, Valuation.map_mul, hvu, mul_one], ?_⟩
  rw [rcl_eq (by rw [hkey]; exact u.2 : c⁻¹ * P.evalAt An.param ∈ A)]
  show IsLocalRing.residue A ⟨c⁻¹ * P.evalAt An.param, _⟩ = IsLocalRing.residue A u
  congr 1; exact Subtype.ext hkey

theorem Interp.unique [Infinite (IsLocalRing.ResidueField A)]
    (hc : A.valuation ((An.modulus : A) : L) < A.valuation c ∧ A.valuation c < 1)
    {f : F} {R R' : RatFunc (IsLocalRing.ResidueField A)} (hR : Interp An c f R) (hR' : Interp An c f R') : R = R' := by
  obtain ⟨t, ht⟩ := hR
  obtain ⟨t', ht'⟩ := hR'
  refine ratFunc_eq_of_evalAt_placeOfPoint_eq R R' (insert 0 (t ∪ t')) fun x hx => ?_
  rw [Finset.mem_insert, Finset.mem_union, not_or, not_or] at hx
  obtain ⟨P, hP, h, hv, hcl⟩ := exists_mem_dom_rcl_eq An hc x hx.1
  obtain ⟨-, -, -, h1⟩ := ht P hP h hv (by rw [hcl]; exact hx.2.1)
  obtain ⟨-, -, -, h2⟩ := ht' P hP h hv (by rw [hcl]; exact hx.2.2)
  rw [hcl] at h1 h2
  rw [← h1, ← h2]

end AlgebraicCurve.Annulus.CircleChart

p2m_open "AlgebraicCurve P2MW.S_AlgebraicCurve_Annulus_exists_ringHom_ratFunc_of_valuation_lt_of_exists_lt.AlgebraicCurve IsLocalRing AlgebraicCurve.RationalFunctionField"
open AlgebraicCurve.Annulus.CircleChart AlgebraicCurve.GaussReduction AlgebraicCurve.StandardAnnulus in

theorem solution
    {L : Type*} [Field L] {A : ValuationSubring L} {F : Type*} [Field F] [Algebra L F]
    (An : Annulus A F)
    (hfin : ∀ f : F, f ≠ 0 → {P : Place L F | P ∈ An.dom ∧ P.ord f ≠ 0}.Finite)
    (c : L) (hc : A.valuation ((An.modulus : A) : L) < A.valuation c ∧ A.valuation c < 1)
    (hinf : Infinite (IsLocalRing.ResidueField A))
    (hR : (∃ b : L, A.valuation c < A.valuation b ∧ A.valuation b < 1) ∧
      (∃ b : L, A.valuation ((An.modulus : A) : L) < A.valuation b ∧ A.valuation b < A.valuation c))
    (V : ValuationSubring F)
    (hV : ∀ f : F, f ∈ V ↔ ∃ t : Finset (IsLocalRing.ResidueField A), ∀ P ∈ An.dom, ∀ h : c⁻¹ * P.evalAt An.param ∈ A,
      A.valuation (P.evalAt An.param) = A.valuation c → IsLocalRing.residue A ⟨c⁻¹ * P.evalAt An.param, h⟩ ∉ t → f ∈ P.toValuationSubring ∧ P.evalAt f ∈ A)
    (hVA : ∀ x : L, algebraMap L F x ∈ V ↔ x ∈ A) :
    ∃ res : ↥V →+* RatFunc (IsLocalRing.ResidueField A),
      Function.Surjective res ∧
      RingHom.ker res = IsLocalRing.maximalIdeal ↥V ∧
      (∀ (a : A) (ha : algebraMap L F (a : L) ∈ V),
          res ⟨algebraMap L F (a : L), ha⟩ = algebraMap (IsLocalRing.ResidueField A) (RatFunc (IsLocalRing.ResidueField A)) (IsLocalRing.residue A a)) ∧
      (∀ hz : algebraMap L F c⁻¹ * An.param ∈ V, res ⟨algebraMap L F c⁻¹ * An.param, hz⟩ = (RatFunc.X : RatFunc (IsLocalRing.ResidueField A))) ∧
      (∀ f : F, f ≠ 0 → ∃ a : L, ∃ h : a • f ∈ V, res ⟨a • f, h⟩ ≠ 0) ∧
      (∀ P ∈ An.dom, ∀ h : c⁻¹ * P.evalAt An.param ∈ A, A.valuation (P.evalAt An.param) = A.valuation c → P.IsRational →
          ∀ (f : F) (hf : f ∈ V),
            (∀ w ∈ An.dom, ∀ h' : c⁻¹ * w.evalAt An.param ∈ A, A.valuation (w.evalAt An.param) = A.valuation c →
                IsLocalRing.residue A ⟨c⁻¹ * w.evalAt An.param, h'⟩ = IsLocalRing.residue A ⟨c⁻¹ * P.evalAt An.param, h⟩ → f ∈ w.toValuationSubring) →
            ∃ (hm : (res ⟨f, hf⟩ : RatFunc (IsLocalRing.ResidueField A)) ∈ (placeOfPoint (IsLocalRing.ResidueField A) (IsLocalRing.residue A ⟨c⁻¹ * P.evalAt An.param, h⟩)).toValuationSubring)
              (hv : P.evalAt f ∈ A),
              algebraMap (IsLocalRing.ResidueField A) (placeOfPoint (IsLocalRing.ResidueField A) (IsLocalRing.residue A ⟨c⁻¹ * P.evalAt An.param, h⟩)).ResidueField
                  (IsLocalRing.residue A ⟨P.evalAt f, hv⟩) =
                IsLocalRing.residue (placeOfPoint (IsLocalRing.ResidueField A) (IsLocalRing.residue A ⟨c⁻¹ * P.evalAt An.param, h⟩)).toValuationSubring ⟨res ⟨f, hf⟩, hm⟩) := by
  classical
  haveI := hinf
  set k := IsLocalRing.ResidueField A
  open AlgebraicCurve.Annulus.CircleChart AlgebraicCurve.GaussReduction AlgebraicCurve.StandardAnnulus in
  have hc0 : c ≠ 0 := by
    intro h0; rw [h0, Valuation.map_zero] at hc; exact (not_lt_of_ge zero_le' hc.1).elim
  have hvc : A.valuation c ≠ 0 := by rwa [ne_eq, Valuation.zero_iff]

  have hgenex : ∀ t : Finset k, ∃ P ∈ An.dom, ∃ h : c⁻¹ * P.evalAt An.param ∈ A,
      A.valuation (P.evalAt An.param) = A.valuation c ∧ rcl A (c⁻¹ * P.evalAt An.param) ∉ t := by
    intro t
    obtain ⟨x, hx⟩ := Infinite.exists_notMem_finset (insert (0 : k) t)
    rw [Finset.mem_insert, not_or] at hx
    obtain ⟨P, hP, h, hv, hcl⟩ := exists_mem_dom_rcl_eq An hc x hx.1
    exact ⟨P, hP, h, hv, by rw [hcl]; exact hx.2⟩

  have hInterp_of_data : ∀ f : F, f ∈ V → f ≠ 0 →
      ∀ (t₀ : Finset k) (Λ : L) (R₀ : RatFunc k), Λ ≠ 0 →
      (∀ P ∈ An.dom, ∀ h : c⁻¹ * P.evalAt An.param ∈ A, A.valuation (P.evalAt An.param) = A.valuation c →
        rcl A (c⁻¹ * P.evalAt An.param) ∉ t₀ →
          P.ord f = 0 ∧ A.valuation (Λ⁻¹ * P.evalAt f) = 1 ∧ Λ⁻¹ * P.evalAt f ∈ A ∧
          R₀ ∈ (placeOfPoint k (rcl A (c⁻¹ * P.evalAt An.param))).toValuationSubring ∧
            rcl A (Λ⁻¹ * P.evalAt f) = (placeOfPoint k (rcl A (c⁻¹ * P.evalAt An.param))).evalAt R₀) →
      Λ ∈ A ∧ Interp An c f (algebraMap k (RatFunc k) (rcl A Λ) * R₀) := by
    intro f hfV hf0 t₀ Λ R₀ hΛ0 hgen
    obtain ⟨t₁, ht₁⟩ := (hV f).mp hfV

    have hΛA : Λ ∈ A := by
      obtain ⟨P, hP, h, hv, hnot⟩ := hgenex (t₀ ∪ t₁)
      rw [Finset.mem_union, not_or] at hnot
      obtain ⟨-, hv1, hTA, -⟩ := hgen P hP h hv hnot.1
      obtain ⟨-, hfA⟩ := ht₁ P hP h hv (by rw [← rcl_eq h]; exact hnot.2)
      rw [← A.valuation_le_one_iff] at hfA ⊢
      have : A.valuation (P.evalAt f) = A.valuation Λ := by
        have h2 := hv1; rw [Valuation.map_mul, Valuation.map_inv] at h2
        have hvΛ : A.valuation Λ ≠ 0 := by rwa [ne_eq, Valuation.zero_iff]
        calc A.valuation (P.evalAt f) = A.valuation Λ * ((A.valuation Λ)⁻¹ * A.valuation (P.evalAt f)) := by
              rw [← mul_assoc, mul_inv_cancel₀ hvΛ, one_mul]
          _ = A.valuation Λ := by rw [h2, mul_one]
      rwa [this] at hfA
    refine ⟨hΛA, t₀ ∪ t₁, fun P hP h hv hnot => ?_⟩
    rw [Finset.mem_union, not_or] at hnot
    obtain ⟨hord, hv1, hTA, hR₀m, hval⟩ := hgen P hP h hv hnot.1
    obtain ⟨hfm, hfA⟩ := ht₁ P hP h hv (by rw [← rcl_eq h]; exact hnot.2)
    have hrat := isRational_placeOfPoint' (k := k) (rcl A (c⁻¹ * P.evalAt An.param))
    have hCm : algebraMap k (RatFunc k) (rcl A Λ) ∈ (placeOfPoint k (rcl A (c⁻¹ * P.evalAt An.param))).toValuationSubring :=
      Place.algebraMap_mem' _ _
    refine ⟨hfm, hfA, mul_mem hCm hR₀m, ?_⟩
    rw [evalAt_mul_of_mem _ hrat hCm hR₀m, evalAt_algebraMap_const _ hrat, ← hval, ← rcl_mul hΛA hTA,
      ← mul_assoc, mul_inv_cancel₀ hΛ0, one_mul]
  have hInterp : ∀ f : V, ∃ R : RatFunc k, Interp An c (f : F) R := by
    intro f
    by_cases hf0 : (f : F) = 0
    · exact ⟨0, by rw [hf0]; exact interp_zero An c⟩
    obtain ⟨t₀, Λ, R₀, hΛ0, -, hgen, -⟩ := exists_interpolant' An hfin c hc hinf hR (f : F) hf0
    exact ⟨_, (hInterp_of_data f f.2 hf0 t₀ Λ R₀ hΛ0 hgen).2⟩
  choose res hres using hInterp
  have huniq : ∀ (f : V) (R : RatFunc k), Interp An c (f : F) R → res f = R :=
    fun f R hR' => Interp.unique hc (hres f) hR'

  let resHom : V →+* RatFunc k :=
    { toFun := res
      map_one' := huniq 1 1 (interp_one An c)
      map_mul' := fun f g => huniq (f * g) _ ((hres f).mul (hres g))
      map_zero' := huniq 0 0 (interp_zero An c)
      map_add' := fun f g => huniq (f + g) _ ((hres f).add (hres g)) }
  have hresHom : ∀ f : V, resHom f = res f := fun _ => rfl

  have hconstV : ∀ (a : L) (ha : a ∈ A) (haV : algebraMap L F a ∈ V),
      res ⟨algebraMap L F a, haV⟩ = algebraMap k (RatFunc k) (rcl A a) :=
    fun a ha haV => huniq ⟨_, haV⟩ _ (interp_const An c ha)
  have hzV : algebraMap L F c⁻¹ * An.param ∈ V := by
    rw [hV]
    refine ⟨∅, fun P hP h hv _ => ?_⟩
    obtain ⟨hPrat, hzP, -⟩ := An.mem_dom P hP
    refine ⟨mul_mem (P.algebraMap_mem' _) hzP, ?_⟩
    rw [evalAt_mul_of_mem P hPrat (P.algebraMap_mem' _) hzP, evalAt_algebraMap_const P hPrat]; exact h
  have hXV : ∀ hz : algebraMap L F c⁻¹ * An.param ∈ V, res ⟨algebraMap L F c⁻¹ * An.param, hz⟩ = RatFunc.X :=
    fun hz => huniq ⟨_, hz⟩ _ (interp_X An c)

  have hunit_of_val : ∀ f : F, f ∈ V → f ≠ 0 → ∀ (t₀ : Finset k) (Λ : L), Λ ≠ 0 → A.valuation Λ = 1 →
      (∀ P ∈ An.dom, ∀ h : c⁻¹ * P.evalAt An.param ∈ A, A.valuation (P.evalAt An.param) = A.valuation c →
        rcl A (c⁻¹ * P.evalAt An.param) ∉ t₀ → P.ord f = 0 ∧ A.valuation (Λ⁻¹ * P.evalAt f) = 1) → f⁻¹ ∈ V := by
    intro f hfV hf0 t₀ Λ hΛ0 hvΛ hgen
    rw [hV]
    refine ⟨t₀, fun P hP h hv hnot => ?_⟩
    obtain ⟨hord, hv1⟩ := hgen P hP h hv (by rw [rcl_eq h]; exact hnot)
    have hPrat := (An.mem_dom P hP).1
    refine ⟨mem_of_ord_nonneg_gen P (inv_ne_zero hf0) (by rw [P.ord_inv]; omega), ?_⟩
    rw [evalAt_inv_of_ord_eq_zero P hPrat hf0 hord, ← A.valuation_le_one_iff, Valuation.map_inv]
    rw [Valuation.map_mul, Valuation.map_inv, hvΛ, inv_one, one_mul] at hv1
    rw [hv1, inv_one]
  have hker : RingHom.ker resHom = IsLocalRing.maximalIdeal V := by
    ext f
    rw [RingHom.mem_ker, hresHom, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    constructor
    ·
      intro h0 hU
      have hI : Interp An c (f : F) 0 := by rw [← h0]; exact hres f
      obtain ⟨t, ht⟩ := hI
      have hf0 : (f : F) ≠ 0 := by
        intro hz; exact not_isUnit_zero (by rwa [show f = 0 from Subtype.ext hz] at hU)

      obtain ⟨u, hu⟩ := hU
      have hinvV : (f : F)⁻¹ ∈ V := by
        have h1 : ((u⁻¹ : Vˣ) : V) * f = 1 := by rw [← hu]; exact u.inv_mul
        have h2 : (((u⁻¹ : Vˣ) : V) : F) * (f : F) = 1 := by
          have := congrArg (fun x : V => (x : F)) h1; simpa using this
        have h3 : (((u⁻¹ : Vˣ) : V) : F) = (f : F)⁻¹ := eq_inv_of_mul_eq_one_left h2
        rw [← h3]; exact ((u⁻¹ : Vˣ) : V).2
      obtain ⟨t', ht'⟩ := (hV _).mp hinvV
      obtain ⟨P, hP, h, hv, hnot⟩ := hgenex (t ∪ t')
      rw [Finset.mem_union, not_or] at hnot
      obtain ⟨hfm, hfA, -, hfr⟩ := ht P hP h hv hnot.1
      obtain ⟨him, hiA⟩ := ht' P hP h hv (by rw [← rcl_eq h]; exact hnot.2)
      have hPrat := (An.mem_dom P hP).1
      have hrat := isRational_placeOfPoint' (k := k) (rcl A (c⁻¹ * P.evalAt An.param))
      rw [evalAt_zero' _ hrat] at hfr

      have hlt : A.valuation (P.evalAt (f : F)) < 1 := by
        rw [rcl_eq hfA, IsLocalRing.residue_eq_zero_iff, ValuationSubring.valuation_lt_one_iff] at hfr; exact hfr
      have hone : P.evalAt (f : F) * P.evalAt ((f : F)⁻¹) = 1 := by
        rw [← evalAt_mul_of_mem P hPrat hfm him, mul_inv_cancel₀ hf0, P.evalAt_one]
      have hv1 : A.valuation (P.evalAt (f : F)) * A.valuation (P.evalAt (f : F)⁻¹) = 1 := by
        rw [← Valuation.map_mul, hone, Valuation.map_one]
      have hle : A.valuation (P.evalAt (f : F)⁻¹) ≤ 1 := (A.valuation_le_one_iff _).mpr hiA
      have : A.valuation (P.evalAt (f : F)) * A.valuation (P.evalAt (f : F)⁻¹) < 1 :=
        calc A.valuation (P.evalAt (f : F)) * A.valuation (P.evalAt (f : F)⁻¹)
            ≤ A.valuation (P.evalAt (f : F)) * 1 := mul_le_mul_right hle _
          _ = A.valuation (P.evalAt (f : F)) := mul_one _
          _ < 1 := hlt
      rw [hv1] at this
      exact lt_irrefl _ this
    ·
      intro hnu
      by_cases hf0 : (f : F) = 0
      · have : f = 0 := Subtype.ext hf0
        rw [this]; exact huniq 0 0 (interp_zero An c)
      obtain ⟨t₀, Λ, R₀, hΛ0, -, hgen, -⟩ := exists_interpolant' An hfin c hc hinf hR (f : F) hf0
      obtain ⟨hΛA, hI⟩ := hInterp_of_data f f.2 hf0 t₀ Λ R₀ hΛ0 hgen
      rw [huniq f _ hI]

      suffices hr : rcl A Λ = 0 by rw [hr, map_zero, zero_mul]
      by_contra hr
      have hvΛ : A.valuation Λ = 1 := valuation_eq_one_of_rcl_ne_zero hΛA hr
      have hinvV := hunit_of_val (f : F) f.2 hf0 t₀ Λ hΛ0 hvΛ (fun P hP h hv hnot => ⟨(hgen P hP h hv hnot).1, (hgen P hP h hv hnot).2.1⟩)
      apply hnu
      refine ⟨⟨f, ⟨(f : F)⁻¹, hinvV⟩, Subtype.ext (mul_inv_cancel₀ hf0), Subtype.ext (inv_mul_cancel₀ hf0)⟩, rfl⟩

  have hpoly : ∀ p : Polynomial k, ∃ g : V, res g = algebraMap (Polynomial k) (RatFunc k) p := by
    intro p
    induction p using Polynomial.induction_on' with
    | add p q hp hq =>
      obtain ⟨gp, hgp⟩ := hp
      obtain ⟨gq, hgq⟩ := hq
      exact ⟨gp + gq, by rw [← hresHom, map_add, hresHom, hresHom, hgp, hgq, map_add]⟩
    | monomial n a =>
      obtain ⟨â, hâ⟩ := Ideal.Quotient.mk_surjective a
      have hâV : algebraMap L F (â : L) ∈ V := (hVA _).mpr â.2
      refine ⟨⟨algebraMap L F (â : L), hâV⟩ * ⟨algebraMap L F c⁻¹ * An.param, hzV⟩ ^ n, ?_⟩
      rw [← hresHom, map_mul, map_pow, hresHom, hresHom, hconstV _ â.2 hâV, hXV hzV, ← Polynomial.C_mul_X_pow_eq_monomial,
        map_mul, map_pow, RatFunc.algebraMap_C, RatFunc.algebraMap_X, RatFunc.algebraMap_eq_C]
      congr 2
      rw [rcl_eq â.2]
      show IsLocalRing.residue A ⟨(â : L), â.2⟩ = a
      rw [← hâ]; rfl
  have hsurj : Function.Surjective resHom := by
    intro R
    obtain ⟨gp, hgp⟩ := hpoly R.num
    obtain ⟨gq, hgq⟩ := hpoly R.denom
    have hq0 : res gq ≠ 0 := by
      rw [hgq, ne_eq, map_eq_zero_iff _ (IsFractionRing.injective (Polynomial k) (RatFunc k))]; exact RatFunc.denom_ne_zero R
    have hgqU : IsUnit gq := by
      by_contra hnu
      have : gq ∈ RingHom.ker resHom := by
        rw [hker, IsLocalRing.mem_maximalIdeal]; exact hnu
      exact hq0 (by rwa [RingHom.mem_ker, hresHom] at this)
    obtain ⟨uq, huq⟩ := hgqU
    refine ⟨gp * ↑uq⁻¹, ?_⟩
    have h1 : resHom ↑uq⁻¹ = (resHom gq)⁻¹ := by rw [← huq, map_units_inv]
    rw [map_mul, h1, hresHom, hresHom, hgp, hgq]
    conv_rhs => rw [← RatFunc.num_div_denom R, div_eq_mul_inv]

  have hsmul : ∀ f : F, f ≠ 0 → ∃ a : L, ∃ h : a • f ∈ V, resHom ⟨a • f, h⟩ ≠ 0 := by
    intro f hf0
    obtain ⟨t₀, Λ, R₀, hΛ0, hR₀0, hgen, -⟩ := exists_interpolant' An hfin c hc hinf hR f hf0
    have hmemV : Λ⁻¹ • f ∈ V := by
      rw [hV]
      refine ⟨t₀, fun P hP h hv hnot => ?_⟩
      obtain ⟨hord, hv1, hTA, -⟩ := hgen P hP h hv (by rw [rcl_eq h]; exact hnot)
      have hPrat := (An.mem_dom P hP).1
      have hfm : f ∈ P.toValuationSubring := mem_of_ord_nonneg_gen P hf0 hord.ge
      rw [Algebra.smul_def]
      refine ⟨mul_mem (P.algebraMap_mem' _) hfm, ?_⟩
      rw [evalAt_mul_of_mem P hPrat (P.algebraMap_mem' _) hfm, evalAt_algebraMap_const P hPrat]; exact hTA
    refine ⟨Λ⁻¹, hmemV, ?_⟩
    have hI : Interp An c (Λ⁻¹ • f) R₀ := by
      refine ⟨t₀, fun P hP h hv hnot => ?_⟩
      obtain ⟨hord, hv1, hTA, hR₀m, hval⟩ := hgen P hP h hv hnot
      have hPrat := (An.mem_dom P hP).1
      have hfm : f ∈ P.toValuationSubring := mem_of_ord_nonneg_gen P hf0 hord.ge
      have hev : P.evalAt (Λ⁻¹ • f) = Λ⁻¹ * P.evalAt f := by
        rw [Algebra.smul_def, evalAt_mul_of_mem P hPrat (P.algebraMap_mem' _) hfm, evalAt_algebraMap_const P hPrat]
      rw [Algebra.smul_def] at hev ⊢
      exact ⟨mul_mem (P.algebraMap_mem' _) hfm, by rw [hev]; exact hTA, hR₀m, by rw [hev]; exact hval⟩
    rw [hresHom, huniq ⟨_, hmemV⟩ R₀ hI]; exact hR₀0

  have hpt : ∀ P ∈ An.dom, ∀ h : c⁻¹ * P.evalAt An.param ∈ A, A.valuation (P.evalAt An.param) = A.valuation c →
      P.IsRational → ∀ (f : F) (hf : f ∈ V),
        (∀ w ∈ An.dom, ∀ h' : c⁻¹ * w.evalAt An.param ∈ A, A.valuation (w.evalAt An.param) = A.valuation c →
            IsLocalRing.residue A ⟨c⁻¹ * w.evalAt An.param, h'⟩ = IsLocalRing.residue A ⟨c⁻¹ * P.evalAt An.param, h⟩ →
              f ∈ w.toValuationSubring) →
        ∃ (hm : (resHom ⟨f, hf⟩ : RatFunc k) ∈ (placeOfPoint k (IsLocalRing.residue A ⟨c⁻¹ * P.evalAt An.param, h⟩)).toValuationSubring)
          (hv : P.evalAt f ∈ A),
          algebraMap k (placeOfPoint k (IsLocalRing.residue A ⟨c⁻¹ * P.evalAt An.param, h⟩)).ResidueField
              (IsLocalRing.residue A ⟨P.evalAt f, hv⟩) =
            IsLocalRing.residue (placeOfPoint k (IsLocalRing.residue A ⟨c⁻¹ * P.evalAt An.param, h⟩)).toValuationSubring
              ⟨resHom ⟨f, hf⟩, hm⟩ := by
    intro P hP h hv hPrat f hfV hreg
    have hcls : IsLocalRing.residue A ⟨c⁻¹ * P.evalAt An.param, h⟩ = rcl A (c⁻¹ * P.evalAt An.param) := (rcl_eq h).symm
    have hfP : f ∈ P.toValuationSubring := hreg P hP h hv rfl

    have hmain : P.evalAt f ∈ A ∧ (res ⟨f, hfV⟩) ∈ (placeOfPoint k (rcl A (c⁻¹ * P.evalAt An.param))).toValuationSubring ∧
        rcl A (P.evalAt f) = (placeOfPoint k (rcl A (c⁻¹ * P.evalAt An.param))).evalAt (res ⟨f, hfV⟩) := by
      have hrat := isRational_placeOfPoint' (k := k) (rcl A (c⁻¹ * P.evalAt An.param))
      by_cases hf0 : f = 0
      · subst hf0
        have : res ⟨0, hfV⟩ = 0 := huniq ⟨0, hfV⟩ 0 (interp_zero An c)
        rw [this, evalAt_zero' P hPrat, rcl_zero, evalAt_zero' _ hrat]
        exact ⟨A.zero_mem, zero_mem _, rfl⟩
      obtain ⟨t₀, Λ, R₀, hΛ0, -, hgen, hclass⟩ := exists_interpolant' An hfin c hc hinf hR f hf0
      obtain ⟨hΛA, hI⟩ := hInterp_of_data f hfV hf0 t₀ Λ R₀ hΛ0 hgen
      have hresf : res ⟨f, hfV⟩ = algebraMap k (RatFunc k) (rcl A Λ) * R₀ := huniq ⟨f, hfV⟩ _ hI
      obtain ⟨hTA, hR₀m, hval⟩ := hclass P hP h hv hfP (fun w hw h' hvw hcl =>
        hreg w hw h' hvw (by rw [rcl_eq h', rcl_eq h] at hcl; exact hcl))
      have hfA : P.evalAt f ∈ A := by
        have : P.evalAt f = Λ * (Λ⁻¹ * P.evalAt f) := by rw [← mul_assoc, mul_inv_cancel₀ hΛ0, one_mul]
        rw [this]; exact mul_mem hΛA hTA
      have hCm : algebraMap k (RatFunc k) (rcl A Λ) ∈ (placeOfPoint k (rcl A (c⁻¹ * P.evalAt An.param))).toValuationSubring :=
        Place.algebraMap_mem' _ _
      refine ⟨hfA, by rw [hresf]; exact mul_mem hCm hR₀m, ?_⟩
      rw [hresf, evalAt_mul_of_mem _ hrat hCm hR₀m, evalAt_algebraMap_const _ hrat, ← hval, ← rcl_mul hΛA hTA,
        ← mul_assoc, mul_inv_cancel₀ hΛ0, one_mul]
    obtain ⟨hfA, hm, hval⟩ := hmain
    have hm' : (resHom ⟨f, hfV⟩ : RatFunc k) ∈ (placeOfPoint k (IsLocalRing.residue A ⟨c⁻¹ * P.evalAt An.param, h⟩)).toValuationSubring := by
      rw [hcls]; exact hm
    refine ⟨hm', hfA, ?_⟩

    have hrat := isRational_placeOfPoint' (k := k) (IsLocalRing.residue A ⟨c⁻¹ * P.evalAt An.param, h⟩)
    rw [← Place.algebraMap_evalAt _ hrat hm']
    congr 1
    rw [← rcl_eq hfA, hval, hresHom]
    congr 2 <;> rw [hcls]
  refine ⟨resHom, hsurj, hker, fun a ha => ?_, hXV, hsmul, hpt⟩
  rw [hresHom, hconstV (a : L) a.2 ha, rcl_eq a.2]

end S_AlgebraicCurve_Annulus_exists_ringHom_ratFunc_of_valuation_lt_of_exists_lt
end P2MW
export P2MW.S_AlgebraicCurve_Annulus_exists_ringHom_ratFunc_of_valuation_lt_of_exists_lt (solution)

-- Prove2me | solution 1 for Apery.outer_entry
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-10-12T21:55:39.402247+00:00
-- url     : https://prove2.me/submissions/8851553f-0f7a-4d4d-9e83-dd92ff71abe0

/-
# The outer-range entry bound (source `Apery/Arith/OuterEntryMain.lean`)

For a prime $p \\ge 7$ with $40n < 3p$, $2\\cdot 40n < p^2$ and $3n < p$, and any two outer rows
$(c_s, i_s)$, $(c_t, i_t)$, the entry
$\\mu_X(tpol\\,entryO) - \\mu_{\\ge}(tpol\\,entryO / D_{40n})$ has Gauss valuation at least
$\\mathrm{wO}(c_s, i_s) + \\mathrm{wO}(c_t, i_t)$. The file ports
`Apery/Arith/OuterEntryMain.lean` (the decomposition $\\mu_X = \\mu_{\\ge} + \\mu_{<}$, the pole sums,
the residue bounds `VG_res_entry` and the pole case analysis `pole_case_a`/`pole_case_b`/
`pole_case_zero`), together with the residue lemmas of `Apery/Arith/OuterEntry.lean`, the
class-count and zero-class bounds of `Apery/Arith/OuterEntries.lean`, the valuation toolkit of
`Apery/Arith/{DirectBound,PoleVal,IntPoly,MomentVal,DirectPoly}.lean`, `Apery/Degree.lean` and the
class facts of `Apery/Arith/{ClassCount,ClassFrame}.lean`, importing the proved platform theorem
`Apery.pair_GV`, faithful to mo271/Zeta5 @ 7fe736760f4b96bfdb4334b68e3b3124ecbe10b0.
-/

import Mathlib
import Definitions.Def_Zeta5_SourceConstruction
import Definitions.Def_Zeta5_SourceArith
import Definitions.Def_Zeta5_SourceGrowthTables
import Definitions.Def_Zeta5_SourceInner
import Definitions.Def_Zeta5_SourceOuter
import Definitions.Def_Zeta5_SourcePoleFun
import Definitions.Def_Zeta5_SourcePullback
import Definitions.Def_Zeta5_SourceValToolkit
import Theorems.Thm_Apery_pair_GV

set_option autoImplicit false

section Port0

set_option autoImplicit false

open Finset Polynomial Matrix

namespace Apery

variable {p : ℕ} [hp : Fact p.Prime] {m : ℕ}

lemma eval_derivative_D {K j : ℕ} (hj : j ∈ Icc 1 K) :
    (derivative (D K)).eval (-(j : ℚ) ^ 2) = ∏ i ∈ (Icc 1 K).erase j, ((i : ℚ) ^ 2 - (j : ℚ) ^ 2) := by
  rw [D, derivative_prod_finset, eval_finsetSum, Finset.sum_eq_single j]
  · simp only [derivative_add, derivative_X, derivative_C, add_zero, eval_mul, eval_one, mul_one,
      eval_prod, eval_add, eval_X, eval_C]
    exact Finset.prod_congr rfl fun i _ => by ring
  · intro b _ hb
    rw [eval_mul, eval_prod]
    exact mul_eq_zero_of_left (Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨hb.symm, hj⟩) (by simp)) _
  · intro h; exact absurd hj h

lemma eval_derivative_D_ne_zero {K j : ℕ} (hj : j ∈ Icc 1 K) :
    (derivative (D K)).eval (-(j : ℚ) ^ 2) ≠ 0 := by
  rw [eval_derivative_D hj]
  refine Finset.prod_ne_zero_iff.mpr fun i hi => ?_
  have hij : i ≠ j := (Finset.mem_erase.mp hi).1
  have : (i : ℚ) ≠ j := by exact_mod_cast hij
  have h0i : (0 : ℚ) ≤ i := by positivity
  have h0j : (0 : ℚ) ≤ j := by positivity
  intro h
  have hfac : ((i : ℚ) - j) * ((i : ℚ) + j) = 0 := by linear_combination h
  rcases mul_eq_zero.mp hfac with h' | h'
  · exact this (by linarith)
  · have hj1 : (1 : ℚ) ≤ j := by exact_mod_cast (Finset.mem_Icc.mp hj).1
    linarith

lemma zmod_eq_iff_dvd {a b : ℤ} : (a : ZMod p) = b ↔ (p : ℤ) ∣ a - b := by
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]; push_cast; exact sub_eq_zero.symm

lemma VG_int_one {z : ℤ} (h : (p : ℤ) ∣ z) : VG p (z : ℚ) 1 := by
  by_cases hz : z = 0
  · left; simp [hz]
  right
  rw [padicValRat.of_int]
  have := (padicValInt_dvd_iff (p := p) 1 z).mp (by simpa using h)
  rcases this with h | h
  · exact absurd h hz
  · exact_mod_cast h

lemma padicValRat_int_eq_zero {z : ℤ} (h : ¬ (p : ℤ) ∣ z) : padicValRat p (z : ℚ) = 0 := by
  rw [padicValRat.of_int]
  have hz : z ≠ 0 := fun h' => h (h' ▸ dvd_zero _)
  by_contra hne
  have h1 : 1 ≤ padicValInt p z := Nat.one_le_iff_ne_zero.mpr (by exact_mod_cast hne)
  exact h (by simpa using (padicValInt_dvd_iff (p := p) 1 z).mpr (Or.inr h1))

lemma padicValRat_int_le_one {z : ℤ} (h2 : ¬ (p : ℤ) ^ 2 ∣ z) : padicValRat p (z : ℚ) ≤ 1 := by
  rw [padicValRat.of_int]
  by_contra hne
  rw [not_le] at hne
  have : 2 ≤ padicValInt p z := by exact_mod_cast hne
  have hz : z ≠ 0 := by rintro rfl; simp at hne
  exact h2 ((padicValInt_dvd_iff (p := p) 2 z).mpr (Or.inr this))

lemma padicValRat_finset_prod {ι : Type*} (s : Finset ι) (f : ι → ℚ) (hf : ∀ i ∈ s, f i ≠ 0) :
    padicValRat p (∏ i ∈ s, f i) = ∑ i ∈ s, padicValRat p (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha, padicValRat.mul (hf a (mem_insert_self _ _))
      (Finset.prod_ne_zero_iff.mpr fun i hi => hf i (mem_insert_of_mem hi)),
      ih fun i hi => hf i (mem_insert_of_mem hi)]

lemma VG.multiset_prod (s : Multiset ℚ) (b : ℚ → ℚ) (h : ∀ q ∈ s, VG p q (b q)) :
    VG p s.prod (s.map b).sum := by
  induction s using Multiset.induction_on with
  | empty => right; simp
  | cons a s ih =>
    rw [Multiset.prod_cons, Multiset.map_cons, Multiset.sum_cons]
    exact (h a (Multiset.mem_cons_self _ _)).mul (ih fun q hq => h q (Multiset.mem_cons_of_mem hq))

lemma card_filter_replicate (k : ℕ) (v : ℤ) (P : ℤ → Prop) [DecidablePred P] :
    ((Multiset.replicate k v).filter P).card = if P v then k else 0 := by
  split_ifs with h
  · rw [Multiset.filter_eq_self.mpr fun a ha => by rw [Multiset.eq_of_mem_replicate ha]; exact h]
    simp
  · rw [Multiset.filter_eq_nil.mpr fun a ha => by rw [Multiset.eq_of_mem_replicate ha]; exact h]
    simp

lemma card_filter_sum_replicate {α : Type*} (s : Finset α) (L : α → ℕ) (v : α → ℤ) (P : ℤ → Prop)
    [DecidablePred P] :
    ((∑ c ∈ s, Multiset.replicate (L c) (v c)).filter P).card = ∑ c ∈ s, if P (v c) then L c else 0 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Multiset.filter_add, Multiset.card_add, ih, Finset.sum_insert ha,
      card_filter_replicate]

lemma tpol_add (M M' : Multiset ℤ) : tpol (M + M') = tpol M * tpol M' := by
  simp [tpol, Multiset.map_add, Multiset.prod_add]

lemma tpolZ_map_Q (M : Multiset ℤ) : (tpolZ M).map (Int.castRingHom ℚ) = tpol M := by
  simp [tpolZ, tpol, Polynomial.map_multiset_prod, Multiset.map_map, Function.comp]



/-!
# Outer range: general residue and pole-value lemmas

For a numerator `tpol M = ∏_{γ ∈ M} (t + γ²)`:
* `res_tpol` : `res K (tpol M) j = ∏_γ (γ² - j²) / ∏_{i ≠ j} (i² - j²)`;
* valuation bounds for residues and pole values;
* `PV_congr` : `poleValue (p - c) ≡ poleValue c (mod p)`.
-/

open Finset Polynomial


variable {p : ℕ} [hp : Fact p.Prime]

lemma sq_injective {p m : ℕ} [hp : Fact p.Prime] (hm : 2 * m + 1 = p) :
    Function.Injective fun c : Fin (m + 1) => -(((c : ℕ) : ZMod p) ^ 2) := by
  intro c c' h
  simp only [neg_inj] at h
  have h2 : (p : ℤ) ∣ ((c : ℕ) - (c' : ℕ) : ℤ) * ((c : ℕ) + (c' : ℕ) : ℤ) := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]; push_cast
    linear_combination h
  have hc := c.isLt; have hc' := c'.isLt
  rcases (Int.Prime.dvd_mul' hp.out h2) with h3 | h3
  · have := Int.eq_zero_of_abs_lt_dvd h3 (by rw [abs_lt]; constructor <;> push_cast <;> omega)
    exact Fin.ext (by omega)
  · have := Int.eq_zero_of_abs_lt_dvd h3 (by rw [abs_lt]; constructor <;> push_cast <;> omega)
    exact Fin.ext (by omega)

lemma ccls_spec (hm : 2 * m + 1 = p) (c : ZMod p) :
    (((ccls hm c : ℕ) : ℤ) : ZMod p) = c ∨ (((ccls hm c : ℕ) : ℤ) : ZMod p) = -c := by
  have hp0 : NeZero p := ⟨hp.out.ne_zero⟩
  unfold ccls
  split_ifs with h
  · left; simp
  · right
    have hv := c.val_lt
    simp only [Fin.val_mk]
    rw [show ((p - c.val : ℕ) : ℤ) = (p : ℤ) - (c.val : ℤ) by push_cast [Nat.cast_sub hv.le]; ring]
    push_cast
    rw [ZMod.natCast_self, zero_sub, ZMod.natCast_zmod_val]

lemma ccls_unique (hm : 2 * m + 1 = p) (c : ZMod p) (a : Fin (m + 1))
    (h : (((a : ℕ) : ℤ) : ZMod p) = c ∨ (((a : ℕ) : ℤ) : ZMod p) = -c) : a = ccls hm c := by
  have h1 := ccls_spec hm c
  apply sq_injective hm
  simp only
  have e : ∀ x : ZMod p, x = c ∨ x = -c → x ^ 2 = c ^ 2 := by
    rintro x (rfl | rfl) <;> ring
  have ha := e _ h
  have hc := e _ h1
  push_cast at ha hc
  rw [ha, hc]

lemma sq_eq_iff_ccls (hm : 2 * m + 1 = p) (x y : ZMod p) :
    x ^ 2 = y ^ 2 ↔ ccls hm x = ccls hm y := by
  constructor
  · intro h
    have h2 : (x - y) * (x + y) = 0 := by linear_combination h
    rcases mul_eq_zero.mp h2 with h3 | h3
    · rw [sub_eq_zero.mp h3]
    · have : x = -y := by linear_combination h3
      rw [this]
      exact (ccls_unique hm (-y) (ccls hm y) (by
        rcases ccls_spec hm y with h4 | h4
        · right; rw [h4, neg_neg]
        · left; rw [h4])).symm
  · intro h
    have e : ∀ z : ZMod p, z ^ 2 = ((((ccls hm z : ℕ) : ℤ) : ZMod p)) ^ 2 := by
      intro z
      rcases ccls_spec hm z with h4 | h4 <;> rw [h4]; ring
    rw [e x, e y, h]

lemma ccls_self (hm : 2 * m + 1 = p) (c : Fin (m + 1)) : ccls hm ((((c : ℕ) : ℤ) : ZMod p)) = c :=
  (ccls_unique hm _ c (Or.inl rfl)).symm

lemma sq_jc (hm : 2 * m + 1 = p) (j : ℕ) : (((j : ℤ) : ZMod p)) ^ 2 = ((((jc hm j : ℕ) : ℤ) : ZMod p)) ^ 2 := by
  rw [sq_eq_iff_ccls hm, ccls_self]; rfl

lemma GV.pow {F : ℚ[X]} {r : ℚ} (h : GV p F r) (n : ℕ) : GV p (F ^ n) (n * r) := by
  induction n with
  | zero => simpa using GV.C (p := p) (VG.one (p := p))
  | succ n ih => rw [pow_succ]; convert ih.mul h using 1; push_cast; ring

lemma GV.comp {F G : ℚ[X]} (hF : GV p F 0) (hG : GV p G 0) : GV p (F.comp G) 0 := by
  rw [comp_eq_sum_left, Polynomial.sum]
  refine GV.sum _ fun n _ => ?_
  have := GV.C_mul (hF n) (hG.pow n)
  simpa using this

lemma VG.eval {F : ℚ[X]} {z : ℚ} (hF : GV p F 0) (hz : VG p z 0) : VG p (F.eval z) 0 := by
  rw [eval_eq_sum, Polynomial.sum]
  refine VG.sum _ fun n _ => ?_
  have := (hF n).mul (hz.pow n)
  simpa using this

lemma VG.eval_zero {F : ℚ[X]} {r : ℚ} (hF : GV p F r) : VG p (F.eval 0) r := by
  rw [← coeff_zero_eq_eval_zero]; exact hF 0

lemma GV.divByMonic_X_sub_C {F : ℚ[X]} {a : ℚ} (hF : GV p F 0) (ha : VG p a 0) :
    GV p (F /ₘ (Polynomial.X - Polynomial.C a)) 0 := fun n => by
  rw [coeff_divByMonic_X_sub_C]
  refine VG.sum _ fun i _ => ?_
  have := (ha.pow (i - (n + 1))).mul (hF i)
  simpa using this

lemma VG_inv_nat_le {u : ℕ} (hu : u ≠ 0) {e : ℕ} (he : padicValNat p u ≤ e) :
    VG p ((u : ℚ)⁻¹) (-(e : ℚ)) := by
  refine VG.inv (by exact_mod_cast hu) ?_
  rw [padicValRat.of_nat]; exact_mod_cast he

lemma padicValNat_lt_p {u : ℕ} (hu : 1 ≤ u) (hup : u < p) : padicValNat p u = 0 :=
  padicValNat.eq_zero_of_not_dvd fun h => absurd (Nat.le_of_dvd (by omega) h) (by omega)

lemma VG_inv_2j (hp3 : 3 ≤ p) {j e : ℕ} (hj : 1 ≤ j) (he : padicValNat p j ≤ e) :
    VG p (1 / (2 * (j : ℚ))) (-(e : ℚ)) := by
  rw [one_div, show (2 * (j : ℚ)) = ((2 * j : ℕ) : ℚ) by push_cast; ring]
  refine VG_inv_nat_le (by omega) ?_
  have := Fact.mk Nat.prime_two
  rw [padicValNat.mul (by norm_num) (by omega), padicValNat_primes (p := p) (q := 2) (by omega)]
  omega

lemma VG_int_dvd_one {z : ℤ} (h : (p : ℤ) ∣ z) : VG p (z : ℚ) 1 := VG_int_one h

lemma VG_pair (hp3 : 3 ≤ p) {u : ℕ} (hu : 1 ≤ u) (hup : u < p) :
    VG p (1 / ((p : ℚ) - u) ^ 5 + 1 / (u : ℚ) ^ 5) 1 := by
  have hpu : ((p : ℚ) - u) = ((p - u : ℕ) : ℚ) := by push_cast [Nat.cast_sub hup.le]; ring
  have hne1 : ((p - u : ℕ) : ℚ) ≠ 0 := by exact_mod_cast (by omega : p - u ≠ 0)
  have hne2 : (u : ℚ) ≠ 0 := by exact_mod_cast (by omega : u ≠ 0)
  rw [hpu, div_add_div _ _ (pow_ne_zero _ hne1) (pow_ne_zero _ hne2), div_eq_mul_inv]
  have hnum : VG p (1 * (u : ℚ) ^ 5 + ((p - u : ℕ) : ℚ) ^ 5 * 1) 1 := by
    have := VG_int_one (p := p) (z := (u : ℤ) ^ 5 + ((p : ℤ) - u) ^ 5) (by
      rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]; push_cast
      rw [ZMod.natCast_self]; ring)
    convert this using 1
    push_cast [Nat.cast_sub hup.le]; ring
  have hden : VG p (((p - u : ℕ) : ℚ) ^ 5 * (u : ℚ) ^ 5)⁻¹ 0 := by
    rw [show ((p - u : ℕ) : ℚ) ^ 5 * (u : ℚ) ^ 5 = (((p - u) ^ 5 * u ^ 5 : ℕ) : ℚ) by push_cast; ring]
    have hA : (p - u) ^ 5 ≠ 0 := pow_ne_zero _ (by omega)
    have hB : u ^ 5 ≠ 0 := pow_ne_zero _ (by omega)
    refine (VG_inv_nat_le (e := 0) (mul_ne_zero hA hB) ?_).mono (by norm_num)
    rw [padicValNat.mul hA hB, padicValNat.pow (p := p) _ 5,
      padicValNat.pow (p := p) _ 5, padicValNat_lt_p (by omega) (by omega),
      padicValNat_lt_p hu hup]
  simpa using hnum.mul hden

lemma VG_H5_pm1 (hp3 : 3 ≤ p) : VG p (H5 (p - 1)) 1 := by
  have h2 : 2 * H5 (p - 1) = ∑ u ∈ Icc 1 (p - 1), (1 / ((p : ℚ) - u) ^ 5 + 1 / (u : ℚ) ^ 5) := by
    unfold H5
    rw [Finset.sum_add_distrib, two_mul]
    congr 1
    apply Finset.sum_nbij' (fun u => p - u) (fun u => p - u)
    · intro u hu; simp only [Finset.coe_Icc, Set.mem_Icc, Finset.mem_coe, Finset.mem_Icc] at hu ⊢
      omega
    · intro u hu; simp only [Finset.coe_Icc, Set.mem_Icc, Finset.mem_coe, Finset.mem_Icc] at hu ⊢
      omega
    · intro u hu; simp only [Finset.coe_Icc, Set.mem_Icc, Finset.mem_coe, Finset.mem_Icc] at hu
      omega
    · intro u hu; simp only [Finset.coe_Icc, Set.mem_Icc, Finset.mem_coe, Finset.mem_Icc] at hu
      omega
    · intro u hu
      simp only [Finset.coe_Icc, Set.mem_Icc, Finset.mem_coe, Finset.mem_Icc] at hu
      push_cast [Nat.cast_sub (show u ≤ p by omega)]; ring_nf
  have hsum : VG p (2 * H5 (p - 1)) 1 := by
    rw [h2]; exact VG.sum _ fun u hu =>
      VG_pair hp3 (Finset.mem_Icc.mp hu).1 (by have := (Finset.mem_Icc.mp hu).2; omega)
  have hhalf : VG p ((1 / 2 : ℚ)) 0 := by
    rw [one_div, show (2 : ℚ) = ((2 : ℕ) : ℚ) by norm_num]
    have := Fact.mk Nat.prime_two
    refine (VG_inv_nat_le (e := 0) (by norm_num) ?_).mono (by norm_num)
    rw [padicValNat_primes (p := p) (q := 2) (by omega)]
  have := hhalf.mul hsum
  rw [show 1 / 2 * (2 * H5 (p - 1)) = H5 (p - 1) by ring] at this
  simpa using this

lemma H5_succ' {j : ℕ} (hj : 1 ≤ j) : H5 j = H5 (j - 1) + 1 / (j : ℚ) ^ 5 := by
  obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
  unfold H5
  rw [Finset.sum_Icc_succ_top (by omega), Nat.add_sub_cancel]

lemma H5_split {c : ℕ} (hc : 1 ≤ c) (hcp : c < p) :
    H5 (p - 1) = H5 (p - c) + ∑ u ∈ Icc 1 (c - 1), 1 / ((p : ℚ) - u) ^ 5 := by
  unfold H5
  rw [show Icc 1 (p - 1) = Ioc 0 (p - 1) from Finset.Icc_add_one_left_eq_Ioc 0 _,
    show Icc 1 (p - c) = Ioc 0 (p - c) from Finset.Icc_add_one_left_eq_Ioc 0 _]
  have h := Finset.sum_Ioc_consecutive (fun k : ℕ => 1 / (k : ℚ) ^ 5) (Nat.zero_le (p - c))
    (show p - c ≤ p - 1 by omega)
  rw [← h]
  congr 1
  apply Finset.sum_nbij' (fun k => p - k) (fun u => p - u)
  · intro k hk; simp only [Finset.mem_Ioc, Finset.mem_Icc, Finset.coe_Ioc, Finset.coe_Icc,
      Set.mem_Ioc, Set.mem_Icc, Finset.mem_coe] at hk ⊢; omega
  · intro u hu; simp only [Finset.mem_Ioc, Finset.mem_Icc, Finset.coe_Ioc, Finset.coe_Icc,
      Set.mem_Ioc, Set.mem_Icc, Finset.mem_coe] at hu ⊢; omega
  · intro k hk; simp only [Finset.mem_Ioc, Finset.coe_Ioc, Set.mem_Ioc, Finset.mem_coe] at hk; omega
  · intro u hu; simp only [Finset.mem_Icc, Finset.coe_Icc, Set.mem_Icc, Finset.mem_coe] at hu; omega
  · intro k hk
    simp only [Finset.mem_Ioc, Finset.coe_Ioc, Set.mem_Ioc, Finset.mem_coe] at hk
    push_cast [Nat.cast_sub (show k ≤ p by omega)]
    ring_nf

theorem GV_poleValue_congr (hp3 : 3 ≤ p) {c : ℕ} (hc : 1 ≤ c) (hcp : c < p) :
    GV p (poleValue (p - c) - poleValue c) 1 := by
  set d := p - c with hd
  have hdq : (d : ℚ) = p - c := by rw [hd]; push_cast [Nat.cast_sub hcp.le]; ring
  have hc0 : (c : ℚ) ≠ 0 := by exact_mod_cast (by omega : c ≠ 0)
  have hd0 : (d : ℚ) ≠ 0 := by exact_mod_cast (by omega : d ≠ 0)
  set S' := ∑ u ∈ Icc 1 (c - 1), 1 / ((p : ℚ) - u) ^ 5 with hS'
  set Sc := ∑ u ∈ Icc 1 (c - 1), 1 / (u : ℚ) ^ 5 with hSc
  have hHd : H5 d = H5 (p - 1) - S' := by rw [H5_split hc hcp]; ring
  have hHc : H5 c = Sc + 1 / (c : ℚ) ^ 5 := by rw [H5_succ' hc]; rfl
  set κ : ℚ := -(d : ℚ) ^ 4 * H5 d + (c : ℚ) ^ 4 * H5 c + (1 / (2 * (d : ℚ)) - 1 / (2 * (c : ℚ)))
    with hκ
  have hκ' : κ = -(d : ℚ) ^ 4 * H5 (p - 1) + ((d : ℚ) ^ 4 - (c : ℚ) ^ 4) * S' +
      (c : ℚ) ^ 4 * ∑ u ∈ Icc 1 (c - 1), (1 / ((p : ℚ) - u) ^ 5 + 1 / (u : ℚ) ^ 5) +
      (1 / (2 * (c : ℚ)) + 1 / (2 * (d : ℚ))) := by
    rw [hκ, hHd, hHc, Finset.sum_add_distrib, ← hS', ← hSc]
    field_simp
    ring
  have hdiff : poleValue d - poleValue c = C ((d : ℚ) ^ 4 - (c : ℚ) ^ 4) * X + C κ := by
    unfold poleValue
    rw [hκ]
    ext n
    simp only [coeff_add, coeff_sub, coeff_C_mul, coeff_C, coeff_X, coeff_neg, mul_sub]
    split_ifs <;> ring
  rw [hdiff]
  have hd4 : VG p ((d : ℚ) ^ 4 - (c : ℚ) ^ 4) 1 := by
    have := VG_int_one (p := p) (z := (d : ℤ) ^ 4 - (c : ℤ) ^ 4) (by
      rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]; push_cast
      rw [hd, Nat.cast_sub hcp.le, ZMod.natCast_self]; ring)
    simpa using this
  refine (by simpa using GV.C_mul hd4 (GV.X (p := p)) : GV p _ 1).add (GV.C ?_)
  rw [hκ']
  have t1 : VG p (-(d : ℚ) ^ 4 * H5 (p - 1)) 1 := by
    have := ((VG.natCast (p := p) (d ^ 4)).mul (VG_H5_pm1 hp3)).neg
    rw [show -(d : ℚ) ^ 4 * H5 (p - 1) = -(((d ^ 4 : ℕ) : ℚ) * H5 (p - 1)) by push_cast; ring]
    simpa using this
  refine ((t1.add ?_).add ?_).add ?_
  · refine (hd4.mul (VG.sum (r := 0) _ fun u hu => ?_)).mono (by norm_num)
    have hu' := Finset.mem_Icc.mp hu
    have hu2 : u < p := by omega
    rw [show ((p : ℚ) - u) = ((p - u : ℕ) : ℚ) by push_cast [Nat.cast_sub (show u ≤ p by omega)]; ring,
      one_div, show (((p - u : ℕ) : ℚ) ^ 5) = (((p - u) ^ 5 : ℕ) : ℚ) by push_cast; ring]
    refine (VG_inv_nat_le (e := 0) (pow_ne_zero _ (Nat.sub_ne_zero_of_lt hu2)) ?_).mono (by norm_num)
    rw [padicValNat.pow (p := p) _ 5, padicValNat_lt_p (Nat.one_le_iff_ne_zero.mpr
      (Nat.sub_ne_zero_of_lt hu2)) (Nat.sub_lt (by omega) (by omega))]
  · have := (VG.natCast (p := p) (c ^ 4)).mul (VG.sum (r := 1) _ fun u hu =>
      VG_pair hp3 (Finset.mem_Icc.mp hu).1
        (lt_of_le_of_lt (Finset.mem_Icc.mp hu).2 (lt_of_le_of_lt (Nat.sub_le c 1) hcp)))
    simpa using this
  · have e : 1 / (2 * (c : ℚ)) + 1 / (2 * (d : ℚ)) = (p : ℚ) * (1 / (2 * (c * d : ℕ) : ℚ)) := by
      push_cast; rw [hdq]
      have : ((p : ℚ) - c) ≠ 0 := by rw [← hdq]; exact hd0
      field_simp; ring
    rw [e]
    have hp1 : VG p (p : ℚ) 1 := by simpa using VG.primePow (p := p) 1
    refine (hp1.mul (VG_inv_2j (e := 0) hp3 (Nat.one_le_iff_ne_zero.mpr
      (Nat.mul_ne_zero (by omega) (by omega))) ?_)).mono
      (by norm_num)
    rw [padicValNat.mul (by omega) (by omega), padicValNat_lt_p hc hcp,
      padicValNat_lt_p (by omega) (by omega)]

lemma VG_H5_lt {j : ℕ} (hj : j < p) : VG p (H5 j) 0 := by
  unfold H5
  refine VG.sum _ fun u hu => ?_
  have hu' := Finset.mem_Icc.mp hu
  rw [one_div, show ((u : ℚ) ^ 5) = ((u ^ 5 : ℕ) : ℚ) by push_cast; ring]
  refine (VG_inv_nat_le (e := 0) (pow_ne_zero _ (by omega)) ?_).mono (by norm_num)
  rw [padicValNat.pow (p := p) u 5, padicValNat_lt_p hu'.1 (by omega)]

lemma VG_quarter (hp3 : 3 ≤ p) : VG p (1 / 4 : ℚ) 0 := by
  rw [one_div, show (4 : ℚ) = ((4 : ℕ) : ℚ) by norm_num]
  refine (VG_inv_nat_le (e := 0) (by norm_num) ?_).mono (by norm_num)
  rw [show (4 : ℕ) = 2 ^ 2 by norm_num, padicValNat.pow (p := p) 2 2]
  have := Fact.mk Nat.prime_two
  rw [padicValNat_primes (p := p) (q := 2) (by omega)]

lemma GV_poleValue_lt (hp3 : 3 ≤ p) {j : ℕ} (hj : 1 ≤ j) (hjp : j < p) : GV p (poleValue j) 0 := by
  unfold poleValue
  have h1 : GV p (C ((j : ℚ) ^ 4) * (X - C (H5 j))) 0 := by
    have := GV.C_mul (VG.natCast (p := p) (j ^ 4)) (GV.X.sub (GV.C (VG_H5_lt hjp)))
    simpa using this
  refine (h1.sub (GV.C (VG_quarter hp3))).add (GV.C ?_)
  have := VG_inv_2j hp3 hj (e := 0) (by rw [padicValNat_lt_p hj hjp])
  simpa using this

theorem factor_roots (ρs : Finset ℚ) (hρ : ∀ ρ ∈ ρs, VG p ρ 0) {F : ℚ[X]} (hF : GV p F 0)
    (hroot : ∀ ρ ∈ ρs, F.eval ρ = 0) :
    ∃ S : ℚ[X], GV p S 0 ∧ F = (∏ ρ ∈ ρs, (X - C ρ)) * S := by
  classical
  induction ρs using Finset.induction_on generalizing F with
  | empty => exact ⟨F, hF, by simp⟩
  | insert a ρs ha ih =>
    have hra : F.IsRoot a := hroot a (Finset.mem_insert_self _ _)
    set F1 := F /ₘ (X - C a) with hF1
    have hFeq : F = (X - C a) * F1 := ((mul_divByMonic_eq_iff_isRoot).mpr hra).symm
    have hF1int : GV p F1 0 := GV.divByMonic_X_sub_C hF (hρ a (Finset.mem_insert_self _ _))
    have hF1root : ∀ ρ ∈ ρs, F1.eval ρ = 0 := by
      intro ρ hρs
      have h1 := hroot ρ (Finset.mem_insert_of_mem hρs)
      rw [hFeq, eval_mul, eval_sub, eval_X, eval_C] at h1
      have hne : ρ - a ≠ 0 := sub_ne_zero.mpr fun h => ha (h ▸ hρs)
      exact (mul_eq_zero.mp h1).resolve_left hne
    obtain ⟨S, hS, hSeq⟩ := ih (fun ρ h => hρ ρ (Finset.mem_insert_of_mem h)) hF1int hF1root
    exact ⟨S, hS, by rw [hFeq, hSeq, Finset.prod_insert ha, mul_assoc]⟩

lemma padicValNat_lt_sq {u : ℕ} (hu : 1 ≤ u) (hup : u < p ^ 2) : padicValNat p u ≤ 1 := by
  by_contra h
  rw [not_le] at h
  have : p ^ 2 ∣ u := (padicValNat_dvd_iff_le (by omega)).mpr h
  exact absurd (Nat.le_of_dvd (by omega) this) (by omega)

lemma VG_H5 {m : ℕ} (hm : m < p ^ 2) : VG p (H5 m) (-5) := by
  unfold H5
  refine VG.sum _ fun v hv => ?_
  rw [Finset.mem_Icc] at hv
  rw [one_div]
  apply VG.inv (pow_ne_zero _ (by exact_mod_cast (by omega : v ≠ 0)))
  rw [show ((v : ℚ) ^ 5) = ((v ^ 5 : ℕ) : ℚ) by push_cast; ring, padicValRat.of_nat,
    padicValNat.pow (p := p) v 5]
  have : padicValNat p v ≤ 1 := by
    by_contra hne
    rw [not_le] at hne
    have h2 : p ^ 2 ∣ v := (padicValNat_dvd_iff_le (by omega)).mpr hne
    exact absurd (Nat.le_of_dvd (by omega) h2) (by omega)
  push_cast
  have h3 : (padicValRat p (v : ℚ) : ℚ) ≤ 1 := by rw [padicValRat.of_nat]; exact_mod_cast this
  linarith

lemma GV_poleValue_sq (hp3 : 3 ≤ p) {j : ℕ} (hj : 1 ≤ j) (hjp : j < p ^ 2) :
    GV p (poleValue j) (-5) := by
  unfold poleValue
  have h1 : GV p (C ((j : ℚ) ^ 4) * (X - C (H5 j))) (-5) := by
    have := GV.C_mul (VG.natCast (p := p) (j ^ 4)) ((GV.X.mono (by norm_num)).sub (GV.C (VG_H5 hjp)))
    simpa using this
  refine (h1.sub ((GV.C (VG_quarter hp3)).mono (by norm_num))).add (GV.C ?_)
  exact (VG_inv_2j hp3 hj (e := 1) (padicValNat_lt_sq hj hjp)).mono (by norm_num)



/-!
# Outer range: general residue and pole-value lemmas

For a numerator `tpol M = ∏_{γ ∈ M} (t + γ²)`:
* `res_tpol` : `res K (tpol M) j = ∏_γ (γ² - j²) / ∏_{i ≠ j} (i² - j²)`;
* valuation bounds for residues and pole values;
* `PV_congr` : `poleValue (p - c) ≡ poleValue c (mod p)`.
-/

open Finset Polynomial


variable {p : ℕ} [hp : Fact p.Prime]

lemma padicValNat_24 (hp5 : 5 ≤ p) : padicValNat p 24 = 0 := by
  apply padicValNat.eq_zero_of_not_dvd
  intro h
  have h1 : p ≤ 24 := Nat.le_of_dvd (by norm_num) h
  have hpr := hp.out
  interval_cases p <;> first | omega | (norm_num at hpr) | (norm_num at h)

lemma VG_bernoulli_even (k : ℕ) : VG p (_root_.bernoulli (2 * k)) (-1) := by
  obtain ⟨z, hz⟩ := Bernoulli.vonStaudt_clausen k
  have e : _root_.bernoulli (2 * k) = (z : ℚ) - ∑ q ∈ range (2 * k + 2) with q.Prime ∧ (q - 1) ∣ 2 * k,
      (1 : ℚ) / q := by rw [hz]; ring
  rw [e]
  refine ((VG.intCast (p := p) z).mono (by norm_num)).sub (VG.sum _ fun q hq => ?_)
  rw [Finset.mem_filter] at hq
  have hq0 : (q : ℚ) ≠ 0 := by exact_mod_cast hq.2.1.ne_zero
  rw [one_div]
  refine VG.inv hq0 ?_
  rw [padicValRat.of_nat]
  have : padicValNat p q ≤ 1 := by
    by_cases hpq : p = q
    · subst hpq; rw [padicValNat_self]
    · have := Fact.mk hq.2.1
      rw [padicValNat_primes hpq]; omega
  exact_mod_cast this

lemma VG_bernoulli_even_int (k : ℕ) (hk : ¬ (p - 1) ∣ 2 * k) :
    VG p (_root_.bernoulli (2 * k)) 0 := by
  obtain ⟨z, hz⟩ := Bernoulli.vonStaudt_clausen k
  have e : _root_.bernoulli (2 * k) = (z : ℚ) - ∑ q ∈ range (2 * k + 2) with q.Prime ∧ (q - 1) ∣ 2 * k,
      (1 : ℚ) / q := by rw [hz]; ring
  rw [e]
  refine (VG.intCast (p := p) z).sub (VG.sum _ fun q hq => ?_)
  rw [Finset.mem_filter] at hq
  have hq0 : (q : ℚ) ≠ 0 := by exact_mod_cast hq.2.1.ne_zero
  have hpq : p ≠ q := fun h => hk (h ▸ hq.2.2)
  rw [one_div]
  refine (VG.inv (r := 0) hq0 ?_).mono (by norm_num)
  have := Fact.mk hq.2.1
  rw [padicValRat.of_nat, padicValNat_primes hpq]; simp

lemma VG_inv24 (hp5 : 5 ≤ p) : VG p ((24 : ℚ)⁻¹) 0 := by
  refine (VG.inv (r := 0) (by norm_num) ?_).mono (by norm_num)
  rw [show (24 : ℚ) = ((24 : ℕ) : ℚ) by norm_num, padicValRat.of_nat, padicValNat_24 hp5]; simp

theorem VG_μmono (hp5 : 5 ≤ p) (e : ℕ) : VG p (μmono e) (-1) := by
  unfold μmono
  rw [show 2 * e + 2 = 2 * (e + 1) by ring, div_eq_mul_inv]
  have h1 : VG p ((-1 : ℚ) ^ e) 0 := by
    rcases neg_one_pow_eq_or ℚ e with h | h <;> rw [h]
    · exact VG.one
    · exact VG.one.neg
  have h3 : VG p (((2 * e + 3) * (2 * e + 4) * (2 * e + 5) : ℕ) : ℚ) 0 := VG.natCast _
  have := ((h1.mul (VG_bernoulli_even (e + 1))).mul h3).mul (VG_inv24 hp5)
  push_cast at this
  simpa using this

theorem VG_μmono_int (hp5 : 5 ≤ p) {e : ℕ} (he : e + 3 < 2 * p) : VG p (μmono e) 0 := by
  unfold μmono
  rw [show 2 * e + 2 = 2 * (e + 1) by ring, div_eq_mul_inv]
  have h1 : VG p ((-1 : ℚ) ^ e) 0 := by
    rcases neg_one_pow_eq_or ℚ e with h | h <;> rw [h]
    · exact VG.one
    · exact VG.one.neg
  by_cases hd : (p - 1) ∣ 2 * (e + 1)
  · -- `2e + 2 = j (p - 1)` with `j ∈ {1, 2, 3}`
    obtain ⟨j, hj⟩ := hd
    have hp1 : 1 ≤ p - 1 := by omega
    have hj3 : j ≤ 3 := by
      by_contra h; rw [not_le] at h
      have : (p - 1) * 4 ≤ (p - 1) * j := Nat.mul_le_mul_left _ h
      omega
    have hj0 : 1 ≤ j := by
      rcases Nat.eq_zero_or_pos j with h | h
      · rw [h, mul_zero] at hj; omega
      · exact h
    have hprod : VG p (((2 * e + 3) * (2 * e + 4) * (2 * e + 5) : ℕ) : ℚ) 1 := by
      apply VG.of_eq
      intro hne
      rw [padicValRat.of_nat]
      have hdvd : p ∣ (2 * e + 3) * (2 * e + 4) * (2 * e + 5) := by
        interval_cases j
        · exact Dvd.dvd.mul_right (Dvd.dvd.mul_right ⟨1, by omega⟩ _) _
        · exact Dvd.dvd.mul_right (Dvd.dvd.mul_left ⟨2, by omega⟩ _) _
        · exact Dvd.dvd.mul_left ⟨3, by omega⟩ _
      have hne' : (2 * e + 3) * (2 * e + 4) * (2 * e + 5) ≠ 0 := by positivity
      have := one_le_padicValNat_of_dvd hne' hdvd
      exact_mod_cast this
    have := ((h1.mul (VG_bernoulli_even (e + 1))).mul hprod).mul (VG_inv24 hp5)
    push_cast at this
    simpa using this
  · have h3 : VG p (((2 * e + 3) * (2 * e + 4) * (2 * e + 5) : ℕ) : ℚ) 0 := VG.natCast _
    have := ((h1.mul (VG_bernoulli_even_int (e + 1) hd)).mul h3).mul (VG_inv24 hp5)
    push_cast at this
    simpa using this

lemma D_eq_tpol (m : ℕ) : D m = tpol ((Icc 1 m).val.map fun j : ℕ => (j : ℤ)) := by
  unfold D tpol
  rw [Multiset.map_map, Finset.prod_eq_multiset_prod]
  congr 1

lemma GV_divByMonic_D (K : ℕ) (Pz : ℤ[X]) :
    GV p (Pz.map (Int.castRingHom ℚ) /ₘ D K) 0 := by
  have hD : D K = (tpolZ ((Icc 1 K).val.map fun j : ℕ => (j : ℤ))).map (Int.castRingHom ℚ) := by
    rw [tpolZ_map_Q, D_eq_tpol]
  have hmon : (tpolZ ((Icc 1 K).val.map fun j : ℕ => (j : ℤ))).Monic := by
    unfold tpolZ
    exact monic_multiset_prod_of_monic _ _ fun γ _ => monic_X_add_C _
  rw [hD, ← map_divByMonic _ hmon]
  intro n
  rw [coeff_map]
  exact VG.intCast _

lemma GV_poleValue_mul (hp3 : 3 ≤ p) {k : ℕ} (hk : 1 ≤ k) (hkp : k < p) :
    GV p (poleValue (p * k)) (-1) := by
  have hj : 1 ≤ p * k := Nat.one_le_iff_ne_zero.mpr (by positivity)
  have hjp : p * k < p ^ 2 := by rw [sq]; exact Nat.mul_lt_mul_of_pos_left hkp (by omega)
  unfold poleValue
  have h4 : VG p (((p * k : ℕ) : ℚ) ^ 4) 4 := by
    right
    rw [padicValRat.pow, padicValRat.of_nat, padicValNat.mul (by omega) (by omega),
      padicValNat_self, padicValNat_lt_p hk hkp]; norm_num
  have h1 : GV p (C (((p * k : ℕ) : ℚ) ^ 4) * (X - C (H5 (p * k)))) (-1) := by
    have := GV.C_mul h4 ((GV.X.mono (by norm_num)).sub (GV.C (VG_H5 hjp)))
    refine this.mono (by norm_num)
  refine (h1.sub ((GV.C (VG_quarter hp3)).mono (by norm_num))).add (GV.C ?_)
  exact VG_inv_2j hp3 hj (e := 1) (padicValNat_lt_sq hj hjp)

lemma tpol_nsmul (k : ℕ) (M : Multiset ℤ) : tpol (k • M) = tpol M ^ k := by
  induction k with
  | zero => simp [tpol]
  | succ k ih => rw [succ_nsmul, tpol_add, ih, pow_succ]

lemma mem_rootsO_other (hm : 2 * m + 1 = p) (n : ℕ) {c : Fin (m + 1)} {i j : ℕ} (hj : j ∈ tailO n) (hc : jc hm j ≠ c) :
    (j : ℤ) ∈ rootsO hm n c i := by
  unfold rootsO
  refine Multiset.mem_add.mpr (Or.inl (Multiset.mem_map.mpr ⟨j, ?_, rfl⟩))
  exact Finset.mem_val.mpr (Finset.mem_filter.mpr ⟨hj, hc⟩)

lemma mem_rootsO_big (hm : 2 * m + 1 = p) (n : ℕ) {c : Fin (m + 1)} {i j : ℕ} (hi : nbC hm n c ≤ i) (hj : j ∈ bigC hm n c) :
    (j : ℤ) ∈ rootsO hm n c i := by
  unfold rootsO
  rw [if_neg (by omega)]
  refine Multiset.mem_add.mpr (Or.inr (Multiset.mem_add.mpr (Or.inl ?_)))
  exact Multiset.mem_map.mpr ⟨j, Finset.mem_val.mpr hj, rfl⟩

lemma padicValRat_den_zero_le {K j : ℕ} (hj : j ∈ Icc 1 K) (hK : 2 * K < p ^ 2)
    (hj0 : (p : ℤ) ∣ (j : ℤ)) :
    (padicValRat p (∏ i ∈ (Icc 1 K).erase j, ((i : ℚ) ^ 2 - (j : ℚ) ^ 2)) : ℚ) ≤
      2 * (((Icc 1 K).erase j).filter fun i : ℕ => (p : ℤ) ∣ (i : ℤ)).card := by
  have hne : ∀ i ∈ (Icc 1 K).erase j, ((i : ℚ) ^ 2 - (j : ℚ) ^ 2) ≠ 0 := by
    intro i hi
    have hij := (Finset.mem_erase.mp hi).1
    have : (i : ℚ) ≠ j := by exact_mod_cast hij
    intro h
    have h2 : ((i : ℚ) - j) * ((i : ℚ) + j) = 0 := by linear_combination h
    rcases mul_eq_zero.mp h2 with h3 | h3
    · exact this (by linarith)
    · have : (0 : ℚ) ≤ i := by positivity
      have : (1 : ℚ) ≤ j := by exact_mod_cast (Finset.mem_Icc.mp hj).1
      linarith
  rw [padicValRat_finset_prod _ _ hne]
  push_cast
  have hrhs : (2 * ((((Icc 1 K).erase j).filter fun i : ℕ => (p : ℤ) ∣ (i : ℤ)).card : ℚ)) =
      ∑ i ∈ (Icc 1 K).erase j, (if (p : ℤ) ∣ (i : ℤ) then (2 : ℚ) else 0) := by
    rw [Finset.card_filter]; push_cast; rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by split_ifs <;> norm_num
  rw [hrhs]
  refine Finset.sum_le_sum fun i hi => ?_
  have hi' := Finset.mem_erase.mp hi
  have hiK := (Finset.mem_Icc.mp hi'.2)
  have hjK := (Finset.mem_Icc.mp hj)
  rw [show ((i : ℚ) ^ 2 - (j : ℚ) ^ 2) = (((i - j) * (i + j) : ℤ) : ℚ) by push_cast; ring]
  have hz : ((i : ℤ) - j) * ((i : ℤ) + j) ≠ 0 := by
    have := hne i hi
    intro h; apply this; rw [show ((i : ℚ) ^ 2 - (j : ℚ) ^ 2) =
      (((i - j) * (i + j) : ℤ) : ℚ) by push_cast; ring, h]; simp
  have hz1 := (mul_ne_zero_iff.mp hz).1
  have hz2 := (mul_ne_zero_iff.mp hz).2
  split_ifs with hc
  · rw [padicValRat.of_int, padicValInt.mul hz1 hz2]
    have hle : ∀ z : ℤ, z ≠ 0 → |z| ≤ 2 * K → padicValInt p z ≤ 1 := by
      intro z hz0 hzK
      have := padicValRat_int_le_one (p := p) (z := z) (fun hd => by
        have h1 := Int.natAbs_dvd_natAbs.mpr hd
        rw [Int.natAbs_pow, Int.natAbs_natCast] at h1
        have h2 := Nat.le_of_dvd (Int.natAbs_pos.mpr hz0) h1
        have h3 : (z.natAbs : ℤ) ≤ 2 * K := by rw [Int.natCast_natAbs]; exact hzK
        omega)
      rw [padicValRat.of_int] at this; exact_mod_cast this
    have hb1 := hle _ hz1 (by rw [abs_le]; constructor <;> omega)
    have hb2 := hle _ hz2 (by rw [abs_le]; constructor <;> omega)
    push_cast
    have : ((padicValInt p ((i : ℤ) - j) : ℕ) : ℚ) ≤ 1 := by exact_mod_cast hb1
    have : ((padicValInt p ((i : ℤ) + j) : ℕ) : ℚ) ≤ 1 := by exact_mod_cast hb2
    linarith
  · have hnd : ¬ (p : ℤ) ∣ ((i : ℤ) - j) * ((i : ℤ) + j) := by
      intro hd
      rcases Int.Prime.dvd_mul' hp.out hd with h1 | h1
      · exact hc (by have := dvd_add h1 hj0; simpa using this)
      · exact hc (by have := dvd_sub h1 hj0; simpa using this)
    rw [padicValRat_int_eq_zero hnd]; simp


lemma sq_ne_of_ne {i j : ℕ} (h : i ≠ j) : (i : ℚ) ^ 2 - (j : ℚ) ^ 2 ≠ 0 := by
  intro h2
  have h3 : ((i : ℚ) - j) * ((i : ℚ) + j) = 0 := by linear_combination h2
  rcases mul_eq_zero.mp h3 with h4 | h4
  · exact h (by exact_mod_cast (sub_eq_zero.mp h4))
  · have : (0 : ℚ) ≤ i := by positivity
    have : (0 : ℚ) ≤ j := by positivity
    have hi : (i : ℚ) = 0 := by linarith
    have hj : (j : ℚ) = 0 := by linarith
    exact h (by exact_mod_cast hi.trans hj.symm)

lemma mem_entryO_small (hm : 2 * m + 1 = p) (n : ℕ) {cs ct : Fin (m + 1)} {is it : ℕ} {k : ℕ} (hk : k ∈ Icc 1 (3 * n)) :
    (k : ℤ) ∈ entryO hm n cs is ct it := by
  unfold entryO
  refine Multiset.mem_add.mpr (Or.inl (Multiset.mem_add.mpr (Or.inl ?_)))
  rw [Multiset.mem_nsmul_of_ne_zero (by norm_num)]
  exact Multiset.mem_map.mpr ⟨k, hk, rfl⟩

lemma mem_entryO_left (hm : 2 * m + 1 = p) (n : ℕ) {cs ct : Fin (m + 1)} {is it : ℕ} {γ : ℤ} (h : γ ∈ rootsO hm n cs is) :
    γ ∈ entryO hm n cs is ct it := by
  unfold entryO
  exact Multiset.mem_add.mpr (Or.inl (Multiset.mem_add.mpr (Or.inr h)))

lemma mem_entryO_right (hm : 2 * m + 1 = p) (n : ℕ) {cs ct : Fin (m + 1)} {is it : ℕ} {γ : ℤ} (h : γ ∈ rootsO hm n ct it) :
    γ ∈ entryO hm n cs is ct it := by
  unfold entryO
  exact Multiset.mem_add.mpr (Or.inr h)

lemma count_rootsO (hm : 2 * m + 1 = p) (n : ℕ) (c : Fin (m + 1)) (i : ℕ) (x : ZMod p)
    (hx : x ^ 2 = ((((c : ℕ) : ℤ) : ZMod p)) ^ 2) :
    i ≤ ((rootsO hm n c i).filter fun γ : ℤ => ((γ : ZMod p)) ^ 2 = x ^ 2).card := by
  have hcx : ((((c : ℕ) : ℤ) : ZMod p)) ^ 2 = x ^ 2 := hx.symm
  unfold rootsO
  rw [Multiset.filter_add, Multiset.card_add]
  split_ifs with h
  · rw [card_filter_replicate, if_pos hcx]; omega
  · rw [Multiset.filter_add, Multiset.card_add, card_filter_replicate, if_pos hcx]
    have hbig : ((bigC hm n c).val.map fun j : ℕ => (j : ℤ)).filter
        (fun γ : ℤ => ((γ : ZMod p)) ^ 2 = x ^ 2) = (bigC hm n c).val.map fun j : ℕ => (j : ℤ) := by
      refine Multiset.filter_eq_self.mpr fun γ hγ => ?_
      obtain ⟨j, hj, rfl⟩ := Multiset.mem_map.mp hγ
      have hj' : j ∈ bigC hm n c := Finset.mem_val.mp hj
      have hjc : jc hm j = c := (Finset.mem_filter.mp (Finset.mem_filter.mp hj').1).2
      rw [hx, sq_jc hm j, hjc]
    rw [hbig, Multiset.card_map, Finset.card_val]
    have : nbC hm n c = (bigC hm n c).card := rfl
    omega

lemma VG_prod_sq_sub_zero (M : Multiset ℤ) {j : ℤ} (hj : (p : ℤ) ∣ j) :
    VG p ((M.map fun γ : ℤ => (γ : ℚ) ^ 2 - (j : ℚ) ^ 2).prod)
      (2 * (M.filter fun γ : ℤ => (p : ℤ) ∣ γ).card) := by
  induction M using Multiset.induction_on with
  | empty => right; simp
  | cons a M ih =>
    rw [Multiset.map_cons, Multiset.prod_cons, Multiset.filter_cons]
    split_ifs with h
    · rw [Multiset.card_add, Multiset.card_singleton]
      have h1 : VG p ((a : ℚ) ^ 2 - (j : ℚ) ^ 2) 2 := by
        rw [show (a : ℚ) ^ 2 - (j : ℚ) ^ 2 = ((a - j : ℤ) : ℚ) * ((a + j : ℤ) : ℚ) by push_cast; ring]
        have := (VG_int_one (p := p) (dvd_sub h hj)).mul (VG_int_one (p := p) (dvd_add h hj))
        simpa [one_add_one_eq_two] using this
      convert h1.mul ih using 1; push_cast; ring
    · rw [zero_add]
      have h1 : VG p ((a : ℚ) ^ 2 - (j : ℚ) ^ 2) 0 := by
        have := VG.intCast (p := p) (a ^ 2 - j ^ 2); push_cast at this; exact this
      simpa using h1.mul ih

lemma ccls_eq_zero_iff (hm : 2 * m + 1 = p) (c : ZMod p) : ccls hm c = 0 ↔ c = 0 := by
  constructor
  · intro h
    have hs := ccls_spec hm c
    rw [h] at hs
    simp only [Fin.val_zero, Nat.cast_zero, Int.cast_zero] at hs
    rcases hs with h1 | h1
    · exact h1.symm
    · exact neg_eq_zero.mp h1.symm
  · rintro rfl
    unfold ccls
    rw [dif_pos (by simp)]
    ext; simp


lemma eval_tpol (M : Multiset ℤ) (x : ℚ) :
    (tpol M).eval x = (M.map fun γ : ℤ => x + (γ : ℚ) ^ 2).prod := by
  unfold tpol
  rw [eval_multiset_prod, Multiset.map_map]
  congr 1
  exact Multiset.map_congr rfl fun γ _ => by simp

lemma res_tpol {K j : ℕ} (hj : j ∈ Icc 1 K) (M : Multiset ℤ) :
    res K (tpol M) j = (M.map fun γ : ℤ => (γ : ℚ) ^ 2 - (j : ℚ) ^ 2).prod /
      ∏ i ∈ (Icc 1 K).erase j, ((i : ℚ) ^ 2 - (j : ℚ) ^ 2) := by
  unfold res
  rw [eval_derivative_D hj, eval_tpol]
  congr 1
  congr 1
  exact Multiset.map_congr rfl fun γ _ => by ring

lemma res_tpol_eq_zero {K j : ℕ} (hj : j ∈ Icc 1 K) {M : Multiset ℤ} {γ : ℤ} (hγ : γ ∈ M)
    (h : γ ^ 2 = (j : ℤ) ^ 2) : res K (tpol M) j = 0 := by
  rw [res_tpol hj, Multiset.prod_eq_zero, zero_div]
  rw [Multiset.mem_map]
  exact ⟨γ, hγ, by rw [sub_eq_zero]; exact_mod_cast h⟩

/-- The numerator valuation: at least the number of roots `γ` with `γ² ≡ j²`. -/
lemma VG_prod_sq_sub (M : Multiset ℤ) (j : ℤ) :
    VG p ((M.map fun γ : ℤ => (γ : ℚ) ^ 2 - (j : ℚ) ^ 2).prod)
      ((M.filter fun γ : ℤ => ((γ : ZMod p)) ^ 2 = (j : ZMod p) ^ 2).card) := by
  induction M using Multiset.induction_on with
  | empty => right; simp
  | cons a M ih =>
    rw [Multiset.map_cons, Multiset.prod_cons, Multiset.filter_cons]
    split_ifs with h
    · rw [Multiset.card_add, Multiset.card_singleton]
      have h1 : VG p ((a : ℚ) ^ 2 - (j : ℚ) ^ 2) 1 := by
        have := VG_int_one (p := p) (z := a ^ 2 - j ^ 2) (by
          rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]; push_cast; rw [h, sub_self])
        simpa using this
      convert h1.mul ih using 1; push_cast; ring
    · rw [zero_add]
      have h1 : VG p ((a : ℚ) ^ 2 - (j : ℚ) ^ 2) 0 := by
        have := VG.intCast (p := p) (a ^ 2 - j ^ 2); push_cast at this; exact this
      simpa using h1.mul ih

/-- The denominator valuation for a nonzero class: at most the number of other nodes in the
class (each factor has valuation `≤ 1`). -/
lemma padicValRat_den_le (hp3 : 3 ≤ p) {K j : ℕ} (hj : j ∈ Icc 1 K) (hK : 2 * K < p ^ 2)
    (hj0 : ¬ (p : ℤ) ∣ (j : ℤ)) :
    (padicValRat p (∏ i ∈ (Icc 1 K).erase j, ((i : ℚ) ^ 2 - (j : ℚ) ^ 2)) : ℚ) ≤
      (((Icc 1 K).erase j).filter fun i : ℕ => ((i : ℤ) : ZMod p) ^ 2 = ((j : ℤ) : ZMod p) ^ 2).card := by
  have hne : ∀ i ∈ (Icc 1 K).erase j, ((i : ℚ) ^ 2 - (j : ℚ) ^ 2) ≠ 0 := by
    intro i hi
    have hij := (Finset.mem_erase.mp hi).1
    have : (i : ℚ) ≠ j := by exact_mod_cast hij
    intro h
    have h2 : ((i : ℚ) - j) * ((i : ℚ) + j) = 0 := by linear_combination h
    rcases mul_eq_zero.mp h2 with h3 | h3
    · exact this (by linarith)
    · have : (0 : ℚ) ≤ i := by positivity
      have : (1 : ℚ) ≤ j := by exact_mod_cast (Finset.mem_Icc.mp hj).1
      linarith
  rw [padicValRat_finset_prod _ _ hne]
  push_cast
  rw [Finset.card_filter]
  push_cast
  refine Finset.sum_le_sum fun i hi => ?_
  have hi' := Finset.mem_erase.mp hi
  have hiK := (Finset.mem_Icc.mp hi'.2)
  have hjK := (Finset.mem_Icc.mp hj)
  rw [show ((i : ℚ) ^ 2 - (j : ℚ) ^ 2) = (((i - j) * (i + j) : ℤ) : ℚ) by push_cast; ring]
  split_ifs with hc
  · -- exactly one factor divisible by `p`, with valuation `≤ 1`
    rw [padicValRat.of_int]
    have hz : ((i : ℤ) - j) * ((i : ℤ) + j) ≠ 0 := by
      have := hne i hi
      intro h; apply this; rw [show ((i : ℚ) ^ 2 - (j : ℚ) ^ 2) =
        (((i - j) * (i + j) : ℤ) : ℚ) by push_cast; ring, h]; simp
    have hz1 := (mul_ne_zero_iff.mp hz).1
    have hz2 := (mul_ne_zero_iff.mp hz).2
    rw [padicValInt.mul hz1 hz2]
    have hle : ∀ z : ℤ, z ≠ 0 → |z| ≤ 2 * K → padicValInt p z ≤ 1 := by
      intro z hz0 hzK
      have := padicValRat_int_le_one (p := p) (z := z) (fun hd => by
        have h1 := Int.natAbs_dvd_natAbs.mpr hd
        rw [Int.natAbs_pow, Int.natAbs_natCast] at h1
        have h2 := Nat.le_of_dvd (Int.natAbs_pos.mpr hz0) h1
        have h3 : (z.natAbs : ℤ) ≤ 2 * K := by rw [Int.natCast_natAbs]; exact hzK
        omega)
      rw [padicValRat.of_int] at this; exact_mod_cast this
    have hb1 : padicValInt p ((i : ℤ) - j) ≤ 1 := hle _ hz1 (by rw [abs_le]; constructor <;> omega)
    have hb2 : padicValInt p ((i : ℤ) + j) ≤ 1 := hle _ hz2 (by rw [abs_le]; constructor <;> omega)
    have hp2 : ¬ ((p : ℤ) ∣ ((i : ℤ) - j) ∧ (p : ℤ) ∣ ((i : ℤ) + j)) := by
      rintro ⟨h1, h2⟩
      apply hj0
      have h3 : (p : ℤ) ∣ 2 * (j : ℤ) := by
        have := dvd_sub h2 h1; rw [show (i : ℤ) + j - (i - j) = 2 * j by ring] at this; exact this
      rcases (Int.Prime.dvd_mul' hp.out h3) with h4 | h4
      · exfalso
        have : (p : ℤ) ≤ 2 := Int.le_of_dvd (by norm_num) h4
        omega
      · exact h4
    by_cases hd1 : (p : ℤ) ∣ ((i : ℤ) - j)
    · have hd2 : ¬ (p : ℤ) ∣ ((i : ℤ) + j) := fun h => hp2 ⟨hd1, h⟩
      have : padicValInt p ((i : ℤ) + j) = 0 := padicValInt.eq_zero_of_not_dvd hd2
      rw [this]; push_cast; linarith [(show (padicValInt p ((i : ℤ) - j) : ℚ) ≤ 1 by exact_mod_cast hb1)]
    · have : padicValInt p ((i : ℤ) - j) = 0 := padicValInt.eq_zero_of_not_dvd hd1
      rw [this]; push_cast; linarith [(show (padicValInt p ((i : ℤ) + j) : ℚ) ≤ 1 by exact_mod_cast hb2)]
  · have hnd : ¬ (p : ℤ) ∣ ((i : ℤ) - j) * ((i : ℤ) + j) := by
      intro hd
      apply hc
      rw [← ZMod.intCast_zmod_eq_zero_iff_dvd] at hd
      push_cast at hd
      linear_combination hd
    rw [padicValRat_int_eq_zero hnd]; simp

lemma VG_res_class (hp3 : 3 ≤ p) {K : ℕ} (hK : 2 * K < p ^ 2) (M : Multiset ℤ) {j : ℕ}
    (hj : j ∈ Icc 1 K) (hj0 : ¬ (p : ℤ) ∣ (j : ℤ)) :
    VG p (res K (tpol M) j) (((M.filter fun γ : ℤ => ((γ : ZMod p)) ^ 2 = ((j : ℤ) : ZMod p) ^ 2).card : ℚ)
      - (((Icc 1 K).erase j).filter fun i : ℕ => ((i : ℤ) : ZMod p) ^ 2 = ((j : ℤ) : ZMod p) ^ 2).card) := by
  rw [res_tpol hj, div_eq_mul_inv]
  have hden : ∏ i ∈ (Icc 1 K).erase j, ((i : ℚ) ^ 2 - (j : ℚ) ^ 2) ≠ 0 := by
    refine Finset.prod_ne_zero_iff.mpr fun i hi => ?_
    have hij := (Finset.mem_erase.mp hi).1
    have : (i : ℚ) ≠ j := by exact_mod_cast hij
    intro h
    have h2 : ((i : ℚ) - j) * ((i : ℚ) + j) = 0 := by linear_combination h
    rcases mul_eq_zero.mp h2 with h3 | h3
    · exact this (by linarith)
    · have : (0 : ℚ) ≤ i := by positivity
      have : (1 : ℚ) ≤ j := by exact_mod_cast (Finset.mem_Icc.mp hj).1
      linarith
  have h1 := VG_prod_sq_sub (p := p) M (j : ℤ)
  have h2 := VG.inv (p := p) hden (padicValRat_den_le hp3 hj hK hj0)
  push_cast at h1
  simpa [sub_eq_add_neg] using h1.mul h2

lemma VG_μpoly_sub_μGe (hp5 : 5 ≤ p) {Q : ℚ[X]} (hQ : GV p Q 0) : VG p (μpoly Q - μGe p Q) 0 := by
  have e : μpoly Q = ∑ e ∈ range (Q.natDegree + 1), Q.coeff e * μmono e := by
    unfold μpoly; rw [Polynomial.sum_over_range]; intro n; simp
  rw [e, μGe, ← Finset.sum_sub_distrib]
  refine VG.sum _ fun e _ => ?_
  split_ifs with h
  · simp [VG.zero]
  · simpa using (hQ e).mul (VG_μmono_int hp5 (by omega))

/-- `μ_X` minus its high part, expanded. -/
lemma μX_sub_μGe (K : ℕ) (P : ℚ[X]) :
    μX K P - C (μGe p (P /ₘ D K)) = C (μpoly (P /ₘ D K) - μGe p (P /ₘ D K)) +
      ∑ j ∈ Icc 1 K, C (res K P j) * poleValue j := by
  unfold μX res; rw [map_sub]; ring

variable (hm : 2 * m + 1 = p) (n : ℕ)

lemma entryO_eq (cs : Fin (m + 1)) (is : ℕ) (ct : Fin (m + 1)) (it : ℕ) :
    D (3 * n) ^ 6 * (tpolZ (rootsO hm n cs is)).map (Int.castRingHom ℚ) *
      (tpolZ (rootsO hm n ct it)).map (Int.castRingHom ℚ) = tpol (entryO hm n cs is ct it) := by
  rw [tpolZ_map_Q, tpolZ_map_Q, D_eq_tpol, ← tpol_nsmul, ← tpol_add, ← tpol_add]; rfl

/-- The integral numerator quotient. -/
lemma GV_entry_quot (cs : Fin (m + 1)) (is : ℕ) (ct : Fin (m + 1)) (it : ℕ) :
    GV p (tpol (entryO hm n cs is ct it) /ₘ D (40 * n)) 0 := by
  rw [← tpolZ_map_Q]; exact GV_divByMonic_D _ _

/-- Residues vanish at poles `j ≤ N` and at tail poles outside the common class. -/
lemma res_entry_zero {cs ct : Fin (m + 1)} {is it : ℕ} {j : ℕ} (hj : j ∈ Icc 1 (40 * n))
    (h : j ≤ 3 * n ∨ jc hm j ≠ cs ∨ jc hm j ≠ ct) :
    res (40 * n) (tpol (entryO hm n cs is ct it)) j = 0 := by
  have hj' := Finset.mem_Icc.mp hj
  rcases h with h | h | h
  · exact res_tpol_eq_zero hj (mem_entryO_small hm n (Finset.mem_Icc.mpr ⟨hj'.1, h⟩)) rfl
  · by_cases hN : j ≤ 3 * n
    · exact res_tpol_eq_zero hj (mem_entryO_small hm n (Finset.mem_Icc.mpr ⟨hj'.1, hN⟩)) rfl
    · exact res_tpol_eq_zero hj (mem_entryO_left hm n (mem_rootsO_other hm n
        (Finset.mem_Icc.mpr ⟨by omega, hj'.2⟩) h)) rfl
  · by_cases hN : j ≤ 3 * n
    · exact res_tpol_eq_zero hj (mem_entryO_small hm n (Finset.mem_Icc.mpr ⟨hj'.1, hN⟩)) rfl
    · exact res_tpol_eq_zero hj (mem_entryO_right hm n (mem_rootsO_other hm n
        (Finset.mem_Icc.mpr ⟨by omega, hj'.2⟩) h)) rfl

/-- The pole sum reduces to the tail poles of the common class. -/
lemma pole_sum_reduce (c : Fin (m + 1)) (is it : ℕ) :
    ∑ j ∈ Icc 1 (40 * n), C (res (40 * n) (tpol (entryO hm n c is c it)) j) * poleValue j =
      ∑ j ∈ tailC hm n c, C (res (40 * n) (tpol (entryO hm n c is c it)) j) * poleValue j := by
  symm
  apply Finset.sum_subset
  · intro j hj
    have := (Finset.mem_filter.mp hj).1
    unfold tailO at this
    exact Finset.mem_Icc.mpr ⟨by have := (Finset.mem_Icc.mp this).1; omega, (Finset.mem_Icc.mp this).2⟩
  · intro j hj hjn
    rw [res_entry_zero hm n hj, C_0, zero_mul]
    by_contra h
    push Not at h
    apply hjn
    exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨by omega, (Finset.mem_Icc.mp hj).2⟩, h.2.1⟩

lemma pole_sum_cross {cs ct : Fin (m + 1)} (hc : cs ≠ ct) (is it : ℕ) :
    ∑ j ∈ Icc 1 (40 * n), C (res (40 * n) (tpol (entryO hm n cs is ct it)) j) * poleValue j = 0 := by
  refine Finset.sum_eq_zero fun j hj => ?_
  rw [res_entry_zero hm n hj, C_0, zero_mul]
  by_cases h : jc hm j = cs
  · right; right; rw [h]; exact hc
  · right; left; exact h

lemma wO_nonpos (c : Fin (m + 1)) (i : ℕ) : wO hm n c i ≤ 0 := by
  unfold wO; split_ifs <;> first | exact min_le_left _ _ | norm_num

lemma jc_eq_zero_iff (j : ℕ) : jc hm j = 0 ↔ (p : ℤ) ∣ (j : ℤ) := by
  unfold jc; rw [ccls_eq_zero_iff, ZMod.intCast_zmod_eq_zero_iff_dvd]

/-- Denominator count for a nonzero class. -/
lemma den_count {c : Fin (m + 1)} {j : ℕ} (hj : j ∈ Icc 1 (40 * n)) (hjc : jc hm j = c) :
    (((Icc 1 (40 * n)).erase j).filter fun i : ℕ =>
      ((i : ℤ) : ZMod p) ^ 2 = ((j : ℤ) : ZMod p) ^ 2).card = ellC hm n c - 1 := by
  have e : (((Icc 1 (40 * n)).erase j).filter fun i : ℕ =>
      ((i : ℤ) : ZMod p) ^ 2 = ((j : ℤ) : ZMod p) ^ 2) =
      ((Icc 1 (40 * n)).filter fun i => jc hm i = c).erase j := by
    rw [Finset.filter_erase]
    congr 1
    ext i
    simp only [Finset.mem_filter, sq_eq_iff_ccls hm]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨h1, h2.trans hjc⟩
    · rintro ⟨h1, h2⟩; exact ⟨h1, h2.trans hjc.symm⟩
  rw [e, Finset.card_erase_of_mem (Finset.mem_filter.mpr ⟨hj, hjc⟩)]
  rfl

/-- Numerator count for a nonzero class. -/
lemma num_count {c : Fin (m + 1)} (hc0 : c ≠ 0) {is it : ℕ} {j : ℕ} (hjc : jc hm j = c) :
    6 * delC n c + is + it ≤ ((entryO hm n c is c it).filter fun γ : ℤ =>
      ((γ : ZMod p)) ^ 2 = ((j : ℤ) : ZMod p) ^ 2).card := by
  have hx : ((j : ℤ) : ZMod p) ^ 2 = ((((c : ℕ) : ℤ) : ZMod p)) ^ 2 := by
    rw [sq_jc hm j, hjc]
  unfold entryO
  rw [Multiset.filter_add, Multiset.filter_add, Multiset.card_add, Multiset.card_add]
  have h1 := count_rootsO hm n c is _ hx
  have h2 := count_rootsO hm n c it _ hx
  have h3 : 6 * delC n c ≤ ((6 • ((Icc 1 (3 * n)).val.map fun j : ℕ => (j : ℤ))).filter
      fun γ : ℤ => ((γ : ZMod p)) ^ 2 = ((j : ℤ) : ZMod p) ^ 2).card := by
    unfold delC
    split_ifs with hc
    · rw [Multiset.filter_nsmul, Multiset.card_nsmul]
      have : 1 ≤ (((Icc 1 (3 * n)).val.map fun j : ℕ => (j : ℤ)).filter
          fun γ : ℤ => ((γ : ZMod p)) ^ 2 = ((j : ℤ) : ZMod p) ^ 2).card := by
        apply Multiset.card_pos_iff_exists_mem.mpr
        refine ⟨((c : ℕ) : ℤ), Multiset.mem_filter.mpr ⟨Multiset.mem_map.mpr ⟨c, ?_, rfl⟩, hx.symm⟩⟩
        have : (c : ℕ) ≠ 0 := fun h => hc0 (Fin.ext h)
        exact Finset.mem_val.mpr (Finset.mem_Icc.mpr ⟨by omega, hc⟩)
      omega
    · omega
  omega

lemma ellC_pos {c : Fin (m + 1)} {j : ℕ} (hj : j ∈ Icc 1 (40 * n)) (hjc : jc hm j = c) :
    1 ≤ ellC hm n c :=
  Finset.card_pos.mpr ⟨j, Finset.mem_filter.mpr ⟨hj, hjc⟩⟩

lemma mem_Icc_of_tailC {c : Fin (m + 1)} {j : ℕ} (hj : j ∈ tailC hm n c) : j ∈ Icc 1 (40 * n) := by
  have := Finset.mem_Icc.mp (Finset.mem_filter.mp hj).1
  exact Finset.mem_Icc.mpr ⟨by omega, this.2⟩

/-- Residue bound on a nonzero class. -/
lemma VG_res_entry (hp3 : 3 ≤ p) (hK : 2 * (40 * n) < p ^ 2) {c : Fin (m + 1)} (hc0 : c ≠ 0)
    {is it : ℕ} {j : ℕ} (hj : j ∈ tailC hm n c) :
    VG p (res (40 * n) (tpol (entryO hm n c is c it)) j)
      ((6 * delC n c + is + it : ℕ) - ((ellC hm n c : ℚ) - 1)) := by
  have hjc : jc hm j = c := (Finset.mem_filter.mp hj).2
  have hjI := mem_Icc_of_tailC hm n hj
  have hj0 : ¬ (p : ℤ) ∣ (j : ℤ) := fun h => hc0 (hjc ▸ (jc_eq_zero_iff hm j).mpr h)
  have h := VG_res_class hp3 hK (entryO hm n c is c it) hjI hj0
  rw [den_count hm n hjI hjc] at h
  refine h.mono ?_
  have h1 := num_count hm n hc0 (is := is) (it := it) hjc
  have h2 := ellC_pos hm n hjI hjc
  push_cast [h2]
  have : ((6 * delC n c + is + it : ℕ) : ℚ) ≤ ((entryO hm n c is c it).filter fun γ : ℤ =>
      ((γ : ZMod p)) ^ 2 = ((j : ℤ) : ZMod p) ^ 2).card := by exact_mod_cast h1
  push_cast at this
  linarith

/-- **Case (a)**: both rows below `nb`. -/
lemma pole_case_a (hp3 : 3 ≤ p) (hK : 2 * (40 * n) < p ^ 2) {c : Fin (m + 1)} (hc0 : c ≠ 0)
    {is it : ℕ} (his : is < nbC hm n c) (hit : it < nbC hm n c) :
    GV p (∑ j ∈ tailC hm n c, C (res (40 * n) (tpol (entryO hm n c is c it)) j) * poleValue j)
      (wO hm n c is + wO hm n c it) := by
  refine GV.sum _ fun j hj => ?_
  have hjI := mem_Icc_of_tailC hm n hj
  have hjI' := Finset.mem_Icc.mp hjI
  have hPV := GV_poleValue_sq hp3 hjI'.1 (by nlinarith)
  refine (GV.C_mul (VG_res_entry hm n hp3 hK hc0 hj) hPV).mono ?_
  unfold wO
  rw [if_neg hc0, if_neg hc0, if_pos his, if_pos hit]
  have e1 := min_le_right (0 : ℚ) ((is : ℚ) + 3 * delC n c - ((ellC hm n c : ℚ) + 4) / 2)
  have e2 := min_le_right (0 : ℚ) ((it : ℚ) + 3 * delC n c - ((ellC hm n c : ℚ) + 4) / 2)
  push_cast
  linarith

lemma count_rootsO_zero (i : ℕ) :
    i ≤ ((rootsO hm n 0 i).filter fun γ : ℤ => (p : ℤ) ∣ γ).card := by
  unfold rootsO
  rw [Multiset.filter_add, Multiset.card_add]
  have hz : (p : ℤ) ∣ (((0 : Fin (m + 1)) : ℕ) : ℤ) := by simp
  split_ifs with h
  · rw [card_filter_replicate, if_pos hz]; omega
  · rw [Multiset.filter_add, Multiset.card_add, card_filter_replicate, if_pos hz]
    have hbig : ((bigC hm n 0).val.map fun j : ℕ => (j : ℤ)).filter (fun γ : ℤ => (p : ℤ) ∣ γ) =
        (bigC hm n 0).val.map fun j : ℕ => (j : ℤ) := by
      refine Multiset.filter_eq_self.mpr fun γ hγ => ?_
      obtain ⟨j, hj, rfl⟩ := Multiset.mem_map.mp hγ
      have hj' : j ∈ bigC hm n 0 := Finset.mem_val.mp hj
      exact (jc_eq_zero_iff hm j).mp (Finset.mem_filter.mp (Finset.mem_filter.mp hj').1).2
    rw [hbig, Multiset.card_map, Finset.card_val]
    have : nbC hm n 0 = (bigC hm n 0).card := rfl
    omega

/-- Multiples of `p` up to `K` are `p` and the big zero-class poles. -/
lemma mult_count (hpN : 3 * n < p) :
    ((Icc 1 (40 * n)).filter fun i : ℕ => (p : ℤ) ∣ (i : ℤ)).card ≤ nbC hm n 0 + 1 := by
  have hsub : ((Icc 1 (40 * n)).filter fun i : ℕ => (p : ℤ) ∣ (i : ℤ)) ⊆ insert p (bigC hm n 0) := by
    intro i hi
    rw [Finset.mem_filter, Finset.mem_Icc] at hi
    rw [Finset.mem_insert]
    by_cases hip : i ≤ p
    · left
      have hd : p ∣ i := by exact_mod_cast hi.2
      have := Nat.le_of_dvd (by omega) hd
      omega
    · right
      refine Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨?_, (jc_eq_zero_iff hm i).mpr hi.2⟩, by omega⟩
      unfold tailO; exact Finset.mem_Icc.mpr ⟨by omega, hi.1.2⟩
  have := Finset.card_le_card hsub
  have h2 := Finset.card_insert_le p (bigC hm n 0)
  have : nbC hm n 0 = (bigC hm n 0).card := rfl
  omega

lemma nbC_zero_le (hK3 : 40 * n < 3 * p) : nbC hm n 0 ≤ 1 := by
  have hsub : bigC hm n 0 ⊆ {2 * p} := by
    intro j hj
    have h1 := Finset.mem_filter.mp hj
    have h2 := Finset.mem_filter.mp h1.1
    have h3 := Finset.mem_Icc.mp h2.1
    have hd : p ∣ j := by exact_mod_cast (jc_eq_zero_iff hm j).mp h2.2
    obtain ⟨k, rfl⟩ := hd
    have hk1 : 1 < k := by
      by_contra h; rw [not_lt] at h; interval_cases k <;> omega
    have hk3 : k < 3 := by
      by_contra h; rw [not_lt] at h
      have : p * 3 ≤ p * k := Nat.mul_le_mul_left _ h
      omega
    rw [Finset.mem_singleton]
    interval_cases k; ring
  have := Finset.card_le_card hsub
  rw [Finset.card_singleton] at this
  exact this

/-- **Zero class.** -/
lemma pole_case_zero (hp7 : 7 ≤ p) (hK3 : 40 * n < 3 * p) (hK : 2 * (40 * n) < p ^ 2)
    (hpN : 3 * n < p) (is it : ℕ) :
    GV p (∑ j ∈ tailC hm n 0, C (res (40 * n) (tpol (entryO hm n 0 is 0 it)) j) * poleValue j)
      (wO hm n 0 is + wO hm n 0 it) := by
  have hnb := nbC_zero_le hm n hK3
  refine GV.sum _ fun j hj => ?_
  have hjI := mem_Icc_of_tailC hm n hj
  have hjI' := Finset.mem_Icc.mp hjI
  have hjc : jc hm j = 0 := (Finset.mem_filter.mp hj).2
  have hpj : (p : ℤ) ∣ (j : ℤ) := (jc_eq_zero_iff hm j).mp hjc
  obtain ⟨k, hk⟩ : ∃ k, j = p * k := by exact_mod_cast hpj
  have hk1 : 1 ≤ k := by
    rcases Nat.eq_zero_or_pos k with h | h
    · subst h; simp at hk; omega
    · exact h
  have hkp : k < p := by
    by_contra h; rw [not_lt] at h
    have : p * p ≤ p * k := Nat.mul_le_mul_left _ h
    nlinarith
  have hPV : GV p (poleValue j) (-1) := by rw [hk]; exact GV_poleValue_mul (by omega) hk1 hkp
  -- residue bound
  have hden : ∏ i ∈ (Icc 1 (40 * n)).erase j, ((i : ℚ) ^ 2 - (j : ℚ) ^ 2) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun i hi => sq_ne_of_ne (Finset.mem_erase.mp hi).1
  have hnum := VG_prod_sq_sub_zero (p := p) (entryO hm n 0 is 0 it) hpj
  have hdv := VG.inv (p := p) hden (padicValRat_den_zero_le hjI hK hpj)
  have hres : VG p (res (40 * n) (tpol (entryO hm n 0 is 0 it)) j)
      (2 * (is + it : ℚ) - 2 * nbC hm n 0) := by
    rw [res_tpol hjI, div_eq_mul_inv]
    refine (hnum.mul hdv).mono ?_
    have hc1 : (is + it : ℕ) ≤ ((entryO hm n 0 is 0 it).filter fun γ : ℤ => (p : ℤ) ∣ γ).card := by
      unfold entryO
      rw [Multiset.filter_add, Multiset.filter_add, Multiset.card_add, Multiset.card_add]
      have := count_rootsO_zero hm n is
      have := count_rootsO_zero hm n it
      omega
    have hc2 : (((Icc 1 (40 * n)).erase j).filter fun i : ℕ => (p : ℤ) ∣ (i : ℤ)).card ≤
        nbC hm n 0 := by
      have h1 := mult_count hm n hpN
      rw [Finset.filter_erase] at *
      rw [Finset.card_erase_of_mem (Finset.mem_filter.mpr ⟨hjI, hpj⟩)]
      omega
    have e1 : ((is + it : ℕ) : ℚ) ≤ (((entryO hm n 0 is 0 it).filter fun γ : ℤ => (p : ℤ) ∣ γ).card : ℚ) := by
      exact_mod_cast hc1
    have e2 : ((((Icc 1 (40 * n)).erase j).filter fun i : ℕ => (p : ℤ) ∣ (i : ℤ)).card : ℚ) ≤
        nbC hm n 0 := by exact_mod_cast hc2
    push_cast at e1 ⊢
    linarith
  refine (GV.C_mul hres hPV).mono ?_
  unfold wO
  rw [if_pos rfl, if_pos rfl]
  interval_cases h : nbC hm n 0
  · simp
    norm_num
    have : (0 : ℚ) ≤ is := by positivity
    have : (0 : ℚ) ≤ it := by positivity
    linarith
  · by_cases h1 : is < 1 <;> by_cases h2 : it < 1
    · rw [if_pos h1, if_pos h2]; push_cast; have : is = 0 := by omega
      have : it = 0 := by omega
      subst_vars; norm_num
    · rw [if_pos h1, if_neg h2, if_neg (by norm_num)]
      have : (1 : ℚ) ≤ it := by exact_mod_cast (by omega : 1 ≤ it)
      have : (0 : ℚ) ≤ is := by positivity
      push_cast; linarith
    · rw [if_neg h1, if_pos h2, if_neg (by norm_num)]
      have : (1 : ℚ) ≤ is := by exact_mod_cast (by omega : 1 ≤ is)
      have : (0 : ℚ) ≤ it := by positivity
      push_cast; linarith
    · rw [if_neg h1, if_neg h2, if_neg (by norm_num)]
      have : (1 : ℚ) ≤ is := by exact_mod_cast (by omega : 1 ≤ is)
      have : (1 : ℚ) ≤ it := by exact_mod_cast (by omega : 1 ≤ it)
      push_cast; linarith


lemma jc_small {i : ℕ} (hi : i < p) :
    ((jc hm i : ℕ) = i ∧ i ≤ m) ∨ ((jc hm i : ℕ) = p - i ∧ m < i) := by
  have hv : (((i : ℤ) : ZMod p)).val = i := by
    rw [Int.cast_natCast, ZMod.val_natCast, Nat.mod_eq_of_lt hi]
  unfold jc ccls
  split_ifs with h
  · left; rw [hv] at h; exact ⟨by simp [Nat.mod_eq_of_lt hi], h⟩
  · right; rw [hv] at h; exact ⟨by simp [Nat.mod_eq_of_lt hi], by omega⟩

lemma jc_small_eq {c : Fin (m + 1)} {i : ℕ} (hi : i < p) (h : jc hm i = c) :
    i = c ∨ i = p - c := by
  have hc := c.isLt
  rcases jc_small hm hi with ⟨h1, _⟩ | ⟨h1, _⟩ <;> rw [h] at h1 <;> omega

/-- Class members up to `K`: the big ones plus at most the two small ones. -/
lemma ellC_le (hpN : 3 * n < p) {c : Fin (m + 1)} (hc0 : c ≠ 0) :
    ellC hm n c ≤ nbC hm n c + ((Icc 1 (40 * n)).filter fun i => jc hm i = c ∧ i < p).card := by
  have hsub : ((Icc 1 (40 * n)).filter fun j => jc hm j = c) ⊆
      bigC hm n c ∪ ((Icc 1 (40 * n)).filter fun i => jc hm i = c ∧ i < p) := by
    intro i hi
    obtain ⟨hiI, hic⟩ := Finset.mem_filter.mp hi
    have hiI' := Finset.mem_Icc.mp hiI
    rw [Finset.mem_union]
    by_cases hip : i < p
    · right; exact Finset.mem_filter.mpr ⟨hiI, hic, hip⟩
    · left
      have hne : i ≠ p := by
        intro hh; rw [hh] at hic
        exact hc0 (hic ▸ (jc_eq_zero_iff hm p).mpr dvd_rfl)
      refine Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨?_, hic⟩, by omega⟩
      unfold tailO; exact Finset.mem_Icc.mpr ⟨by omega, hiI'.2⟩
  have := Finset.card_le_card hsub
  have := Finset.card_union_le (bigC hm n c) ((Icc 1 (40 * n)).filter fun i => jc hm i = c ∧ i < p)
  unfold ellC nbC
  omega

lemma small_sub {c : Fin (m + 1)} :
    ((Icc 1 (40 * n)).filter fun i => jc hm i = c ∧ i < p) ⊆ {(c : ℕ), p - c} := by
  intro i hi
  obtain ⟨_, hic, hip⟩ := Finset.mem_filter.mp hi
  rcases jc_small_eq hm hip hic with h | h <;> simp [h]

lemma small_card_le {c : Fin (m + 1)} :
    ((Icc 1 (40 * n)).filter fun i => jc hm i = c ∧ i < p).card ≤ 2 :=
  (Finset.card_le_card (small_sub hm n)).trans (Finset.card_le_two)

/-- **Case (b)**: one row at or above `nb`; the pole sum is integral. -/
lemma pole_case_b (hp3 : 3 ≤ p) (hK : 2 * (40 * n) < p ^ 2) (hpN : 3 * n < p) {c : Fin (m + 1)}
    (hc0 : c ≠ 0) {is it : ℕ} (his : nbC hm n c ≤ is) :
    GV p (∑ j ∈ tailC hm n c, C (res (40 * n) (tpol (entryO hm n c is c it)) j) * poleValue j) 0 := by
  have hcm := c.isLt
  have hc1 : 1 ≤ (c : ℕ) := by
    rcases Nat.eq_zero_or_pos (c : ℕ) with h | h
    · exact absurd (Fin.ext h) hc0
    · exact h
  have hℓ := ellC_le hm n hpN hc0
  have hS2 := small_card_le hm n (c := c)
  set Sm := (Icc 1 (40 * n)).filter fun i => jc hm i = c ∧ i < p with hSm
  -- big poles have zero residue
  have hbig : ∀ j ∈ tailC hm n c, ¬ j < p → res (40 * n) (tpol (entryO hm n c is c it)) j = 0 := by
    intro j hj hjp
    have hjc : jc hm j = c := (Finset.mem_filter.mp hj).2
    have hne : j ≠ p := by
      intro hh; rw [hh] at hjc
      exact hc0 (hjc ▸ (jc_eq_zero_iff hm p).mpr dvd_rfl)
    have hjb : j ∈ bigC hm n c := Finset.mem_filter.mpr ⟨hj, by omega⟩
    exact res_tpol_eq_zero (mem_Icc_of_tailC hm n hj)
      (mem_entryO_left hm n (mem_rootsO_big hm n his hjb)) rfl
  rw [← Finset.sum_filter_add_sum_filter_not _ (fun j => j < p)]
  rw [Finset.sum_eq_zero (s := (tailC hm n c).filter fun j => ¬ j < p) (fun j hj => by
    have := Finset.mem_filter.mp hj
    rw [hbig j this.1 this.2, C_0, zero_mul]), add_zero]
  -- individual small-pole bound
  have hind : ∀ j ∈ (tailC hm n c).filter (fun j => j < p),
      (0 : ℚ) ≤ ((6 * delC n c + is + it : ℕ) : ℚ) - ((ellC hm n c : ℚ) - 1) →
      GV p (C (res (40 * n) (tpol (entryO hm n c is c it)) j) * poleValue j) 0 := by
    intro j hj h0
    have hj' := Finset.mem_filter.mp hj
    have hjI' := Finset.mem_Icc.mp (mem_Icc_of_tailC hm n hj'.1)
    refine (GV.C_mul (VG_res_entry hm n hp3 hK hc0 hj'.1) (GV_poleValue_lt hp3 hjI'.1 hj'.2)).mono ?_
    linarith
  by_cases hδ : delC n c = 1
  · refine GV.sum _ fun j hj => hind j hj ?_
    have : (ellC hm n c : ℚ) ≤ nbC hm n c + 2 := by exact_mod_cast (by omega : ellC hm n c ≤ nbC hm n c + 2)
    have : (nbC hm n c : ℚ) ≤ is := by exact_mod_cast his
    rw [hδ]; push_cast; linarith
  have hcN : 3 * n < (c : ℕ) := by unfold delC at hδ; split_ifs at hδ with h <;> omega
  have hδ0 : delC n c = 0 := by unfold delC; rw [if_neg (by omega)]
  -- small class members all lie in the tail
  have hSmT : Sm ⊆ (tailC hm n c).filter (fun j => j < p) := by
    intro i hi
    obtain ⟨hiI, hic, hip⟩ := Finset.mem_filter.mp hi
    have hiI' := Finset.mem_Icc.mp hiI
    have : 3 * n < i := by rcases jc_small_eq hm hip hic with h | h <;> omega
    have hiT : i ∈ tailO n := by unfold tailO; exact Finset.mem_Icc.mpr ⟨by omega, hiI'.2⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨hiT, hic⟩, hip⟩
  have hTSm : (tailC hm n c).filter (fun j => j < p) ⊆ Sm := by
    intro i hi
    have h1 := Finset.mem_filter.mp hi
    exact Finset.mem_filter.mpr ⟨mem_Icc_of_tailC hm n h1.1, (Finset.mem_filter.mp h1.1).2, h1.2⟩
  have hTeq : (tailC hm n c).filter (fun j => j < p) = Sm := Finset.Subset.antisymm hTSm hSmT
  by_cases hS1 : Sm.card ≤ 1
  · refine GV.sum _ fun j hj => hind j hj ?_
    have : (ellC hm n c : ℚ) ≤ nbC hm n c + 1 := by exact_mod_cast (by omega : ellC hm n c ≤ nbC hm n c + 1)
    have : (nbC hm n c : ℚ) ≤ is := by exact_mod_cast his
    push_cast; linarith
  -- the pair case
  have hSeq : Sm = {(c : ℕ), p - c} :=
    Finset.eq_of_subset_of_card_le (small_sub hm n) ((Finset.card_le_two).trans (by omega))
  have hcne : (c : ℕ) ≠ p - c := by omega
  have hmemc : (c : ℕ) ∈ Sm := by rw [hSeq]; simp
  have hmemb : p - (c : ℕ) ∈ Sm := by rw [hSeq]; simp
  have hcK := (Finset.mem_Icc.mp (Finset.mem_filter.mp hmemc).1).2
  have hbK := (Finset.mem_Icc.mp (Finset.mem_filter.mp hmemb).1).2
  rw [hTeq, hSeq, Finset.sum_pair hcne]
  refine pair_GV hp3 _ hc1 (by omega) hcne hcK hbK ?_ ?_
  · intro i hi hia hib
    have hi' := Finset.mem_Icc.mp hi
    by_cases hiN : i ≤ 3 * n
    · exact mem_entryO_small hm n (Finset.mem_Icc.mpr ⟨hi'.1, hiN⟩)
    have hiT : i ∈ tailO n := by unfold tailO; exact Finset.mem_Icc.mpr ⟨by omega, hi'.2⟩
    by_cases hic : jc hm i = c
    · refine mem_entryO_left hm n (mem_rootsO_big hm n his ?_)
      have hne : i ≠ p := by
        intro hh; rw [hh] at hic
        exact hc0 (hic ▸ (jc_eq_zero_iff hm p).mpr dvd_rfl)
      have hip : ¬ i < p := fun hip => by
        rcases jc_small_eq hm hip hic with h | h
        · exact hia h
        · exact hib h
      exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨hiT, hic⟩, by omega⟩
    · exact mem_entryO_left hm n (mem_rootsO_other hm n hiT hic)
  · have hjb : p - (c : ℕ) ∈ tailC hm n c := (Finset.mem_filter.mp (hSmT hmemb)).1
    refine (VG_res_entry hm n hp3 hK hc0 hjb).mono ?_
    have : (ellC hm n c : ℚ) ≤ nbC hm n c + 2 := by exact_mod_cast (by omega : ellC hm n c ≤ nbC hm n c + 2)
    have : (nbC hm n c : ℚ) ≤ is := by exact_mod_cast his
    push_cast; linarith


lemma entryO_comm (c : Fin (m + 1)) (is it : ℕ) : entryO hm n c is c it = entryO hm n c it c is := by
  unfold entryO; rw [add_right_comm]

/-- **The outer entry theorem.** -/
theorem outer_entry_aux (hp7 : 7 ≤ p) (hK3 : 40 * n < 3 * p) (hK : 2 * (40 * n) < p ^ 2)
    (hpN : 3 * n < p) (cs : Fin (m + 1)) (is : ℕ) (ct : Fin (m + 1)) (it : ℕ) :
    GV p (μX (40 * n) (tpol (entryO hm n cs is ct it)) -
      C (μGe p (tpol (entryO hm n cs is ct it) /ₘ D (40 * n)))) (wO hm n cs is + wO hm n ct it) := by
  have hp3 : 3 ≤ p := by omega
  have hw := add_nonpos (wO_nonpos hm n cs is) (wO_nonpos hm n ct it)
  rw [μX_sub_μGe]
  refine GV.add ((GV.C (VG_μpoly_sub_μGe (by omega) (GV_entry_quot hm n cs is ct it))).mono hw) ?_
  by_cases hc : cs = ct
  · subst hc
    rw [pole_sum_reduce]
    by_cases hc0 : cs = 0
    · subst hc0; exact pole_case_zero hm n hp7 hK3 hK hpN is it
    by_cases his : nbC hm n cs ≤ is
    · exact (pole_case_b hm n hp3 hK hpN hc0 his).mono hw
    by_cases hit : nbC hm n cs ≤ it
    · rw [entryO_comm]; exact (pole_case_b hm n hp3 hK hpN hc0 hit).mono hw
    exact pole_case_a hm n hp3 hK hc0 (by omega) (by omega)
  · rw [pole_sum_cross hm n hc]; exact (GV.zero _).mono hw

end Apery

end Port0

open Finset Polynomial Matrix in
theorem solution {m p : ℕ} [hp : Fact p.Prime] (hm : 2 * m + 1 = p) (n : ℕ)
    (hp7 : 7 ≤ p) (hK3 : 40 * n < 3 * p) (hK : 2 * (40 * n) < p ^ 2)
    (hpN : 3 * n < p) (cs : Fin (m + 1)) (is : ℕ) (ct : Fin (m + 1)) (it : ℕ) :
    Apery.GV p (Apery.μX (40 * n) (Apery.tpol (Apery.entryO hm n cs is ct it)) -
      C (Apery.μGe p (Apery.tpol (Apery.entryO hm n cs is ct it) /ₘ Apery.D (40 * n))))
      (Apery.wO hm n cs is + Apery.wO hm n ct it) :=
  Apery.outer_entry_aux hm n hp7 hK3 hK hpN cs is ct it

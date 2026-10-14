-- Prove2me | solution 1 for Apery.pair_GV
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-10-12T21:47:12.34089+00:00
-- url     : https://prove2.me/submissions/6563d509-a0bc-4144-8812-b6327c23683e

/-
# The pairing lemma: two remaining poles $a, p-a$ give an integral contribution
(source `Apery/Arith/OuterEntries.lean`)

For a multiset $M$ of roots containing all $i \\in [1,K]$ with $i \\ne a, p-a$, if the residue
$\\mathrm{res}\\,K\\,(tpol\\,M)\\,(p-a)$ has valuation $\\ge -1$, then the pair contribution
$\\mathrm{res}_a \\mathrm{poleValue}\\,a + \\mathrm{res}_{p-a} \\mathrm{poleValue}\\,(p-a)$ is
$p$-integral. The file ports `Apery/Arith/OuterEntry.lean` (the general residue lemmas
`eval_tpol`, `res_tpol`, `VG_prod_sq_sub`, the denominators `padicValRat_den_le`) and
`Apery/Arith/OuterEntries.lean` (memberships, root counts, zero-class valuations, the
congruence `GV_poleValue_congr` and the theorem), together with the valuation helpers of
`Apery/Degree.lean`, `Apery/Arith/DirectBound.lean`, `Apery/Arith/PoleVal.lean`,
`Apery/Arith/IntPoly.lean`, `Apery/Arith/ClassCount.lean` and `Apery/Arith/ClassFrame.lean`,
faithful to mo271/Zeta5 @ 7fe736760f4b96bfdb4334b68e3b3124ecbe10b0.
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


/-!
# Outer range: entry bounds

Helper lemmas (memberships, root counts, zero-class valuations).
-/

open Finset Polynomial


variable {p : ℕ} [hp : Fact p.Prime] {m : ℕ}

variable (hm : 2 * m + 1 = p) (n : ℕ)

lemma mem_entryO_small {cs ct : Fin (m + 1)} {is it : ℕ} {k : ℕ} (hk : k ∈ Icc 1 (3 * n)) :
    (k : ℤ) ∈ entryO hm n cs is ct it := by
  unfold entryO
  refine Multiset.mem_add.mpr (Or.inl (Multiset.mem_add.mpr (Or.inl ?_)))
  rw [Multiset.mem_nsmul_of_ne_zero (by norm_num)]
  exact Multiset.mem_map.mpr ⟨k, hk, rfl⟩

lemma mem_rootsO_other {c : Fin (m + 1)} {i j : ℕ} (hj : j ∈ tailO n) (hc : jc hm j ≠ c) :
    (j : ℤ) ∈ rootsO hm n c i := by
  unfold rootsO
  refine Multiset.mem_add.mpr (Or.inl (Multiset.mem_map.mpr ⟨j, ?_, rfl⟩))
  exact Finset.mem_val.mpr (Finset.mem_filter.mpr ⟨hj, hc⟩)

lemma mem_rootsO_big {c : Fin (m + 1)} {i j : ℕ} (hi : nbC hm n c ≤ i) (hj : j ∈ bigC hm n c) :
    (j : ℤ) ∈ rootsO hm n c i := by
  unfold rootsO
  rw [if_neg (by omega)]
  refine Multiset.mem_add.mpr (Or.inr (Multiset.mem_add.mpr (Or.inl ?_)))
  exact Multiset.mem_map.mpr ⟨j, Finset.mem_val.mpr hj, rfl⟩

lemma mem_entryO_left {cs ct : Fin (m + 1)} {is it : ℕ} {γ : ℤ} (h : γ ∈ rootsO hm n cs is) :
    γ ∈ entryO hm n cs is ct it := by
  unfold entryO
  exact Multiset.mem_add.mpr (Or.inl (Multiset.mem_add.mpr (Or.inr h)))

lemma mem_entryO_right {cs ct : Fin (m + 1)} {is it : ℕ} {γ : ℤ} (h : γ ∈ rootsO hm n ct it) :
    γ ∈ entryO hm n cs is ct it := by
  unfold entryO
  exact Multiset.mem_add.mpr (Or.inr h)

/-- Count of roots in the class of `c` in a row of class `c`. -/
lemma count_rootsO (c : Fin (m + 1)) (i : ℕ) (x : ZMod p)
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

/-- The valuation of `∏ (γ² - j²)` for `p ∣ j`: two per root divisible by `p`. -/
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

/-- Denominator for `p ∣ j`: at most two per other multiple of `p`. -/
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

/-- Residue bound for a nonzero class. -/
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

/-- Divided differences of integral polynomials are integral. -/
lemma eval_sub_eval_int {S : ℚ[X]} (hS : GV p S 0) {u v : ℚ} (hu : VG p u 0) (hv : VG p v 0) :
    ∃ T : ℚ, S.eval u - S.eval v = (u - v) * T ∧ VG p T 0 := by
  refine ⟨∑ k ∈ range (S.natDegree + 1), S.coeff k * ∑ i ∈ range k, u ^ i * v ^ (k - 1 - i), ?_, ?_⟩
  · rw [eval_eq_sum_range, eval_eq_sum_range, ← Finset.sum_sub_distrib, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    have := Commute.geom_sum₂_mul (Commute.all u v) k
    rw [← mul_sub, ← this]; ring
  · refine VG.sum _ fun k _ => ?_
    have : VG p (∑ i ∈ range k, u ^ i * v ^ (k - 1 - i)) 0 :=
      VG.sum _ fun i _ => by simpa using (hu.pow i).mul (hv.pow (k - 1 - i))
    simpa using (hS k).mul this

lemma GV_tpol (M : Multiset ℤ) : GV p (tpol M) 0 := by
  rw [← tpolZ_map_Q]; intro k; rw [coeff_map]; exact VG.intCast _

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

/-- **The pairing lemma**: two remaining poles `a, p - a` give an integral contribution. -/
theorem pair_GV_aux (hp3 : 3 ≤ p) {K : ℕ} (M : Multiset ℤ) {a : ℕ} (ha1 : 1 ≤ a) (hap : a < p)
    (hne : a ≠ p - a) (haK : a ≤ K) (hbK : p - a ≤ K)
    (hroots : ∀ i ∈ Icc 1 K, i ≠ a → i ≠ p - a → (i : ℤ) ∈ M)
    (hres : VG p (res K (tpol M) (p - a)) (-1)) :
    GV p (C (res K (tpol M) a) * poleValue a + C (res K (tpol M) (p - a)) * poleValue (p - a)) 0 := by
  set b := p - a with hb
  set W := ((Icc 1 K).erase a).erase b with hW
  set ρ : ℕ → ℚ := fun i => -(i : ℚ) ^ 2 with hρ
  have hinj : Set.InjOn ρ W := by
    intro i _ j _ h
    simp only [hρ, neg_inj] at h
    have := (sq_ne_of_ne (i := i) (j := j))
    by_contra hij; exact this hij (by rw [h]; ring)
  have hroot : ∀ x ∈ W.image ρ, (tpol M).eval x = 0 := by
    intro x hx
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
    have hi' := Finset.mem_erase.mp hi
    have hi'' := Finset.mem_erase.mp hi'.2
    rw [eval_tpol]
    apply Multiset.prod_eq_zero
    exact Multiset.mem_map.mpr ⟨i, hroots i hi''.2 hi''.1 hi'.1, by simp [hρ]⟩
  have hsqv : ∀ i : ℕ, VG p (-(i : ℚ) ^ 2) 0 := fun i => by
    have := (VG.natCast (p := p) (i ^ 2)).neg; push_cast at this; exact this
  obtain ⟨S, hS, hNum⟩ := factor_roots (W.image ρ) (fun x hx => by
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
    exact hsqv i) (GV_tpol M) hroot
  rw [Finset.prod_image hinj] at hNum
  have haIcc : a ∈ Icc 1 K := Finset.mem_Icc.mpr ⟨ha1, haK⟩
  have hbIcc : b ∈ Icc 1 K := Finset.mem_Icc.mpr ⟨by omega, hbK⟩
  have hPW : ∀ j : ℕ, j ∉ W → ∏ i ∈ W, ((i : ℚ) ^ 2 - (j : ℚ) ^ 2) ≠ 0 → True := fun _ _ _ => trivial
  have hWne : ∀ j, j = a ∨ j = b → ∏ i ∈ W, ((i : ℚ) ^ 2 - (j : ℚ) ^ 2) ≠ 0 := by
    intro j hj
    refine Finset.prod_ne_zero_iff.mpr fun i hi => sq_ne_of_ne ?_
    have hi' := Finset.mem_erase.mp hi
    have hi'' := Finset.mem_erase.mp hi'.2
    rcases hj with rfl | rfl
    · exact hi''.1
    · exact hi'.1
  have hNumEval : ∀ j : ℕ, (tpol M).eval (-(j : ℚ) ^ 2) =
      (∏ i ∈ W, ((i : ℚ) ^ 2 - (j : ℚ) ^ 2)) * S.eval (-(j : ℚ) ^ 2) := by
    intro j
    rw [hNum, eval_mul, eval_prod]
    congr 1
    refine Finset.prod_congr rfl fun i _ => ?_
    simp [hρ]; ring
  have hEa : (Icc 1 K).erase a = insert b W := by
    rw [hW, Finset.insert_erase (Finset.mem_erase.mpr ⟨Ne.symm hne, hbIcc⟩)]
  have hEb : (Icc 1 K).erase b = insert a W := by
    rw [hW, Finset.erase_right_comm, Finset.insert_erase (Finset.mem_erase.mpr ⟨hne, haIcc⟩)]
  have hbW : b ∉ W := by simp [hW]
  have haW : a ∉ W := by simp [hW]
  have hres_a : res K (tpol M) a = S.eval (-(a : ℚ) ^ 2) / ((b : ℚ) ^ 2 - (a : ℚ) ^ 2) := by
    unfold res
    rw [eval_derivative_D haIcc, hEa, Finset.prod_insert hbW, hNumEval]
    field_simp [hWne a (Or.inl rfl), sq_ne_of_ne (Ne.symm hne)]
  have hres_b : res K (tpol M) b = S.eval (-(b : ℚ) ^ 2) / ((a : ℚ) ^ 2 - (b : ℚ) ^ 2) := by
    unfold res
    rw [eval_derivative_D hbIcc, hEb, Finset.prod_insert haW, hNumEval]
    field_simp [hWne b (Or.inr rfl), sq_ne_of_ne hne]
  obtain ⟨T, hT, hTv⟩ := eval_sub_eval_int hS (u := -(a : ℚ) ^ 2) (v := -(b : ℚ) ^ 2)
    (hsqv a) (hsqv b)
  have hsum : res K (tpol M) a + res K (tpol M) b = T := by
    rw [hres_a, hres_b]
    have hab : (b : ℚ) ^ 2 - (a : ℚ) ^ 2 ≠ 0 := sq_ne_of_ne (Ne.symm hne)
    have hba : (a : ℚ) ^ 2 - (b : ℚ) ^ 2 ≠ 0 := sq_ne_of_ne hne
    have key : S.eval (-(a : ℚ) ^ 2) - S.eval (-(b : ℚ) ^ 2) = ((b : ℚ) ^ 2 - (a : ℚ) ^ 2) * T := by
      rw [hT]; ring
    rw [div_add_div _ _ hab hba, div_eq_iff (mul_ne_zero hab hba)]
    linear_combination ((a : ℚ) ^ 2 - (b : ℚ) ^ 2) * key
  have hsplit : C (res K (tpol M) a) * poleValue a + C (res K (tpol M) b) * poleValue b =
      C T * poleValue a + C (res K (tpol M) b) * (poleValue b - poleValue a) := by
    rw [← hsum, C_add]; ring
  rw [hsplit]
  have hPa := GV_poleValue_lt hp3 ha1 hap
  have hcong := GV_poleValue_congr hp3 ha1 hap
  exact ((GV.C_mul hTv hPa).mono (by norm_num)).add ((GV.C_mul hres hcong).mono (by norm_num))
end Apery

end Port0

open Finset Polynomial Matrix in
theorem solution {p : ℕ} [hp : Fact p.Prime] (hp3 : 3 ≤ p) {K : ℕ} (M : Multiset ℤ) {a : ℕ}
    (ha1 : 1 ≤ a) (hap : a < p) (hne : a ≠ p - a) (haK : a ≤ K) (hbK : p - a ≤ K)
    (hroots : ∀ i ∈ Icc 1 K, i ≠ a → i ≠ p - a → (i : ℤ) ∈ M)
    (hres : Apery.VG p (Apery.res K (Apery.tpol M) (p - a)) (-1)) :
    Apery.GV p (C (Apery.res K (Apery.tpol M) a) * Apery.poleValue a +
      C (Apery.res K (Apery.tpol M) (p - a)) * Apery.poleValue (p - a)) 0 :=
  Apery.pair_GV_aux hp3 M ha1 hap hne haK hbK hroots hres

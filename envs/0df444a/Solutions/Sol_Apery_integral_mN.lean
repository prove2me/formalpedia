-- Prove2me | solution 1 for Apery.integral_mN
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-10-12T19:14:09.479945+00:00
-- url     : https://prove2.me/submissions/f8245f18-8131-422e-8c3f-4a8e735b0471

/-
# Integrality of the normaliser: `Apery.integral_mN` (source `Apery/Norm.lean`)

For every $n \ge 1$ the normaliser $m_K = \prod_{p \le 2h} p^{-L_p}$ times the Hankel
determinant $F_K$ has integer coefficients, i.e. $m_K F_K \in \mathbb{Z}[X]$. The proof
follows `Apery/Norm.lean`: every prime $p$ gets a local exponent $L_p$, valid because

* for small primes, $v_p^G(F_K) \ge L_p$ is the small-prime bound (3.12)
  (`Apery.small_prime_bound`);
* in the inner range the water-filling allocation gives `Apery.inner_bound_cap`;
* in the outer range the outer weights give `Apery.outer_bound`;
* for large primes the Legendre formula (5.3) makes `S_K` a unit.

The three bounds are imported as *child* theorems, so this is a reduction of
`Apery.integral_mN` to them. Faithful port of mo271/Zeta5 @
7fe736760f4b96bfdb4334b68e3b3124ecbe10b0, `Apery/Norm.lean` (with the local helper lemmas
`vS_eq` of `Apery/Legendre.lean`, `mem_PlK_iff`, `ccls_spec`/`ccls_eq_zero_iff`/
`jc_eq_zero_iff` and `padicValRat_finset_prod`).
-/

import Mathlib
import Definitions.Def_Zeta5_SourceConstruction
import Definitions.Def_Zeta5_SourceNorm
import Definitions.Def_Zeta5_SourceArith
import Definitions.Def_Zeta5_SourceGrowthTables
import Definitions.Def_Zeta5_SourceValToolkit
import Theorems.Thm_Apery_small_prime_bound
import Theorems.Thm_Apery_inner_bound_cap
import Theorems.Thm_Apery_outer_bound

set_option autoImplicit false

section Port0

set_option autoImplicit false

open Polynomial Finset

namespace Apery

variable {p : ℕ} [hp : Fact p.Prime] {m : ℕ}

structure InnerData where
  n : ℕ
  M : ℕ
  p : ℕ

namespace InnerData

variable (D : InnerData)

/-- `v_p(S_K)`. -/
noncomputable def vS : ℤ := padicValRat D.p (S D.n)

end InnerData

lemma padicValNat_finset_prod (p : ℕ) [hp : Fact p.Prime] {ι : Type*} (s : Finset ι) (f : ι → ℕ)
    (hf : ∀ i ∈ s, f i ≠ 0) :
    padicValNat p (∏ i ∈ s, f i) = ∑ i ∈ s, padicValNat p (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha, padicValNat.mul (hf a (Finset.mem_insert_self _ _))
      (Finset.prod_ne_zero_iff.mpr fun i hi => hf i (Finset.mem_insert_of_mem hi)),
      ih fun i hi => hf i (Finset.mem_insert_of_mem hi)]

lemma S_eq_div (n : ℕ) :
    S n = (((40 * n).factorial ^ (2 * (37 * n)) * 4 ^ (37 * n - 1) : ℕ) : ℚ) /
      (((3 * n).factorial ^ (12 * (37 * n)) * ∏ i ∈ Icc 1 (37 * n - 1), (2 * i).factorial ^ 2 : ℕ) : ℚ) := by
  unfold S
  push_cast
  ring

theorem vS_eq {n : ℕ} (hn : 0 < n) {p : ℕ} (hp : p.Prime) :
    (InnerData.mk n 200 p).vS =
      2 * (37 * n : ℤ) * padicValNat p (40 * n).factorial -
        12 * (37 * n : ℤ) * padicValNat p (3 * n).factorial -
        2 * ∑ i ∈ Icc 1 (37 * n - 1), (padicValNat p (2 * i).factorial : ℤ) +
        ((37 * n : ℤ) - 1) * padicValNat p 4 := by
  have := Fact.mk hp
  unfold InnerData.vS
  rw [S_eq_div]
  have hA : (((40 * n).factorial ^ (2 * (37 * n)) * 4 ^ (37 * n - 1) : ℕ) : ℚ) ≠ 0 := by
    norm_cast; positivity
  have hB : (((3 * n).factorial ^ (12 * (37 * n)) *
      ∏ i ∈ Icc 1 (37 * n - 1), (2 * i).factorial ^ 2 : ℕ) : ℚ) ≠ 0 := by
    norm_cast
    apply mul_ne_zero (by positivity)
    exact Finset.prod_ne_zero_iff.mpr fun i _ => by positivity
  rw [padicValRat.div hA hB, ← padicValRat_of_nat, ← padicValRat_of_nat,
    padicValNat.mul (by positivity) (by positivity),
    padicValNat.mul (by positivity) (Finset.prod_ne_zero_iff.mpr fun i _ => by positivity),
    padicValNat.pow, padicValNat.pow, padicValNat.pow,
    padicValNat_finset_prod p _ _ (fun i _ => by positivity)]
  simp only [padicValNat.pow]
  push_cast
  rw [Nat.cast_sub (by omega : 1 ≤ 37 * n)]
  push_cast
  simp only [Finset.mul_sum]
  ring

lemma mem_PlK_iff {K : ℕ} {r : ℤ} (hr : r ∈ PlK K) :
    ∃ j ∈ Icc 1 K, ∃ ε : ℤ, (ε = 1 ∨ ε = -1) ∧ r = ε * j := by
  simp only [PlK, Finset.mem_union, Finset.mem_image] at hr
  rcases hr with ⟨j, hj, rfl⟩ | ⟨j, hj, rfl⟩
  · exact ⟨j, hj, 1, Or.inl rfl, by ring⟩
  · exact ⟨j, hj, -1, Or.inr rfl, by ring⟩

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

lemma jc_eq_zero_iff (hm : 2 * m + 1 = p) (j : ℕ) : jc hm j = 0 ↔ (p : ℤ) ∣ (j : ℤ) := by
  unfold jc; rw [ccls_eq_zero_iff, ZMod.intCast_zmod_eq_zero_iff_dvd]

lemma padicValRat_finset_prod {ι : Type*} (s : Finset ι) (f : ι → ℚ) (hf : ∀ i ∈ s, f i ≠ 0) :
    padicValRat p (∏ i ∈ s, f i) = ∑ i ∈ s, padicValRat p (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha, padicValRat.mul (hf a (mem_insert_self _ _))
      (Finset.prod_ne_zero_iff.mpr fun i hi => hf i (mem_insert_of_mem hi)),
      ih fun i hi => hf i (mem_insert_of_mem hi)]

lemma mN_pos (n : ℕ) : 0 < mN n := by
  unfold mN
  apply Finset.prod_pos
  intro p hp
  have : 0 < p := (Finset.mem_filter.mp hp).2.pos
  exact zpow_pos (by exact_mod_cast this) _

/-! ### Validity of the local exponents -/

lemma Sep_PlK {K : ℕ} (hK : 2 * K < p ^ 2) : Sep p (PlK K) := by
  intro r hr s hs hrs _ hdvd
  obtain ⟨j, hj, ε, hε, rfl⟩ := mem_PlK_iff hr
  obtain ⟨j', hj', ε', hε', rfl⟩ := mem_PlK_iff hs
  have h1 := Finset.mem_Icc.mp hj
  have h2 := Finset.mem_Icc.mp hj'
  have hlt : |ε * (j : ℤ) - ε' * j'| < (p : ℤ) ^ 2 := by
    rcases hε with rfl | rfl <;> rcases hε' with rfl | rfl <;> rw [abs_lt] <;> constructor <;>
      push_cast <;> nlinarith
  have := Int.eq_zero_of_abs_lt_dvd hdvd hlt
  exact hrs (by linarith)

lemma GV_F_of_Δ {n : ℕ} {r : ℚ} (h : GV p (Δ n) r) : GV p (F n) ((vSK n p : ℚ) + r) := by
  unfold F
  have hS : VG p (S n) (vSK n p) := by
    unfold vSK; right; exact le_refl _
  exact GV.C_mul hS h

lemma GV_F_Lsmall {n : ℕ} (hn : 1 ≤ n) : GV p (F n) (Lsmall n p) := by
  have := small_prime_bound (p := p) hn
  have e : ((Lsmall n p : ℤ) : ℚ) = -(6 * ((37 * n : ℕ) : ℚ) * (Nat.log p (200 * n) : ℚ) +
      ((37 * n : ℕ) : ℚ) * (padicValNat p 24 : ℚ)) := by
    simp only [Lsmall, Int.cast_neg, Int.cast_add, Int.cast_mul, Int.cast_natCast, Int.cast_ofNat]
  rw [e]; exact this

lemma GV_F_inner {n : ℕ} (h : InnerOK n p) : GV p (F n) (vSK n p + ⌊2 * WI n p⌋) := by
  obtain ⟨hm, hm1, hp5, hsep, hK, hdeg, hsum, hZ⟩ := h
  have hΔ := inner_bound_cap hp5 hm hm1 n (allocI n p (p / 2)) hsum hsep hK hdeg hZ
  have hW : WI n p = ∑ s, wcap hm1 (allocI n p (p / 2)) (Bse p (40 * n) (3 * n)) s := by
    unfold WI; rw [dif_pos hm1]
  rw [← hW] at hΔ
  have := GV_F_of_Δ hΔ
  push_cast
  exact this.mono (by have := Int.floor_le (2 * WI n p); linarith)

lemma GV_F_outer {n : ℕ} (h : OuterOK n p) : GV p (F n) (vSK n p + ⌊WO n p⌋) := by
  obtain ⟨hm, hp7, hK3, hK, hpN⟩ := h
  have hΔ := outer_bound hm n hp7 hK3 hK hpN
  have hW : WO n p = 2 * ∑ c, ∑ i ∈ range (LoC hm n c), wO hm n c i -
      ((37 * n - ((2 * p + 22 * n - 3) - (37 * n - 1)) : ℕ) : ℚ) := by
    unfold WO; rw [dif_pos hp.out, dif_pos hm]
  rw [← hW] at hΔ
  have := GV_F_of_Δ hΔ
  push_cast
  exact this.mono (by have := Int.floor_le (WO n p); linarith)

/-- **Every local exponent is valid.** -/
theorem GV_F_Lp {n : ℕ} (hn : 1 ≤ n) : GV p (F n) (Lp n p) := by
  unfold Lp
  split_ifs with h1 h2 h3 h4
  · exact GV_F_Lsmall hn
  · exact_mod_cast GV_F_inner h3
  · exact GV_F_Lsmall hn
  · exact_mod_cast GV_F_outer h4
  · exact GV_F_Lsmall hn

/-! ### Integrality -/

lemma padicValNat_factorial_lt {k : ℕ} (hk : k < p) : padicValNat p k.factorial = 0 :=
  padicValNat.eq_zero_of_not_dvd (fun h => by
    have := (Nat.Prime.dvd_factorial hp.out).mp h; omega)

lemma vSK_big {n : ℕ} (hn : 1 ≤ n) (hbig : 2 * (37 * n) < p) : vSK n p = 0 := by
  have h := vS_eq (by omega : 0 < n) hp.out
  have e : vSK n p = (InnerData.mk n 200 p).vS := rfl
  rw [e, h, padicValNat_factorial_lt (by omega), padicValNat_factorial_lt (by omega)]
  have h4 : padicValNat p 4 = 0 :=
    padicValNat.eq_zero_of_not_dvd (fun hd => by have := Nat.le_of_dvd (by norm_num) hd; omega)
  rw [h4, Finset.sum_eq_zero (fun i hi => by
    rw [padicValNat_factorial_lt (by have := Finset.mem_Icc.mp hi; omega)]; rfl)]
  simp

lemma OuterOK_big {n : ℕ} (hn : 1 ≤ n) (hbig : 2 * (37 * n) < p) : OuterOK n p := by
  have hodd : 2 * (p / 2) + 1 = p := by
    have := hp.out.eq_one_or_self_of_dvd 2
    rcases Nat.even_or_odd p with ⟨k, hk⟩ | ⟨k, hk⟩
    · have := this ⟨k, by omega⟩; omega
    · omega
  refine ⟨hodd, by omega, by omega, by nlinarith, by omega⟩

lemma WO_big {n : ℕ} (hbig : 2 * (37 * n) < p) : 0 ≤ WO n p := by
  unfold WO
  rw [dif_pos hp.out]
  split_ifs with hm
  · have hsum : ∑ c, ∑ i ∈ range (LoC hm n c), wO hm n c i = 0 := by
      refine Finset.sum_eq_zero fun c _ => Finset.sum_eq_zero fun i hi => ?_
      by_cases hc : c = 0
      · exfalso
        subst hc
        have hL : LoC hm n 0 = 0 := by
          unfold LoC tailC
          rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
          intro j hj hj0
          have hj' := Finset.mem_Icc.mp hj
          have hd : p ∣ j := by exact_mod_cast (jc_eq_zero_iff hm j).mp hj0
          have := Nat.le_of_dvd (by omega) hd
          omega
        rw [hL] at hi; simp at hi
      · have hnb : nbC hm n c = 0 := by
          unfold nbC bigC
          rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
          intro j hj
          have := Finset.mem_Icc.mp (Finset.mem_filter.mp hj).1
          omega
        unfold wO
        rw [if_neg hc, hnb, if_neg (by omega)]
    rw [hsum, show 37 * n - ((2 * p + 22 * n - 3) - (37 * n - 1)) = 0 by omega]
    simp
  · exact le_refl _

lemma GV_F_big {n : ℕ} (hn : 1 ≤ n) (hbig : 2 * (37 * n) < p) : GV p (F n) 0 := by
  have h := GV_F_outer (OuterOK_big hn hbig)
  rw [vSK_big hn hbig] at h
  refine h.mono ?_
  have := WO_big (n := n) hbig
  have h0 : (0 : ℤ) ≤ ⌊WO n p⌋ := Int.floor_nonneg.mpr this
  have h0' : (0 : ℚ) ≤ (⌊WO n p⌋ : ℚ) := by exact_mod_cast h0
  push_cast
  linarith

omit hp in
lemma padicValRat_mN (n : ℕ) (p : ℕ) [Fact p.Prime] :
    padicValRat p (mN n) = if p ≤ 2 * (37 * n) then -Lp n p else 0 := by
  unfold mN
  rw [padicValRat_finset_prod _ _ (fun q hq => by
    have := (Finset.mem_filter.mp hq).2.pos
    exact zpow_ne_zero _ (by exact_mod_cast this.ne'))]
  simp only [padicValRat.zpow, padicValRat.of_nat]
  have hval : ∀ q ∈ (range (2 * (37 * n) + 1)).filter Nat.Prime,
      (padicValNat p q : ℤ) = if q = p then 1 else 0 := by
    intro q hq
    have hq' : q.Prime := (Finset.mem_filter.mp hq).2
    have := Fact.mk hq'
    split_ifs with h
    · subst h; simp [padicValNat.self (Fact.out : q.Prime).one_lt]
    · rw [padicValNat_primes (Ne.symm h)]; rfl
  rw [Finset.sum_congr rfl (fun q hq => by rw [hval q hq])]
  simp only [mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_eq']
  have hpp : (Fact.out : p.Prime) = (Fact.out : p.Prime) := rfl
  by_cases h : p ≤ 2 * (37 * n)
  · rw [if_pos (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), Fact.out⟩), if_pos h]
  · rw [if_neg (fun hm => h (by have := Finset.mem_range.mp (Finset.mem_filter.mp hm).1; omega)),
      if_neg h]

/-- A rational number which is `p`-integral at every prime is an integer. -/
lemma rat_int_of_VG {q : ℚ} (h : ∀ p : ℕ, ∀ _ : Fact p.Prime, VG p q 0) : ∃ z : ℤ, q = z := by
  by_contra hne
  have hden : q.den ≠ 1 := fun h1 => hne ⟨q.num, (Rat.coe_int_num_of_den_eq_one h1).symm⟩
  set p := q.den.minFac with hpdef
  have hpp : p.Prime := Nat.minFac_prime hden
  have := Fact.mk hpp
  have hdvd : p ∣ q.den := Nat.minFac_dvd _
  rcases h p ‹_› with h0 | hv
  · exact hne ⟨0, by simp [h0]⟩
  · have hnum : ¬ (p : ℤ) ∣ q.num := by
      intro hd
      have hc := q.reduced
      have : p ∣ Nat.gcd q.num.natAbs q.den :=
        Nat.dvd_gcd (Int.natCast_dvd.mp hd) hdvd
      rw [hc] at this
      exact hpp.one_lt.ne' (Nat.dvd_one.mp this)
    have h1 : padicValInt p q.num = 0 := padicValInt.eq_zero_of_not_dvd hnum
    have h2 : 1 ≤ padicValNat p q.den := one_le_padicValNat_of_dvd q.den_ne_zero hdvd
    have e : padicValRat p q = padicValInt p q.num - padicValNat p q.den := rfl
    have hlt : padicValRat p q < 0 := by rw [e, h1]; omega
    have : (padicValRat p q : ℚ) < 0 := by exact_mod_cast hlt
    linarith

/-- **Integrality** (Proposition 5.1 for the normaliser `mN`). -/
theorem integral_mN {n : ℕ} (hn : 1 ≤ n) :
    ∃ Q : ℤ[X], Q.map (Int.castRingHom ℚ) = C (mN n) * F n := by
  have hall : ∀ p : ℕ, ∀ _ : Fact p.Prime, GV p (C (mN n) * F n) 0 := by
    intro p _
    have hm : VG p (mN n) (if p ≤ 2 * (37 * n) then -Lp n p else 0 : ℤ) := by
      right; rw [padicValRat_mN]
    by_cases hbig : p ≤ 2 * (37 * n)
    · rw [if_pos hbig] at hm
      have := GV.C_mul hm (GV_F_Lp (p := p) hn)
      refine this.mono ?_
      push_cast; linarith
    · rw [if_neg hbig] at hm
      have := GV.C_mul hm (GV_F_big (p := p) hn (by omega))
      simpa using this
  have hcoef : ∀ k, ∃ z : ℤ, (C (mN n) * F n).coeff k = z := fun k =>
    rat_int_of_VG fun p hp => hall p hp k
  have hlift : C (mN n) * F n ∈ lifts (Int.castRingHom ℚ) := by
    rw [lifts_iff_coeff_lifts]
    intro k
    obtain ⟨z, hz⟩ := hcoef k
    exact ⟨z, by simp [hz]⟩
  obtain ⟨Q, hQ⟩ := hlift
  exact ⟨Q, hQ⟩

end Apery

end Port0

open Polynomial Finset in
/-- The platform target `Apery.integral_mN`, restated at top level as `solution`. -/
theorem solution {n : ℕ} (hn : 1 ≤ n) :
    ∃ Q : ℤ[X], Q.map (Int.castRingHom ℚ) = Polynomial.C (Apery.mN n) * Apery.F n :=
  Apery.integral_mN hn

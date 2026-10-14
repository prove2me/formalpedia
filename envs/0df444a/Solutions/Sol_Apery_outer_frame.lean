-- Prove2me | solution 1 for Apery.outer_frame
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-10-12T21:45:05.303988+00:00
-- url     : https://prove2.me/submissions/abcb94c5-16fc-4344-9f26-2419e64ec31b

/-
# The outer-range framework (source `Apery/Arith/OuterFrame.lean`)

Writing $\\mu = \\mu_{<} + \\mu_{\\ge}$ with $\\mu_{\\ge}$ the moments $\\mu(t^e)$, $e \\ge 2p-3$ (which may
have $v_p = -1$): in any basis the $\\mu_{\\ge}$-part of the Hankel matrix has rank $\\le r$ and is
$p^{-1}$ times an integral product $UV$; with weights $w \\le 0$ on the integral part this gives
$v_p^G(\\Delta) \\ge 2\\sum w - r$. The file ports `Apery/Arith/LowRank.lean`
(`det_lowrank_bound`), `Apery/Arith/MomentVal.lean` (the von Staudt–Clausen bounds for
$\\mu(t^e)$), the `divByMonic` linearity lemmas of `Apery/Arith/BasisChange.lean`, the degree
facts of `Apery/PartialFractions.lean` and the framework of `Apery/Arith/OuterFrame.lean`
verbatim (with `coeffMat_det_unit` and `det_basis_change` imported as platform theorems),
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
import Theorems.Thm_Apery_coeffMat_det_unit
import Theorems.Thm_Apery_det_basis_change

set_option autoImplicit false

section Port0

set_option autoImplicit false

open Finset Polynomial Matrix

namespace Apery

variable {p : ℕ} [hp : Fact p.Prime]

noncomputable def coeffMat {h : ℕ} (E : Fin h → ℚ[X]) : Matrix (Fin h) (Fin h) ℚ :=
  Matrix.of fun a k => (E a).coeff k

lemma coeffMat_det_unit_cm {h : ℕ} {p : ℕ} [hp : Fact p.Prime] {ι : Type*} [Fintype ι]
    [DecidableEq ι] (Ez : Fin h → ℤ[X]) (hdeg : ∀ a, (Ez a).natDegree < h)
    (γ : ι → ZMod p) (hγ : Function.Injective γ) (L : ι → ℕ) (cls : Fin h → ι) (idx : Fin h → ℕ)
    (hidx : ∀ a, idx a < L (cls a)) (hinj : ∀ a b, cls a = cls b → idx a = idx b → a = b)
    (hred : ∀ a, (Ez a).map (Int.castRingHom (ZMod p)) =
      (∏ c ∈ Finset.univ.erase (cls a), (X - C (γ c)) ^ L c) * (X - C (γ (cls a))) ^ idx a) :
    (coeffMat fun a => (Ez a).map (Int.castRingHom ℚ)).det ≠ 0 ∧
      padicValRat p (coeffMat fun a => (Ez a).map (Int.castRingHom ℚ)).det = 0 := by
  simpa only [coeffMat] using
    (coeffMat_det_unit (p := p) Ez hdeg γ hγ L cls idx hidx hinj hred)

lemma det_basis_change_cm (n : ℕ) (E : Fin (37 * n) → ℚ[X])
    (hE : ∀ a, (E a).natDegree < 37 * n) :
    (Matrix.of fun a b => μX (40 * n) (D (3 * n) ^ 6 * E a * E b)).det =
      C ((coeffMat E).det ^ 2) * Δ n := by
  simpa only [coeffMat] using det_basis_change n E hE

lemma tpolZ_map_Q (M : Multiset ℤ) : (tpolZ M).map (Int.castRingHom ℚ) = tpol M := by
  simp [tpolZ, tpol, Polynomial.map_multiset_prod, Multiset.map_map, Function.comp]

lemma natDegree_tpolZ (M : Multiset ℤ) : (tpolZ M).natDegree ≤ M.card := by
  unfold tpolZ
  refine (natDegree_multiset_prod_le _).trans ?_
  rw [Multiset.map_map]
  have : ∀ γ ∈ M, (natDegree ∘ fun γ : ℤ => X + C (γ ^ 2)) γ = 1 := fun γ _ =>
    natDegree_X_add_C _
  rw [Multiset.map_congr rfl this, Multiset.map_const', Multiset.sum_replicate, smul_eq_mul,
    mul_one]

lemma D_eq_tpol (m : ℕ) : D m = tpol ((Icc 1 m).val.map fun j : ℕ => (j : ℤ)) := by
  unfold D tpol
  rw [Multiset.map_map, Finset.prod_eq_multiset_prod]
  congr 1

lemma divByMonic_add' {q : ℚ[X]} (hq : q.Monic) (P Q : ℚ[X]) :
    (P + Q) /ₘ q = P /ₘ q + Q /ₘ q := by
  refine ((div_modByMonic_unique (P /ₘ q + Q /ₘ q) (P %ₘ q + Q %ₘ q) hq ⟨?_, ?_⟩).1)
  · have h1 := modByMonic_add_div P q
    have h2 := modByMonic_add_div Q q
    rw [mul_add]; linear_combination h1 + h2
  · exact (degree_add_le _ _).trans_lt (max_lt (degree_modByMonic_lt _ hq) (degree_modByMonic_lt _ hq))

lemma divByMonic_C_mul' {q : ℚ[X]} (hq : q.Monic) (c : ℚ) (P : ℚ[X]) :
    (C c * P) /ₘ q = C c * (P /ₘ q) := by
  refine ((div_modByMonic_unique (C c * (P /ₘ q)) (C c * (P %ₘ q)) hq ⟨?_, ?_⟩).1)
  · have h1 := modByMonic_add_div P q
    linear_combination C c * h1
  · rw [← smul_eq_C_mul]; exact (degree_smul_le _ _).trans_lt (degree_modByMonic_lt _ hq)

lemma sum_coeffMat {h : ℕ} (E : Fin h → ℚ[X]) (hE : ∀ a, (E a).natDegree < h) (a : Fin h) :
    E a = ∑ k : Fin h, C (coeffMat E a k) * X ^ (k : ℕ) := by
  conv_lhs => rw [as_sum_range' (E a) h (hE a)]
  rw [Finset.sum_range (fun k => monomial k ((E a).coeff k))]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [coeffMat, Matrix.of_apply, C_mul_X_pow_eq_monomial]

lemma D_monic (K : ℕ) : (D K).Monic := by
  unfold D; exact monic_prod_of_monic _ _ fun j _ => monic_X_add_C _

lemma natDegree_D (K : ℕ) : (D K).natDegree = K := by
  unfold D; rw [natDegree_prod_of_monic _ _ fun j _ => monic_X_add_C _]
  simp only [natDegree_X_add_C, Finset.sum_const, smul_eq_mul, mul_one, Nat.card_Icc]
  omega

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

theorem det_lowrank_bound {h r : ℕ} (A : Matrix (Fin h) (Fin h) ℚ[X])
    (U : Matrix (Fin h) (Fin r) ℚ) (V : Matrix (Fin r) (Fin h) ℚ) (w : Fin h → ℚ)
    (hw : ∀ s, w s ≤ 0) (hA : ∀ s t, GV p (A s t) (w s + w t))
    (hU : ∀ s u, VG p (U s u) 0) (hV : ∀ u t, VG p (V u t) 0) :
    GV p (A + (((p : ℚ)⁻¹ • (U * V)).map (C : ℚ →+* ℚ[X]))).det (2 * ∑ s, w s - r) := by
  set B : Matrix (Fin h) (Fin r) ℚ[X] := (-U).map (C : ℚ →+* ℚ[X])
  set Cm : Matrix (Fin r) (Fin h) ℚ[X] := ((p : ℚ)⁻¹ • V).map (C : ℚ →+* ℚ[X])
  have hdet : (A + (((p : ℚ)⁻¹ • (U * V)).map (C : ℚ →+* ℚ[X]))).det =
      (Matrix.fromBlocks A B Cm 1).det := by
    rw [det_fromBlocks_one₂₂]
    congr 1
    refine Matrix.ext fun s t => ?_
    simp only [B, Cm, Matrix.add_apply, Matrix.sub_apply, Matrix.mul_apply, Matrix.map_apply,
      Matrix.neg_apply, Matrix.smul_apply, smul_eq_mul, map_sum, map_mul, map_neg,
      Finset.sum_neg_distrib, Finset.mul_sum]
    rw [sub_eq_add_neg, ← Finset.sum_neg_distrib]
    congr 1
    refine Finset.sum_congr rfl fun u _ => ?_
    ring
  rw [hdet]
  have hinv : VG p ((p : ℚ)⁻¹) (-1) := by
    have := VG.primePow (p := p) (-1)
    simpa using this
  have key := det_GV (Matrix.fromBlocks A B Cm 1)
    (Sum.elim w fun _ => (-1 : ℚ)) (Sum.elim w fun _ => (0 : ℚ)) (by
      intro i j
      rcases i with s | u <;> rcases j with t | u'
      · exact hA s t
      · simp only [Matrix.fromBlocks_apply₁₂, B, Matrix.map_apply, Matrix.neg_apply,
          Sum.elim_inl, Sum.elim_inr, add_zero]
        exact (GV.C (hU s u').neg).mono (hw s)
      · simp only [Matrix.fromBlocks_apply₂₁, Cm, Matrix.map_apply, Matrix.smul_apply,
          smul_eq_mul, Sum.elim_inl, Sum.elim_inr]
        refine (GV.C (hinv.mul (hV u t))).mono ?_
        linarith [hw t]
      · simp only [Matrix.fromBlocks_apply₂₂, Sum.elim_inr, add_zero]
        rw [Matrix.one_apply]
        split_ifs
        · exact (GV.C (p := p) VG.one).mono (by norm_num)
        · exact GV.zero _)
  refine key.mono (le_of_eq ?_)
  simp [Fintype.sum_sum_type]
  ring

lemma μGe_eq (p : ℕ) (Q : ℚ[X]) {N : ℕ} (hN : Q.natDegree < N) :
    μGe p Q = ∑ e ∈ range N, if 2 * p ≤ e + 3 then Q.coeff e * μmono e else 0 := by
  unfold μGe
  apply Finset.sum_subset (Finset.range_subset_range.mpr (by omega))
  intro e _ he
  rw [Finset.mem_range] at he
  rw [coeff_eq_zero_of_natDegree_lt (by omega)]; simp

lemma μGe_add (P Q : ℚ[X]) : μGe p (P + Q) = μGe p P + μGe p Q := by
  set N := max (max P.natDegree Q.natDegree) (P + Q).natDegree + 1 with hN
  rw [μGe_eq p (P + Q) (N := N) (by omega), μGe_eq p P (N := N) (by omega),
    μGe_eq p Q (N := N) (by omega),
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun e _ => ?_
  split_ifs <;> simp [add_mul]

lemma μGe_C_mul (c : ℚ) (Q : ℚ[X]) : μGe p (C c * Q) = c * μGe p Q := by
  set N := max Q.natDegree (C c * Q).natDegree + 1 with hN
  rw [μGe_eq p (C c * Q) (N := N) (by omega), μGe_eq p Q (N := N) (by omega), Finset.mul_sum]
  refine Finset.sum_congr rfl fun e _ => ?_
  split_ifs <;> simp [coeff_C_mul]; ring

lemma μGe_eq_zero {Q : ℚ[X]} (hQ : Q.natDegree + 3 < 2 * p) : μGe p Q = 0 := by
  unfold μGe
  refine Finset.sum_eq_zero fun e he => ?_
  rw [Finset.mem_range] at he
  rw [if_neg (by omega)]

lemma VG_p_μGe (hp5 : 5 ≤ p) {Q : ℚ[X]} (hQ : GV p Q 0) : VG p ((p : ℚ) * μGe p Q) 0 := by
  have h : VG p (μGe p Q) (-1) := by
    unfold μGe
    refine VG.sum _ fun e _ => ?_
    split_ifs
    · simpa using (hQ e).mul (VG_μmono hp5 e)
    · exact VG.zero _
  simpa using (VG.primePow (p := p) 1).mul h

/-- The quotient of an integer polynomial by `D_K` has integral coefficients. -/
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

lemma μGe_sum {ι : Type*} (s : Finset ι) (f : ι → ℚ[X]) :
    μGe p (∑ i ∈ s, f i) = ∑ i ∈ s, μGe p (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [μGe]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, μGe_add, ih]

lemma divByMonic_sum' {q : ℚ[X]} (hq : q.Monic) {ι : Type*} (s : Finset ι) (f : ι → ℚ[X]) :
    (∑ i ∈ s, f i) /ₘ q = ∑ i ∈ s, f i /ₘ q := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, divByMonic_add' hq, ih]

lemma D_pow_mul_X_pow_int (N e : ℕ) : ∃ Pz : ℤ[X], Pz.map (Int.castRingHom ℚ) = D N ^ 6 * X ^ e := by
  refine ⟨tpolZ ((Icc 1 N).val.map fun j : ℕ => (j : ℤ)) ^ 6 * X ^ e, ?_⟩
  rw [Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_pow, Polynomial.map_X, tpolZ_map_Q,
    D_eq_tpol]

/-- **The outer-range framework.** -/
theorem outer_frame_aux (hp5 : 5 ≤ p) (n : ℕ) (Ez : Fin (37 * n) → ℤ[X])
    (hdegZ : ∀ s, (Ez s).natDegree < 37 * n) {ι : Type*} [Fintype ι] [DecidableEq ι]
    (γ : ι → ZMod p) (hγ : Function.Injective γ) (Lc : ι → ℕ) (cls : Fin (37 * n) → ι)
    (idx : Fin (37 * n) → ℕ) (hidx : ∀ a, idx a < Lc (cls a))
    (hinj : ∀ a b, cls a = cls b → idx a = idx b → a = b)
    (hred : ∀ a, (Ez a).map (Int.castRingHom (ZMod p)) =
      (∏ c ∈ Finset.univ.erase (cls a), (X - C (γ c)) ^ Lc c) * (X - C (γ (cls a))) ^ idx a)
    (w : Fin (37 * n) → ℚ) (hw : ∀ s, w s ≤ 0)
    (hA : ∀ s t, GV p (μX (40 * n) (D (3 * n) ^ 6 * (Ez s).map (Int.castRingHom ℚ) *
        (Ez t).map (Int.castRingHom ℚ)) -
      C (μGe p ((D (3 * n) ^ 6 * (Ez s).map (Int.castRingHom ℚ) *
        (Ez t).map (Int.castRingHom ℚ)) /ₘ D (40 * n)))) (w s + w t)) :
    GV p (Δ n) (2 * ∑ s, w s - ((37 * n - ((2 * p + 22 * n - 3) - (37 * n - 1)) : ℕ) : ℚ)) := by
  classical
  set k0 := (2 * p + 22 * n - 3) - (37 * n - 1) with hk0
  set r := 37 * n - k0 with hr
  set E : Fin (37 * n) → ℚ[X] := fun s => (Ez s).map (Int.castRingHom ℚ) with hE
  have hdegE : ∀ s, (E s).natDegree < 37 * n := fun s => (natDegree_map_le).trans_lt (hdegZ s)
  have hunit := coeffMat_det_unit_cm Ez hdegZ γ hγ Lc cls idx hidx hinj hred
  set dC := (coeffMat E).det with hdC
  have hbc := det_basis_change_cm n E hdegE
  set Cq := coeffMat E with hCq
  have hCqint : ∀ s k, VG p (Cq s k) 0 := fun s k => by
    simp only [hCq, coeffMat, Matrix.of_apply, hE, coeff_map]; exact VG.intCast _
  set β0 : ℕ → ℚ := fun e => μGe p ((D (3 * n) ^ 6 * X ^ e) /ₘ D (40 * n)) with hβ0
  have hβ0int : ∀ e, VG p ((p : ℚ) * β0 e) 0 := fun e => by
    obtain ⟨Pz, hPz⟩ := D_pow_mul_X_pow_int (3 * n) e
    have := GV_divByMonic_D (p := p) (40 * n) Pz
    rw [hPz] at this
    exact VG_p_μGe hp5 this
  have hβ0zero : ∀ e, e + 18 * n < 2 * p - 3 + 40 * n → β0 e = 0 := by
    intro e he
    apply μGe_eq_zero
    rw [natDegree_divByMonic _ (D_monic _), natDegree_mul (pow_ne_zero _ (D_monic _).ne_zero)
      (pow_ne_zero _ X_ne_zero), natDegree_pow, natDegree_D, natDegree_D, natDegree_X_pow]
    omega
  -- the correction as a double sum
  have hβ : ∀ s t, μGe p ((D (3 * n) ^ 6 * E s * E t) /ₘ D (40 * n)) =
      ∑ k : Fin (37 * n), ∑ l : Fin (37 * n), Cq s k * Cq t l * β0 (k + l) := by
    intro s t
    have hexp : D (3 * n) ^ 6 * E s * E t = ∑ k : Fin (37 * n), ∑ l : Fin (37 * n),
        C (Cq s k * Cq t l) * (D (3 * n) ^ 6 * X ^ ((k : ℕ) + (l : ℕ))) := by
      rw [sum_coeffMat E hdegE s, sum_coeffMat E hdegE t]
      simp only [Finset.mul_sum, Finset.sum_mul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
      rw [C_mul, pow_add]; ring
    rw [hexp, divByMonic_sum' (D_monic _), μGe_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [divByMonic_sum' (D_monic _), μGe_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [divByMonic_C_mul' (D_monic _), μGe_C_mul]
  -- the low-rank factorization
  set U : Matrix (Fin (37 * n)) (Fin r) ℚ := fun s u => Cq s ⟨k0 + u, by omega⟩ with hU
  set V : Matrix (Fin r) (Fin (37 * n)) ℚ :=
    fun u t => (p : ℚ) * ∑ l : Fin (37 * n), β0 (k0 + u + l) * Cq t l with hV
  have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  have hUV : ∀ s t, μGe p ((D (3 * n) ^ 6 * E s * E t) /ₘ D (40 * n)) =
      ((p : ℚ)⁻¹ • (U * V)) s t := by
    intro s t
    rw [hβ, Matrix.smul_apply, Matrix.mul_apply, smul_eq_mul, Finset.mul_sum]
    set F : Fin (37 * n) → ℚ := fun k => ∑ l : Fin (37 * n), Cq s k * Cq t l * β0 (k + l)
    have hF0 : ∀ k : Fin (37 * n), (k : ℕ) < k0 → F k = 0 := by
      intro k hk
      refine Finset.sum_eq_zero fun l _ => ?_
      rw [hβ0zero _ (by have := l.isLt; omega), mul_zero]
    set F' : ℕ → ℚ := fun k => if hk : k < 37 * n then F ⟨k, hk⟩ else 0 with hF'
    have hL : ∑ k : Fin (37 * n), F k = ∑ k ∈ range (37 * n), F' k := by
      rw [← Fin.sum_univ_eq_sum_range (fun k => F' k) (37 * n)]
      refine Finset.sum_congr rfl fun k _ => ?_
      simp [hF', k.isLt]
    have hR : ∑ u : Fin r, (p : ℚ)⁻¹ * (U s u * V u t) = ∑ u ∈ range r, F' (k0 + u) := by
      rw [← Fin.sum_univ_eq_sum_range (fun u => F' (k0 + u)) r]
      refine Finset.sum_congr rfl fun u _ => ?_
      have hu : k0 + (u : ℕ) < 37 * n := by omega
      simp only [hF', dif_pos hu, F, hU, hV]
      rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro l _
      field_simp
    have hzero : ∀ k, k < k0 → F' k = 0 := by
      intro k hk
      simp only [hF']
      split_ifs with h
      · exact hF0 ⟨k, h⟩ hk
      · rfl
    rw [hL, hR]
    by_cases hk : k0 ≤ 37 * n
    · rw [Finset.range_eq_Ico, ← Finset.sum_Ico_consecutive _ (Nat.zero_le k0) hk,
        Finset.sum_eq_zero (fun k hk' => hzero k (Finset.mem_Ico.mp hk').2), zero_add,
        Finset.sum_Ico_eq_sum_range]
    · rw [show r = 0 by omega, Finset.sum_range_zero]
      exact Finset.sum_eq_zero fun k hk' => hzero k (by rw [Finset.mem_range] at hk'; omega)
  -- the matrix identity
  set A' : Matrix (Fin (37 * n)) (Fin (37 * n)) ℚ[X] := Matrix.of fun s t =>
    μX (40 * n) (D (3 * n) ^ 6 * E s * E t) - C (μGe p ((D (3 * n) ^ 6 * E s * E t) /ₘ D (40 * n)))
  have hG : (Matrix.of fun a b => μX (40 * n) (D (3 * n) ^ 6 * E a * E b)) =
      A' + (((p : ℚ)⁻¹ • (U * V)).map (C : ℚ →+* ℚ[X])) := by
    refine Matrix.ext fun s t => ?_
    simp only [A', Matrix.add_apply, Matrix.of_apply, Matrix.map_apply, ← hUV]
    ring
  have hlow := det_lowrank_bound A' U V w hw (fun s t => by
      simp only [A', Matrix.of_apply]; exact hA s t)
    (fun s u => hCqint s _) (fun u t => by
      simp only [hV, Finset.mul_sum]
      exact VG.sum _ fun l _ => by
        rw [← mul_assoc]; simpa using (hβ0int _).mul (hCqint t l))
  rw [← hG, hbc] at hlow
  have hΔ : Δ n = C ((dC ^ 2)⁻¹) * (C (dC ^ 2) * Δ n) := by
    rw [← mul_assoc, ← C_mul, inv_mul_cancel₀ (pow_ne_zero _ hunit.1), C_1, one_mul]
  rw [hΔ]
  have hu : VG p ((dC ^ 2)⁻¹) 0 := by
    refine (VG.inv (p := p) (r := 0) (pow_ne_zero _ hunit.1) ?_).mono (by norm_num)
    rw [padicValRat.pow, hunit.2]; simp
  have := GV.C_mul hu hlow
  rw [zero_add] at this
  exact this

end Apery

end Port0

open Finset Polynomial Matrix in
theorem solution {p : ℕ} [hp : Fact p.Prime] (hp5 : 5 ≤ p) (n : ℕ) (Ez : Fin (37 * n) → ℤ[X])
    (hdegZ : ∀ s, (Ez s).natDegree < 37 * n) {ι : Type*} [Fintype ι] [DecidableEq ι]
    (γ : ι → ZMod p) (hγ : Function.Injective γ) (Lc : ι → ℕ) (cls : Fin (37 * n) → ι)
    (idx : Fin (37 * n) → ℕ) (hidx : ∀ a, idx a < Lc (cls a))
    (hinj : ∀ a b, cls a = cls b → idx a = idx b → a = b)
    (hred : ∀ a, (Ez a).map (Int.castRingHom (ZMod p)) =
      (∏ c ∈ Finset.univ.erase (cls a), (X - C (γ c)) ^ Lc c) * (X - C (γ (cls a))) ^ idx a)
    (w : Fin (37 * n) → ℚ) (hw : ∀ s, w s ≤ 0)
    (hA : ∀ s t, Apery.GV p (Apery.μX (40 * n) (Apery.D (3 * n) ^ 6 * (Ez s).map (Int.castRingHom ℚ) *
        (Ez t).map (Int.castRingHom ℚ)) -
      C (Apery.μGe p ((Apery.D (3 * n) ^ 6 * (Ez s).map (Int.castRingHom ℚ) *
        (Ez t).map (Int.castRingHom ℚ)) /ₘ Apery.D (40 * n)))) (w s + w t)) :
    Apery.GV p (Apery.Δ n) (2 * ∑ s, w s - ((37 * n - ((2 * p + 22 * n - 3) - (37 * n - 1)) : ℕ) : ℚ)) :=
  Apery.outer_frame_aux hp5 n Ez hdegZ γ hγ Lc cls idx hidx hinj hred w hw hA

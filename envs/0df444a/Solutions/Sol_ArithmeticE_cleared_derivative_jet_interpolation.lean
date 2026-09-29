-- Prove2me | solution 1 for ArithmeticE.cleared_derivative_jet_interpolation
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-09-12T18:29:34.808271+00:00
-- url     : https://prove2.me/submissions/6dc6bb6d-cca9-4563-85f3-a5c5b53a8ee8

import Definitions.Def_clearedDerivativeRows

noncomputable section
open scoped BigOperators
open Polynomial ArithmeticE
namespace CyclicInterpolation

lemma rows_add {m : ℕ} (T : Polynomial ℚ)
    (B : Matrix (Fin m) (Fin m) (Polynomial ℚ))
    (P Q : Fin m → Polynomial ℂ) (k : ℕ) :
    clearedDerivativeRows T B (P+Q) k =
      clearedDerivativeRows T B P k + clearedDerivativeRows T B Q k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    funext i
    simp only [clearedDerivativeRows, ih, Pi.add_apply, derivative_add,
      add_mul, mul_add, Finset.sum_add_distrib]
    ring

lemma rows_factor {m : ℕ} (T : Polynomial ℚ)
    (B : Matrix (Fin m) (Fin m) (Polynomial ℚ))
    (ξ : ℂ) (v : Fin m → ℂ) (N k : ℕ) (hk : k ≤ N) :
    ∃ Q : Fin m → Polynomial ℂ,
      (∀ i, clearedDerivativeRows T B
        (fun i => (X-C ξ)^N * C (v i)) k i = (X-C ξ)^(N-k) * Q i) ∧
      ∀ i, (Q i).eval ξ = (N.descFactorial k : ℂ) *
        (T.eval₂ (algebraMap ℚ ℂ) ξ)^k * v i := by
  induction k with
  | zero =>
    refine ⟨fun i => C (v i), ?_, ?_⟩
    · intro i; simp [clearedDerivativeRows]
    · intro i; simp
  | succ k ih =>
    obtain ⟨Q,hQ,he⟩ := ih (by omega)
    let t := T.map (algebraMap ℚ ℂ)
    let Y : Polynomial ℂ := X-C ξ
    let r := N-(k+1)
    have hexp : N-k = r+1 := by dsimp [r]; omega
    let U : Fin m → Polynomial ℂ := fun i =>
      t * (C ((r+1 : ℕ) : ℂ) * Q i + Y * (Q i).derivative) +
      Y * (∑ j, Q j * (B j i).map (algebraMap ℚ ℂ)) -
      C (k:ℂ) * t.derivative * Y * Q i
    refine ⟨U, ?_, ?_⟩
    · intro i
      simp only [clearedDerivativeRows]
      simp_rw [hQ, hexp]
      simp only [derivative_mul, derivative_pow, derivative_sub,
        derivative_X, derivative_C, sub_zero, mul_one]
      simp only [Nat.add_sub_cancel, pow_succ]
      dsimp [U, Y, t, r]
      simp only [Finset.mul_sum]
      ring_nf
      simp only [Finset.sum_mul, sub_mul]
    · intro i
      dsimp [U]
      simp only [eval_add, eval_mul, eval_sub, eval_C]
      have hY : Y.eval ξ = 0 := by simp [Y]
      rw [hY]
      simp only [zero_mul, add_zero]
      rw [he, Nat.cast_mul, pow_succ]
      have ht : t.eval ξ = T.eval₂ (algebraMap ℚ ℂ) ξ := by simp only [t, eval_map]
      rw [ht, hexp]
      ring


lemma rows_eval_lower {m : ℕ} (T : Polynomial ℚ)
    (B : Matrix (Fin m) (Fin m) (Polynomial ℚ))
    (ξ : ℂ) (v : Fin m → ℂ) (N k : ℕ) (hk : k < N) (i : Fin m) :
    (clearedDerivativeRows T B (fun i => (X-C ξ)^N * C (v i)) k i).eval ξ = 0 := by
  obtain ⟨Q,hQ,_⟩ := rows_factor T B ξ v N k hk.le
  rw [hQ]
  simp [show N-k ≠ 0 by omega]

lemma rows_eval_diag {m : ℕ} (T : Polynomial ℚ)
    (B : Matrix (Fin m) (Fin m) (Polynomial ℚ))
    (ξ : ℂ) (v : Fin m → ℂ) (N : ℕ) (i : Fin m) :
    (clearedDerivativeRows T B (fun i => (X-C ξ)^N * C (v i)) N i).eval ξ =
      (N.factorial:ℂ) * T.eval₂ (algebraMap ℚ ℂ) ξ ^ N * v i := by
  obtain ⟨Q,hQ,he⟩ := rows_factor T B ξ v N N le_rfl
  simpa [hQ, Nat.descFactorial_self] using he i

private lemma alg_sum {ι : Type*} (s : Finset ι) (v : ι → ℂ)
    (h : ∀ i ∈ s, IsAlgebraic ℚ (v i)) : IsAlgebraic ℚ (∑ i ∈ s, v i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (isAlgebraic_zero : IsAlgebraic ℚ (0:ℂ))
  | @insert i s hi ih =>
    rw [Finset.sum_insert hi]
    exact (h i (Finset.mem_insert_self _ _)).add
      (ih (fun j hj => h j (Finset.mem_insert_of_mem hj)))

private def AP (p : Polynomial ℂ) := ∀ k, IsAlgebraic ℚ (p.coeff k)
private lemma ap_zero : AP 0 := by intro k; simpa using (isAlgebraic_zero : IsAlgebraic ℚ (0:ℂ))
private lemma ap_C {c : ℂ} (hc : IsAlgebraic ℚ c) : AP (C c) := by
  intro k
  by_cases h : k=0
  · simpa [h] using hc
  · simpa [coeff_C, h] using (isAlgebraic_zero : IsAlgebraic ℚ (0:ℂ))
private lemma ap_X : AP (X : Polynomial ℂ) := by
  intro k
  by_cases h : k=1
  · simpa [h] using (isAlgebraic_one : IsAlgebraic ℚ (1:ℂ))
  · simpa [coeff_X, h, eq_comm] using (isAlgebraic_zero : IsAlgebraic ℚ (0:ℂ))
private lemma ap_add {p q : Polynomial ℂ} (hp : AP p) (hq : AP q) : AP (p+q) := by
  intro k; simpa using (hp k).add (hq k)
private lemma ap_sub {p q : Polynomial ℂ} (hp : AP p) (hq : AP q) : AP (p-q) := by
  intro k; simpa using (hp k).sub (hq k)
private lemma ap_mul {p q : Polynomial ℂ} (hp : AP p) (hq : AP q) : AP (p*q) := by
  intro k
  rw [coeff_mul]
  exact alg_sum _ _ (fun ij _ => (hp ij.1).mul (hq ij.2))
private lemma ap_pow {p : Polynomial ℂ} (hp : AP p) (n : ℕ) : AP (p^n) := by
  induction n with
  | zero => simpa using ap_C (isAlgebraic_one : IsAlgebraic ℚ (1:ℂ))
  | succ n ih => simpa [pow_succ] using ap_mul ih hp
private lemma ap_deriv {p : Polynomial ℂ} (hp : AP p) : AP p.derivative := by
  intro k
  rw [coeff_derivative]
  simpa only [Nat.cast_add, Nat.cast_one] using (hp (k+1)).mul (isAlgebraic_natCast (k+1))
private lemma ap_sum {ι : Type*} (s : Finset ι) (p : ι → Polynomial ℂ)
    (hp : ∀ i ∈ s, AP (p i)) : AP (∑ i ∈ s, p i) := by
  intro k
  rw [finsetSum_coeff]
  exact alg_sum _ _ (fun i hi => hp i hi k)
private lemma ap_map (p : Polynomial ℚ) : AP (p.map (algebraMap ℚ ℂ)) := by
  intro k
  simp only [coeff_map]
  exact isAlgebraic_algebraMap _
private lemma ap_eval {p : Polynomial ℂ} (hp : AP p) {ξ : ℂ} (hξ : IsAlgebraic ℚ ξ) :
    IsAlgebraic ℚ (p.eval ξ) := by
  rw [eval_eq_sum]
  exact alg_sum _ _ (fun i _ => (hp i).mul (hξ.pow i))
private lemma ap_rows {m : ℕ} (T : Polynomial ℚ)
    (B : Matrix (Fin m) (Fin m) (Polynomial ℚ))
    (P : Fin m → Polynomial ℂ) (hP : ∀ i, AP (P i)) (k : ℕ) :
    ∀ i, AP (clearedDerivativeRows T B P k i) := by
  induction k with
  | zero => exact hP
  | succ k ih =>
    intro i
    exact ap_sub
      (ap_add (ap_mul (ap_map T) (ap_deriv (ih i)))
        (ap_sum _ _ (fun j _ => ap_mul (ih j) (ap_map (B j i)))))
      (ap_mul (ap_mul (ap_C (isAlgebraic_natCast k)) (ap_deriv (ap_map T))) (ih i))

lemma interpolation (m : ℕ) (T : Polynomial ℚ)
    (B : Matrix (Fin m) (Fin m) (Polynomial ℚ))
    (ξ : ℂ) (hξ : IsAlgebraic ℚ ξ)
    (hreg : T.eval₂ (algebraMap ℚ ℂ) ξ ≠ 0)
    (N : ℕ) (w : ℕ → Fin m → ℂ)
    (hw : ∀ k < N, ∀ i, IsAlgebraic ℚ (w k i)) :
    ∃ P : Fin m → Polynomial ℂ,
      (∀ i k, IsAlgebraic ℚ ((P i).coeff k)) ∧
      ∀ k < N, ∀ i, (clearedDerivativeRows T B P k i).eval ξ = w k i := by
  induction N with
  | zero => exact ⟨fun _ => 0, fun _ => ap_zero, by simp⟩
  | succ N ih =>
    obtain ⟨P,hP,hjets⟩ := ih (fun k hk => hw k (by omega))
    let t := T.eval₂ (algebraMap ℚ ℂ) ξ
    let v : Fin m → ℂ := fun i =>
      (w N i - (clearedDerivativeRows T B P N i).eval ξ) / ((N.factorial:ℂ)*t^N)
    have ht : IsAlgebraic ℚ t := by
      simpa only [t, eval_map, aeval_def] using ap_eval (ap_map T) hξ
    have hv : ∀ i, IsAlgebraic ℚ (v i) := by
      intro i
      dsimp [v]
      rw [div_eq_mul_inv]
      exact ((hw N (by omega) i).sub (ap_eval (ap_rows T B P hP N i) hξ)).mul
        (((isAlgebraic_natCast _).mul (ht.pow N)).inv)
    let Q : Fin m → Polynomial ℂ := fun i => (X-C ξ)^N * C (v i)
    refine ⟨P+Q, fun i => ap_add (hP i) (ap_mul (ap_pow (ap_sub ap_X (ap_C hξ)) N) (ap_C (hv i))), ?_⟩
    intro k hk i
    rw [rows_add]
    simp only [Pi.add_apply, eval_add]
    by_cases he : k=N
    · subst k
      rw [rows_eval_diag]
      have hf : (N.factorial:ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero N
      dsimp [v, t]
      field_simp [hf, hreg]
      ring
    · have hkN : k<N := by omega
      rw [hjets k hkN i, rows_eval_lower T B ξ v N k hkN i, add_zero]

end CyclicInterpolation

theorem solution
    (m : ℕ) (T : Polynomial ℚ) (B : Matrix (Fin m) (Fin m) (Polynomial ℚ))
    (ξ : ℂ) (hξ : IsAlgebraic ℚ ξ)
    (hreg : T.eval₂ (algebraMap ℚ ℂ) ξ ≠ 0)
    (N : ℕ) (w : ℕ → Fin m → ℂ)
    (hw : ∀ k < N, ∀ i, IsAlgebraic ℚ (w k i)) :
    ∃ P : Fin m → Polynomial ℂ,
      (∀ i k, IsAlgebraic ℚ ((P i).coeff k)) ∧
      ∀ k < N, ∀ i, (clearedDerivativeRows T B P k i).eval ξ = w k i := by
  exact CyclicInterpolation.interpolation m T B ξ hξ hreg N w hw
#print axioms solution

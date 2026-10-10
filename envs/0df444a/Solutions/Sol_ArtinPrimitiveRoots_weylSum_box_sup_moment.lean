-- Prove2me | solution 1 for ArtinPrimitiveRoots.weylSum_box_sup_moment
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-09T15:07:56.152903+00:00
-- url     : https://prove2.me/submissions/7dc5b93b-226d-481a-8929-c17afdd7e35f

import Mathlib
import Definitions.Def_ArtinVinogradov

section
/-!
# L33B, step 2: exponential series + Cauchy–Schwarz

For a finite family `c u` and real vectors `y u ∈ [-Y, Y]^k`, uniformly in `t ∈ [-1, 1]^k`:
`‖∑ u, c u * e(t · y u)‖² ≤ exp (2πkY) * ∑' ℓ, aw ℓ / Y^ℓ * ∑_{f : Fin ℓ → Fin k} ‖A ℓ f‖²`,
where `A ℓ f = ∑ u, c u * ∏ r, y u (f r)` does not depend on `t`.
-/

namespace ArtinPrimitiveRoots.L33B

open Real Complex Finset

/-- The exponential-series weight `(2π)^ℓ / ℓ!`. -/
noncomputable def aw (ℓ : ℕ) : ℝ := (2 * π) ^ ℓ / (ℓ.factorial : ℝ)

lemma aw_pos (ℓ : ℕ) : 0 < aw ℓ := by
  unfold aw; have := Real.pi_pos; positivity

/-- The `t`-free moments `A ℓ f = ∑ u, c u * ∏ r, y u (f r)`. -/
noncomputable def mom {U : Type*} [Fintype U] {k : ℕ} (c : U → ℂ) (y : U → Fin k → ℝ)
    (ℓ : ℕ) (f : Fin ℓ → Fin k) : ℂ :=
  ∑ u, c u * ((∏ r, y u (f r) : ℝ) : ℂ)

lemma hasSum_expand {U : Type*} [Fintype U] {k : ℕ} (c : U → ℂ) (y : U → Fin k → ℝ)
    (t : Fin k → ℝ) :
    HasSum (fun ℓ : ℕ => (2 * π * I) ^ ℓ / (ℓ.factorial : ℂ) *
        ∑ f : Fin ℓ → Fin k, ((∏ r, t (f r) : ℝ) : ℂ) * mom c y ℓ f)
      (∑ u, c u * Complex.exp (2 * π * I * ((∑ j, t j * y u j : ℝ) : ℂ))) := by
  have h : ∀ u ∈ (Finset.univ : Finset U), HasSum (fun ℓ : ℕ => c u *
      ((2 * π * I * ((∑ j, t j * y u j : ℝ) : ℂ)) ^ ℓ / (ℓ.factorial : ℂ)))
      (c u * Complex.exp (2 * π * I * ((∑ j, t j * y u j : ℝ) : ℂ))) := by
    intro u _
    rw [Complex.exp_eq_exp_ℂ]
    exact (NormedSpace.expSeries_div_hasSum_exp _).mul_left (c u)
  convert hasSum_sum h using 1
  funext ℓ
  simp only [mom, mul_pow, Complex.ofReal_sum, Complex.ofReal_mul, Complex.ofReal_prod,
    Fintype.sum_pow, Finset.prod_mul_distrib]
  rw [Finset.mul_sum]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [Finset.sum_div, Finset.mul_sum]
  refine Finset.sum_congr rfl fun f _ => ?_
  ring

lemma norm_term_le {U : Type*} [Fintype U] {k : ℕ} (c : U → ℂ) (y : U → Fin k → ℝ)
    (t : Fin k → ℝ) (ht : ∀ j, |t j| ≤ 1) (ℓ : ℕ) :
    ‖(2 * π * I) ^ ℓ / (ℓ.factorial : ℂ) *
        ∑ f : Fin ℓ → Fin k, ((∏ r, t (f r) : ℝ) : ℂ) * mom c y ℓ f‖ ≤
      aw ℓ * ∑ f : Fin ℓ → Fin k, ‖mom c y ℓ f‖ := by
  rw [norm_mul]
  have h1 : ‖(2 * π * I) ^ ℓ / (ℓ.factorial : ℂ)‖ = aw ℓ := by
    rw [norm_div, norm_pow, norm_mul, norm_mul, Complex.norm_I, Complex.norm_real,
      Complex.norm_natCast, Complex.norm_two, Real.norm_eq_abs, abs_of_pos Real.pi_pos, mul_one]
    rfl
  rw [h1]
  refine mul_le_mul_of_nonneg_left ?_ (aw_pos ℓ).le
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun f _ => ?_)
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, Finset.abs_prod]
  have : ∏ r, |t (f r)| ≤ 1 :=
    Finset.prod_le_one (fun r _ => abs_nonneg _) (fun r _ => ht (f r))
  calc (∏ r, |t (f r)|) * ‖mom c y ℓ f‖ ≤ 1 * ‖mom c y ℓ f‖ :=
        mul_le_mul_of_nonneg_right this (norm_nonneg _)
    _ = ‖mom c y ℓ f‖ := one_mul _

lemma norm_mom_le {U : Type*} [Fintype U] {k : ℕ} (c : U → ℂ) (hc : ∀ u, ‖c u‖ ≤ 1)
    (y : U → Fin k → ℝ) {Y : ℝ} (hy : ∀ u j, |y u j| ≤ Y) (ℓ : ℕ) (f : Fin ℓ → Fin k) :
    ‖mom c y ℓ f‖ ≤ Fintype.card U * Y ^ ℓ := by
  unfold mom
  refine (norm_sum_le _ _).trans ?_
  have : ∀ u, ‖c u * ((∏ r, y u (f r) : ℝ) : ℂ)‖ ≤ Y ^ ℓ := by
    intro u
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, Finset.abs_prod]
    have h2 : ∏ r, |y u (f r)| ≤ Y ^ ℓ := by
      calc ∏ r, |y u (f r)| ≤ ∏ _r : Fin ℓ, Y :=
            Finset.prod_le_prod (fun r _ => abs_nonneg _) (fun r _ => hy u (f r))
        _ = Y ^ ℓ := by simp
    calc ‖c u‖ * ∏ r, |y u (f r)| ≤ 1 * Y ^ ℓ :=
          mul_le_mul (hc u) h2 (Finset.prod_nonneg fun r _ => abs_nonneg _) zero_le_one
      _ = Y ^ ℓ := one_mul _
  calc ∑ u, ‖c u * ((∏ r, y u (f r) : ℝ) : ℂ)‖ ≤ ∑ _u : U, Y ^ ℓ :=
        Finset.sum_le_sum fun u _ => this u
    _ = Fintype.card U * Y ^ ℓ := by simp

/-- The `t`-free series is summable. -/
lemma summable_momSeries {U : Type*} [Fintype U] {k : ℕ} (c : U → ℂ) (hc : ∀ u, ‖c u‖ ≤ 1)
    (y : U → Fin k → ℝ) {Y : ℝ} (hY : 0 < Y) (hy : ∀ u j, |y u j| ≤ Y) :
    Summable (fun ℓ : ℕ => aw ℓ / Y ^ ℓ * ∑ f : Fin ℓ → Fin k, ‖mom c y ℓ f‖ ^ 2) := by
  have hb : ∀ ℓ, aw ℓ / Y ^ ℓ * ∑ f : Fin ℓ → Fin k, ‖mom c y ℓ f‖ ^ 2 ≤
      (Fintype.card U : ℝ) ^ 2 * ((2 * π * k * Y) ^ ℓ / (ℓ.factorial : ℝ)) := by
    intro ℓ
    have hYl : 0 < Y ^ ℓ := pow_pos hY ℓ
    have h1 : ∑ f : Fin ℓ → Fin k, ‖mom c y ℓ f‖ ^ 2 ≤
        ∑ _f : Fin ℓ → Fin k, ((Fintype.card U : ℝ) * Y ^ ℓ) ^ 2 :=
      Finset.sum_le_sum fun f _ =>
        pow_le_pow_left₀ (norm_nonneg _) (norm_mom_le c hc y hy ℓ f) 2
    have h2 : ∑ _f : Fin ℓ → Fin k, ((Fintype.card U : ℝ) * Y ^ ℓ) ^ 2 =
        (k : ℝ) ^ ℓ * ((Fintype.card U : ℝ) * Y ^ ℓ) ^ 2 := by
      simp [Finset.card_univ, Fintype.card_fin]
    calc aw ℓ / Y ^ ℓ * ∑ f : Fin ℓ → Fin k, ‖mom c y ℓ f‖ ^ 2
        ≤ aw ℓ / Y ^ ℓ * ((k : ℝ) ^ ℓ * ((Fintype.card U : ℝ) * Y ^ ℓ) ^ 2) := by
          rw [← h2]
          exact mul_le_mul_of_nonneg_left h1 (div_nonneg (aw_pos ℓ).le hYl.le)
      _ = (Fintype.card U : ℝ) ^ 2 * ((2 * π * k * Y) ^ ℓ / (ℓ.factorial : ℝ)) := by
          unfold aw
          field_simp
          ring
  refine Summable.of_nonneg_of_le (fun ℓ => ?_) hb
    ((Real.summable_pow_div_factorial _).mul_left _)
  exact mul_nonneg (div_nonneg (aw_pos ℓ).le (pow_pos hY ℓ).le)
    (Finset.sum_nonneg fun f _ => sq_nonneg _)

lemma hasSum_aw_mul (x : ℝ) : HasSum (fun ℓ : ℕ => aw ℓ * x ^ ℓ) (Real.exp (2 * π * x)) := by
  have := NormedSpace.expSeries_div_hasSum_exp (2 * π * x)
  rw [← Real.exp_eq_exp_ℝ] at this
  have h' : (fun ℓ : ℕ => aw ℓ * x ^ ℓ) = fun n : ℕ => (2 * π * x) ^ n / (n.factorial : ℝ) := by
    funext ℓ
    unfold aw
    rw [mul_pow]
    ring
  rw [h']
  exact this

/-- **Step 2.** Exponential series and Cauchy–Schwarz, uniformly in `t ∈ [-1,1]^k`. -/
theorem taylor_cs {U : Type*} [Fintype U] {k : ℕ} (c : U → ℂ) (hc : ∀ u, ‖c u‖ ≤ 1)
    (y : U → Fin k → ℝ) {Y : ℝ} (hY : 0 < Y) (hy : ∀ u j, |y u j| ≤ Y)
    (t : Fin k → ℝ) (ht : ∀ j, |t j| ≤ 1) :
    ‖∑ u, c u * Complex.exp (2 * π * I * ((∑ j, t j * y u j : ℝ) : ℂ))‖ ^ 2 ≤
      Real.exp (2 * π * (k * Y)) *
        ∑' ℓ : ℕ, aw ℓ / Y ^ ℓ * ∑ f : Fin ℓ → Fin k, ‖mom c y ℓ f‖ ^ 2 := by
  have hv := hasSum_expand c y t
  set x : ℕ → ℝ := fun ℓ => aw ℓ * ∑ f : Fin ℓ → Fin k, ‖mom c y ℓ f‖ with hx
  set w : ℕ → ℝ := fun ℓ => aw ℓ * ((k : ℝ) * Y) ^ ℓ with hw
  set q : ℕ → ℝ := fun ℓ => aw ℓ / Y ^ ℓ * ∑ f : Fin ℓ → Fin k, ‖mom c y ℓ f‖ ^ 2 with hq
  have hwS : HasSum w (Real.exp (2 * π * (k * Y))) := hasSum_aw_mul _
  have hqS : Summable q := summable_momSeries c hc y hY hy
  have hw0 : ∀ ℓ, 0 ≤ w ℓ := fun ℓ =>
    mul_nonneg (aw_pos ℓ).le (pow_nonneg (mul_nonneg (Nat.cast_nonneg _) hY.le) _)
  have hq0 : ∀ ℓ, 0 ≤ q ℓ := fun ℓ =>
    mul_nonneg (div_nonneg (aw_pos ℓ).le (pow_pos hY ℓ).le)
      (Finset.sum_nonneg fun f _ => sq_nonneg _)
  have hxwq : ∀ ℓ, x ℓ ^ 2 ≤ w ℓ * q ℓ := by
    intro ℓ
    have hcs := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset (Fin ℓ → Fin k)))
      (f := fun f => ‖mom c y ℓ f‖)
    simp only [Finset.card_univ, Fintype.card_fun, Fintype.card_fin, Nat.cast_pow] at hcs
    have hYl : 0 < Y ^ ℓ := pow_pos hY ℓ
    have ha := aw_pos ℓ
    simp only [hx, hw, hq]
    calc (aw ℓ * ∑ f : Fin ℓ → Fin k, ‖mom c y ℓ f‖) ^ 2
        = aw ℓ ^ 2 * (∑ f : Fin ℓ → Fin k, ‖mom c y ℓ f‖) ^ 2 := by ring
      _ ≤ aw ℓ ^ 2 * ((k : ℝ) ^ ℓ * ∑ f : Fin ℓ → Fin k, ‖mom c y ℓ f‖ ^ 2) :=
          mul_le_mul_of_nonneg_left hcs (sq_nonneg _)
      _ = aw ℓ * ((k : ℝ) * Y) ^ ℓ *
            (aw ℓ / Y ^ ℓ * ∑ f : Fin ℓ → Fin k, ‖mom c y ℓ f‖ ^ 2) := by
          field_simp
          ring
  have hpart : ∀ F : Finset ℕ, ‖∑ ℓ ∈ F, (2 * π * I) ^ ℓ / (ℓ.factorial : ℂ) *
        ∑ f : Fin ℓ → Fin k, ((∏ r, t (f r) : ℝ) : ℂ) * mom c y ℓ f‖ ^ 2 ≤
      Real.exp (2 * π * (k * Y)) * ∑' ℓ, q ℓ := by
    intro F
    have h1 : ‖∑ ℓ ∈ F, (2 * π * I) ^ ℓ / (ℓ.factorial : ℂ) *
        ∑ f : Fin ℓ → Fin k, ((∏ r, t (f r) : ℝ) : ℂ) * mom c y ℓ f‖ ≤ ∑ ℓ ∈ F, x ℓ :=
      (norm_sum_le _ _).trans (Finset.sum_le_sum fun ℓ _ => norm_term_le c y t ht ℓ)
    have h2 : (∑ ℓ ∈ F, x ℓ) ^ 2 ≤ (∑ ℓ ∈ F, w ℓ) * ∑ ℓ ∈ F, q ℓ :=
      Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul F (fun ℓ _ => hw0 ℓ) (fun ℓ _ => hq0 ℓ)
        (fun ℓ _ => hxwq ℓ)
    have h3 : ∑ ℓ ∈ F, w ℓ ≤ Real.exp (2 * π * (k * Y)) := by
      rw [← hwS.tsum_eq]; exact hwS.summable.sum_le_tsum F (fun ℓ _ => hw0 ℓ)
    have h4 : ∑ ℓ ∈ F, q ℓ ≤ ∑' ℓ, q ℓ := hqS.sum_le_tsum F (fun ℓ _ => hq0 ℓ)
    calc _ ≤ (∑ ℓ ∈ F, x ℓ) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
      _ ≤ (∑ ℓ ∈ F, w ℓ) * ∑ ℓ ∈ F, q ℓ := h2
      _ ≤ Real.exp (2 * π * (k * Y)) * ∑' ℓ, q ℓ :=
          mul_le_mul h3 h4 (Finset.sum_nonneg fun ℓ _ => hq0 ℓ) (Real.exp_pos _).le
  exact le_of_tendsto' ((hv.norm).pow 2) hpart

end ArtinPrimitiveRoots.L33B
end

section
/-!
# L33B, steps 3–4: orthogonality on the grid of box corners, and the congruence count

* `grid_orth`: for integer frequency vectors `n u` and moduli `N j`,
  `∑_m ‖∑_u e(∑_j m_j n_{u,j}/N_j) W u‖² = (∏ N_j) * ∑_{(u,v) ∈ R} W u W v`,
  `R = {(u,v) : N_j ∣ n_{u,j} - n_{v,j} ∀ j}`.
* `card_congr_le`: if `0 ≤ n_{u,j} ≤ s N_j` then `#R ≤ (2s+1)^k * #{(u,v) : n u = n v}`.
-/

namespace ArtinPrimitiveRoots.L33B

open Real Complex Finset

lemma sum_exp_root (N : ℕ) (hN : 0 < N) (d : ℤ) :
    ∑ a ∈ range N, Complex.exp (2 * π * I * (((a : ℝ) / N * d : ℝ) : ℂ)) =
      if (N : ℤ) ∣ d then (N : ℂ) else 0 := by
  have hN' : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
  set z := Complex.exp (2 * π * I * ((d : ℂ) / N)) with hz
  have hterm : ∀ a : ℕ, Complex.exp (2 * π * I * (((a : ℝ) / N * d : ℝ) : ℂ)) = z ^ a := by
    intro a
    rw [hz, ← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  simp_rw [hterm]
  split_ifs with h
  · obtain ⟨e, he⟩ := h
    have hz1 : z = 1 := by
      rw [hz, he]
      have : 2 * π * I * (((N * e : ℤ) : ℂ) / N) = (e : ℂ) * (2 * π * I) := by
        push_cast
        field_simp
      rw [this, Complex.exp_int_mul_two_pi_mul_I]
    simp [hz1]
  · have hz1 : z ≠ 1 := by
      intro h1
      rw [hz, Complex.exp_eq_one_iff] at h1
      obtain ⟨n, hn⟩ := h1
      apply h
      refine ⟨n, ?_⟩
      have hpi : (2 * π * I : ℂ) ≠ 0 := by simp [Real.pi_ne_zero, Complex.I_ne_zero]
      have h2 : (d : ℂ) / N = n := mul_left_cancel₀ hpi (hn.trans (mul_comm _ _))
      have h3 : (d : ℂ) = (N : ℂ) * n := by rw [← h2]; field_simp
      exact_mod_cast h3
    have hzN : z ^ N = 1 := by
      rw [hz, ← Complex.exp_nat_mul]
      have : (N : ℂ) * (2 * π * I * ((d : ℂ) / N)) = (d : ℂ) * (2 * π * I) := by
        field_simp
      rw [this, Complex.exp_int_mul_two_pi_mul_I]
    rw [geom_sum_eq hz1, hzN, sub_self, zero_div]

/-- The phase `e(∑_j m_j n_j / N_j)` at the grid point `m`. -/
noncomputable def gphase {k : ℕ} (N : Fin k → ℕ) (m : Fin k → ℕ) (n : Fin k → ℤ) : ℂ :=
  Complex.exp (2 * π * I * ((∑ j, (m j : ℝ) / N j * n j : ℝ) : ℂ))

lemma gphase_mul_conj {k : ℕ} (N : Fin k → ℕ) (m : Fin k → ℕ) (a b : Fin k → ℤ) :
    gphase N m a * (starRingEnd ℂ) (gphase N m b) =
      ∏ j, Complex.exp (2 * π * I * ((((m j : ℕ) : ℝ) / N j * ((a j - b j : ℤ) : ℝ) : ℝ) : ℂ)) := by
  unfold gphase
  rw [← Complex.exp_conj, ← Complex.exp_add, ← Complex.exp_sum]
  congr 1
  simp only [map_mul, Complex.conj_ofReal, Complex.conj_I, map_ofNat]
  push_cast
  simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

theorem grid_orth {U : Type*} [Fintype U] {k : ℕ} (N : Fin k → ℕ) (hN : ∀ j, 0 < N j)
    (n : U → Fin k → ℤ) (W : U → ℝ) :
    ∑ m ∈ Fintype.piFinset (fun j => range (N j)), ‖∑ u, gphase N m (n u) * (W u : ℂ)‖ ^ 2
      = (∏ j, (N j : ℝ)) * ∑ p ∈ (univ : Finset (U × U)).filter
          (fun p => ∀ j, (N j : ℤ) ∣ n p.1 j - n p.2 j), W p.1 * W p.2 := by
  apply Complex.ofReal_injective
  have hL : ∀ m : Fin k → ℕ, (((‖∑ u, gphase N m (n u) * (W u : ℂ)‖ ^ 2 : ℝ)) : ℂ) =
      ∑ u, ∑ v, ((W u * W v : ℝ) : ℂ) * ∏ j, Complex.exp (2 * π * I *
        ((((m j : ℕ) : ℝ) / N j * ((n u j - n v j : ℤ) : ℝ) : ℝ) : ℂ)) := by
    intro m
    rw [Complex.ofReal_pow, ← Complex.mul_conj', map_sum, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ => ?_
    rw [map_mul, Complex.conj_ofReal, ← gphase_mul_conj]
    push_cast
    ring
  have hinner : ∀ u v : U, ∑ m ∈ Fintype.piFinset (fun j => range (N j)),
      ∏ j, Complex.exp (2 * π * I * ((((m j : ℕ) : ℝ) / N j * ((n u j - n v j : ℤ) : ℝ) : ℝ) : ℂ))
        = ∏ j, (if (N j : ℤ) ∣ (n u j - n v j) then (N j : ℂ) else 0) := by
    intro u v
    rw [← Finset.prod_univ_sum (fun j => range (N j)) (fun j (a : ℕ) =>
      Complex.exp (2 * π * I * ((((a : ℕ) : ℝ) / N j * ((n u j - n v j : ℤ) : ℝ) : ℝ) : ℂ)))]
    exact Finset.prod_congr rfl fun j _ => sum_exp_root (N j) (hN j) _
  rw [Complex.ofReal_sum]
  simp_rw [hL]
  rw [Finset.sum_comm]
  simp_rw [Finset.sum_comm (s := Fintype.piFinset (fun j => range (N j))), ← Finset.mul_sum, hinner,
    Fintype.prod_ite_zero]
  rw [Finset.sum_filter, Complex.ofReal_mul, Complex.ofReal_sum, Complex.ofReal_prod,
    Finset.mul_sum, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ => ?_
  split_ifs <;> push_cast <;> ring

/-- `#{(a,b) | g a = h b} = ∑_{x ∈ T} #{g = x} * #{h = x}` when `T` contains the image of `g`. -/
lemma card_match_eq {U X : Type*} [Fintype U] [DecidableEq X] (g h : U → X) (T : Finset X)
    (hg : ∀ a, g a ∈ T) :
    ((univ : Finset (U × U)).filter (fun p => g p.1 = h p.2)).card =
      ∑ x ∈ T, (univ.filter (fun a => g a = x)).card * (univ.filter (fun b => h b = x)).card := by
  rw [card_eq_sum_card_fiberwise (f := fun p : U × U => g p.1) (t := T) (fun p _ => hg p.1)]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [← Finset.card_product]
  congr 1
  ext ⟨a, b⟩
  simp only [mem_filter, mem_univ, true_and, mem_product]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨h2, h1 ▸ h2⟩
  · rintro ⟨h1, h2⟩; exact ⟨h1.trans h2.symm, h1⟩

/-- `2 #{φ a = ψ b} ≤ #{φ a = φ a'} + #{ψ b = ψ b'}` (Cauchy–Schwarz on fibre sizes). -/
lemma two_mul_card_match_le {U X : Type*} [Fintype U] [DecidableEq X] (φ ψ : U → X) :
    2 * ((univ : Finset (U × U)).filter (fun p => φ p.1 = ψ p.2)).card ≤
      ((univ : Finset (U × U)).filter (fun p => φ p.1 = φ p.2)).card +
        ((univ : Finset (U × U)).filter (fun p => ψ p.1 = ψ p.2)).card := by
  set T := univ.image φ ∪ univ.image ψ
  have hφ : ∀ a, φ a ∈ T := fun a => mem_union_left _ (mem_image_of_mem _ (mem_univ a))
  have hψ : ∀ a, ψ a ∈ T := fun a => mem_union_right _ (mem_image_of_mem _ (mem_univ a))
  rw [card_match_eq φ ψ T hφ, card_match_eq φ φ T hφ, card_match_eq ψ ψ T hψ, Finset.mul_sum,
    ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun x _ => ?_
  set A := (univ.filter (fun a => φ a = x)).card
  set B := (univ.filter (fun a => ψ a = x)).card
  zify
  nlinarith [sq_nonneg ((A : ℤ) - B)]

/-- **Step 4.** The congruence count. -/
theorem card_congr_le {U : Type*} [Fintype U] {k : ℕ} (N : Fin k → ℕ) (hN : ∀ j, 0 < N j)
    (n : U → Fin k → ℤ) (s : ℕ) (hn0 : ∀ u j, 0 ≤ n u j) (hns : ∀ u j, n u j ≤ s * N j) :
    ((univ : Finset (U × U)).filter (fun p => ∀ j, (N j : ℤ) ∣ n p.1 j - n p.2 j)).card ≤
      (2 * s + 1) ^ k * ((univ : Finset (U × U)).filter (fun p => n p.1 = n p.2)).card := by
  classical
  set J := ((univ : Finset (U × U)).filter (fun p => n p.1 = n p.2)).card
  set C := Fintype.piFinset (fun _ : Fin k => Finset.Icc (-(s : ℤ)) s)
  have hsub : (univ : Finset (U × U)).filter (fun p => ∀ j, (N j : ℤ) ∣ n p.1 j - n p.2 j) ⊆
      C.biUnion (fun c => (univ : Finset (U × U)).filter
        (fun p => n p.1 = fun j => n p.2 j + c j * N j)) := by
    intro p hp
    simp only [mem_filter, mem_univ, true_and] at hp
    rw [mem_biUnion]
    refine ⟨fun j => (n p.1 j - n p.2 j) / N j, ?_, ?_⟩
    · rw [Fintype.mem_piFinset]
      intro j
      have hNj : (0 : ℤ) < N j := by exact_mod_cast hN j
      have he := Int.mul_ediv_cancel' (hp j)
      have h1 := hn0 p.1 j; have h2 := hn0 p.2 j; have h3 := hns p.1 j; have h4 := hns p.2 j
      rw [Finset.mem_Icc]
      constructor <;> nlinarith
    · simp only [mem_filter, mem_univ, true_and]
      funext j
      have he := Int.mul_ediv_cancel' (hp j)
      linarith
  have hfib : ∀ c ∈ C, ((univ : Finset (U × U)).filter
      (fun p => n p.1 = fun j => n p.2 j + c j * N j)).card ≤ J := by
    intro c _
    have h := two_mul_card_match_le n (fun v j => n v j + c j * N j)
    have hJ : ((univ : Finset (U × U)).filter (fun p => (fun j => n p.1 j + c j * N j) =
        fun j => n p.2 j + c j * N j)).card = J := by
      congr 1
      refine Finset.filter_congr fun p _ => ?_
      constructor
      · intro h1; funext j; have := congr_fun h1 j; simpa using this
      · intro h1; rw [h1]
    rw [hJ] at h
    omega
  calc _ ≤ (C.biUnion (fun c => (univ : Finset (U × U)).filter
        (fun p => n p.1 = fun j => n p.2 j + c j * N j))).card := card_le_card hsub
    _ ≤ ∑ c ∈ C, ((univ : Finset (U × U)).filter
        (fun p => n p.1 = fun j => n p.2 j + c j * N j)).card := card_biUnion_le
    _ ≤ ∑ _c ∈ C, J := Finset.sum_le_sum hfib
    _ = (2 * s + 1) ^ k * J := by
      rw [Finset.sum_const, smul_eq_mul, Fintype.card_piFinset]
      simp only [Int.card_Icc, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
      congr 2
      omega

end ArtinPrimitiveRoots.L33B
end

section
/-!
# L33B: `weylSum_box_sup_moment` ([22] (3.11))

Assembly: step 1 (`weylSum_pow`, `phase_split`), the per-box bound `box_bound`
(via `taylor_cs`), the sum over boxes `sum_G_le` (via `grid_orth`), the congruence count
(`card_congr_le`) and the identification with `vinogradovCount`.
-/

namespace ArtinPrimitiveRoots.L33B

open Real Complex Finset

/-- Power sums `n_j(u) = ∑_i (u_i + 1)^(j+1)`. -/
def psum {s M k : ℕ} (u : Fin s → Fin M) (j : Fin k) : ℕ :=
  ∑ i, ((u i : ℕ) + 1) ^ (j.val + 1)

lemma psum_le {s M k : ℕ} (u : Fin s → Fin M) (j : Fin k) : psum u j ≤ s * M ^ (j.val + 1) := by
  unfold psum
  calc ∑ i, ((u i : ℕ) + 1) ^ (j.val + 1) ≤ ∑ _i : Fin s, M ^ (j.val + 1) :=
        Finset.sum_le_sum fun i _ => Nat.pow_le_pow_left (by have := (u i).isLt; omega) _
    _ = s * M ^ (j.val + 1) := by simp

/-- Step 1: `S(α)^s = ∑_u e(∑_j α_j n_j(u))`. -/
lemma weylSum_pow (M k s : ℕ) (α : Fin k → ℝ) :
    weylSum M k α ^ s = ∑ u : Fin s → Fin M,
      Complex.exp (2 * π * I * ((∑ j, α j * (psum u j : ℝ) : ℝ) : ℂ)) := by
  have h1 : weylSum M k α = ∑ a : Fin M,
      Complex.exp (2 * π * I * ((∑ j : Fin k, α j * (((a : ℕ) + 1 : ℕ) : ℝ) ^ (j.val + 1) : ℝ) : ℂ)) := by
    unfold weylSum
    have : Finset.Icc 1 M = (Finset.range M).map ⟨(· + 1), add_left_injective 1⟩ := by
      ext x; simp only [Finset.mem_Icc, Finset.mem_map, Finset.mem_range,
        Function.Embedding.coeFn_mk]
      constructor
      · intro hx; exact ⟨x - 1, by omega, by omega⟩
      · rintro ⟨a, ha, rfl⟩; omega
    rw [this, Finset.sum_map]
    exact (Fin.sum_univ_eq_sum_range (fun a => Complex.exp (2 * π * I *
      ((∑ j : Fin k, α j * (((a + 1 : ℕ)) : ℝ) ^ (j.val + 1) : ℝ) : ℂ))) M).symm
  rw [h1, Fintype.sum_pow]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [← Complex.exp_sum]
  congr 1
  rw [← Finset.mul_sum]
  congr 1
  unfold psum
  push_cast
  rw [Finset.sum_comm]
  simp only [Finset.mul_sum]

/-- Splitting the phase at the corner `m / N` of the box. -/
lemma phase_split {k : ℕ} (N : Fin k → ℕ) (hN : ∀ j, 0 < N j) (m : Fin k → ℕ) (α : Fin k → ℝ)
    (P : Fin k → ℕ) :
    Complex.exp (2 * π * I * ((∑ j, α j * (P j : ℝ) : ℝ) : ℂ)) =
      gphase N m (fun j => (P j : ℤ)) *
        Complex.exp (2 * π * I * ((∑ j, (α j * N j - m j) * ((P j : ℝ) / N j) : ℝ) : ℂ)) := by
  unfold gphase
  rw [← Complex.exp_add]
  congr 1
  rw [← mul_add]
  congr 1
  push_cast
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  have : (N j : ℂ) ≠ 0 := by exact_mod_cast (hN j).ne'
  field_simp
  ring

lemma norm_gphase {k : ℕ} (N : Fin k → ℕ) (m : Fin k → ℕ) (n : Fin k → ℤ) :
    ‖gphase N m n‖ = 1 := by
  unfold gphase
  rw [show (2 * π * I * ((∑ j, (m j : ℝ) / N j * n j : ℝ) : ℂ)) =
    ((2 * π * ∑ j, (m j : ℝ) / N j * n j : ℝ) : ℂ) * I by push_cast; ring]
  exact Complex.norm_exp_ofReal_mul_I _

/-- The moduli `N_j = M^(j+1)`. -/
def Nv (M k : ℕ) (j : Fin k) : ℕ := M ^ (j.val + 1)

/-- Integer frequency vectors. -/
def nZ (s M k : ℕ) (u : Fin s → Fin M) (j : Fin k) : ℤ := (psum u j : ℤ)

/-- Rescaled frequencies `y_j(u) = n_j(u) / N_j ∈ [0, s]`. -/
noncomputable def yv (s M k : ℕ) (u : Fin s → Fin M) (j : Fin k) : ℝ :=
  (psum u j : ℝ) / (Nv M k j : ℝ)

/-- The `t`-free bound attached to the box with corner `m`. -/
noncomputable def Gbox (s M k : ℕ) (m : Fin k → ℕ) : ℝ :=
  ∑' ℓ : ℕ, aw ℓ / (s : ℝ) ^ ℓ * ∑ f : Fin ℓ → Fin k,
    ‖mom (fun u : Fin s → Fin M => gphase (Nv M k) m (nZ s M k u)) (yv s M k) ℓ f‖ ^ 2

lemma Nv_pos {M k : ℕ} (hM : 1 ≤ M) (j : Fin k) : 0 < Nv M k j := pow_pos hM _

lemma yv_nonneg (s M k : ℕ) (u : Fin s → Fin M) (j : Fin k) : 0 ≤ yv s M k u j := by
  unfold yv; positivity

lemma yv_le {s M k : ℕ} (hM : 1 ≤ M) (u : Fin s → Fin M) (j : Fin k) : yv s M k u j ≤ s := by
  unfold yv
  have hN : (0 : ℝ) < Nv M k j := by exact_mod_cast Nv_pos hM j
  rw [div_le_iff₀ hN]
  have := psum_le (k := k) u j
  unfold Nv
  exact_mod_cast this

lemma abs_yv_le {s M k : ℕ} (hM : 1 ≤ M) (u : Fin s → Fin M) (j : Fin k) :
    |yv s M k u j| ≤ s := by
  rw [abs_of_nonneg (yv_nonneg s M k u j)]; exact yv_le hM u j

/-- The per-box bound, uniform over the box. -/
lemma box_bound (M k s : ℕ) (hM : 1 ≤ M) (hs : 1 ≤ s) (m : Fin k → ℕ) (α : Fin k → ℝ)
    (hα : ∀ j, (m j : ℝ) / (M : ℝ) ^ (j.val + 1) ≤ α j ∧
      α j < ((m j : ℝ) + 1) / (M : ℝ) ^ (j.val + 1)) :
    ‖weylSum M k α‖ ^ (2 * s) ≤ Real.exp (2 * π * (k * s)) * Gbox s M k m := by
  have hN : ∀ j, 0 < Nv M k j := Nv_pos hM
  have hpow : ‖weylSum M k α‖ ^ (2 * s) = ‖weylSum M k α ^ s‖ ^ 2 := by
    rw [norm_pow, ← pow_mul, mul_comm]
  rw [hpow, weylSum_pow]
  have hsplit : ∀ u : Fin s → Fin M,
      Complex.exp (2 * π * I * ((∑ j, α j * (psum u j : ℝ) : ℝ) : ℂ)) =
        gphase (Nv M k) m (nZ s M k u) * Complex.exp (2 * π * I *
          ((∑ j, (α j * Nv M k j - m j) * yv s M k u j : ℝ) : ℂ)) :=
    fun u => phase_split (Nv M k) hN m α (fun j => psum u j)
  rw [Finset.sum_congr rfl fun u _ => hsplit u]
  have ht : ∀ j, |α j * Nv M k j - m j| ≤ 1 := by
    intro j
    have hNj : (0 : ℝ) < (M : ℝ) ^ (j.val + 1) := by
      have : (0 : ℝ) < M := by exact_mod_cast hM
      positivity
    obtain ⟨h1, h2⟩ := hα j
    rw [div_le_iff₀ hNj] at h1
    rw [lt_div_iff₀ hNj] at h2
    have hc : (Nv M k j : ℝ) = (M : ℝ) ^ (j.val + 1) := by unfold Nv; push_cast; ring
    rw [hc, abs_le]
    constructor <;> linarith
  have hY : (0 : ℝ) < s := by exact_mod_cast hs
  exact taylor_cs (fun u => gphase (Nv M k) m (nZ s M k u)) (fun u => (norm_gphase _ _ _).le)
    (yv s M k) hY (fun u j => abs_yv_le hM u j) _ ht

lemma summable_G (M k s : ℕ) (hM : 1 ≤ M) (hs : 1 ≤ s) (m : Fin k → ℕ) :
    Summable (fun ℓ : ℕ => aw ℓ / (s : ℝ) ^ ℓ * ∑ f : Fin ℓ → Fin k,
      ‖mom (fun u : Fin s → Fin M => gphase (Nv M k) m (nZ s M k u)) (yv s M k) ℓ f‖ ^ 2) :=
  summable_momSeries _ (fun u => (norm_gphase _ _ _).le) _ (by exact_mod_cast hs)
    (fun u j => abs_yv_le hM u j)

/-- The congruence set `R`. -/
noncomputable def Rset (s M k : ℕ) : Finset ((Fin s → Fin M) × (Fin s → Fin M)) :=
  (univ : Finset ((Fin s → Fin M) × (Fin s → Fin M))).filter
    (fun p => ∀ j, (Nv M k j : ℤ) ∣ nZ s M k p.1 j - nZ s M k p.2 j)

/-- Summing the per-box bounds over all boxes. -/
lemma sum_G_le (M k s : ℕ) (hM : 1 ≤ M) (hs : 1 ≤ s) :
    ∑ m ∈ Fintype.piFinset (fun j : Fin k => range (Nv M k j)), Gbox s M k m ≤
      Real.exp (2 * π * (k * s)) * ((∏ j, (Nv M k j : ℝ)) * (Rset s M k).card) := by
  have hN : ∀ j, 0 < Nv M k j := Nv_pos hM
  have hs' : (0 : ℝ) < s := by exact_mod_cast hs
  set C : ℝ := (∏ j, (Nv M k j : ℝ)) * (Rset s M k).card with hC
  have hC0 : 0 ≤ C := by positivity
  unfold Gbox
  rw [← Summable.tsum_finsetSum (fun m _ => summable_G M k s hM hs m)]
  have hterm : ∀ ℓ : ℕ, ∑ m ∈ Fintype.piFinset (fun j : Fin k => range (Nv M k j)),
      aw ℓ / (s : ℝ) ^ ℓ * ∑ f : Fin ℓ → Fin k,
        ‖mom (fun u : Fin s → Fin M => gphase (Nv M k) m (nZ s M k u)) (yv s M k) ℓ f‖ ^ 2 ≤
      aw ℓ * ((k : ℝ) * s) ^ ℓ * C := by
    intro ℓ
    rw [← Finset.mul_sum, Finset.sum_comm]
    have hf : ∀ f : Fin ℓ → Fin k, ∑ m ∈ Fintype.piFinset (fun j : Fin k => range (Nv M k j)),
        ‖mom (fun u : Fin s → Fin M => gphase (Nv M k) m (nZ s M k u)) (yv s M k) ℓ f‖ ^ 2 ≤
          C * ((s : ℝ) ^ ℓ) ^ 2 := by
      intro f
      have hg := grid_orth (Nv M k) hN (nZ s M k) (fun u => ∏ r, yv s M k u (f r))
      simp only [mom]
      rw [hg]
      have hW0 : ∀ u : Fin s → Fin M, 0 ≤ ∏ r, yv s M k u (f r) :=
        fun u => Finset.prod_nonneg fun r _ => yv_nonneg s M k u (f r)
      have hW1 : ∀ u : Fin s → Fin M, ∏ r, yv s M k u (f r) ≤ (s : ℝ) ^ ℓ := by
        intro u
        calc ∏ r, yv s M k u (f r) ≤ ∏ _r : Fin ℓ, (s : ℝ) :=
              Finset.prod_le_prod (fun r _ => yv_nonneg s M k u (f r)) (fun r _ => yv_le hM u (f r))
          _ = (s : ℝ) ^ ℓ := by simp
      have hsum : ∑ p ∈ Rset s M k, (∏ r, yv s M k p.1 (f r)) * (∏ r, yv s M k p.2 (f r)) ≤
          (Rset s M k).card * ((s : ℝ) ^ ℓ) ^ 2 := by
        calc ∑ p ∈ Rset s M k, (∏ r, yv s M k p.1 (f r)) * (∏ r, yv s M k p.2 (f r))
            ≤ ∑ _p ∈ Rset s M k, ((s : ℝ) ^ ℓ) ^ 2 := by
              refine Finset.sum_le_sum fun p _ => ?_
              rw [sq]
              exact mul_le_mul (hW1 p.1) (hW1 p.2) (hW0 p.2) (by positivity)
          _ = (Rset s M k).card * ((s : ℝ) ^ ℓ) ^ 2 := by rw [Finset.sum_const, nsmul_eq_mul]
      have hP : (0 : ℝ) ≤ ∏ j, (Nv M k j : ℝ) := by positivity
      calc (∏ j, (Nv M k j : ℝ)) * ∑ p ∈ Rset s M k,
            (∏ r, yv s M k p.1 (f r)) * (∏ r, yv s M k p.2 (f r))
          ≤ (∏ j, (Nv M k j : ℝ)) * ((Rset s M k).card * ((s : ℝ) ^ ℓ) ^ 2) :=
            mul_le_mul_of_nonneg_left hsum hP
        _ = C * ((s : ℝ) ^ ℓ) ^ 2 := by rw [hC]; ring
    calc aw ℓ / (s : ℝ) ^ ℓ * ∑ f : Fin ℓ → Fin k, ∑ m ∈ Fintype.piFinset
          (fun j : Fin k => range (Nv M k j)),
          ‖mom (fun u : Fin s → Fin M => gphase (Nv M k) m (nZ s M k u)) (yv s M k) ℓ f‖ ^ 2
        ≤ aw ℓ / (s : ℝ) ^ ℓ * ∑ _f : Fin ℓ → Fin k, C * ((s : ℝ) ^ ℓ) ^ 2 :=
          mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun f _ => hf f)
            (div_nonneg (aw_pos ℓ).le (by positivity))
      _ = aw ℓ * ((k : ℝ) * s) ^ ℓ * C := by
          rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ, Fintype.card_fun,
            Fintype.card_fin, Fintype.card_fin]
          have : (s : ℝ) ^ ℓ ≠ 0 := by positivity
          push_cast
          field_simp
          ring
  have hB := (hasSum_aw_mul ((k : ℝ) * s)).mul_right C
  calc ∑' ℓ, ∑ m ∈ Fintype.piFinset (fun j : Fin k => range (Nv M k j)),
        aw ℓ / (s : ℝ) ^ ℓ * ∑ f : Fin ℓ → Fin k,
          ‖mom (fun u : Fin s → Fin M => gphase (Nv M k) m (nZ s M k u)) (yv s M k) ℓ f‖ ^ 2
      ≤ ∑' ℓ : ℕ, aw ℓ * ((k : ℝ) * s) ^ ℓ * C :=
        Summable.tsum_le_tsum hterm (summable_sum fun m _ => summable_G M k s hM hs m)
          hB.summable
    _ = Real.exp (2 * π * (k * s)) * C := hB.tsum_eq

lemma Rset_card_le (M k s : ℕ) (hM : 1 ≤ M) :
    (Rset s M k).card ≤ (2 * s + 1) ^ k * vinogradovCount s k M := by
  have h := card_congr_le (Nv M k) (Nv_pos hM) (nZ s M k) s
    (fun u j => by unfold nZ; positivity)
    (fun u j => by unfold nZ Nv; exact_mod_cast psum_le u j)
  have hJ : ((univ : Finset ((Fin s → Fin M) × (Fin s → Fin M))).filter
      (fun p => nZ s M k p.1 = nZ s M k p.2)).card = vinogradovCount s k M := by
    unfold vinogradovCount
    rw [Finset.univ_product_univ]
    congr 1
    ext p
    simp only [mem_filter, mem_univ, true_and]
    constructor
    · intro h j hj
      rw [Finset.mem_Icc] at hj
      have := congr_fun h ⟨j - 1, by omega⟩
      simp only [nZ, psum, Nat.cast_inj] at this
      have hj1 : j - 1 + 1 = j := by omega
      rw [hj1] at this
      exact this
    · intro h
      funext j
      have := h (j.val + 1) (by rw [Finset.mem_Icc]; omega)
      simp only [nZ, psum]
      exact_mod_cast this
  rw [hJ] at h
  exact h

lemma prod_Nv (M k : ℕ) : ∏ j, (Nv M k j : ℝ) = (M : ℝ) ^ (k * (k + 1) / 2) := by
  simp only [Nv, Nat.cast_pow]
  rw [Finset.prod_pow_eq_pow_sum]
  congr 1
  rw [Fin.sum_univ_eq_sum_range (fun i => i + 1)]
  have h2 : ∀ n, 2 * ∑ i ∈ range n, (i + 1) = n * (n + 1) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih => rw [Finset.sum_range_succ, mul_add, ih]; ring
  rw [← h2 k, Nat.mul_div_cancel_left _ two_pos]

end ArtinPrimitiveRoots.L33B

namespace ArtinPrimitiveRoots

open Real

end ArtinPrimitiveRoots
end

section
open ArtinPrimitiveRoots
open Real
open L33B in
theorem solution :
    ∃ C : ℝ, ∀ M k s : ℕ, 1 ≤ M → 1 ≤ k → 1 ≤ s →
      ∑ m ∈ Fintype.piFinset (fun j : Fin k => Finset.range (M ^ (j.val + 1))),
          (⨆ α : {α : Fin k → ℝ // ∀ j, (m j : ℝ) / (M : ℝ) ^ (j.val + 1) ≤ α j ∧
              α j < ((m j : ℝ) + 1) / (M : ℝ) ^ (j.val + 1)},
            ‖weylSum M k α.1‖ ^ (2 * s)) ≤
        exp (C * ((s : ℝ) * k + k)) * (M : ℝ) ^ (k * (k + 1) / 2) * (vinogradovCount s k M : ℝ) := by
  refine ⟨15, fun M k s hM hk hs => ?_⟩
  set E := Real.exp (2 * π * (k * s)) with hE
  have hE0 : 0 ≤ E := (Real.exp_pos _).le
  have hbox : ∀ m ∈ Fintype.piFinset (fun j : Fin k => Finset.range (M ^ (j.val + 1))),
      (⨆ α : {α : Fin k → ℝ // ∀ j, (m j : ℝ) / (M : ℝ) ^ (j.val + 1) ≤ α j ∧
          α j < ((m j : ℝ) + 1) / (M : ℝ) ^ (j.val + 1)}, ‖weylSum M k α.1‖ ^ (2 * s)) ≤
        E * Gbox s M k m := by
    intro m _
    have : Nonempty {α : Fin k → ℝ // ∀ j, (m j : ℝ) / (M : ℝ) ^ (j.val + 1) ≤ α j ∧
        α j < ((m j : ℝ) + 1) / (M : ℝ) ^ (j.val + 1)} := by
      refine ⟨⟨fun j => (m j : ℝ) / (M : ℝ) ^ (j.val + 1), fun j => ⟨le_rfl, ?_⟩⟩⟩
      have : (0 : ℝ) < (M : ℝ) ^ (j.val + 1) := by
        have : (0 : ℝ) < M := by exact_mod_cast hM
        positivity
      exact div_lt_div_of_pos_right (by linarith) this
    exact ciSup_le fun α => box_bound M k s hM hs m α.1 α.2
  have hG := sum_G_le M k s hM hs
  have hR : ((Rset s M k).card : ℝ) ≤ (2 * s + 1 : ℝ) ^ k * vinogradovCount s k M := by
    exact_mod_cast Rset_card_le M k s hM
  have hP := prod_Nv M k
  have hJ0 : (0 : ℝ) ≤ vinogradovCount s k M := Nat.cast_nonneg _
  have hMK : (0 : ℝ) ≤ (M : ℝ) ^ (k * (k + 1) / 2) := by positivity
  have h2s : (2 * s + 1 : ℝ) ^ k ≤ Real.exp (2 * s * k) := by
    rw [mul_comm (2 * (s : ℝ)) k, Real.exp_nat_mul]
    exact pow_le_pow_left₀ (by positivity) (by linarith [Real.add_one_le_exp (2 * (s : ℝ))]) k
  have hfin : E * E * Real.exp (2 * s * k) ≤ Real.exp (15 * ((s : ℝ) * k + k)) := by
    rw [hE, ← Real.exp_add, ← Real.exp_add, Real.exp_le_exp]
    have hpi := Real.pi_lt_d2
    have hks : (0 : ℝ) ≤ (k : ℝ) * s := by positivity
    have hk0 : (0 : ℝ) ≤ k := by positivity
    nlinarith
  calc ∑ m ∈ Fintype.piFinset (fun j : Fin k => Finset.range (M ^ (j.val + 1))),
        (⨆ α : {α : Fin k → ℝ // ∀ j, (m j : ℝ) / (M : ℝ) ^ (j.val + 1) ≤ α j ∧
            α j < ((m j : ℝ) + 1) / (M : ℝ) ^ (j.val + 1)}, ‖weylSum M k α.1‖ ^ (2 * s))
      ≤ ∑ m ∈ Fintype.piFinset (fun j : Fin k => Finset.range (M ^ (j.val + 1))),
          E * Gbox s M k m := Finset.sum_le_sum hbox
    _ = E * ∑ m ∈ Fintype.piFinset (fun j : Fin k => Finset.range (Nv M k j)), Gbox s M k m := by
        rw [Finset.mul_sum]; rfl
    _ ≤ E * (E * ((∏ j, (Nv M k j : ℝ)) * (Rset s M k).card)) :=
        mul_le_mul_of_nonneg_left hG hE0
    _ ≤ E * (E * ((M : ℝ) ^ (k * (k + 1) / 2) *
          ((2 * s + 1 : ℝ) ^ k * vinogradovCount s k M))) := by
        rw [hP]
        gcongr
    _ = (E * E * (2 * s + 1 : ℝ) ^ k) * (M : ℝ) ^ (k * (k + 1) / 2) *
          (vinogradovCount s k M : ℝ) := by ring
    _ ≤ Real.exp (15 * ((s : ℝ) * k + k)) * (M : ℝ) ^ (k * (k + 1) / 2) *
          (vinogradovCount s k M : ℝ) := by
        gcongr
        calc E * E * (2 * s + 1 : ℝ) ^ k ≤ E * E * Real.exp (2 * s * k) :=
              mul_le_mul_of_nonneg_left h2s (by positivity)
          _ ≤ _ := hfin
end

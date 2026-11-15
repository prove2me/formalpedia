-- Prove2me | Definitions.Def_RPLib_S3_EllW2K1
-- name    : RPLib_S3_EllW2K1
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-14T12:28:15.101682+00:00
-- url     : https://prove2.me/theorems/c9474b54-18b2-43db-ad1f-b28772f09301
-- title:
--   The Eichler-Selberg trace formula in weight two: discrepancy of a periodic sequence through its finite Fourier transform
-- statement:
--   Discrepancy of a periodic sequence through its finite Fourier transform.
--
--   For `g : ZMod q → ℂ` with discrete Fourier transform `ZMod.dft g j = Σ_x e(-xj/q) g x`:
--   * `two_mul_div_le_sin`, `min_div_le_sin`: Jordan's inequality `sin (π v / q) ≥ 2 min(v, q-v) / q`.
--   * `norm_stdAddChar_sub_one_ge`: `‖e(j/q) - 1‖ ≥ 4 min(j, q-j) / q`.
--   * `norm_geom_sum_le`, `norm_sum_stdAddChar_le`: `‖Σ_{u<m} e(ju/q)‖ ≤ q / (2 min(j, q-j))` for `j ≠ 0`.
--   * **`norm_sum_sub_dft_le`**: `‖Σ_{u<m} (g u - 𝓕g(0)/q)‖ ≤ Σ_{j≠0} ‖𝓕g(j)‖ / (2 min(j, q-j))` (any `m`).
--   * `sum_zmod_val`, `dft_val_apply`: the transform of `x ↦ f x.val` as a sum over `range q`.
--   * **`norm_sum_sub_le_dft_int`**: the same bound for a `q`-periodic `f : ℤ → ℂ` with mean `μ`.
--
--   **Formalization note.** Library module of a formalization of the Ramanujan-Petersson conjecture (trace-formula layer in weight two: the Eichler-Selberg / Cohen-Oesterlé trace formula for $T_n \langle \delta \rangle$ on $S_2(\Gamma_1(M))$, $M \ge 4$, proved by Zagier's kernel method with Hecke's convergence trick $|cz+d|^{-2s}$, $s \to 0^+$). It contains definitions together with proved lemmas (no `sorry`), so that later solution files can import them.
-- source:
--   H. Cohen, Trace des opérateurs de Hecke sur Γ0(N), Séminaire de Théorie des Nombres de Bordeaux 1976-1977, exp. 4; J. Oesterlé, Sur la trace des opérateurs de Hecke, Thèse de 3e cycle, Université Paris-Sud (Orsay) 1977; D. Zagier, The Eichler-Selberg trace formula on SL2(Z), appendix to S. Lang, Introduction to Modular Forms, Grundlehren 222, Springer 1976; H. Cohen and F. Strömberg, Modular Forms: A Classical Approach, Graduate Studies in Mathematics 179, AMS 2017, Section 12.4; E. Hecke, Theorie der Eisensteinschen Reihen höherer Stufe und ihre Anwendung auf Funktionentheorie und Arithmetik, Abh. Math. Sem. Univ. Hamburg 5 (1927), 199-224; A. Weil, On some exponential sums, Proc. Nat. Acad. Sci. USA 34 (1948), 204-207; H. Iwaniec and E. Kowalski, Analytic Number Theory, AMS Colloquium Publications 53, 2004, Chapters 11 and 16

import Mathlib
import Definitions.Def_RPLib_S3_EllW2AS

/-!
# S3-ES-Wt2 (O6, file K1): discrepancy of a periodic sequence through its finite Fourier transform

For `g : ZMod q → ℂ` with discrete Fourier transform `ZMod.dft g j = Σ_x e(-xj/q) g x`:
* `two_mul_div_le_sin`, `min_div_le_sin`: Jordan's inequality `sin (π v / q) ≥ 2 min(v, q-v) / q`.
* `norm_stdAddChar_sub_one_ge`: `‖e(j/q) - 1‖ ≥ 4 min(j, q-j) / q`.
* `norm_geom_sum_le`, `norm_sum_stdAddChar_le`: `‖Σ_{u<m} e(ju/q)‖ ≤ q / (2 min(j, q-j))` for `j ≠ 0`.
* **`norm_sum_sub_dft_le`**: `‖Σ_{u<m} (g u - 𝓕g(0)/q)‖ ≤ Σ_{j≠0} ‖𝓕g(j)‖ / (2 min(j, q-j))` (any `m`).
* `sum_zmod_val`, `dft_val_apply`: the transform of `x ↦ f x.val` as a sum over `range q`.
* **`norm_sum_sub_le_dft_int`**: the same bound for a `q`-periodic `f : ℤ → ℂ` with mean `μ`.
-/

open Finset

set_option autoImplicit false

noncomputable section

namespace RamanujanPetersson.EllW2

/-- Jordan's inequality in the form used here. -/
lemma two_mul_div_le_sin {a q : ℝ} (hq : 0 < q) (ha : 0 ≤ a) (h2 : 2 * a ≤ q) :
    2 * a / q ≤ Real.sin (Real.pi * a / q) := by
  have hpi := Real.pi_pos
  have hx : 0 ≤ Real.pi * a / q := by positivity
  have hx' : Real.pi * a / q ≤ Real.pi / 2 := by
    rw [div_le_div_iff₀ hq two_pos]; nlinarith
  have h := Real.mul_le_sin hx hx'
  have e : 2 * a / q = 2 / Real.pi * (Real.pi * a / q) := by
    field_simp
  rw [e]; exact h

lemma min_div_le_sin {v q : ℕ} (hv : v < q) :
    2 * ((min v (q - v) : ℕ) : ℝ) / q ≤ Real.sin (Real.pi * v / q) := by
  have hq : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  rcases le_total v (q - v) with h | h
  · rw [min_eq_left h]
    exact two_mul_div_le_sin hq (by positivity) (by exact_mod_cast (show 2 * v ≤ q by omega))
  · rw [min_eq_right h]
    have hpq : Real.pi * ((q : ℝ) - v) / q = Real.pi - Real.pi * v / q := by
      rw [mul_sub, sub_div, mul_div_assoc Real.pi (q : ℝ) (q : ℝ), div_self hq.ne', mul_one]
    have e : Real.sin (Real.pi * v / q) = Real.sin (Real.pi * ((q - v : ℕ) : ℝ) / q) := by
      rw [Nat.cast_sub hv.le, hpq, Real.sin_pi_sub]
    rw [e]
    exact two_mul_div_le_sin hq (by positivity) (by exact_mod_cast (show 2 * (q - v) ≤ q by omega))

lemma norm_stdAddChar_sub_one_ge {q : ℕ} [NeZero q] (j : ZMod q) :
    4 * ((min j.val (q - j.val) : ℕ) : ℝ) / q ≤ ‖(ZMod.stdAddChar j : ℂ) - 1‖ := by
  have hj : ((j.val : ℤ) : ZMod q) = j := by
    rw [Int.cast_natCast, ZMod.natCast_zmod_val]
  have e : (ZMod.stdAddChar j : ℂ) =
      Complex.exp (Complex.I * ((2 * Real.pi * j.val / q : ℝ) : ℂ)) := by
    have e0 := ZMod.stdAddChar_coe (N := q) (j.val : ℤ)
    rw [hj] at e0
    rw [e0]; congr 1; push_cast; ring
  rw [e, Complex.norm_exp_I_mul_ofReal_sub_one, Real.norm_eq_abs]
  have h1 := min_div_le_sin (ZMod.val_lt j)
  have h2 : 2 * Real.pi * j.val / q / 2 = Real.pi * j.val / q := by ring
  rw [h2]
  calc 4 * ((min j.val (q - j.val) : ℕ) : ℝ) / q
        = 2 * (2 * ((min j.val (q - j.val) : ℕ) : ℝ) / q) := by ring
    _ ≤ 2 * Real.sin (Real.pi * j.val / q) := by gcongr
    _ ≤ |2 * Real.sin (Real.pi * j.val / q)| := le_abs_self _

lemma norm_geom_sum_le {ζ : ℂ} (hζ : ‖ζ‖ = 1) (h1 : ζ ≠ 1) (m : ℕ) :
    ‖∑ u ∈ range m, ζ ^ u‖ ≤ 2 / ‖ζ - 1‖ := by
  rw [geom_sum_eq h1 m, norm_div]
  have h0 : 0 < ‖ζ - 1‖ := norm_pos_iff.mpr (sub_ne_zero.mpr h1)
  have h2 : ‖ζ ^ m - 1‖ ≤ 2 := by
    calc ‖ζ ^ m - 1‖ ≤ ‖ζ ^ m‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
      _ = 2 := by rw [norm_pow, hζ, one_pow, norm_one]; norm_num
  exact div_le_div_of_nonneg_right h2 h0.le

lemma norm_sum_stdAddChar_le {q : ℕ} [NeZero q] {j : ZMod q} (hj : j ≠ 0) (m : ℕ) :
    ‖∑ u ∈ range m, (ZMod.stdAddChar (j * (u : ZMod q)) : ℂ)‖ ≤
      q / (2 * ((min j.val (q - j.val) : ℕ) : ℝ)) := by
  have hq : (0 : ℝ) < q := by exact_mod_cast (NeZero.pos q)
  have hv0 : 0 < j.val := by
    rcases Nat.eq_zero_or_pos j.val with h | h
    · exact absurd ((ZMod.val_eq_zero j).mp h) hj
    · exact h
  have hvq := ZMod.val_lt j
  have hmin : (0 : ℝ) < ((min j.val (q - j.val) : ℕ) : ℝ) := by
    exact_mod_cast (show 0 < min j.val (q - j.val) by omega)
  have e : ∀ u : ℕ, (ZMod.stdAddChar (j * (u : ZMod q)) : ℂ) = (ZMod.stdAddChar j) ^ u := by
    intro u; rw [mul_comm, ← nsmul_eq_mul, AddChar.map_nsmul_eq_pow]
  simp_rw [e]
  have hζ : ‖(ZMod.stdAddChar j : ℂ)‖ = 1 := AddChar.norm_apply _ _
  have h1 : (ZMod.stdAddChar j : ℂ) ≠ 1 := by
    intro h; apply hj; apply ZMod.injective_stdAddChar; rw [h, AddChar.map_zero_eq_one]
  have hlow := norm_stdAddChar_sub_one_ge j
  have hpos : 0 < 4 * ((min j.val (q - j.val) : ℕ) : ℝ) / q := by positivity
  calc _ ≤ 2 / ‖(ZMod.stdAddChar j : ℂ) - 1‖ := norm_geom_sum_le hζ h1 m
    _ ≤ 2 / (4 * ((min j.val (q - j.val) : ℕ) : ℝ) / q) :=
        div_le_div_of_nonneg_left (by norm_num) hpos hlow
    _ = _ := by field_simp; ring

/-- **Discrepancy through the finite Fourier transform.** -/
theorem norm_sum_sub_dft_le {q : ℕ} [NeZero q] (g : ZMod q → ℂ) (m : ℕ) :
    ‖∑ u ∈ range m, (g u - ZMod.dft g 0 / q)‖ ≤
      ∑ j ∈ univ.erase (0 : ZMod q),
        ‖ZMod.dft g j‖ / (2 * ((min j.val (q - j.val) : ℕ) : ℝ)) := by
  have hinv : ∀ u : ZMod q, g u - ZMod.dft g 0 / q =
      (q : ℂ)⁻¹ * ∑ j ∈ univ.erase (0 : ZMod q), (ZMod.stdAddChar (j * (u : ZMod q)) : ℂ) * ZMod.dft g j := by
    intro u
    have h := congrFun (ZMod.dft.symm_apply_apply g) u
    rw [ZMod.invDFT_apply] at h
    rw [← h, smul_eq_mul, ← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ (0 : ZMod q))]
    simp only [smul_eq_mul, zero_mul, AddChar.map_zero_eq_one, one_mul]
    ring
  have hsum : ∑ u ∈ range m, (g u - ZMod.dft g 0 / q) =
      (q : ℂ)⁻¹ * ∑ j ∈ univ.erase (0 : ZMod q),
        ZMod.dft g j * ∑ u ∈ range m, (ZMod.stdAddChar (j * (u : ZMod q)) : ℂ) := by
    rw [Finset.sum_congr rfl (fun (u : ℕ) _ => hinv (u : ZMod q)), ← Finset.mul_sum, Finset.sum_comm]
    congr 1
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun u _ => by ring)
  have hq' : (0 : ℝ) < q := by exact_mod_cast NeZero.pos q
  have hqne : (q : ℝ) ≠ 0 := hq'.ne'
  rw [hsum, norm_mul, norm_inv, Complex.norm_natCast]
  calc (q : ℝ)⁻¹ * ‖∑ j ∈ univ.erase (0 : ZMod q),
          ZMod.dft g j * ∑ u ∈ range m, (ZMod.stdAddChar (j * (u : ZMod q)) : ℂ)‖
      ≤ (q : ℝ)⁻¹ * ∑ j ∈ univ.erase (0 : ZMod q),
          ‖ZMod.dft g j‖ * ((q : ℝ) / (2 * ((min j.val (q - j.val) : ℕ) : ℝ))) := by
        gcongr
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j hj => ?_)
        rw [norm_mul]
        gcongr
        exact norm_sum_stdAddChar_le (Finset.ne_of_mem_erase hj) m
    _ = _ := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        have hi : (q : ℝ)⁻¹ * q = 1 := inv_mul_cancel₀ hqne
        calc (q : ℝ)⁻¹ * (‖ZMod.dft g j‖ * ((q : ℝ) / (2 * ((min j.val (q - j.val) : ℕ) : ℝ))))
            = ‖ZMod.dft g j‖ * ((q : ℝ)⁻¹ * q) / (2 * ((min j.val (q - j.val) : ℕ) : ℝ)) := by ring
          _ = _ := by rw [hi, mul_one]

/-- Sums over `ZMod q` of a function of the value are sums over `range q`. -/
lemma sum_zmod_val {q : ℕ} [NeZero q] (h : ℕ → ℂ) :
    ∑ x : ZMod q, h x.val = ∑ u ∈ range q, h u := by
  refine Finset.sum_bij' (fun x _ => x.val) (fun u _ => (u : ZMod q))
    (fun x _ => Finset.mem_range.mpr (ZMod.val_lt x)) (fun u _ => Finset.mem_univ _)
    (fun x _ => ZMod.natCast_zmod_val x) (fun u hu => ZMod.val_natCast_of_lt (Finset.mem_range.mp hu))
    (fun x _ => rfl)

lemma dft_val_apply {q : ℕ} [NeZero q] (f : ℤ → ℂ) (j : ZMod q) :
    ZMod.dft (fun x : ZMod q => f (x.val : ℤ)) j =
      ∑ u ∈ range q, (ZMod.stdAddChar (-((u : ZMod q) * j)) : ℂ) * f u := by
  rw [ZMod.dft_apply]
  have := sum_zmod_val (q := q) (fun v => (ZMod.stdAddChar (-((v : ZMod q) * j)) : ℂ) * f v)
  simp only [ZMod.natCast_zmod_val] at this
  rw [← this]
  exact Finset.sum_congr rfl fun x _ => by rw [smul_eq_mul]

/-- **Discrepancy of a periodic sequence** through its finite Fourier transform. -/
theorem norm_sum_sub_le_dft_int {f : ℤ → ℂ} {q : ℕ} [NeZero q] (hf : ∀ t, f (t + q) = f t)
    {μ : ℂ} (hμ : ∑ u ∈ range q, f u = q * μ) (m : ℕ) :
    ‖∑ u ∈ range m, (f u - μ)‖ ≤
      ∑ j ∈ univ.erase (0 : ZMod q),
        ‖ZMod.dft (fun x : ZMod q => f (x.val : ℤ)) j‖ / (2 * ((min j.val (q - j.val) : ℕ) : ℝ)) := by
  have h0 : ZMod.dft (fun x : ZMod q => f (x.val : ℤ)) 0 / q = μ := by
    have hq : (q : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne q
    rw [ZMod.dft_apply_zero, sum_zmod_val (q := q) (fun v => f v), hμ]; field_simp
  have hgu : ∀ u : ℕ, f ((u % q : ℕ) : ℤ) = f u := by
    intro u; rw [Int.natCast_mod]; exact (periodic_emod hf u).symm
  have h := norm_sum_sub_dft_le (fun x : ZMod q => f (x.val : ℤ)) m
  rw [h0] at h
  simp only [ZMod.val_natCast, hgu] at h
  exact h

end RamanujanPetersson.EllW2



-- Prove2me | Definitions.Def_RPLib_S3_KernelA
-- name    : RPLib_S3_KernelA
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-13T20:52:06.284053+00:00
-- url     : https://prove2.me/theorems/26fe52db-bcea-41b1-a612-668495df7c5d
-- title:
--   The Eichler-Selberg trace formula, kernel part A: the Hecke kernel $\omega$ and its convergence
-- statement:
--   For $M \ge 1$, $k \ge 3$, $n \ge 1$ and a residue $\delta'$ mod $M$, let $\Delta = \{g \in M_2(\mathbb{Z}) : \det g = n,\ c \equiv 0,\ a \equiv \delta' \pmod M\}$ and
--   $$\omega(z,w) = \sum_{g \in \Delta} (c z w + d w + a z + b)^{-k}.$$
--   The series converges absolutely for $z, w$ in the upper half plane and is holomorphic in $z$; the proof uses the lattice bound $\sum_{\det g = n} N(g)^{-s} < \infty$ for $s > 1$.
--
--   **Formalization note.** Library module of a formalization of the Ramanujan-Petersson conjecture (trace-formula layer: the Eichler-Selberg trace formula on $S_k(\Gamma_1(M))$ for $k \ge 3$, proved by Zagier's kernel method). It contains definitions together with proved lemmas (no `sorry`), so that later solution files can import them.
-- source:
--   D. Zagier, The Eichler-Selberg trace formula on SL2(Z), appendix to S. Lang, Introduction to Modular Forms, Grundlehren 222, Springer 1976 (with the Correction in later printings); H. Cohen and F. Strömberg, Modular Forms: A Classical Approach, Graduate Studies in Mathematics 179, AMS 2017, Section 12.4

import Mathlib

/-!
# S3-Kernel, part A: the Hecke kernel `ω`, its absolute convergence and holomorphy (`k ≥ 3`)

* lattice lemma `summable_N_rpow`: `Σ_{det g = n} N(g)^(-s) < ∞` for `s > 1` (`N` = sum of squared entries);
* geometric bound `N_le_normSq_Q`: `(y v)² N(g) ≤ (1 + |z|²)(1 + |w|²) |Q(g; z, w)|²`, and `two_det_le_normSq_Q`;
* `DeltaSet M n δ' = {g : det g = n, c ≡ 0, a ≡ δ' (mod M)}` and
  `omega M k n δ' z w = Σ_{g ∈ DeltaSet} (c z w + d w + a z + b)^(-k)` (`Q g z w = [1 w] g [z 1]ᵀ`);
* `summable_omega` (absolute convergence) and `differentiableOn_omega` (holomorphy in `z` on `Im z > 0`).
-/

open Filter Complex

set_option autoImplicit false

noncomputable section

namespace RamanujanPetersson.Kernel

/-- Integer `2 × 2` matrices of determinant `n`. -/
abbrev DetSet (n : ℤ) := {g : Matrix (Fin 2) (Fin 2) ℤ // g.det = n}

/-- Sum of squares of the entries. -/
def N (g : Matrix (Fin 2) (Fin 2) ℤ) : ℝ :=
  (g 0 0 : ℝ) ^ 2 + (g 0 1 : ℝ) ^ 2 + (g 1 0 : ℝ) ^ 2 + (g 1 1 : ℝ) ^ 2

lemma det_eq (g : Matrix (Fin 2) (Fin 2) ℤ) : g.det = g 0 0 * g 1 1 - g 0 1 * g 1 0 :=
  Matrix.det_fin_two g

/-- The row-line index: `g ↦ ((c, d), ⌊(ac + bd) n / (c² + d²)⌋)`. -/
def phi (n : ℤ) (g : Matrix (Fin 2) (Fin 2) ℤ) : (Fin 2 → ℤ) × ℤ :=
  (![g 1 0, g 1 1], ⌊((g 0 0 * g 1 0 + g 0 1 * g 1 1 : ℤ) : ℝ) * n / ((g 1 0 : ℝ) ^ 2 + (g 1 1 : ℝ) ^ 2)⌋)

lemma R_pos {n : ℤ} (hn : 0 < n) (g : DetSet n) : 0 < (g.1 1 0 : ℝ) ^ 2 + (g.1 1 1 : ℝ) ^ 2 := by
  by_contra h
  have h1 : (g.1 1 0 : ℝ) = 0 := by nlinarith [sq_nonneg (g.1 1 0 : ℝ), sq_nonneg (g.1 1 1 : ℝ)]
  have h2 : (g.1 1 1 : ℝ) = 0 := by nlinarith [sq_nonneg (g.1 1 0 : ℝ), sq_nonneg (g.1 1 1 : ℝ)]
  have h1' : g.1 1 0 = 0 := by exact_mod_cast h1
  have h2' : g.1 1 1 = 0 := by exact_mod_cast h2
  have := g.2
  rw [det_eq, h1', h2'] at this
  omega

lemma phi_injective {n : ℤ} (hn : 0 < n) : Function.Injective (fun g : DetSet n => phi n g.1) := by
  rintro ⟨g, hg⟩ ⟨g', hg'⟩ h
  simp only [phi, Prod.mk.injEq] at h
  obtain ⟨hr, hj⟩ := h
  have hc : g 1 0 = g' 1 0 := by simpa using congrFun hr 0
  have hd : g 1 1 = g' 1 1 := by simpa using congrFun hr 1
  have hR := R_pos hn ⟨g, hg⟩
  rw [det_eq] at hg hg'
  set a := g 0 0; set b := g 0 1; set c := g 1 0; set d := g 1 1
  set a' := g' 0 0; set b' := g' 0 1
  rw [← hc, ← hd] at hj hg'
  set R : ℝ := (c : ℝ) ^ 2 + (d : ℝ) ^ 2 with hRdef
  -- the two real indices differ by the integer `a (b - b') - b (a - a')`
  have hK : (((a * c + b * d : ℤ) : ℝ) * n / R) =
      (((a' * c + b' * d : ℤ) : ℝ) * n / R) + ((a * (b - b') - b * (a - a') : ℤ) : ℝ) := by
    rw [div_add' _ _ _ hR.ne', div_left_inj' hR.ne']
    have e1 : (a - a') * d = (b - b') * c := by linarith
    have e1' : ((a : ℝ) - a') * d = ((b : ℝ) - b') * c := by exact_mod_cast e1
    have en : (n : ℝ) = a * d - b * c := by exact_mod_cast hg.symm
    push_cast
    rw [en]
    linear_combination ((a : ℝ) * c + b * d) * e1'
  have hfl : ⌊(((a * c + b * d : ℤ) : ℝ) * n / R)⌋ = ⌊(((a' * c + b' * d : ℤ) : ℝ) * n / R)⌋ +
      (a * (b - b') - b * (a - a')) := by rw [hK, Int.floor_add_intCast]
  have hK0 : a * (b - b') - b * (a - a') = 0 := by
    have : ⌊(((a * c + b * d : ℤ) : ℝ) * n / R)⌋ = ⌊(((a' * c + b' * d : ℤ) : ℝ) * n / R)⌋ := hj
    omega
  rw [hK0, Int.cast_zero, add_zero, div_left_inj' hR.ne'] at hK
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hm : a * c + b * d = a' * c + b' * d := by
    have := mul_right_cancel₀ hn' hK
    exact_mod_cast this
  have e1 : (a - a') * d = (b - b') * c := by linarith
  have hRi : 0 < c ^ 2 + d ^ 2 := by
    have h : (0:ℝ) < (c:ℝ) ^ 2 + (d:ℝ) ^ 2 := hR
    exact_mod_cast h
  have hα : (a - a') * (c ^ 2 + d ^ 2) = 0 := by linear_combination c * hm + d * e1
  have hβ : (b - b') * (c ^ 2 + d ^ 2) = 0 := by linear_combination d * hm - c * e1
  have ha : a = a' := by
    rcases mul_eq_zero.1 hα with h | h <;> [linarith; linarith]
  have hb : b = b' := by
    rcases mul_eq_zero.1 hβ with h | h <;> [linarith; linarith]
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j
  · exact ha
  · exact hb
  · exact hc
  · exact hd

/-- The lower bound `N g ≥ (c² + d²)(1 + j²)/(3 n²)` with `j` the row-line index. -/
lemma N_ge {n : ℤ} (hn : 0 < n) (g : DetSet n) :
    ((g.1 1 0 : ℝ) ^ 2 + (g.1 1 1 : ℝ) ^ 2) * (1 + ((phi n g.1).2 : ℝ) ^ 2) / (3 * (n : ℝ) ^ 2) ≤ N g.1 := by
  have hR := R_pos hn g
  have hg := g.2
  rw [det_eq] at hg
  set a := g.1 0 0; set b := g.1 0 1; set c := g.1 1 0; set d := g.1 1 1
  set R : ℝ := (c : ℝ) ^ 2 + (d : ℝ) ^ 2 with hRdef
  set m : ℝ := ((a * c + b * d : ℤ) : ℝ) with hmdef
  set x : ℝ := m * n / R with hxdef
  have hj : (phi n g.1).2 = ⌊x⌋ := rfl
  rw [hj]
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < n := by linarith
  -- `|⌊x⌋| ≤ |x| + 1`, so `⌊x⌋² ≤ 2 x² + 2`
  have hfl1 := Int.floor_le x
  have hfl2 := Int.lt_floor_add_one x
  have hj2 : ((⌊x⌋ : ℤ) : ℝ) ^ 2 ≤ 2 * x ^ 2 + 2 := by
    rcases le_or_gt 0 ((⌊x⌋ : ℤ) : ℝ) with h | h
    · nlinarith
    · have : (1 - x) ^ 2 ≤ 2 * x ^ 2 + 2 := by nlinarith [sq_nonneg (x + 1)]
      nlinarith
  -- Lagrange: `(a² + b²) R = m² + n²`
  have hlag : ((a : ℝ) ^ 2 + (b : ℝ) ^ 2) * R = m ^ 2 + (n : ℝ) ^ 2 := by
    have en : (n : ℝ) = a * d - b * c := by exact_mod_cast hg.symm
    rw [hmdef, en]; push_cast; ring
  have hxR : x * R = m * n := by rw [hxdef]; field_simp
  -- `N ≥ m²/R + R ≥ R (1 + x²/n²)`
  have hN : N g.1 = ((a : ℝ) ^ 2 + (b : ℝ) ^ 2) + R := by simp only [N, hRdef]; ring
  rw [hN, div_le_iff₀ (by positivity)]
  have key : R * (1 + x ^ 2 / n ^ 2) ≤ (a : ℝ) ^ 2 + (b : ℝ) ^ 2 + R := by
    have h1 : x ^ 2 / (n : ℝ) ^ 2 * R = m ^ 2 / R := by
      have hsq : (x * R) ^ 2 = (m * n) ^ 2 := by rw [hxR]
      field_simp
      linear_combination hsq
    have h2 : m ^ 2 / R ≤ (a : ℝ) ^ 2 + (b : ℝ) ^ 2 := by
      rw [div_le_iff₀ hR]; nlinarith [sq_nonneg (n : ℝ)]
    nlinarith [h1, h2]
  have hx2 : (1 + ((⌊x⌋ : ℤ) : ℝ) ^ 2) ≤ 3 * (n : ℝ) ^ 2 * (1 + x ^ 2 / n ^ 2) := by
    have : 3 * (n : ℝ) ^ 2 * (1 + x ^ 2 / n ^ 2) = 3 * n ^ 2 + 3 * x ^ 2 := by field_simp
    rw [this]; nlinarith
  calc R * (1 + ((⌊x⌋ : ℤ) : ℝ) ^ 2) ≤ R * (3 * (n : ℝ) ^ 2 * (1 + x ^ 2 / n ^ 2)) :=
        mul_le_mul_of_nonneg_left hx2 hR.le
    _ = R * (1 + x ^ 2 / n ^ 2) * (3 * n ^ 2) := by ring
    _ ≤ ((a : ℝ) ^ 2 + (b : ℝ) ^ 2 + R) * (3 * n ^ 2) :=
        mul_le_mul_of_nonneg_right key (by positivity)

lemma summable_one_add_sq_rpow {s : ℝ} (hs : 1 < s) :
    Summable fun j : ℤ => (1 + (j : ℝ) ^ 2) ^ (-s) := by
  have h2 := Real.summable_abs_int_rpow (b := 2 * s) (by linarith)
  have hite : Summable fun j : ℤ => if j = 0 then (1 : ℝ) else 0 :=
    summable_of_ne_finset_zero (s := {0}) (by intro j hj; simp at hj; simp [hj])
  refine (h2.add hite).of_nonneg_of_le (fun j => by positivity) (fun j => ?_)
  by_cases hj : j = 0
  · subst hj; simpa using Real.rpow_nonneg (le_refl (0:ℝ)) (-(2 * s))
  · simp only [hj, if_false, add_zero]
    have hj1 : (0 : ℝ) < |(j : ℝ)| := by positivity
    calc (1 + (j : ℝ) ^ 2) ^ (-s) ≤ ((j : ℝ) ^ 2) ^ (-s) :=
          Real.rpow_le_rpow_of_nonpos (by positivity) (by linarith) (by linarith)
      _ = |(j : ℝ)| ^ (-(2 * s)) := by
          rw [← sq_abs, ← Real.rpow_natCast, ← Real.rpow_mul (abs_nonneg _)]
          congr 1; push_cast; ring

lemma norm_sq_le (c d : ℤ) : ‖(![c, d] : Fin 2 → ℤ)‖ ^ 2 ≤ (c : ℝ) ^ 2 + (d : ℝ) ^ 2 := by
  have h : ‖(![c, d] : Fin 2 → ℤ)‖ ≤ Real.sqrt ((c : ℝ) ^ 2 + (d : ℝ) ^ 2) := by
    refine (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).2 (fun i => ?_)
    fin_cases i
    · simp only [Fin.zero_eta, Matrix.cons_val_zero, Int.norm_eq_abs]
      exact Real.abs_le_sqrt (by nlinarith [sq_nonneg (d : ℝ)])
    · simp only [Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_fin_one, Int.norm_eq_abs]
      exact Real.abs_le_sqrt (by nlinarith [sq_nonneg (c : ℝ)])
  calc ‖(![c, d] : Fin 2 → ℤ)‖ ^ 2 ≤ (Real.sqrt ((c : ℝ) ^ 2 + (d : ℝ) ^ 2)) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) h 2
    _ = _ := Real.sq_sqrt (by positivity)

lemma phi_fst_ne_zero {n : ℤ} (hn : 0 < n) (g : DetSet n) : (phi n g.1).1 ≠ 0 := by
  change (![g.1 1 0, g.1 1 1] : Fin 2 → ℤ) ≠ 0
  intro h0
  have h10 : g.1 1 0 = 0 := by have := congrFun h0 0; simpa using this
  have h11 : g.1 1 1 = 0 := by have := congrFun h0 1; simpa using this
  have := g.2; rw [det_eq, h10, h11] at this; omega

/-- **Lattice lemma.** `Σ_{det g = n} N(g)^(-s) < ∞` for `s > 1`. -/
theorem summable_N_rpow {n : ℤ} (hn : 0 < n) {s : ℝ} (hs : 1 < s) :
    Summable fun g : DetSet n => (N g.1) ^ (-s) := by
  have hmaj : Summable fun p : (Fin 2 → ℤ) × ℤ =>
      ‖p.1‖ ^ (-(2 * s)) * ((3 * (n : ℝ) ^ 2) ^ s * (1 + (p.2 : ℝ) ^ 2) ^ (-s)) :=
    Summable.mul_of_nonneg (EisensteinSeries.summable_one_div_norm_rpow (by linarith))
      ((summable_one_add_sq_rpow hs).mul_left _) (fun _ => by positivity) (fun _ => by positivity)
  refine ((hmaj.comp_injective (phi_injective hn))).of_nonneg_of_le (fun g => ?_) (fun g => ?_)
  · have : 0 ≤ N g.1 := by unfold N; positivity
    positivity
  · simp only [Function.comp_apply]
    have hR := R_pos hn g
    have hNge := N_ge hn g
    have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
    have hJ : 0 < 1 + ((phi n g.1).2 : ℝ) ^ 2 := by positivity
    have hL : 0 < ((g.1 1 0 : ℝ) ^ 2 + (g.1 1 1 : ℝ) ^ 2) * (1 + ((phi n g.1).2 : ℝ) ^ 2) /
        (3 * (n : ℝ) ^ 2) := by positivity
    have hnorm : ‖(phi n g.1).1‖ ^ 2 ≤ (g.1 1 0 : ℝ) ^ 2 + (g.1 1 1 : ℝ) ^ 2 := norm_sq_le _ _
    have hnpos2 : 0 < ‖(phi n g.1).1‖ := norm_pos_iff.2 (phi_fst_ne_zero hn g)
    calc (N g.1) ^ (-s) ≤ (((g.1 1 0 : ℝ) ^ 2 + (g.1 1 1 : ℝ) ^ 2) * (1 + ((phi n g.1).2 : ℝ) ^ 2) /
          (3 * (n : ℝ) ^ 2)) ^ (-s) := Real.rpow_le_rpow_of_nonpos hL hNge (by linarith)
      _ = ((g.1 1 0 : ℝ) ^ 2 + (g.1 1 1 : ℝ) ^ 2) ^ (-s) *
          ((3 * (n : ℝ) ^ 2) ^ s * (1 + ((phi n g.1).2 : ℝ) ^ 2) ^ (-s)) := by
          rw [Real.div_rpow (by positivity) (by positivity), Real.mul_rpow hR.le hJ.le,
            Real.rpow_neg (by positivity : (0:ℝ) ≤ 3 * (n:ℝ) ^ 2), div_inv_eq_mul]
          ring
      _ ≤ ‖(phi n g.1).1‖ ^ (-(2 * s)) * ((3 * (n : ℝ) ^ 2) ^ s * (1 + ((phi n g.1).2 : ℝ) ^ 2) ^ (-s)) := by
          gcongr
          rw [show -(2 * s) = 2 * (-s) by ring, Real.rpow_mul (norm_nonneg _), Real.rpow_two]
          exact Real.rpow_le_rpow_of_nonpos (by positivity) hnorm (by linarith)

/-! ## The bilinear form `Q` and the geometric bound -/

/-- `Q g z w = c z w + d w + a z + b = [1 w] g [z 1]ᵀ`. -/
def Q (g : Matrix (Fin 2) (Fin 2) ℤ) (z w : ℂ) : ℂ :=
  (g 1 0 : ℂ) * z * w + (g 1 1 : ℂ) * w + (g 0 0 : ℂ) * z + (g 0 1 : ℂ)

/-- `2 × 2` Frobenius submultiplicativity, entrywise. -/
lemma frob (p00 p01 p10 p11 q00 q01 q10 q11 : ℝ) :
    (p00 * q00 + p01 * q10) ^ 2 + (p00 * q01 + p01 * q11) ^ 2 + (p10 * q00 + p11 * q10) ^ 2 +
        (p10 * q01 + p11 * q11) ^ 2 ≤
      (p00 ^ 2 + p01 ^ 2 + p10 ^ 2 + p11 ^ 2) * (q00 ^ 2 + q01 ^ 2 + q10 ^ 2 + q11 ^ 2) := by
  nlinarith [sq_nonneg (p00 * q10 - p01 * q00), sq_nonneg (p00 * q11 - p01 * q01),
    sq_nonneg (p10 * q10 - p11 * q00), sq_nonneg (p10 * q11 - p11 * q01)]

lemma Q_re (g : Matrix (Fin 2) (Fin 2) ℤ) (z w : ℂ) :
    (Q g z w).re = g 1 0 * (z.re * w.re - z.im * w.im) + g 1 1 * w.re + g 0 0 * z.re + g 0 1 := by
  simp [Q, Complex.mul_re, Complex.mul_im]; ring

lemma Q_im (g : Matrix (Fin 2) (Fin 2) ℤ) (z w : ℂ) :
    (Q g z w).im = g 1 0 * (z.re * w.im + z.im * w.re) + g 1 1 * w.im + g 0 0 * z.im := by
  simp [Q, Complex.mul_re, Complex.mul_im]; ring

/-- `|Q|² = N(β) + 2 det(g) y v` with `β = [[1,u],[0,v]] g [[y,x],[0,1]]`. -/
lemma normSq_Q (g : Matrix (Fin 2) (Fin 2) ℤ) (z w : ℂ) :
    Complex.normSq (Q g z w) =
      (z.im * (g 0 0 + w.re * g 1 0)) ^ 2 + (g 0 0 * z.re + g 0 1 + w.re * (g 1 0 * z.re + g 1 1)) ^ 2 +
        (w.im * g 1 0 * z.im) ^ 2 + (w.im * (g 1 0 * z.re + g 1 1)) ^ 2 +
        2 * (g.det : ℝ) * z.im * w.im := by
  rw [Complex.normSq_apply, Q_re, Q_im, det_eq]; push_cast; ring

lemma two_det_le_normSq_Q (g : Matrix (Fin 2) (Fin 2) ℤ) (z w : ℂ) :
    2 * (g.det : ℝ) * z.im * w.im ≤ Complex.normSq (Q g z w) := by
  rw [normSq_Q]; nlinarith [sq_nonneg (z.im * (g 0 0 + w.re * g 1 0)),
    sq_nonneg (g 0 0 * z.re + g 0 1 + w.re * (g 1 0 * z.re + g 1 1)), sq_nonneg (w.im * g 1 0 * z.im),
    sq_nonneg (w.im * (g 1 0 * z.re + g 1 1))]

/-- The real-variable form of the geometric bound. -/
lemma geom_aux (a b c d x y u v : ℝ) (hy : 0 ≤ y) (hv : 0 ≤ v) (hdet : 0 ≤ a * d - b * c) :
    (y * v) ^ 2 * (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2) ≤
      (1 + (x * x + y * y)) * (1 + (u * u + v * v)) *
        ((c * (x * u - y * v) + d * u + a * x + b) * (c * (x * u - y * v) + d * u + a * x + b) +
          (c * (x * v + y * u) + d * v + a * y) * (c * (x * v + y * u) + d * v + a * y)) := by
  have h1 := frob v (-u) 0 1 (y * (a + u * c)) (a * x + b + u * (c * x + d)) (v * c * y) (v * (c * x + d))
  have h2 := frob (v * (y * (a + u * c)) + -u * (v * c * y)) (v * (a * x + b + u * (c * x + d)) + -u * (v * (c * x + d)))
    (0 * (y * (a + u * c)) + 1 * (v * c * y)) (0 * (a * x + b + u * (c * x + d)) + 1 * (v * (c * x + d))) 1 (-x) 0 y
  have hdv : 0 ≤ y * v * (a * d - b * c) := mul_nonneg (mul_nonneg hy hv) hdet
  have hQ : (y * (a + u * c)) ^ 2 + (a * x + b + u * (c * x + d)) ^ 2 + (v * c * y) ^ 2 + (v * (c * x + d)) ^ 2 ≤
      (c * (x * u - y * v) + d * u + a * x + b) * (c * (x * u - y * v) + d * u + a * x + b) +
        (c * (x * v + y * u) + d * v + a * y) * (c * (x * v + y * u) + d * v + a * y) := by
    have e : (c * (x * u - y * v) + d * u + a * x + b) * (c * (x * u - y * v) + d * u + a * x + b) +
        (c * (x * v + y * u) + d * v + a * y) * (c * (x * v + y * u) + d * v + a * y) =
        (y * (a + u * c)) ^ 2 + (a * x + b + u * (c * x + d)) ^ 2 + (v * c * y) ^ 2 + (v * (c * x + d)) ^ 2 +
          2 * (y * v * (a * d - b * c)) := by ring
    rw [e]; linarith
  have hNY : (0 : ℝ) ≤ 1 ^ 2 + (-x) ^ 2 + 0 ^ 2 + y ^ 2 := by positivity
  have hNX : (0 : ℝ) ≤ v ^ 2 + (-u) ^ 2 + 0 ^ 2 + 1 ^ 2 := by positivity
  have h1' := mul_le_mul_of_nonneg_right h1 hNY
  have hQ' := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hQ hNX) hNY
  have e2 : (y * v) ^ 2 * (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2) =
      ((v * (y * (a + u * c)) + -u * (v * c * y)) * 1 + (v * (a * x + b + u * (c * x + d)) + -u * (v * (c * x + d))) * 0) ^ 2 +
      ((v * (y * (a + u * c)) + -u * (v * c * y)) * -x + (v * (a * x + b + u * (c * x + d)) + -u * (v * (c * x + d))) * y) ^ 2 +
      ((0 * (y * (a + u * c)) + 1 * (v * c * y)) * 1 + (0 * (a * x + b + u * (c * x + d)) + 1 * (v * (c * x + d))) * 0) ^ 2 +
      ((0 * (y * (a + u * c)) + 1 * (v * c * y)) * -x + (0 * (a * x + b + u * (c * x + d)) + 1 * (v * (c * x + d))) * y) ^ 2 := by
    ring
  have e3 : (1 + (x * x + y * y)) * (1 + (u * u + v * v)) *
        ((c * (x * u - y * v) + d * u + a * x + b) * (c * (x * u - y * v) + d * u + a * x + b) +
          (c * (x * v + y * u) + d * v + a * y) * (c * (x * v + y * u) + d * v + a * y)) =
      (v ^ 2 + (-u) ^ 2 + 0 ^ 2 + 1 ^ 2) *
        ((c * (x * u - y * v) + d * u + a * x + b) * (c * (x * u - y * v) + d * u + a * x + b) +
          (c * (x * v + y * u) + d * v + a * y) * (c * (x * v + y * u) + d * v + a * y)) *
        (1 ^ 2 + (-x) ^ 2 + 0 ^ 2 + y ^ 2) := by ring
  rw [e2, e3]
  linarith

/-- **Geometric bound.** `(y v)² N(g) ≤ (1 + |z|²)(1 + |w|²) |Q|²` when `det g ≥ 0`, `Im z, Im w ≥ 0`. -/
theorem N_le_normSq_Q (g : Matrix (Fin 2) (Fin 2) ℤ) (hdet : 0 ≤ g.det) (z w : ℂ) (hy : 0 ≤ z.im)
    (hv : 0 ≤ w.im) :
    (z.im * w.im) ^ 2 * N g ≤ (1 + ‖z‖ ^ 2) * (1 + ‖w‖ ^ 2) * Complex.normSq (Q g z w) := by
  have hd : (0 : ℝ) ≤ (g 0 0 : ℝ) * g 1 1 - g 0 1 * g 1 0 := by
    rw [det_eq] at hdet; exact_mod_cast (sub_nonneg.2 (by linarith : g 0 1 * g 1 0 ≤ g 0 0 * g 1 1))
  have h := geom_aux (g 0 0) (g 0 1) (g 1 0) (g 1 1) z.re z.im w.re w.im hy hv hd
  rw [Complex.sq_norm, Complex.sq_norm, Complex.normSq_apply, Complex.normSq_apply, Complex.normSq_apply,
    Q_re, Q_im]
  exact h

/-! ## The kernel and its absolute convergence -/

lemma N_pos {g : Matrix (Fin 2) (Fin 2) ℤ} (hdet : 0 < g.det) : 0 < N g := by
  have : (0 : ℝ) < (g 0 0 : ℝ) * g 1 1 - g 0 1 * g 1 0 := by
    rw [det_eq] at hdet; exact_mod_cast (sub_pos.2 (by linarith : g 0 1 * g 1 0 < g 0 0 * g 1 1))
  unfold N
  nlinarith [sq_nonneg ((g 0 0 : ℝ) - g 1 1), sq_nonneg ((g 0 1 : ℝ) + g 1 0)]

/-- The constant `B(z,w) = (y v)² / ((1 + |z|²)(1 + |w|²))` of the geometric bound. -/
def B (z w : ℂ) : ℝ := (z.im * w.im) ^ 2 / ((1 + ‖z‖ ^ 2) * (1 + ‖w‖ ^ 2))

lemma B_pos {z w : ℂ} (hy : 0 < z.im) (hv : 0 < w.im) : 0 < B z w := by unfold B; positivity

lemma norm_inv_Q_pow_le {g : Matrix (Fin 2) (Fin 2) ℤ} (hdet : 0 < g.det) {z w : ℂ} (hy : 0 < z.im)
    (hv : 0 < w.im) (k : ℕ) :
    ‖(Q g z w ^ k)⁻¹‖ ≤ B z w ^ (-(k : ℝ) / 2) * N g ^ (-(k : ℝ) / 2) := by
  have hN := N_pos hdet
  have hB := B_pos hy hv
  have hBN : B z w * N g ≤ ‖Q g z w‖ ^ 2 := by
    rw [Complex.sq_norm, B, div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    have := N_le_normSq_Q g hdet.le z w hy.le hv.le
    linarith
  have hpos : 0 < B z w * N g := mul_pos hB hN
  rw [norm_inv, norm_pow, ← Real.mul_rpow hB.le hN.le]
  have hQ0 : 0 ≤ ‖Q g z w‖ := norm_nonneg _
  have e1 : (‖Q g z w‖ ^ k)⁻¹ = ‖Q g z w‖ ^ (-(k : ℝ)) := by
    rw [Real.rpow_neg hQ0, Real.rpow_natCast]
  have e2 : (‖Q g z w‖ ^ 2) ^ (-(k : ℝ) / 2) = ‖Q g z w‖ ^ (-(k : ℝ)) := by
    rw [← Real.rpow_two, ← Real.rpow_mul hQ0]; congr 1; ring
  have hk0 : -(k : ℝ) / 2 ≤ 0 := by
    have : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    linarith
  calc (‖Q g z w‖ ^ k)⁻¹ = (‖Q g z w‖ ^ 2) ^ (-(k : ℝ) / 2) := by rw [e1, e2]
    _ ≤ (B z w * N g) ^ (-(k : ℝ) / 2) := Real.rpow_le_rpow_of_nonpos hpos hBN hk0

/-- `Δ^{(δ')}_n(M) = {g : det g = n, c ≡ 0, a ≡ δ' (mod M)}`. -/
def DeltaSet (M : ℕ) (n : ℤ) (δ' : ZMod M) : Set (Matrix (Fin 2) (Fin 2) ℤ) :=
  {g | g.det = n ∧ ((g 1 0 : ℤ) : ZMod M) = 0 ∧ ((g 0 0 : ℤ) : ZMod M) = δ'}

/-- The Hecke kernel `ω(z,w) = Σ_{g ∈ Δ^{(δ')}_n(M)} (c z w + d w + a z + b)^{-k}`. -/
def omega (M k : ℕ) (n : ℤ) (δ' : ZMod M) (z w : ℂ) : ℂ :=
  ∑' g : DeltaSet M n δ', (Q g.1 z w ^ k)⁻¹

lemma mem_DeltaSet {M : ℕ} {n : ℤ} {δ' : ZMod M} {g : Matrix (Fin 2) (Fin 2) ℤ} :
    g ∈ DeltaSet M n δ' ↔ g.det = n ∧ ((g 1 0 : ℤ) : ZMod M) = 0 ∧ ((g 0 0 : ℤ) : ZMod M) = δ' := Iff.rfl

/-- The inclusion `Δ^{(δ')}_n(M) → {det = n}`. -/
def toDet {M : ℕ} {n : ℤ} {δ' : ZMod M} (g : DeltaSet M n δ') : DetSet n :=
  ⟨g.1, (mem_DeltaSet.1 g.2).1⟩

lemma toDet_injective {M : ℕ} {n : ℤ} {δ' : ZMod M} : Function.Injective (toDet (M := M) (n := n) (δ' := δ')) := by
  intro g g' h
  apply Subtype.ext
  have := congrArg Subtype.val h
  exact this

@[simp] lemma toDet_val {M : ℕ} {n : ℤ} {δ' : ZMod M} (g : DeltaSet M n δ') : (toDet g).1 = g.1 := rfl

lemma det_pos_of_mem {M : ℕ} {n : ℤ} {δ' : ZMod M} (hn : 0 < n) (g : DeltaSet M n δ') : 0 < g.1.det := by
  rw [(mem_DeltaSet.1 g.2).1]; exact hn

theorem summable_norm_det {n : ℤ} (hn : 0 < n) {k : ℕ} (hk : 3 ≤ k) {z w : ℂ} (hy : 0 < z.im)
    (hv : 0 < w.im) : Summable fun g : DetSet n => ‖(Q g.1 z w ^ k)⁻¹‖ := by
  have hs : (1 : ℝ) < (k : ℝ) / 2 := by
    have : (3 : ℝ) ≤ k := by exact_mod_cast hk
    linarith
  refine ((summable_N_rpow hn hs).mul_left (B z w ^ (-(k : ℝ) / 2))).of_nonneg_of_le
    (fun _ => norm_nonneg _) (fun g => ?_)
  have := norm_inv_Q_pow_le (g := g.1) (by rw [g.2]; exact hn) hy hv k
  simpa [neg_div] using this

theorem summable_omega (M k : ℕ) {n : ℤ} (hn : 0 < n) (δ' : ZMod M) (hk : 3 ≤ k) {z w : ℂ}
    (hy : 0 < z.im) (hv : 0 < w.im) : Summable fun g : DeltaSet M n δ' => (Q g.1 z w ^ k)⁻¹ := by
  refine Summable.of_norm ?_
  refine ((summable_norm_det hn hk hy hv).comp_injective
    (toDet_injective (M := M) (n := n) (δ' := δ'))).congr (fun g => ?_)
  simp only [Function.comp_apply, toDet_val]

/-! ## Holomorphy in `z` -/

lemma differentiable_Q (g : Matrix (Fin 2) (Fin 2) ℤ) (w : ℂ) : Differentiable ℂ (fun z => Q g z w) := by
  unfold Q; fun_prop

lemma Q_ne_zero {g : Matrix (Fin 2) (Fin 2) ℤ} (hdet : 0 < g.det) {z w : ℂ} (hy : 0 < z.im)
    (hv : 0 < w.im) : Q g z w ≠ 0 := by
  intro h
  have h1 := two_det_le_normSq_Q g z w
  rw [h, Complex.normSq_zero] at h1
  have hd : (0 : ℝ) < g.det := by exact_mod_cast hdet
  have : 0 < 2 * (g.det : ℝ) * z.im * w.im := by positivity
  linarith

/-- On `{Im z > y₀, ‖z‖ < R}` the constant `B z w` is at least `(y₀ v)² / ((1 + R²)(1 + ‖w‖²))`. -/
lemma B_ge {z w : ℂ} {y0 R : ℝ} (hy0 : 0 < y0) (hy : y0 < z.im) (hR : ‖z‖ < R) (hv : 0 < w.im) :
    (y0 * w.im) ^ 2 / ((1 + R ^ 2) * (1 + ‖w‖ ^ 2)) ≤ B z w := by
  unfold B
  have h1 : (y0 * w.im) ^ 2 ≤ (z.im * w.im) ^ 2 :=
    pow_le_pow_left₀ (by positivity) (mul_le_mul_of_nonneg_right hy.le hv.le) 2
  have h2 : (1 + ‖z‖ ^ 2) * (1 + ‖w‖ ^ 2) ≤ (1 + R ^ 2) * (1 + ‖w‖ ^ 2) := by
    have : ‖z‖ ^ 2 ≤ R ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hR.le 2
    have h3 : (0 : ℝ) ≤ 1 + ‖w‖ ^ 2 := by positivity
    nlinarith
  calc (y0 * w.im) ^ 2 / ((1 + R ^ 2) * (1 + ‖w‖ ^ 2))
      ≤ (z.im * w.im) ^ 2 / ((1 + R ^ 2) * (1 + ‖w‖ ^ 2)) := by gcongr
    _ ≤ (z.im * w.im) ^ 2 / ((1 + ‖z‖ ^ 2) * (1 + ‖w‖ ^ 2)) :=
        div_le_div_of_nonneg_left (by positivity) (by positivity) h2

lemma norm_term_le_of_B {g : Matrix (Fin 2) (Fin 2) ℤ} (hdet : 0 < g.det) {z w : ℂ} (hy : 0 < z.im)
    (hv : 0 < w.im) (k : ℕ) {b : ℝ} (hb : 0 < b) (hbB : b ≤ B z w) :
    ‖(Q g z w ^ k)⁻¹‖ ≤ b ^ (-(k : ℝ) / 2) * N g ^ (-(k : ℝ) / 2) := by
  refine (norm_inv_Q_pow_le hdet hy hv k).trans ?_
  have hk0 : -(k : ℝ) / 2 ≤ 0 := by
    have : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    linarith
  exact mul_le_mul_of_nonneg_right (Real.rpow_le_rpow_of_nonpos hb hbB hk0)
    (Real.rpow_nonneg (N_pos hdet).le _)

lemma summable_N_rpow_delta (M : ℕ) {n : ℤ} (hn : 0 < n) (δ' : ZMod M) {s : ℝ} (hs : 1 < s) :
    Summable fun g : DeltaSet M n δ' => N g.1 ^ (-s) := by
  refine ((summable_N_rpow hn hs).comp_injective (toDet_injective (M := M) (n := n) (δ' := δ'))).congr
    (fun g => ?_)
  simp only [Function.comp_apply, toDet_val]

/-- **Holomorphy in `z`.** -/
theorem differentiableOn_omega (M k : ℕ) {n : ℤ} (hn : 0 < n) (δ' : ZMod M) (hk : 3 ≤ k) {w : ℂ}
    (hv : 0 < w.im) : DifferentiableOn ℂ (fun z => omega M k n δ' z w) {z : ℂ | 0 < z.im} := by
  intro z0 hz0
  have hz0' : 0 < z0.im := hz0
  have hUo : IsOpen ({z : ℂ | z0.im / 2 < z.im} ∩ {z : ℂ | ‖z‖ < ‖z0‖ + 1}) :=
    (isOpen_lt continuous_const Complex.continuous_im).inter (isOpen_lt continuous_norm continuous_const)
  have hz0U : z0 ∈ ({z : ℂ | z0.im / 2 < z.im} ∩ {z : ℂ | ‖z‖ < ‖z0‖ + 1}) := by
    refine ⟨?_, ?_⟩
    · show z0.im / 2 < z0.im; linarith
    · show ‖z0‖ < ‖z0‖ + 1; linarith
  obtain ⟨b, hb⟩ : ∃ b : ℝ, b = (z0.im / 2 * w.im) ^ 2 / ((1 + (‖z0‖ + 1) ^ 2) * (1 + ‖w‖ ^ 2)) :=
    ⟨_, rfl⟩
  have hbpos : 0 < b := by rw [hb]; positivity
  have hs : (1 : ℝ) < (k : ℝ) / 2 := by
    have : (3 : ℝ) ≤ k := by exact_mod_cast hk
    linarith
  have hsum : Summable fun g : DeltaSet M n δ' => b ^ (-(k : ℝ) / 2) * N g.1 ^ (-(k : ℝ) / 2) := by
    have := (summable_N_rpow_delta M hn δ' hs).mul_left (b ^ (-(k : ℝ) / 2))
    simpa only [neg_div] using this
  have hD : DifferentiableOn ℂ (fun z => ∑' g : DeltaSet M n δ', (Q g.1 z w ^ k)⁻¹)
      ({z : ℂ | z0.im / 2 < z.im} ∩ {z : ℂ | ‖z‖ < ‖z0‖ + 1}) := by
    refine differentiableOn_tsum_of_summable_norm
      (F := fun (g : DeltaSet M n δ') (z : ℂ) => (Q g.1 z w ^ k)⁻¹) hsum (fun g => ?_) hUo
      (fun g z hz => ?_)
    · intro z hz
      have h1 : z0.im / 2 < z.im := hz.1
      have hzim : 0 < z.im := by linarith
      exact (((differentiable_Q g.1 w).pow k).differentiableAt.inv
        (pow_ne_zero _ (Q_ne_zero (det_pos_of_mem hn g) hzim hv))).differentiableWithinAt
    · have h1 : z0.im / 2 < z.im := hz.1
      have h2 : ‖z‖ < ‖z0‖ + 1 := hz.2
      have hzim : 0 < z.im := by linarith
      have hbB : b ≤ B z w := by rw [hb]; exact B_ge (by linarith) h1 h2 hv
      exact norm_term_le_of_B (det_pos_of_mem hn g) hzim hv k hbpos hbB
  exact (hD.differentiableAt (hUo.mem_nhds hz0U)).differentiableWithinAt

end RamanujanPetersson.Kernel



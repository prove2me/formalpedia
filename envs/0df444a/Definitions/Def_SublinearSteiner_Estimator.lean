-- Prove2me | Definitions.Def_SublinearSteiner_Estimator
-- name    : SublinearSteiner_Estimator
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:45:51.77331+00:00
-- url     : https://prove2.me/theorems/af9565ef-156e-4559-96e7-0888afd9d89b
-- title:
--   Flooring, the grid, the shift law and the estimator $\widehat C$
-- statement:
--   **Flooring.** For a terminal $x_0$, $R_{\mathrm{met}}$ is its largest distance to $T$. For a target improvement $\eta_w\in(0,1)$ put $\lambda_f=\eta_wR_{\mathrm{met}}/(100k)$, and replace every distance between distinct points by $\max\{w(x,y),\lambda_f\}$.
--
--   **The grid.** $q_0=\lceil\log_\omega2\rceil+1$, $I=\lceil\log_\omega(4R_{\mathrm{met}}/\lambda_f)\rceil+q_0+3$, and
--   $$a_i=\lambda_f\Theta\omega^{i-q_0},\quad 0\le i<I,$$
--   where $\Theta$ has density $1/(\Theta\log\omega)$ on $[1,\omega)$.
--
--   **Parameters.** $\mathcal A=1+\frac{10H_c}{\omega-1}+\frac{4\psi hI}{\delta}$, $\varepsilon=e_0/(10^5\mathcal A)$, $B_Q=\lceil400\mathcal A\rceil$, and $c_*=\min\{e_0/(32000Q_S),\sigma_0/(1000Q_Q),e_0/8,1/10\}$.
--
--   **The output.**
--   $$\widehat C=\overline L-\max\Bigl\{\frac{S}{32Q_S},\frac{\widehat T}{Q_Q}\Bigr\}.$$
--
--   **Formalization Note.** The floored metric is shown to be a metric for every value of $\lambda$. `shiftGrid` is the geometric grid $a\Theta\omega^i$, of which (4.2) is the case $a=\lambda_f\omega^{-q_0}$. `shiftLaw` is the law of $\Theta$ as a measure on $\mathbb R$.
-- source:
--   Mahabadi, Roghani, Tarnawski, Vakilian, Tight Bounds for Sublinear Metric Steiner Tree, STOC 2027 submission (manuscript sha256 ae133037…), Section 4.1, p.19; (4.9), p.23; p.24; (4.12), p.24; (4.16), Proposition 4.9, p.25

import Mathlib
import Definitions.Def_SublinearSteiner_Statistics
import Definitions.Def_SublinearSteiner_Retention

open scoped Classical NNReal

namespace SublinearSteiner

/-!
# Flooring, the grid and the estimator's parameters

Mahabadi, Roghani, Tarnawski, Vakilian, *Tight Bounds for Sublinear Metric Steiner Tree*, STOC 2027
submission (manuscript sha256 ae133037…), Section 4.1, p.19; (4.9), p.23; p.24; (4.12), p.24; (4.16) and Proposition 4.9,
p.25.

**Formalization Note.**
* `R_met` is the largest distance from the chosen terminal `x₀` to `T`.
* `logb ω` is the page's `log_ω`. The ceilings are in `ℕ`; their arguments are positive for `k ≥ 3`, `0 < η_w < 1`.
* The floored metric is a metric for any `λ`, so the structure carries no hypothesis on `λ`.
* `shiftLaw` is a measure on `ℝ`, and in Mathlib every set has a measure (the outer measure of a nonmeasurable set).
* `(4.2)`'s `a_i = λ_f Θ ω^{i − q0}` has an integer exponent, which is negative for small `i`.
-/

variable {n : ℕ}

/-- `R_met`: the largest distance from the terminal `x₀` to `T` (p.19). -/
noncomputable def Rmet (w : FinMetric n) (T : Finset (Fin n)) (x₀ : Fin n) : ℝ :=
  ((T.sup fun y => Real.toNNReal (w.d x₀ y) : ℝ≥0) : ℝ)

/-- `λ_f = ζ R_met / k`, `ζ = η_w / 100` (p.19). -/
noncomputable def lambdaF (ηw R : ℝ) (k : ℕ) : ℝ := ηw / 100 * R / k

/-- The floored metric: every distance between distinct points is replaced by `max{w(x, y), λ}` (p.19). -/
noncomputable def floored (w : FinMetric n) (lam : ℝ) : FinMetric n where
  d x y := if x = y then 0 else max (w.d x y) lam
  d_self x := by simp
  d_pos x y h := by
    simp only [h, if_false]
    exact lt_max_of_lt_left (w.d_pos x y h)
  d_symm x y := by
    by_cases h : x = y
    · simp [h]
    · simp [h, Ne.symm h, w.d_symm x y]
  d_triangle x y z := by
    by_cases hxz : x = z
    · subst hxz
      simp only [if_true]
      by_cases hxy : x = y
      · simp [hxy]
      · simp only [hxy, Ne.symm hxy, if_false]
        have := w.d_pos x y hxy
        have h1 : w.d x y ≤ max (w.d x y) lam := le_max_left _ _
        have h2 : w.d y x ≤ max (w.d y x) lam := le_max_left _ _
        have := w.d_pos y x (Ne.symm hxy)
        linarith
    · by_cases hxy : x = y
      · subst hxy; simp [hxz]
      · by_cases hyz : y = z
        · subst hyz; simp [hxz]
        · simp only [hxz, hxy, hyz, if_false]
          have h1 : w.d x y ≤ max (w.d x y) lam := le_max_left _ _
          have h2 : w.d y z ≤ max (w.d y z) lam := le_max_left _ _
          have h3 : lam ≤ max (w.d x y) lam := le_max_right _ _
          have h4 : lam ≤ max (w.d y z) lam := le_max_right _ _
          have h5 := w.d_triangle x y z
          have h6 := w.d_pos x y hxy
          have h7 := w.d_pos y z hyz
          refine max_le (by linarith) ?_
          rcases le_or_gt lam 0 with h | h
          · linarith
          · linarith

/-- `q0 = ⌈log_ω 2⌉ + 1` (p.19). -/
noncomputable def gridQ0 : ℕ := ⌈Real.logb omega 2⌉₊ + 1

/-- `I = ⌈log_ω(4R_met/λ_f)⌉ + q0 + 3` (p.19). -/
noncomputable def gridI (R lam : ℝ) : ℕ := ⌈Real.logb omega (4 * R / lam)⌉₊ + gridQ0 + 3

/-- `a_i = λ_f Θ ω^{i − q0}` (4.2). -/
noncomputable def gridScale (lam Θ : ℝ) (i : ℕ) : ℝ := lam * Θ * omega ^ ((i : ℤ) - (gridQ0 : ℤ))

/-- A log-uniformly shifted geometric grid `a_i = a Θ ω^i`; (4.2) is the case `a = λ_f ω^{−q0}`. -/
noncomputable def shiftGrid (a Θ : ℝ) (i : ℕ) : ℝ := a * Θ * omega ^ i

/-- The law of the shift `Θ`, with density `1/(Θ log ω)` on `[1, ω)` (p.19). -/
noncomputable def shiftLaw : MeasureTheory.Measure ℝ :=
  (MeasureTheory.volume.restrict (Set.Ico 1 omega)).withDensity
    fun θ => ENNReal.ofReal (1 / (θ * Real.log omega))

/-- `A = 1 + 10 H_c/(ω − 1) + 4ψhI/δ` (4.9). -/
noncomputable def coverA (Hc : ℝ) (ψ h I : ℕ) : ℝ :=
  1 + 10 * Hc / (omega - 1) + 4 * ψ * h * I / delta

/-- `ε = e0/(10⁵ A)` (4.12). -/
noncomputable def epsA (A : ℝ) : ℝ := e0 / (100000 * A)

/-- `B_Q = ⌈400A⌉` (p.24). -/
noncomputable def bandCap (A : ℝ) : ℕ := ⌈400 * A⌉₊

/-- `c∗ = min{e0/(32000 Q_S), σ0/(1000 Q_Q), e0/8, 1/10}` (Proposition 4.9). -/
noncomputable def cStar (QS QQ : ℕ) : ℝ :=
  min (min (e0 / (32000 * QS)) (sigma0 / (1000 * QQ))) (min (e0 / 8) (1 / 10))

/-- `Ĉ = L̄ − max{S/(32 Q_S), T̂/Q_Q}` (4.16). -/
noncomputable def estimatorOutput (Lbar S That : ℝ) (QS QQ : ℕ) : ℝ :=
  Lbar - max (S / (32 * QS)) (That / QQ)

end SublinearSteiner



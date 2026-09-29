-- Prove2me | Definitions.Def_ZudilinZetaSetup
-- name    : ZudilinZetaSetup
-- status  : Definition
-- author  : @Lucas
-- created : 2026-09-22T17:00:04.001734+00:00
-- url     : https://prove2.me/theorems/07e5febc-43d7-412e-9091-d78272ce72be
-- title:
--   Zudilin's linear forms $F_n$ in odd zeta values
-- statement:
--   The definition layer of Zudilin's 2001 note.
--
--   `zetaR k` is the real number $\zeta(k) = \sum_{n \ge 1} n^{-k}$, written as the series $\sum_{n \ge 0} 1/(n+1)^k$; it is the value used in the linear forms below (a separate statement identifies it with Mathlib's `riemannZeta` for $k \ge 2$).
--
--   `Params` packages an admissible choice of parameters of the note: odd numbers $q$ and $r$ with $q \ge r+4$, and positive integers $\eta_0, \eta_1, \dots, \eta_q$ with $\eta_1 \le \eta_2 \le \dots \le \eta_q < \eta_0/2$ and $\eta_1 + \dots + \eta_q \le \eta_0 (q-r)/2$, which is condition (1) of the note (written without division as $2\sum_j \eta_j \le \eta_0 (q-r)$).
--
--   `hh P n j` is $h_0 = \eta_0 n + 2$ for $j = 0$ and $h_j = \eta_j n + 1$ for $j \ge 1$.
--
--   `R P n t` is the rational function
--   $$R_n(t) = (h_0 + 2t)\prod_{j=1}^{r}\frac{1}{(h_j-1)!}\frac{\Gamma(h_j+t)}{\Gamma(1+t)}\prod_{j=1}^{r}\frac{1}{(h_j-1)!}\frac{\Gamma(h_0+t)}{\Gamma(1+h_0-h_j+t)}\prod_{j=r+1}^{q}(h_0-2h_j)!\,\frac{\Gamma(h_j+t)}{\Gamma(1+h_0-h_j+t)}$$
--   of the note, as a real-valued function of a real variable $t$.
--
--   `F P n` is the linear form (2), $F_n = \frac{1}{(r-1)!}\sum_{t=0}^{\infty} R_n^{(r-1)}(t)$, the $(r-1)$-st derivative being Lean's `iteratedDeriv` and the sum a `tsum` over natural $t$.
-- source:
--   W. V. Zudilin, One of the numbers ζ(5), ζ(7), ζ(9), ζ(11) is irrational, Uspekhi Mat. Nauk 56:4 (2001), 149–150, https://doi.org/10.4213/rm427 (English transl.: Russian Math. Surveys 56:4 (2001), 774–776)

import Mathlib

/-!
# Zudilin (2001): setup for the linear forms in odd zeta values

Definition layer for the note

  W. V. Zudilin, *One of the numbers ζ(5), ζ(7), ζ(9), ζ(11) is irrational*,
  Uspekhi Mat. Nauk 56:4 (2001), 149–150.

This file fixes the admissible parameter sets `(q, r, η₀, …, η_q)` of the note,
the integers `h₀, …, h_q`, the rational function `Rₙ(t)` and the linear form `Fₙ`.
-/

namespace ZudilinZeta

/-- The value of the Riemann zeta function at an integer `k ≥ 2`, as the real series
`ζ(k) = ∑_{n ≥ 1} n⁻ᵏ`. -/
noncomputable def zetaR (k : ℕ) : ℝ := ∑' n : ℕ, (1 : ℝ) / ((n : ℝ) + 1) ^ k

/-- An admissible choice of parameters in Zudilin's note: odd numbers `q` and `r`
with `q ≥ r + 4`, together with positive integers `η 0, η 1, …, η q` satisfying
`η 1 ≤ η 2 ≤ ⋯ ≤ η q < η 0 / 2` and the constraint (1)
`η 1 + η 2 + ⋯ + η q ≤ η 0 · (q - r) / 2`. -/
structure Params where
  /-- the number of parameters `η 1, …, η q`; odd -/
  q : ℕ
  /-- the order of the derivative shift; odd -/
  r : ℕ
  /-- the parameters `η 0, η 1, …, η q` (values at indices `> q` are irrelevant) -/
  eta : ℕ → ℕ
  q_odd : Odd q
  r_odd : Odd r
  /-- `q ≥ r + 4` -/
  q_ge : r + 4 ≤ q
  /-- all of `η 0, …, η q` are positive integers -/
  eta_pos : ∀ j ∈ Finset.Icc 0 q, 0 < eta j
  /-- `η 1 ≤ η 2 ≤ ⋯ ≤ η q` -/
  eta_mono : ∀ j ∈ Finset.Ico 1 q, eta j ≤ eta (j + 1)
  /-- `η q < η 0 / 2` -/
  eta_lt : 2 * eta q < eta 0
  /-- constraint (1): `η 1 + ⋯ + η q ≤ η 0 · (q - r) / 2` -/
  sum_le : 2 * ∑ j ∈ Finset.Icc 1 q, eta j ≤ eta 0 * (q - r)

/-- The integers `h₀ = η₀ n + 2` and `h_j = η_j n + 1` for `j = 1, …, q`. -/
def hh (P : Params) (n : ℕ) (j : ℕ) : ℕ :=
  if j = 0 then P.eta 0 * n + 2 else P.eta j * n + 1

/-- The rational function

`Rₙ(t) = (h₀ + 2t) · ∏_{j=1}^r 1/(h_j-1)! · Γ(h_j+t)/Γ(1+t)
        · ∏_{j=1}^r 1/(h_j-1)! · Γ(h₀+t)/Γ(1+h₀-h_j+t)
        · ∏_{j=r+1}^q (h₀-2h_j)! · Γ(h_j+t)/Γ(1+h₀-h_j+t)`

of Zudilin's note, as a real-valued function of `t`. -/
noncomputable def R (P : Params) (n : ℕ) (t : ℝ) : ℝ :=
  ((hh P n 0 : ℝ) + 2 * t)
    * (∏ j ∈ Finset.Icc 1 P.r,
        (1 / (Nat.factorial (hh P n j - 1) : ℝ)) * Real.Gamma ((hh P n j : ℝ) + t)
          / Real.Gamma (1 + t))
    * (∏ j ∈ Finset.Icc 1 P.r,
        (1 / (Nat.factorial (hh P n j - 1) : ℝ)) * Real.Gamma ((hh P n 0 : ℝ) + t)
          / Real.Gamma (1 + (hh P n 0 : ℝ) - (hh P n j : ℝ) + t))
    * (∏ j ∈ Finset.Icc (P.r + 1) P.q,
        (Nat.factorial (hh P n 0 - 2 * hh P n j) : ℝ) * Real.Gamma ((hh P n j : ℝ) + t)
          / Real.Gamma (1 + (hh P n 0 : ℝ) - (hh P n j : ℝ) + t))

/-- The linear form (2): `Fₙ = 1/(r-1)! · ∑_{t=0}^∞ Rₙ^{(r-1)}(t)`. -/
noncomputable def F (P : Params) (n : ℕ) : ℝ :=
  (1 / (Nat.factorial (P.r - 1) : ℝ)) * ∑' t : ℕ, iteratedDeriv (P.r - 1) (R P n) (t : ℝ)

end ZudilinZeta



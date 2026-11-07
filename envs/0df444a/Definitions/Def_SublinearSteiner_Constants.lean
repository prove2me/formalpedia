-- Prove2me | Definitions.Def_SublinearSteiner_Constants
-- name    : SublinearSteiner_Constants
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:39:10.59711+00:00
-- url     : https://prove2.me/theorems/90372797-d6ad-4142-958c-3e7f5c99907e
-- title:
--   The standing constants $e_0,\chi,p,b_0,\omega,\alpha_0,\delta_0,\theta_0,\sigma_0,\delta,\tau$
-- statement:
--   The numerical constants fixed throughout Sections 3 and 4 of the paper:
--   $$e_0=10^{-4},\quad \chi=2-e_0,\quad p=2\chi-2,\quad b_0=p-1,\quad \omega=\tfrac{101}{100},\quad \alpha_0=\delta_0=\tfrac1{100},\quad \theta_0=\tfrac1{20},\quad \sigma_0=\tfrac1{1000},$$
--   so that $b_0=1-2e_0$, $p=2-2e_0$ and $b_0<1<p<\chi<2$. Section 4 adds $\delta=10^{-10}$ and $\tau=\sigma_0/100$.
--
--   **Formalization Note.** Each constant is a real number, with its Greek letter spelled out in the Lean name.
-- source:
--   Mahabadi, Roghani, Tarnawski, Vakilian, Tight Bounds for Sublinear Metric Steiner Tree, STOC 2027 submission (manuscript sha256 ae133037…), Section 3, p.14; Section 4.1, p.19

import Mathlib

namespace SublinearSteiner

/-!
# The standing constants of Sections 3 and 4

Mahabadi, Roghani, Tarnawski, Vakilian, *Tight Bounds for Sublinear Metric Steiner Tree*, STOC 2027
submission (manuscript sha256 ae133037…), Section 3, p.14; Section 4.1, p.19.

`e0 = 10⁻⁴, χ = 2 − e0, p = 2χ − 2, b0 = p − 1, ω = 101/100, α0 = δ0 = 1/100, θ0 = 1/20, σ0 = 1/1000`,
and `δ = 10⁻¹⁰, τ = σ0/100`.

**Formalization Note.** Greek names are spelled out (`chi`, `omega`, …); the page's `δ0` is `delta0`, its `δ`
is `delta`, and its `p` is `pConst`.
-/

/-- `e0 = 10⁻⁴` (p.14). -/
noncomputable def e0 : ℝ := 1 / 10000

/-- `χ = 2 − e0` (p.14). -/
noncomputable def chi : ℝ := 2 - e0

/-- `p = 2χ − 2` (p.14). -/
noncomputable def pConst : ℝ := 2 * chi - 2

/-- `b0 = p − 1` (p.14). -/
noncomputable def b0 : ℝ := pConst - 1

/-- `ω = 101/100` (p.14). -/
noncomputable def omega : ℝ := 101 / 100

/-- `α0 = 1/100` (p.14). -/
noncomputable def alpha0 : ℝ := 1 / 100

/-- `δ0 = 1/100` (p.14). -/
noncomputable def delta0 : ℝ := 1 / 100

/-- `θ0 = 1/20` (p.14). -/
noncomputable def theta0 : ℝ := 1 / 20

/-- `σ0 = 1/1000` (p.14). -/
noncomputable def sigma0 : ℝ := 1 / 1000

/-- `δ = 10⁻¹⁰` (p.19). -/
noncomputable def delta : ℝ := 1 / 10000000000

/-- `τ = σ0/100` (p.19). -/
noncomputable def tau : ℝ := sigma0 / 100

end SublinearSteiner



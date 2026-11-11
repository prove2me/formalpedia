-- Prove2me | Definitions.Def_RSBeyondJohnson_FirstOrder_Curve
-- name    : RSBeyondJohnson_FirstOrder_Curve
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T16:30:08.120241+00:00
-- url     : https://prove2.me/theorems/5fd83e40-2f72-4a19-a977-2868fcc00be1
-- title:
--   The first-order agreement curve $a_1(\rho)$ (Definition 3.15)
-- statement:
--   Put $\rho_c := 11-3\sqrt{13}\approx 0.183346$. For $0<\rho<\rho_c$ let $u_\rho$ be the unique positive solution of $u^2(u+3)=\sqrt{\rho/2}$ (the left side increases strictly from $0$ to $\infty$ on $u>0$). The **first-order agreement curve** is
--   $$a_1(\rho)=\begin{cases}\sqrt{\rho/2}\,(1+u_\rho), & 0<\rho<\rho_c,\\[2pt] \dfrac{3\rho+2\sqrt{\rho(5-\rho)(2-\rho)}}{8-\rho}, & \rho_c\le\rho<1.\end{cases}$$
--   It lies strictly between capacity and the Johnson bound, $\rho<a_1(\rho)<\sqrt\rho$, and is the agreement fraction above which the paper's first-order (one hidden derivative) interpolation has more coefficients than constraints.
--
--   **Formalization Note.** $u_\rho$ is `sSup` of the set of positive solutions, which for $\rho>0$ is a singleton, so `uRho ρ` is that solution. The curve is used only for $0<\rho<1$.
-- source:
--   Dao, Kominers, Thaler, Reed–Solomon Codes Beyond Johnson: Efficient Decoding and Smaller Cryptographic Proofs, STOC 2027 submission (manuscript of November 2, 2026, sha256 76a38731…), p. 22, Definition 3.15, (22)–(24)

import Mathlib

namespace RSBeyondJohnson.FirstOrder

/-!
# The first-order agreement curve `a₁(ρ)` (Definition 3.15)

Dao, Kominers, Thaler, *Reed–Solomon Codes Beyond Johnson*, STOC 2027 submission (manuscript of
November 2, 2026), §3.5, p. 22, (22)–(24).

The curve is used only for rates `0 < ρ < 1`; values outside that range are not meaningful.
-/

/-- The branch cutoff `ρ_c := 11 − 3√13 ≈ 0.183346` ((22), p. 22). -/
noncomputable def rhoC : ℝ := 11 - 3 * Real.sqrt 13

/-- `u_ρ`, the unique positive solution `u` of `u² (u + 3) = √(ρ/2)` ((23), p. 22). For `ρ > 0`
the left side increases strictly from `0` to `∞` on `u > 0`, so the set below is a singleton and
its supremum is that solution. -/
noncomputable def uRho (ρ : ℝ) : ℝ :=
  sSup {u : ℝ | 0 < u ∧ u ^ 2 * (u + 3) = Real.sqrt (ρ / 2)}

/-- **Definition 3.15 (First-order agreement curve)**, (24), p. 22:
`a₁(ρ) = √(ρ/2) (1 + u_ρ)` for `0 < ρ < ρ_c`, and
`a₁(ρ) = (3ρ + 2√(ρ(5 − ρ)(2 − ρ)))/(8 − ρ)` for `ρ_c ≤ ρ < 1`. -/
noncomputable def a1 (ρ : ℝ) : ℝ :=
  if ρ < rhoC then Real.sqrt (ρ / 2) * (1 + uRho ρ)
  else (3 * ρ + 2 * Real.sqrt (ρ * (5 - ρ) * (2 - ρ))) / (8 - ρ)

end RSBeyondJohnson.FirstOrder



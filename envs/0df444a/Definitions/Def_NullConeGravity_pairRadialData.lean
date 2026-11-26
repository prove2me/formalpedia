-- Prove2me | Definitions.Def_NullConeGravity_pairRadialData
-- name    : NullConeGravity_pairRadialData
-- status  : Definition
-- author  : @LG
-- created : 2026-11-26T14:12:10.398504+00:00
-- url     : https://prove2.me/theorems/d33bb431-544b-4bbd-aab3-9b20d90aec7e
-- title:
--   Graviton pair radial data
-- statement:
--   Fix the dimensionless corner area $s = \mathscr{A}/(4 G_N \hbar) > 0$ and expand the radiative data on the incoming null cone in radial modes $k = 1,2,\dots$ (represented in Lean by $k+1$ for $k \in \mathbb{N}$). The Gaussian state of the canonical pairs assigns to mode $k$ the variance
--
--   $$ (\Delta q_k)^2 = \frac{1}{2 s k}. $$
--
--   The connected overlap for creating a graviton pair at one insertion and annihilating it at a second insertion, with relative phase $e^{-2ik/s}$, has $k$-th summand
--
--   $$ 2\,(\Delta q_k)^4\, e^{-2ik/s}, $$
--
--   and the full amplitude is the sum over modes, `pairAmplitude s = ∑' k, pairTerm s k`. The factor $2$ counts the two connected Wick contractions, and $(\Delta q_k)^4$ is the squared pair-creation amplitude.
--
--   These definitions package the radial-mode data of the graviton pair computation in Section 4.4 of the source, so that the closed-form amplitude theorem can be stated as an identity between `pairAmplitude` and the dilogarithm.
--
--   **Formalization Note.** `radialVar` is real-valued; it is coerced to `ℂ` inside `pairTerm`, where the phase `Complex.exp (-2 * Complex.I * (k+1) / s)` lives. The mode index is shifted by one so that `ℕ` starts at the fundamental mode $k=1$.
-- source:
--   V. Chandrasekaran, An algebraic quantization of gravity from the null cone, https://arxiv.org/abs/2611.34924, Section 4.4, Eqs. (4.32)–(4.33)

import Mathlib

namespace NullConeGravity

/-- Gaussian variance of radial mode `k+1`: `(Δq_k)² = 1/(2 s k)`, `s = 𝒜/(4 G_N ℏ)`. -/
noncomputable def radialVar (s : ℝ) (k : ℕ) : ℝ := 1 / (2 * s * (k + 1))

/-- The `k`-th summand of the connected graviton-pair overlap: `2 (Δq_k)⁴ exp(-2 i k / s)`. -/
noncomputable def pairTerm (s : ℝ) (k : ℕ) : ℂ :=
  2 * (radialVar s k : ℂ) ^ 2 * Complex.exp (-2 * Complex.I * (k + 1 : ℂ) / (s : ℂ))

/-- The connected graviton pair creation–annihilation amplitude, summed over radial modes. -/
noncomputable def pairAmplitude (s : ℝ) : ℂ := ∑' k : ℕ, pairTerm s k

end NullConeGravity



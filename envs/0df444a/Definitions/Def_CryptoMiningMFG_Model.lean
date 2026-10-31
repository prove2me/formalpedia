-- Prove2me | Definitions.Def_CryptoMiningMFG_Model
-- name    : CryptoMiningMFG_Model
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T18:57:32.762255+00:00
-- url     : https://prove2.me/theorems/14bbcffd-d4b0-43f2-9831-7c3a48d2f20f
-- title:
--   Parameters of the CARA mining game; $U(x)=-\frac1\gamma e^{-\gamma x}$, $w(r;\gamma)$, $a^*$
-- statement:
--   A continuum of miners competes for proof-of-work rewards over a finite period $[t_0,T]$. The model has the following parameters:
--
--   1. $\mathcal K>0$, the reward intensity of the whole system (rewards arrive as a Poisson process with intensity $\mathcal K$);
--   2. $c>0$, the cost per unit of hash rate per unit of time;
--   3. $r>0$, the value of one mining reward;
--   4. $\gamma>0$, the absolute risk aversion of the miners;
--   5. $M>0$, the number of *other* miners ($M+1$ miners in total);
--   6. $t_0<T$, the mining period.
--
--   Three derived quantities are used throughout:
--
--   $$
--   U(x)=-\frac1\gamma e^{-\gamma x},\qquad w(r;\gamma)=\frac{1-e^{-\gamma r}}{\gamma},\qquad a^*=\frac{\mathcal K M}{c(1+M)^2}\,w(r;\gamma).
--   $$
--
--   $U$ is the exponential (CARA) utility of terminal wealth, $w(r;\gamma)$ is the certainty-equivalent factor of one reward, and $a^*$ is the explicit equilibrium hash rate of Proposition 3.1.
--
--   **Formalization Note** $M$ is a positive real number; the paper's $M$ is a positive integer, which nothing in the CARA analysis uses.
-- source:
--   Li, Reppen, Sircar, A Mean Field Games Model for Cryptocurrency Mining, arXiv:1912.01952v2 (preprint, 22 Jan 2022), https://arxiv.org/abs/1912.01952v2, §2.3 pp.8–9 (𝒦 > 0, c > 0, M + 1 miners, r, [t0, T]); eq. (3.1), (3.2) p.14; eq. (3.3) p.14

import Mathlib

namespace CryptoMiningMFG

/-- **Model parameters** of the mining game with exponential utility.
Li, Reppen, Sircar, *A Mean Field Games Model for Cryptocurrency Mining*, arXiv:1912.01952v2,
§2.3, pp.8–9, and §3.1, eqs. (3.1)–(3.2), p.14.

* `K` is the reward intensity of the whole system (the calligraphic 𝒦, "a Poisson process with a
  constant intensity 𝒦 > 0", p.9);
* `c > 0` is the cost per unit of hash rate per unit of time ("a linear cost cα_t", p.8);
* `r` is the value of the mining reward (eq. (2.3), p.9);
* `γ > 0` is the risk aversion of the exponential utility (eq. (3.1), p.14);
* `M` is the number of other miners: `M + 1` is the total number of miners (p.9);
* `[t0, T]` is the mining period (p.8).

**Formalization Note.** `M` is a positive **real** number; the paper's `M` is a positive integer
("assumed large") and nothing in §3.1 uses integrality. The reward is assumed positive (`0 < r`),
as a reward is; `t0 < T` makes the period nondegenerate. -/
structure Model where
  /-- system-wide reward intensity `𝒦` -/
  K : ℝ
  /-- unit cost of hash rate -/
  c : ℝ
  /-- value of one mining reward -/
  r : ℝ
  /-- absolute risk aversion of the exponential utility -/
  γ : ℝ
  /-- number of other miners (`M + 1` miners in total) -/
  M : ℝ
  /-- start of the mining period -/
  t0 : ℝ
  /-- terminal time -/
  T : ℝ
  K_pos : 0 < K
  c_pos : 0 < c
  r_pos : 0 < r
  γ_pos : 0 < γ
  M_pos : 0 < M
  t0_lt_T : t0 < T

namespace Model

variable (P : Model)

/-- The exponential (CARA) utility `U(x) = −(1/γ) e^{−γx}`, eq. (3.1), p.14. -/
noncomputable def U (x : ℝ) : ℝ := -(1 / P.γ) * Real.exp (-P.γ * x)

/-- `w(r; γ) = (1 − e^{−γr}) / γ`, eq. (3.2), p.14. -/
noncomputable def w : ℝ := (1 - Real.exp (-P.γ * P.r)) / P.γ

/-- The constant hash rate `𝒦M w(r; γ) / (c (1 + M)²)` of eq. (3.3), p.14. -/
noncomputable def aStar : ℝ := P.K * P.M * P.w / (P.c * (1 + P.M) ^ 2)

end Model

end CryptoMiningMFG



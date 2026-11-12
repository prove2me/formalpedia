-- Prove2me | Definitions.Def_GaussMixGated_ExactReal_Schedule
-- name    : GaussMixGated_ExactReal_Schedule
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-11T15:24:13.439251+00:00
-- url     : https://prove2.me/theorems/11a0993c-3bc7-4913-823c-96fd000183d0
-- title:
--   The explicit schedule (7)–(9): $A_*$, $H$, $J$, $\beta$, $L_*$, $\sigma_j$, $N_0$, $R_0$
-- statement:
--   With natural logarithms and $\log_4x=\log x/\log4$, the schedule of §2.1 is
--
--   $$A_*=1+2C_{\mathrm{cov}},\quad H=\log(1/\delta),\quad J=\big\lceil\log_4 32(d+H+2)\big\rceil,$$
--
--   $$\beta=\frac{\varepsilon^2}{1000(J+1)A_*^{J+1}},\quad L_*=\log(2k/\beta),\quad \sigma_j=2^{J-j}\ (0\le j\le J),$$
--
--   $$N_0=\lceil(k/\beta)\log(16k/\delta)\rceil,\qquad R_0=\sqrt d+\sqrt{2\log(16N_0/\delta)}.$$
--
--   These quantities are fixed before any data are processed and are used by displays (10) and (12).
-- source:
--   Zheng, Xie, He, Learning Finite Gaussian Location Mixtures via Gated Moments and Posterior Covers, STOC 2027 submission #36 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/36.pdf, PDF p. 7, §2.1, (7)–(9)

import Mathlib

noncomputable section

namespace GaussMixGated.ExactReal

/-!
# The explicit schedule of §2.1 (Zheng–Xie–He, STOC 2027 #36, (7)–(9), PDF p. 7)

All logarithms are natural; `log₄ x = log x / log 4`.
-/

/-- `A* = 1 + 2 C_cov` of (7). -/
def Astar (Ccov : ℝ) : ℝ := 1 + 2 * Ccov

/-- `H = log(1/δ)` of (7). -/
def Hconf (δ : ℝ) : ℝ := Real.log (1 / δ)

/-- `J = ⌈log₄ 32(d + H + 2)⌉` of (7). -/
def Jsched (d : ℕ) (δ : ℝ) : ℕ := ⌈Real.log (32 * (d + Hconf δ + 2)) / Real.log 4⌉₊

/-- `β = ε² / (1000 (J + 1) A*^{J+1})` of (8). -/
def betaSched (d : ℕ) (ε δ Ccov : ℝ) : ℝ :=
  ε ^ 2 / (1000 * ((Jsched d δ : ℝ) + 1) * Astar Ccov ^ (Jsched d δ + 1))

/-- `L* = log(2k/β)` of (8). -/
def Lstar (d k : ℕ) (ε δ Ccov : ℝ) : ℝ := Real.log (2 * k / betaSched d ε δ Ccov)

/-- `σ_j = 2^{J−j}` (`0 ≤ j ≤ J`) of (8). -/
def sigmaSched (d : ℕ) (δ : ℝ) (j : ℕ) : ℝ := 2 ^ (Jsched d δ - j)

/-- `N₀ = ⌈(k/β) log(16k/δ)⌉`, the number of initial centers (§2.1). -/
def N0sched (d k : ℕ) (ε δ Ccov : ℝ) : ℕ :=
  ⌈(k / betaSched d ε δ Ccov) * Real.log (16 * k / δ)⌉₊

/-- `R₀ = √d + √(2 log(16 N₀/δ))` of (9). -/
def R0sched (d k : ℕ) (ε δ Ccov : ℝ) : ℝ :=
  Real.sqrt d + Real.sqrt (2 * Real.log (16 * N0sched d k ε δ Ccov / δ))

end GaussMixGated.ExactReal



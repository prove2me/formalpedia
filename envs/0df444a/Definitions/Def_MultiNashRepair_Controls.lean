-- Prove2me | Definitions.Def_MultiNashRepair_Controls
-- name    : MultiNashRepair_Controls
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T22:29:04.029465+00:00
-- url     : https://prove2.me/theorems/f5afc5f4-e2d2-4372-94cc-17d758d565fd
-- title:
--   Admissible fixed controls $(d, f_0, m_0)$ for a rational target $\sigma$
-- statement:
--   Fix a rational target $\sigma$. **Admissible controls** for $\sigma$ are rationals $d,f_0$ and a natural number $m_0$ with
--   1. $d>0$ and $\sigma+8d<\sigma_\star$;
--   2. $7/12\le f_0\le 3/5$, $\ \min_{0\le H\le f_0}K_{f_0}(H)>\sigma+7d$ and $1/f_0>\sigma+7d$ (5.1);
--   3. $m_0\ge\max\{66/d,\ 1000/u^2,\ 400/d\}$ (5.2),
--
--   where the steps are $u=\tfrac12\min\{1/144,d/100\}$ and $\eta=\tfrac12\min\{1/4,d/24\}$ (3.12). The descent margin at scaled satisfaction $\varsigma$ and history $H$ is $\mu=S_u(H)-\varsigma-d$ (3.13), with $S_u$ evaluated at $(f_0,u)$.
--
--   Algorithm 1 fixes one such tuple from $\sigma$ alone before reading the game.
--
--   **Formalization Note** The run relation and the milestones hold for every admissible tuple, which covers the algorithm's effective choice. The constants $L_{\mathrm{col}}=9$ and $C_E=120$ appear as numerals in the statements.
-- source:
--   J. Tang, S. Ding, C. Fang, Breaking the One-Player Extension Barrier: History-Aware Repair for Multiplayer Approximate Nash Equilibria, arXiv:2611.06076 (preprint; held version, sha256 34b911ed…5c14), §3.3, (3.12), p.10; §5.1, (5.1)–(5.2), p.15; (3.13), p.10

import Mathlib
import Definitions.Def_MultiNashRepair_ScalarCertificate
import Definitions.Def_MultiNashRepair_Knobs

noncomputable section

namespace MultiNashRepair

/-- The repair step scale `u = ½ min{1/144, d/100}` ((3.12), p.10). -/
def uOf (d : ℚ) : ℚ := (1 / 2) * min (1 / 144) (d / 100)

/-- The descent step size `η = ½ min{1/4, d/24}` ((3.12), p.10). -/
def etaOf (d : ℚ) : ℚ := (1 / 2) * min (1 / 4) (d / 24)

/-- **Admissible fixed controls for a rational target `σ`** (Tang, Ding, Fang,
arXiv:2611.06076, §3.3 (3.12) p.10 and §5.1 (5.1)–(5.2) p.15).

A positive rational reserve `d` with `σ + 8d < σ⋆`; a rational activation fraction
`f0 ∈ [7/12, 3/5]` with `min_{0 ≤ H ≤ f0} K_{f0}(H) > σ + 7d` and `1/f0 > σ + 7d` (5.1); and a
player-count cutoff `m0 ≥ max{66/d, 1000/u², 400/d}` (5.2), where `u = ½ min{1/144, d/100}` and
`η = ½ min{1/4, d/24}` (3.12). `Lcol = 9` and `C_E = 120` are fixed numerals in the statements.

**Formalization Note.** Algorithm 1 chooses one such tuple effectively (§5.1, §5.6); the run
relation and every milestone hold for **every** admissible tuple, which covers the algorithm's
choice. The controls `c, t, ρ, β, ν, R0, G0, Q, a_u, L0` are the functions of `Knobs`
evaluated at `(f0, u)`. -/
structure Controls (σ : ℚ) where
  /-- the reserve `d` -/
  d : ℚ
  d_pos : 0 < d
  d_reserve : (σ : ℝ) + 8 * d < sigmaStar
  /-- the activation fraction `f0` -/
  f0 : ℚ
  f0_ge : (7 / 12 : ℚ) ≤ f0
  f0_le : f0 ≤ 3 / 5
  f0_U : (σ : ℝ) + 7 * d < U f0
  f0_inv : (σ : ℝ) + 7 * d < 1 / (f0 : ℝ)
  /-- the player-count cutoff `m0` -/
  m0 : ℕ
  m0_ge_d : 66 / (d : ℝ) ≤ m0
  m0_ge_u : 1000 / ((uOf d : ℚ) : ℝ) ^ 2 ≤ m0
  m0_ge_d' : 400 / (d : ℝ) ≤ m0

namespace Controls

variable {σ : ℚ} (ctrl : Controls σ)

/-- The repair step scale `u` ((3.12), p.10). -/
def u : ℚ := uOf ctrl.d

/-- The descent step size `η` ((3.12), p.10). -/
def η : ℚ := etaOf ctrl.d

/-- The control functions evaluated at `(f0, u)`. -/
def knobs : Knobs := ⟨ctrl.f0, ctrl.u⟩

/-- The descent margin `µ = S_u(H) − ς − d` ((3.13), p.10). -/
def mu (ς H : ℝ) : ℝ := ctrl.knobs.Su H - ς - ctrl.d

end Controls

end MultiNashRepair



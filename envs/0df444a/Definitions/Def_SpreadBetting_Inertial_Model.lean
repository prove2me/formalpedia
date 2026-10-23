-- Prove2me | Definitions.Def_SpreadBetting_Inertial_Model
-- name    : SpreadBetting_Inertial_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-22T12:31:35.723217+00:00
-- url     : https://prove2.me/theorems/921e0b76-42dd-47d8-ad94-7fe91e3ca20b
-- title:
--   §2, §4, (E.1), (G.1)–(G.5), (4.8), (4.13) — spread betting market, Assumption 1, inertial policy, informed bettor's profit and best response (2.3), regret (2.5), threshold z̄, J̄
-- statement:
--   This file sets up the spread betting market of Birge, Feng, Keskin and Schultz together with the market maker's **inertial policy** (IP) and the objects used to analyse it.
--
--   **Market.** An event outcome $X = m + \varepsilon$ has unknown median $m \in \{m_0, m_1\}$ with $s_L < m_0 < m_1 < s_H$; under hypothesis $H_i$ the median is $m_i$ and $X$ has c.d.f. $F_i(x) = F_\varepsilon(x - m_i)$, where $F_\varepsilon(x) = \int_{-\infty}^x f_\varepsilon$ and $\bar F_i = 1 - F_i$. The market maker charges a commission $c \in (0,1)$. The **standing assumptions** are these ranges together with Assumption 1: $f_\varepsilon$ is a continuously differentiable probability density, symmetric around zero, and strictly positive on $|x| \le \max\{s_H - m_0, m_1 - s_L\}$.
--
--   **Constants.** $\alpha := F_1(m_0)$, $r_0 := [\tfrac12 - F_1(\tfrac{m_0+m_1}{2})]^{-1}$, $F_i^{-1}(p) := \inf\{x : p \le F_i(x)\}$, and the bound $\bar r = \min\{2, \bar r_0, \bar r_1\}$ of (G.2) with
--   $$
--   \bar r_0 = \frac{c\, r_0}{(2-c)\zeta_0},\quad \zeta_0 = \max\Big\{1, \max_{s\in[m_0,m_1]} \frac{f_1(s)}{f_0(s)}\Big\},\qquad
--   \bar r_1 = \begin{cases} 2r_0/(-\zeta_1) & \zeta_1 < 0,\\ \infty & \zeta_1 \ge 0,\end{cases}\quad \zeta_1 = \min_{s\in[m_0,m_1]} \Big(\frac{f_1'(s)}{f_1(s)} - \frac{f_0'(s)}{f_0(s)}\Big)\frac{1}{f_0(s)}.
--   $$
--
--   **Inertial policy.** The market state is $Z_t = \sum_{\ell < t} d_\ell$ with $Z_1 = 0$, and the spread line is $s_t = \tilde s(Z_t)$. A residual probability sequence $\rho : \mathbb Z_+ \to (0, \tfrac12 - \alpha)$ determines $\tilde s$ by (4.3): $\tilde s(z) = F_1^{-1}(\tfrac12 - \rho(z))$ for $z > 0$, $\tilde s(0) = \tfrac{m_0+m_1}{2}$, $\tilde s(z) = F_0^{-1}(\tfrac12 + \rho(-z))$ for $z < 0$; and $\rho$ is extended to $\mathbb Z$ by (E.1): $\rho(0) = \tfrac12 - F_1(\tfrac{m_0+m_1}2)$ and $\rho(z) = \tfrac12 - F_1(F_0^{-1}(\tfrac12 + \rho(-z)))$ for $z < 0$. The paper's choice is $\rho(z) = 1/(r_0 + rz)$, whose real extension (G.5) is also defined.
--
--   **Bettors and payoffs.** At each bet the informed bettor chooses $a_t \in \{+1, 0, -1\}$, possibly at random, based on past bets, his own past actions and the current state; if $a_t = 0$ a myopic bettor bets $+1$ with probability $\bar F_i(s_t)$ and $-1$ otherwise. The informed bettor's per-bet expected payoffs are $j_i^+(s) = (1-c)\bar F_i(s) - F_i(s)$ and $j_i^-(s) = (1-c)F_i(s) - \bar F_i(s)$ (2.1). Expected cumulative quantities $\sum_{t=1}^T \mathbb E[w(Z_t, a_t, d_t)]$ and terminal values $\mathbb E[g(Z_{T+1})]$ are defined exactly, by recursion over the finitely many bet histories. From these: the profit $V_i^{\pi,\xi}(T)$ of (2.2); the regret
--   $$
--   \Delta_i^{\pi,\xi}(T) = \frac{cT}{2} - \sum_{t=1}^T \mathbb E_i^{\pi,\xi}\big[\mathbb I\{(X-s_t)d_t<0\} - (1-c)\mathbb I\{(X-s_t)d_t>0\}\big]
--   $$
--   of (2.5); the value $J^i(z) = \sup_\xi \liminf_T V$ from state $z$; and the **best response** (2.3): $\xi^*$ maximizes $\liminf_T V(T)$ if $\sup_\xi \liminf_T V(T) < \infty$, and $\liminf_T V(T)/T$ otherwise.
--
--   **Threshold.** $\bar z := \inf\{z : \frac{\rho(z-1)}{2\rho(z)} - \rho(z) - \rho(z-1) > \tfrac12 - \tfrac{c}{2-c}\}$ (G.1), with $\bar z = \infty$ for an empty set and $-\infty$ for a set unbounded below. The threshold strategy (4.4) is $\xi_1^*(z) = \mathbb I\{z < \bar z\}$, $\xi_0^*(z) = -\mathbb I\{z > -\bar z\}$; the generic $\bar Z$-threshold strategy of Definition 4 is the same with any $\bar Z \in \mathbb Z \cup \{-\infty\}$. The value function (4.8) is $\bar J^1 \equiv 0$ if $\bar z = -\infty$ and otherwise
--   $$
--   \bar J^1(z) = j_1^+(\bar z - 1)\sum_{n \ge (z-\bar z)^+} \Lambda_n + \sum_{i=1}^{(\bar z - z)^+} j_1^+(\bar z - i),\qquad \Lambda_n = \prod_{k=0}^n \frac{\tfrac12 - \rho(\bar z + k)}{\tfrac12 + \rho(\bar z+k)},
--   $$
--   with $j_1^+(z) := j_1^+(\tilde s(z))$ and $\bar J^0(z) := \bar J^1(-z)$. The loss function (4.13) is $l(z) = (2-c)\rho(z)\mathbb I\{z<\bar z\} + (4-2c)\rho^2(z)\mathbb I\{z \ge \bar z\}$.
--
--   These objects are shared by every statement of the mission.
--
--   **Formalization Note** The density $f_\varepsilon$ is the primitive and $F_\varepsilon$ its integral. $\rho$ is a function on $\mathbb N$ of which only the values at $z \ge 1$ enter. A strategy is a function of the list of past (bet, own action) pairs and the current state $Z_t$ (a function of the public history, which determines $s_t$), returning a weight for each action; admissibility means the weights form a probability vector. Expectations are finite recursions, not integrals. The liminfs and suprema of (2.3) and $J^i$ are taken in `EReal`. "$z < \bar z$" is encoded as "$z < w$ for every $w$ in the set of (G.1)", which is right for all three cases of $\bar z$; `zbar` is `sInf` of that set and is used only where the set is nonempty and bounded below. `Jbar1` returns $0$ when the set of (G.1) is empty ($\bar z = +\infty$), a case excluded by Lemma G.2. The infinite sum in `Jbar1` is a `tsum`, which is $0$ for a non-summable series, so Lemma 1 asserts summability separately.
-- source:
--   Birge, Feng, Keskin & Schultz, SSRN 3283392 (version of April 14, 2020), pp. 6–17, 45, 49, §2, §4, Assumption 1, (2.1)–(2.5), (4.1)–(4.4), (4.7)–(4.9), (4.13), (E.1), (G.1)–(G.5), Definition 4 p. 68, (L.4) p. 71

import Mathlib

/-!
Birge, Feng, Keskin & Schultz, *Dynamic Learning and Market Making in Spread Betting Markets
with Informed Bettors*, SSRN 3283392 (version of April 14, 2020).

The spread betting market of §2 (pp. 6–10), Assumption 1 (p. 10), the inertial policy of §4
(pp. 14–17) through its residual probabilities (Proposition 2, (4.3), (E.1)), the informed
bettor's expected profit (2.2) and best response (2.3), the market maker's regret (2.5), the
threshold z̄ of (G.1), the bound r̄ of (G.2)–(G.4), the value function J̄ of (4.8)–(4.9) and the
loss function (4.13).

Expectations are exact finite recursions over bet histories (`cumExp`, `termExp`): an informed
bet `d_t = a_t`, otherwise the myopic bet `ϑ_t = +1` with probability `F̄_i(s_t)` (p. 7).
-/

open MeasureTheory Filter Topology

namespace SpreadBetting.Inertial

/-- The data of the market (§2.2, p. 7): commission `c`, the two candidate medians `m0 < m1`,
the spread-line range `[sL, sH]`, and the density `feps` of the noise `ε` (Assumption 1). -/
structure Market where
  c : ℝ
  m0 : ℝ
  m1 : ℝ
  sL : ℝ
  sH : ℝ
  feps : ℝ → ℝ

/-- The noise c.d.f. `F_ε(x) = ∫_{-∞}^x f_ε`. -/
noncomputable def Feps (M : Market) (x : ℝ) : ℝ := ∫ t in Set.Iic x, M.feps t

/-- The median `m_i` under hypothesis `H_i`. -/
def med (M : Market) (i : Fin 2) : ℝ := if i = 0 then M.m0 else M.m1

/-- `F_i(x) = F_ε(x - m_i)`, the outcome c.d.f. under `H_i`. -/
noncomputable def F (M : Market) (i : Fin 2) (x : ℝ) : ℝ := Feps M (x - med M i)

/-- `F̄_i = 1 - F_i`. -/
noncomputable def Fbar (M : Market) (i : Fin 2) (x : ℝ) : ℝ := 1 - F M i x

/-- `f_i(x) = f_ε(x - m_i)`, the outcome density under `H_i`. -/
def f (M : Market) (i : Fin 2) (x : ℝ) : ℝ := M.feps (x - med M i)

/-- The standing assumptions: the model's ranges `c ∈ (0,1)`, `sL < m0 < m1 < sH` (p. 7), that
`feps` is a probability density, and Assumption 1 (A1:1)–(A1:3) (p. 10). -/
structure Market.Standing (M : Market) : Prop where
  c_pos : 0 < M.c
  c_lt_one : M.c < 1
  sL_lt_m0 : M.sL < M.m0
  m0_lt_m1 : M.m0 < M.m1
  m1_lt_sH : M.m1 < M.sH
  feps_contDiff : ContDiff ℝ 1 M.feps
  feps_nonneg : ∀ x, 0 ≤ M.feps x
  feps_integrable : Integrable M.feps
  feps_integral : ∫ x, M.feps x = 1
  feps_symm : ∀ x, M.feps x = M.feps (-x)
  feps_pos : ∀ x, |x| ≤ max (M.sH - M.m0) (M.m1 - M.sL) → 0 < M.feps x

/-- `α := F_1(m_0)` (p. 15). -/
noncomputable def alpha (M : Market) : ℝ := F M 1 M.m0

/-- `r_0 := [1/2 - F_1((m_0+m_1)/2)]⁻¹` (p. 15). -/
noncomputable def r0 (M : Market) : ℝ := (1 / 2 - F M 1 ((M.m0 + M.m1) / 2))⁻¹

/-- The (generalized) inverse `F_i^{-1}(p) = inf {x : p ≤ F_i(x)}`. -/
noncomputable def Finv (M : Market) (i : Fin 2) (p : ℝ) : ℝ := sInf {x : ℝ | p ≤ F M i x}

/-- `ζ_0 := max {1, max_{s ∈ [m0,m1]} f_1(s)/f_0(s)}` (G.3). -/
noncomputable def zeta0 (M : Market) : ℝ :=
  max 1 (sSup ((fun s => f M 1 s / f M 0 s) '' Set.Icc M.m0 M.m1))

/-- `r̄_0 := c r_0 / ((2-c) ζ_0)` (G.3). -/
noncomputable def rbar0 (M : Market) : ℝ := M.c * r0 M / ((2 - M.c) * zeta0 M)

/-- `ζ_1 := min_{s ∈ [m0,m1]} (f_1'(s)/f_1(s) - f_0'(s)/f_0(s)) / f_0(s)` (G.4). -/
noncomputable def zeta1 (M : Market) : ℝ :=
  sInf ((fun s => (deriv (f M 1) s / f M 1 s - deriv (f M 0) s / f M 0 s) * (1 / f M 0 s)) ''
    Set.Icc M.m0 M.m1)

/-- `r̄_1 := sup {r : ζ_1 r + 2 r_0 > 0}`, which is `2 r_0/(-ζ_1)` if `ζ_1 < 0` and `+∞`
otherwise (G.4). -/
noncomputable def rbar1 (M : Market) : EReal :=
  if zeta1 M < 0 then ((2 * r0 M / (-zeta1 M) : ℝ) : EReal) else ⊤

/-- `r̄ := min {2, r̄_0, r̄_1}` (G.2), with the case `r̄_1 = +∞` written out. -/
noncomputable def rbar (M : Market) : ℝ :=
  if zeta1 M < 0 then min 2 (min (rbar0 M) (2 * r0 M / (-zeta1 M))) else min 2 (rbar0 M)

/-- The extension (E.1) of a residual probability sequence `ρ : ℤ₊ → (0, 1/2 - α)` (given as a
function on `ℕ`, of which only the values at `z ≥ 1` are used) to all of `ℤ`. -/
noncomputable def rhoExt (M : Market) (ρp : ℕ → ℝ) (z : ℤ) : ℝ :=
  if 0 < z then ρp z.toNat
  else if z = 0 then 1 / 2 - F M 1 ((M.m0 + M.m1) / 2)
  else 1 / 2 - F M 1 (Finv M 0 (1 / 2 + ρp (-z).toNat))

/-- The pricing function `s̃` of the inertial policy, (4.3). -/
noncomputable def sTilde (M : Market) (ρp : ℕ → ℝ) (z : ℤ) : ℝ :=
  if 0 < z then Finv M 1 (1 / 2 - ρp z.toNat)
  else if z = 0 then (M.m0 + M.m1) / 2
  else Finv M 0 (1 / 2 + ρp (-z).toNat)

/-- The paper's residual probabilities `ρ(z) = 1/(r_0 + r z)` (p. 15). -/
noncomputable def rhoIP (M : Market) (r : ℝ) (z : ℕ) : ℝ := 1 / (r0 M + r * z)

/-- The real extension (G.5) of `ρ(z) = 1/(r_0 + r z)`. -/
noncomputable def rhoReal (M : Market) (r : ℝ) (x : ℝ) : ℝ :=
  if 0 ≤ x then 1 / (r0 M + r * x)
  else 1 / 2 - F M 1 (Finv M 0 (1 / 2 + 1 / (r0 M - r * x)))

/-- The indicator `𝕀{P} ∈ {0, 1}` of a proposition. -/
noncomputable def indic (P : Prop) : ℝ := by
  classical
  exact if P then 1 else 0

/-- The informed bettor's actions `a_t ∈ {+1, 0, -1}` (p. 8). -/
inductive Act
  | pos
  | wait
  | neg
  deriving DecidableEq

/-- A (possibly randomized, history-dependent) strategy of the informed bettor: given the past
`(bet d_ℓ, own action a_ℓ)` pairs and the current market state `Z_t`, a weight on each action. -/
abbrev Strategy := List (ℤ × Act) → ℤ → Act → ℝ

/-- Admissible: the weights are a probability distribution on actions at every argument. -/
def Admissible (ξ : Strategy) : Prop :=
  (∀ h z a, 0 ≤ ξ h z a) ∧ ∀ h z, ξ h z .pos + ξ h z .wait + ξ h z .neg = 1

/-- Expected cumulative reward `Σ_{t=1}^T E[w(Z_t, a_t, d_t)]` over `T` bets under hypothesis
`H_i`, the inertial policy with residual probabilities `ρp` and the strategy `ξ`, from the bet
history `h` and current state `z`: an informed bet `d = a` when `a ≠ 0`, else the myopic bet
`ϑ = +1` w.p. `F̄_i(s̃(z))` and `-1` w.p. `F_i(s̃(z))`; the state moves `z ↦ z + d`. -/
noncomputable def cumExp (M : Market) (ρp : ℕ → ℝ) (i : Fin 2) (ξ : Strategy)
    (w : ℤ → Act → ℤ → ℝ) : ℕ → List (ℤ × Act) → ℤ → ℝ
  | 0, _, _ => 0
  | T + 1, h, z =>
      ξ h z .pos * (w z .pos 1 + cumExp M ρp i ξ w T (h ++ [(1, .pos)]) (z + 1))
    + ξ h z .neg * (w z .neg (-1) + cumExp M ρp i ξ w T (h ++ [(-1, .neg)]) (z - 1))
    + ξ h z .wait *
        (Fbar M i (sTilde M ρp z) * (w z .wait 1 + cumExp M ρp i ξ w T (h ++ [(1, .wait)]) (z + 1))
        + F M i (sTilde M ρp z) * (w z .wait (-1) + cumExp M ρp i ξ w T (h ++ [(-1, .wait)]) (z - 1)))

/-- Expected terminal value `E[g(Z_{T+1})]` after `T` bets, same dynamics as `cumExp`. -/
noncomputable def termExp (M : Market) (ρp : ℕ → ℝ) (i : Fin 2) (ξ : Strategy)
    (g : ℤ → ℝ) : ℕ → List (ℤ × Act) → ℤ → ℝ
  | 0, _, z => g z
  | T + 1, h, z =>
      ξ h z .pos * termExp M ρp i ξ g T (h ++ [(1, .pos)]) (z + 1)
    + ξ h z .neg * termExp M ρp i ξ g T (h ++ [(-1, .neg)]) (z - 1)
    + ξ h z .wait *
        (Fbar M i (sTilde M ρp z) * termExp M ρp i ξ g T (h ++ [(1, .wait)]) (z + 1)
        + F M i (sTilde M ρp z) * termExp M ρp i ξ g T (h ++ [(-1, .wait)]) (z - 1))

/-- `j_i^+(s) = (1-c) P_i(X > s) + (-1) P_i(X < s)`, (2.1). -/
noncomputable def jPlus (M : Market) (i : Fin 2) (s : ℝ) : ℝ :=
  (1 - M.c) * Fbar M i s + (-1) * F M i s

/-- `j_i^-(s) = (1-c) P_i(X < s) + (-1) P_i(X > s)`, (2.1). -/
noncomputable def jMinus (M : Market) (i : Fin 2) (s : ℝ) : ℝ :=
  (1 - M.c) * F M i s + (-1) * Fbar M i s

/-- `j_i^±(z) := j_i^±(s̃(z))`, the shorthand of (4.7). -/
noncomputable def jPlusZ (M : Market) (ρp : ℕ → ℝ) (i : Fin 2) (z : ℤ) : ℝ :=
  jPlus M i (sTilde M ρp z)

noncomputable def jMinusZ (M : Market) (ρp : ℕ → ℝ) (i : Fin 2) (z : ℤ) : ℝ :=
  jMinus M i (sTilde M ρp z)

/-- The informed bettor's expected profit (2.2) over `T` bets, started from `Z_1 = z`. -/
noncomputable def V (M : Market) (ρp : ℕ → ℝ) (i : Fin 2) (ξ : Strategy) (T : ℕ) (z : ℤ) : ℝ :=
  cumExp M ρp i ξ
    (fun z a _ => match a with
      | .pos => jPlus M i (sTilde M ρp z)
      | .neg => jMinus M i (sTilde M ρp z)
      | .wait => 0) T [] z

/-- The market maker's expected profit on a realized bet `d` at line `s` under `H_i`:
`P_i(X < s) - (1-c) P_i(X > s)` for `d = +1`, `P_i(X > s) - (1-c) P_i(X < s)` for `d = -1`. -/
noncomputable def mmProfit (M : Market) (i : Fin 2) (s : ℝ) (d : ℤ) : ℝ :=
  if d = 1 then F M i s - (1 - M.c) * Fbar M i s else Fbar M i s - (1 - M.c) * F M i s

/-- The market maker's regret (2.5) under `H_i` against the strategy `ξ`, from `Z_1 = 0`. -/
noncomputable def regret (M : Market) (ρp : ℕ → ℝ) (i : Fin 2) (ξ : Strategy) (T : ℕ) : ℝ :=
  M.c * T / 2 - cumExp M ρp i ξ (fun z _ d => mmProfit M i (sTilde M ρp z) d) T [] 0

/-- `liminf_T V_i(T)` in `EReal`, from `Z_1 = z`. -/
noncomputable def liV (M : Market) (ρp : ℕ → ℝ) (i : Fin 2) (ξ : Strategy) (z : ℤ) : EReal :=
  Filter.liminf (fun T : ℕ => ((V M ρp i ξ T z : ℝ) : EReal)) atTop

/-- `liminf_T V_i(T)/T` in `EReal`, from `Z_1 = z`. -/
noncomputable def liAvg (M : Market) (ρp : ℕ → ℝ) (i : Fin 2) (ξ : Strategy) (z : ℤ) : EReal :=
  Filter.liminf (fun T : ℕ => ((V M ρp i ξ T z / T : ℝ) : EReal)) atTop

/-- `J^i(z)`: the informed bettor's maximal (liminf) total expected profit from state `z`, over
all admissible strategies (p. 17), in `EReal`. -/
noncomputable def Jval (M : Market) (ρp : ℕ → ℝ) (i : Fin 2) (z : ℤ) : EReal :=
  ⨆ ξ' : {ξ' : Strategy // Admissible ξ'}, liV M ρp i ξ'.1 z

/-- Best response (2.3), from the market's initial state `Z_1 = 0`. -/
def IsBestResponse (M : Market) (ρp : ℕ → ℝ) (i : Fin 2) (ξ : Strategy) : Prop :=
  Admissible ξ ∧
  ((⨆ ξ' : {ξ' : Strategy // Admissible ξ'}, liV M ρp i ξ'.1 0) < ⊤ →
      ∀ ξ', Admissible ξ' → liV M ρp i ξ' 0 ≤ liV M ρp i ξ 0) ∧
  ((⨆ ξ' : {ξ' : Strategy // Admissible ξ'}, liV M ρp i ξ'.1 0) = ⊤ →
      ∀ ξ', Admissible ξ' → liAvg M ρp i ξ' 0 ≤ liAvg M ρp i ξ 0)

/-- The set inside the infimum (G.1): `z̄ = inf zbarSet`. -/
def zbarSet (M : Market) (ρp : ℕ → ℝ) : Set ℤ :=
  {z : ℤ | rhoExt M ρp (z - 1) / (2 * rhoExt M ρp z) - rhoExt M ρp z - rhoExt M ρp (z - 1)
      > 1 / 2 - M.c / (2 - M.c)}

/-- `z < z̄`, with `z̄ = inf zbarSet ∈ ℤ ∪ {±∞}` (true for all `z` if the set is empty, false for
all `z` if it is unbounded below). -/
def belowZbar (M : Market) (ρp : ℕ → ℝ) (z : ℤ) : Prop := ∀ w ∈ zbarSet M ρp, z < w

/-- `z̄` when it is finite (the set is nonempty and bounded below). -/
noncomputable def zbar (M : Market) (ρp : ℕ → ℝ) : ℤ := sInf (zbarSet M ρp)

/-- A generic threshold strategy: under `H_1`, bet `+1` if `below z` and wait otherwise; under
`H_0`, bet `-1` if `below (-z)` and wait otherwise. With `below = (· < Z̄)` this is the
`Z̄`-threshold strategy of Definition 4 (p. 68); with `below = belowZbar` it is (4.4). -/
noncomputable def threshStrat (i : Fin 2) (below : ℤ → Prop) : Strategy := by
  classical
  exact fun _ z a =>
    if i = 1 then
      (if below z then (if a = .pos then 1 else 0) else (if a = .wait then 1 else 0))
    else
      (if below (-z) then (if a = .neg then 1 else 0) else (if a = .wait then 1 else 0))

/-- The informed bettor's threshold strategy `ξ*_i` of (4.4), at the threshold `z̄` of (G.1). -/
noncomputable def xiStar (M : Market) (ρp : ℕ → ℝ) (i : Fin 2) : Strategy :=
  threshStrat i (belowZbar M ρp)

/-- `z < Z̄` for a generic threshold `Z̄ ∈ ℤ ∪ {-∞}` (`⊥ = -∞`). -/
def belowWB (Zbar : WithBot ℤ) (z : ℤ) : Prop := (z : WithBot ℤ) < Zbar

/-- `Λ_n = ∏_{k=0}^n (1/2 - ρ(Z+k))/(1/2 + ρ(Z+k))`, (4.9) at `Z = z̄`. -/
noncomputable def Lam (M : Market) (ρp : ℕ → ℝ) (Z : ℤ) (n : ℕ) : ℝ :=
  ∏ k ∈ Finset.range (n + 1), (1 / 2 - rhoExt M ρp (Z + k)) / (1 / 2 + rhoExt M ρp (Z + k))

/-- `J̄^1` of (4.8): `0` if `z̄ = -∞`; otherwise
`j_1^+(z̄-1) Σ_{n ≥ (z-z̄)^+} Λ_n + Σ_{i=1}^{(z̄-z)^+} j_1^+(z̄-i)`. It also returns `0` when the
set of (G.1) is empty (`z̄ = +∞`), a case excluded by Lemma G.2. -/
noncomputable def Jbar1 (M : Market) (ρp : ℕ → ℝ) (z : ℤ) : ℝ := by
  classical
  exact if (zbarSet M ρp).Nonempty ∧ BddBelow (zbarSet M ρp) then
      jPlusZ M ρp 1 (zbar M ρp - 1) *
          ∑' n : ℕ, Lam M ρp (zbar M ρp) ((z - zbar M ρp).toNat + n)
        + ∑ k ∈ Finset.Icc 1 (zbar M ρp - z).toNat, jPlusZ M ρp 1 (zbar M ρp - k)
    else 0

/-- `J̄^0(z) := J̄^1(-z)`, (4.8). -/
noncomputable def Jbar0 (M : Market) (ρp : ℕ → ℝ) (z : ℤ) : ℝ := Jbar1 M ρp (-z)

/-- The loss function (4.13) / `l̃` (p. 68): `(2-c)ρ(z)` if `below z`, else `(4-2c)ρ(z)²`. -/
noncomputable def lossFn (M : Market) (ρp : ℕ → ℝ) (below : ℤ → Prop) (z : ℤ) : ℝ := by
  classical
  exact if below z then (2 - M.c) * rhoExt M ρp z else (4 - 2 * M.c) * rhoExt M ρp z ^ 2

end SpreadBetting.Inertial



-- Prove2me | Definitions.Def_LargeCongestion_Poisson_Game
-- name    : LargeCongestion_Poisson_Game
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-22T17:26:29.85551+00:00
-- url     : https://prove2.me/theorems/52967cd3-ce7e-4a8d-8fae-a01cfefd166b
-- title:
--   §2–§4, pp. 9–19 — congestion structure (1), F(d) (2), Wardrop equilibrium (3), Bernoulli congestion games (8)–(11), BNE, conditions (14), (18), c̆_e (17), ζ (19), Λ (20)
-- statement:
--   This file sets up the congestion-game model of Cominetti, Scarsini, Schröder and Stier-Moses.
--
--   **Structure (1).** A finite set $\mathcal E$ of resources with costs $c_e : \mathbb N^* \to \mathbb R_+$, nonnegative and weakly increasing on $\mathbb N^* = \{1,2,\dots\}$, and a finite set $\mathcal T$ of types, each with a nonempty family $\mathcal S_t \subseteq 2^{\mathcal E}$ of feasible actions.
--
--   **Nonatomic games.** For demands $d = (d_t)_t$, a pair $(y,x)$ is *feasible*, $(y,x) \in \mathcal F(d)$, if
--   $$d_t = \sum_{s \in \mathcal S_t} y_{t,s},\quad y_{t,s} \ge 0,\quad x_e = \sum_{t}\sum_{s \in \mathcal S_t} y_{t,s}\mathbb 1_{\{e \in s\}} \qquad (2)$$
--   and a *Wardrop equilibrium* for costs $C_e$ if moreover $\hat y_{t,s} > 0 \Rightarrow \sum_{e \in s} C_e(\hat x_e) \le \sum_{e \in s'} C_e(\hat x_e)$ for all $s, s' \in \mathcal S_t$ (3).
--
--   **Bernoulli congestion games.** Finitely many players $i$, each with a type $t_i$ and a participation probability $u_i \in (0,1]$, play mixed strategies $\sigma_i \in \Delta(\mathcal S_{t_i})$. On $\Omega = \{0,1\}^{\mathcal N} \times \mathcal S$ the probability of $(\omega, s)$ is $\prod_i \mathsf P_i(\omega_i)\sigma_i(s_i)$ with $\mathsf P_i(1) = u_i$, $\mathsf P_i(0) = 1 - u_i$. With $U_{i,e} = U_i\mathbb 1_{\{e \in S_i\}}$ the random flows and loads are
--   $$Y_{t,s} = \sum_{i : t_i = t} U_i \mathbb 1_{\{S_i = s\}},\qquad X_e = \sum_i U_{i,e} \qquad (8)$$
--   with means $y_{t,s} = \sum_{i:t_i = t} u_i\sigma_i(s)$, $x_e = \sum_i u_i\sigma_{i,e}$, $\sigma_{i,e} = \sum_{s \in \mathcal S_{t_i}}\sigma_i(s)\mathbb 1_{\{e\in s\}}$ (5), (9); $Z_{i,e} = \sum_{j \ne i} U_{j,e}$ is the load of the others (10). A profile $\hat\sigma$ is a *Bayesian Nash equilibrium* if $\hat\sigma_i(s) > 0 \Rightarrow \sum_{e\in s}\mathsf E_{\hat\sigma}[c_e(1 + Z_{i,e})] \le \sum_{e \in s'}\mathsf E_{\hat\sigma}[c_e(1+Z_{i,e})]$ for all $s, s' \in \mathcal S_{t_i}$. Laws of random flows, loads and of the flow vector $(Y_{t,s})_{t, s\in\mathcal S_t}$ are the image measures of this probability.
--
--   **Sequences and limit game.** Condition (14) on games $\Gamma^n_B$: $|\mathcal N^n| \to \infty$, $u^n = \max_i u^n_i \to 0$, $d^n_t = \sum_{i: t^n_i = t} u^n_i \to d_t$. Condition (18): $d_{\max} > d_{\mathrm{tot}} = \sum_t d_t$ and $\mathsf E[|\Delta^2 c_e(1 + V)|] \le \nu$ for every $e$, $V \sim \mathrm{Poisson}(d_{\max})$. The auxiliary costs are $\breve c_e(x) = \mathsf E[c_e(1 + X)]$, $X \sim \mathrm{Poisson}(x)$ (17). Lemma 1's constants are
--   $$\zeta = (e^{d_{\max}} - 1)\nu + \max_e (c_e(2) - c_e(1)) \ \ (19),\qquad \Lambda(u) = \frac{\nu d_{\max}}{2}\frac{u e^u}{(1-u)^2} + u\zeta \ \ (20),$$
--   and the corrected $\tilde\Lambda(u) = \frac{\nu d_{\max} e^{d_{\max}}}{2}\frac{u e^u}{(1-u)^2} + u\zeta$.
--
--   These are the objects of Theorem 2: equilibria of the atomic Bernoulli games, and Wardrop equilibria of the nonatomic game $\breve\Gamma^\infty$ with costs $\breve c_e$.
--
--   **Formalization Note** Players are `Fin N` (0-based); strategies are `Finset E`, and $y_{t,s}$ is a function of all `s`, its values off $\mathcal S_t$ being unconstrained in $\mathcal F(d)$ and zero for expected flows of profiles. The page writes $c_e : \mathbb N_+ \to \mathbb N_+$ and $\nu \in \mathbb N$; the blackboard $\mathbb N$ is read as $\mathbb R$, so $c_e : \mathbb N \to \mathbb R$ with $c_e(0)$ never read, and $\nu \in \mathbb R$. Nonempty $\mathcal S_t$ is a standing assumption made explicit. In (18) the expectation is required to be a convergent series (`Summable` together with the bound), since Lean's `tsum` of a divergent series is $0$. $\max_i u_i$ is a supremum, $0$ for a game without players; $\max_e$ in $\zeta$ is a supremum over the finite set $\mathcal E$. $\tilde\Lambda$ is the constant for which Lemma 1 (21) holds; the printed $\Lambda$ is kept for the counterexample item.
-- source:
--   Cominetti, Scarsini, Schröder & Stier-Moses, Approximation and Convergence of Large Atomic Congestion Games, arXiv:2001.02797v7, pp. 9–12, (1), (2), (3), (5), (8)–(11), Bayesian Nash equilibrium; pp. 15–16, (14); p. 18, (17)–(20)

import Mathlib
import Definitions.Def_TotalVariationDist
import Definitions.Def_LargeCongestion_Poisson_PoissonCalculus

namespace LargeCongestion.Poisson

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal Topology

variable {E T : Type*} [Fintype E] [DecidableEq E] [Fintype T] [DecidableEq T]

/-! ### Structure (1), nonatomic games (2)–(3) -/

/-- Standing assumption on the strategy sets (§2, p. 9): every type `t` has a nonempty finite
family `S t ⊆ 2^E` of feasible actions. -/
def StrategiesNonempty (S : T → Finset (Finset E)) : Prop :=
  ∀ t, (S t).Nonempty

/-- Standing assumption on the costs (§2, p. 9; §2.3, p. 12): `c_e : ℕ* → ℝ₊` is nonnegative
and weakly increasing on `ℕ* = {1, 2, …}`. The value `c e 0` is never read. -/
def IsCostFamily (c : E → ℕ → ℝ) : Prop :=
  (∀ e k, 1 ≤ k → 0 ≤ c e k) ∧ ∀ e, MonotoneOn (c e) (Set.Ici 1)

/-- Feasible flow-load pairs `(y, x) ∈ F(d)`, (2), p. 9:
`d_t = ∑_{s ∈ S_t} y_{t,s}`, `y_{t,s} ≥ 0`, `x_e = ∑_t ∑_{s ∈ S_t} y_{t,s} 1{e ∈ s}`.
Values `y t s` with `s ∉ S t` are not constrained. -/
def IsFeasible (S : T → Finset (Finset E)) (d : T → ℝ) (y : T → Finset E → ℝ)
    (x : E → ℝ) : Prop :=
  (∀ t, d t = ∑ s ∈ S t, y t s) ∧ (∀ t, ∀ s ∈ S t, 0 ≤ y t s) ∧
    ∀ e, x e = ∑ t, ∑ s ∈ S t, if e ∈ s then y t s else 0

/-- Wardrop equilibrium (3), p. 10, of the nonatomic game with demands `d` and costs `C`:
`(y, x) ∈ F(d)` and `y_{t,s} > 0 ⟹ ∑_{e ∈ s} C_e(x_e) ≤ ∑_{e ∈ s'} C_e(x_e)` for all
`s, s' ∈ S_t`. -/
def IsWardrop (S : T → Finset (Finset E)) (C : E → ℝ → ℝ) (d : T → ℝ)
    (y : T → Finset E → ℝ) (x : E → ℝ) : Prop :=
  IsFeasible S d y x ∧
    ∀ t, ∀ s ∈ S t, ∀ s' ∈ S t, 0 < y t s → ∑ e ∈ s, C e (x e) ≤ ∑ e ∈ s', C e (x e)

/-! ### Bernoulli congestion games, §2.3, pp. 11–12 -/

/-- Participation probabilities `u_i ∈ (0, 1]` (§2.3, p. 11). Players are `Fin N`. -/
def IsBernoulliGame {N : ℕ} (u : Fin N → ℝ) : Prop :=
  ∀ i, 0 < u i ∧ u i ≤ 1

/-- A mixed strategy profile `σ ∈ Σ = ×_i Δ(S_{t_i})`: `σ i` is a probability vector supported
on `S (τ i)`, where `τ i = t_i` is the type of player `i`. -/
def IsMixedProfile {N : ℕ} (S : T → Finset (Finset E)) (τ : Fin N → T)
    (σ : Fin N → Finset E → ℝ) : Prop :=
  (∀ i s, 0 ≤ σ i s) ∧ (∀ i s, s ∉ S (τ i) → σ i s = 0) ∧ ∀ i, ∑ s ∈ S (τ i), σ i s = 1

/-- An outcome `(ω, s) ∈ Ω = {0,1}^N × S` (p. 12), stored player by player: `(ω i).1 = U_i`
(participation) and `(ω i).2 = S_i` (the realized pure strategy). -/
abbrev Outcome (E : Type*) (N : ℕ) := Fin N → Bool × Finset E

/-- The probability `P_σ(ω, s) = ∏_i P_i(ω_i) σ_i(s_i)` with `P_i(1) = u_i`,
`P_i(0) = 1 − u_i` (p. 12). -/
def weight {N : ℕ} (u : Fin N → ℝ) (σ : Fin N → Finset E → ℝ) (ω : Outcome E N) : ℝ :=
  ∏ i, (if (ω i).1 then u i else 1 - u i) * σ i (ω i).2

/-- The expectation `E_σ[f]` on the finite space `Ω`. -/
def expect {N : ℕ} (u : Fin N → ℝ) (σ : Fin N → Finset E → ℝ) (f : Outcome E N → ℝ) : ℝ :=
  ∑ ω, weight u σ ω * f ω

/-- The law `L(f)` of a random element `f : Ω → α` under `P_σ`. -/
noncomputable def law {α : Type*} [MeasurableSpace α] {N : ℕ} (u : Fin N → ℝ)
    (σ : Fin N → Finset E → ℝ) (f : Outcome E N → α) : Measure α :=
  ∑ ω, ENNReal.ofReal (weight u σ ω) • Measure.dirac (f ω)

/-- `U_{i,e} = U_i 1{e ∈ S_i}` (p. 12). -/
def useIndicator {N : ℕ} (i : Fin N) (e : E) (ω : Outcome E N) : ℕ :=
  if (ω i).1 = true ∧ e ∈ (ω i).2 then 1 else 0

/-- The random flow `Y_{t,s} = ∑_{i : t_i = t} U_i 1{S_i = s}`, (8). -/
def flowRV {N : ℕ} (τ : Fin N → T) (t : T) (s : Finset E) (ω : Outcome E N) : ℕ :=
  ∑ i, if τ i = t ∧ (ω i).1 = true ∧ (ω i).2 = s then 1 else 0

/-- The random load `X_e = ∑_i U_{i,e}`, (8). -/
def loadRV {N : ℕ} (e : E) (ω : Outcome E N) : ℕ :=
  ∑ i, useIndicator i e ω

/-- The load of the other players `Z_{i,e} = ∑_{j ≠ i} U_{j,e}`, (10). -/
def othersLoadRV {N : ℕ} (i : Fin N) (e : E) (ω : Outcome E N) : ℕ :=
  ∑ j ∈ Finset.univ.erase i, useIndicator j e ω

/-- `σ_{i,e} = ∑_{s ∈ S_{t_i}} σ_i(s) 1{e ∈ s}`, (5). -/
def sigmaE {N : ℕ} (S : T → Finset (Finset E)) (τ : Fin N → T) (σ : Fin N → Finset E → ℝ)
    (i : Fin N) (e : E) : ℝ :=
  ∑ s ∈ S (τ i), if e ∈ s then σ i s else 0

/-- Expected strategy flows `y_{t,s} = ∑_{i : t_i = t} u_i σ_i(s)`, (9). -/
def expFlow {N : ℕ} (τ : Fin N → T) (u : Fin N → ℝ) (σ : Fin N → Finset E → ℝ) (t : T)
    (s : Finset E) : ℝ :=
  ∑ i, if τ i = t then u i * σ i s else 0

/-- Expected resource loads `x_e = ∑_i u_i σ_{i,e}`, (9). -/
def expLoad {N : ℕ} (S : T → Finset (Finset E)) (τ : Fin N → T) (u : Fin N → ℝ)
    (σ : Fin N → Finset E → ℝ) (e : E) : ℝ :=
  ∑ i, u i * sigmaE S τ σ i e

/-- Bayesian Nash equilibrium (p. 12): `σ̂` is a mixed profile and, for every player `i` and
`s, s' ∈ S_{t_i}`, `σ̂_i(s) > 0 ⟹ ∑_{e ∈ s} E_σ̂[c_e(1 + Z_{i,e})] ≤ ∑_{e ∈ s'} E_σ̂[c_e(1 + Z_{i,e})]`. -/
def IsBNE {N : ℕ} (S : T → Finset (Finset E)) (c : E → ℕ → ℝ) (τ : Fin N → T)
    (u : Fin N → ℝ) (σ : Fin N → Finset E → ℝ) : Prop :=
  IsMixedProfile S τ σ ∧
    ∀ i, ∀ s ∈ S (τ i), ∀ s' ∈ S (τ i), 0 < σ i s →
      ∑ e ∈ s, expect u σ (fun ω => c e (1 + othersLoadRV i e ω)) ≤
        ∑ e ∈ s', expect u σ (fun ω => c e (1 + othersLoadRV i e ω))

/-- The index set `{(t, s) : t ∈ T, s ∈ S_t}` of strategy flows. -/
abbrev FlowIdx (S : T → Finset (Finset E)) := {p : T × Finset E // p.2 ∈ S p.1}

/-- The random flow vector `(Y_{t,s})_{t ∈ T, s ∈ S_t}`. -/
def flowVec {N : ℕ} (S : T → Finset (Finset E)) (τ : Fin N → T) (ω : Outcome E N) :
    FlowIdx S → ℕ :=
  fun p => flowRV τ p.1.1 p.1.2 ω

/-! ### Sequences of games (14), auxiliary costs (17), condition (18), Lemma 1's constants -/

/-- `u = max_i u_i` (14b); `0` for a game without players. -/
noncomputable def maxU {N : ℕ} (u : Fin N → ℝ) : ℝ :=
  ⨆ i, u i

/-- Expected demand of type `t`: `d_t = ∑_{i : t_i = t} u_i` (p. 11, (14c)). -/
def demand {N : ℕ} (τ : Fin N → T) (u : Fin N → ℝ) (t : T) : ℝ :=
  ∑ i, if τ i = t then u i else 0

/-- Condition (14), pp. 15–16, on a sequence of Bernoulli games `Γ^n_B` with `N n` players, types
`τ n` and participation probabilities `u n`: `|N^n| → ∞` (14a), `u^n = max_i u^n_i → 0` (14b),
`d^n_t → d_t` for all `t` (14c). -/
def Condition14 (N : ℕ → ℕ) (τ : ∀ n, Fin (N n) → T) (u : ∀ n, Fin (N n) → ℝ)
    (d : T → ℝ) : Prop :=
  Tendsto N atTop atTop ∧ Tendsto (fun n => maxU (u n)) atTop (𝓝 0) ∧
    ∀ t, Tendsto (fun n => demand (τ n) (u n) t) atTop (𝓝 (d t))

/-- The moment part of (18): for every `e`, `E[|Δ²c_e(1 + V)|] ≤ ν` with `V ∼ Poisson(d_max)`,
the expectation being a convergent series. -/
def MomentBound (c : E → ℕ → ℝ) (ν dmax : ℝ) : Prop :=
  ∀ e, Summable (fun k : ℕ => |deltaPow 2 (c e) (1 + k)| * poissonPmf dmax k) ∧
    ∑' k : ℕ, |deltaPow 2 (c e) (1 + k)| * poissonPmf dmax k ≤ ν

/-- Condition (18), p. 18: `d_max > d_tot = ∑_t d_t` and `E[|Δ²c_e(1 + V)|] ≤ ν` for all `e`,
`V ∼ Poisson(d_max)`. -/
def Condition18 (c : E → ℕ → ℝ) (d : T → ℝ) (ν dmax : ℝ) : Prop :=
  ∑ t, d t < dmax ∧ MomentBound c ν dmax

/-- Auxiliary costs (17), p. 18: `c̆_e(x) = E[c_e(1 + X)]`, `X ∼ Poisson(x)`. -/
noncomputable def cBreve (c : E → ℕ → ℝ) (e : E) (x : ℝ) : ℝ :=
  poissonMean (fun k => c e (1 + k)) x

/-- `ζ = (e^{d_max} − 1)ν + max_{e ∈ E} (c_e(2) − c_e(1))`, (19), p. 18. -/
noncomputable def zeta (c : E → ℕ → ℝ) (ν dmax : ℝ) : ℝ :=
  (Real.exp dmax - 1) * ν + ⨆ e, (c e 2 - c e 1)

/-- `Λ(u) = (ν d_max / 2) · u e^u / (1 − u)² + u ζ`, (20), p. 18, as printed. -/
noncomputable def Lam (c : E → ℕ → ℝ) (ν dmax u : ℝ) : ℝ :=
  ν * dmax / 2 * (u * Real.exp u / (1 - u) ^ 2) + u * zeta c ν dmax

/-- The corrected constant `Λ̃(u) = (ν d_max e^{d_max} / 2) · u e^u / (1 − u)² + u ζ`: (20) with
`ν e^{d_max}` in place of `ν` in the first term (the printed (21) with `Λ` is false). -/
noncomputable def LamCorr (c : E → ℕ → ℝ) (ν dmax u : ℝ) : ℝ :=
  ν * dmax * Real.exp dmax / 2 * (u * Real.exp u / (1 - u) ^ 2) + u * zeta c ν dmax

end LargeCongestion.Poisson



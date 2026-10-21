-- Prove2me | Definitions.Def_RelationalReciprocity_Dynamics_Model
-- name    : RelationalReciprocity_Dynamics_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-20T09:16:44.323858+00:00
-- url     : https://prove2.me/theorems/01ad871b-5bcd-4b22-8d1f-4ef01c37057e
-- title:
--   §2 and §3.2.1, pp. 8–18 — finite-horizon relational contract with a reciprocal agent: bonus, per-period profit, (DE), first-best levels, optimal path
-- statement:
--   This file fixes the **reduced per-period problem** of Fahn's finite-horizon relational contract with a reciprocal agent (§3.2.1, p. 17), which the paper derives from its game in Lemma 2.
--
--   **Parameters and standing assumptions.** Output per unit of effort is $\theta>0$, the agent's reciprocity parameter is $\eta\ge 0$, the common discount factor is $\delta\in(0,1]$, and the relationship lasts $T$ periods with $1<T<\infty$ (§2, pp. 8–10). These four conditions form the predicate $\mathrm{Standing}$.
--
--   **Deviation effort and bonus.** Given an upfront wage $w\ge0$, an agent who responds only to the norm of reciprocity chooses $\tilde e=\sqrt{\eta w\theta}$ (p. 16). With effort costs $c(e)=e^3/3$, binding incentive constraints and $U_t=\tilde U_t$ give the bonus needed to implement effort $e$ at wage $w$ (p. 17):
--   $$
--   b(e,w)=\frac{e^3}{3}-\eta w\theta e+\frac23\big(\sqrt{\eta w\theta}\big)^3 .
--   $$
--   The principal's per-period profit is $\pi(e,w)=e\theta-b(e,w)-w$, and the agent's per-period utility is $u=w+b-e^3/3+\eta we\theta$ (pp. 10, 14).
--
--   **Period problem.** For a bound $K$ (in period $t$, $K=\delta\Pi_{t+1}$), a pair $(e,w)$ is *feasible* if $e\ge0$, $w\ge0$ and the dynamic enforcement constraint
--   $$
--   \frac{e^3}{3}-\eta w\theta e\le K-\frac23\big(\sqrt{\eta w\theta}\big)^3,\qquad\text{i.e. } b(e,w)\le K, \tag{DE}
--   $$
--   holds; it is *optimal* if it is feasible and no feasible pair has a larger profit. The *first-best* pairs maximize $\pi$ over $e,w\ge0$ without (DE) (p. 18), and (DE) *does not bind* at $K$ when some first-best pair satisfies it.
--
--   **Optimal path.** Paths $e_t,w_t,\Pi_t$ are indexed by periods. A path is *profit-maximizing* if $\Pi_{T+1}=0$ and, for every $1\le t\le T$, $(e_t,w_t)$ is optimal for the bound $\delta\Pi_{t+1}$ and $\Pi_t=\pi(e_t,w_t)+\delta\Pi_{t+1}$ (pp. 11, 17). The bonus paid in period $t$ is $b_t=b(e_t,w_t)$.
--
--   **Thresholds and KKT closed forms.** The file also names $\bar\eta=\sqrt{1/\theta^3}$, $\tilde\eta(\lambda)=\sqrt{1/(\theta^3(1+\lambda))}$, and, for a (DE) multiplier $\lambda$, the closed forms of the proof of Lemma 4 (p. 41): $w(\lambda)=\frac{(\eta^2\theta^3(1+\lambda)-1)^2}{4\eta^3\theta^3(1+\lambda)^2}$, $e(\lambda)=\frac{1+\eta^2\theta^3(1+\lambda)}{2\eta\theta(1+\lambda)}$ and, at a zero wage, $e_0(\lambda)=\sqrt{\theta/(1+\lambda)}$.
--
--   These objects are shared by every statement of the mission.
--
--   **Formalization Note.** The paper's game (histories, the norm function $\eta_t$, subgame norm-perfect equilibrium) is not formalized: the model is the reduced problem the paper states after Lemma 2. Non-negativity of the bonus is not a separate constraint because $b(e,w)\ge0$ for all $e,w\ge0$. In the last period the bound is $\delta\Pi_{T+1}=0$, so the period-$T$ problem is the spot-contract problem of §3.1. Paths are functions $\mathbb N\to\mathbb R$ of which only the indices $1,\dots,T+1$ carry meaning.
-- source:
--   Fahn, Reciprocity in Dynamic Employment Relationships, CRC TRR 190 Discussion Paper No. 198 (Nov. 8, 2019), pp. 8–18 (PDF 10–20), §2, §3.1, §3.2.1–3.2.2; thresholds and closed forms from the proofs of Lemmas 3–4, pp. 40–41 (PDF 42–43)

import Mathlib

namespace RelationalReciprocity.Dynamics

/-- Model parameters (Fahn 2019, §2, pp. 8–10): productivity `θ`, reciprocity parameter `η`,
discount factor `δ`, and the number of periods `T`. -/
structure Params where
  θ : ℝ
  η : ℝ
  δ : ℝ
  T : ℕ

/-- Standing assumptions of §2: `θ > 0` (p. 9), `η ≥ 0` (p. 10), `δ ∈ (0,1]` (p. 9),
`1 < T < ∞` (p. 8). -/
def Params.Standing (P : Params) : Prop :=
  0 < P.θ ∧ 0 ≤ P.η ∧ 0 < P.δ ∧ P.δ ≤ 1 ∧ 2 ≤ P.T

/-- Deviation effort `ẽ = √(ηwθ)` (p. 16): the effort of an agent who responds only to the norm
of reciprocity. -/
noncomputable def devEffort (P : Params) (w : ℝ) : ℝ := Real.sqrt (P.η * w * P.θ)

/-- Bonus under a binding (IC) constraint, `b(e,w) = e³/3 − ηwθe + (2/3)(√(ηwθ))³` (p. 17). -/
noncomputable def bonus (P : Params) (e w : ℝ) : ℝ :=
  e ^ 3 / 3 - P.η * w * P.θ * e + 2 / 3 * Real.sqrt (P.η * w * P.θ) ^ 3

/-- Per-period profit `π = eθ − b(e,w) − w` (p. 17). -/
noncomputable def profit (P : Params) (e w : ℝ) : ℝ := e * P.θ - bonus P e w - w

/-- Agent's per-period utility `u = w + b − e³/3 + ηweθ` (pp. 10, 14). -/
noncomputable def agentUtility (P : Params) (e w b : ℝ) : ℝ :=
  w + b - e ^ 3 / 3 + P.η * w * e * P.θ

/-- Feasible pairs `(e, w)` of the period problem with (DE) bound `K = δΠ_{t+1}` (p. 17):
`e ≥ 0`, `w ≥ 0` and `b(e,w) ≤ K`. -/
def Feasible (P : Params) (K : ℝ) : Set (ℝ × ℝ) :=
  {x | 0 ≤ x.1 ∧ 0 ≤ x.2 ∧ bonus P x.1 x.2 ≤ K}

/-- `(e, w)` solves the period problem with (DE) bound `K`: it is feasible and no feasible pair
has a larger per-period profit. -/
def IsOptimal (P : Params) (K e w : ℝ) : Prop :=
  (e, w) ∈ Feasible P K ∧ ∀ x ∈ Feasible P K, profit P x.1 x.2 ≤ profit P e w

/-- First-best levels (p. 18): `(e, w)` maximizes the per-period profit over `e, w ≥ 0`
without the (DE) constraint. -/
def IsFirstBest (P : Params) (e w : ℝ) : Prop :=
  0 ≤ e ∧ 0 ≤ w ∧ ∀ e' w' : ℝ, 0 ≤ e' → 0 ≤ w' → profit P e' w' ≤ profit P e w

/-- The (DE) constraint with bound `K` does not bind: some first-best pair satisfies it. -/
def DESlack (P : Params) (K : ℝ) : Prop :=
  ∃ e w : ℝ, IsFirstBest P e w ∧ bonus P e w ≤ K

/-- A profit-maximizing path (pp. 11, 17): `Π_{T+1} = 0` and, for every period `1 ≤ t ≤ T`,
`(e_t, w_t)` is optimal for the (DE) bound `δΠ_{t+1}` and `Π_t = π_t + δΠ_{t+1}`. Only the
indices `1, …, T + 1` carry meaning. -/
def IsOptimalPath (P : Params) (e w Pi : ℕ → ℝ) : Prop :=
  Pi (P.T + 1) = 0 ∧
  ∀ t : ℕ, 1 ≤ t → t ≤ P.T →
    IsOptimal P (P.δ * Pi (t + 1)) (e t) (w t) ∧
    Pi t = profit P (e t) (w t) + P.δ * Pi (t + 1)

/-- The reciprocity threshold `η̄ = √(1/θ³)` (proofs of Lemma 3 and Proposition 1). -/
noncomputable def etabar (P : Params) : ℝ := Real.sqrt (1 / P.θ ^ 3)

/-- The threshold `η̃ = √(1/(θ³(1+λ)))` for a (DE) multiplier `λ` (proof of Lemma 4). -/
noncomputable def etatilde (P : Params) (lam : ℝ) : ℝ :=
  Real.sqrt (1 / (P.θ ^ 3 * (1 + lam)))

/-- Interior KKT wage for a (DE) multiplier `λ` (proof of Lemma 4):
`w = (η²θ³(1+λ) − 1)² / (4η³θ³(1+λ)²)`. -/
noncomputable def kktWage (P : Params) (lam : ℝ) : ℝ :=
  (P.η ^ 2 * P.θ ^ 3 * (1 + lam) - 1) ^ 2 / (4 * P.η ^ 3 * P.θ ^ 3 * (1 + lam) ^ 2)

/-- Interior KKT effort for a (DE) multiplier `λ` (proof of Lemma 4):
`e = (1 + η²θ³(1+λ)) / (2ηθ(1+λ))`. -/
noncomputable def kktEffort (P : Params) (lam : ℝ) : ℝ :=
  (1 + P.η ^ 2 * P.θ ^ 3 * (1 + lam)) / (2 * P.η * P.θ * (1 + lam))

/-- KKT effort at a zero wage for a (DE) multiplier `λ` (proof of Lemma 4): `e = √(θ/(1+λ))`. -/
noncomputable def kktEffort0 (P : Params) (lam : ℝ) : ℝ := Real.sqrt (P.θ / (1 + lam))

end RelationalReciprocity.Dynamics



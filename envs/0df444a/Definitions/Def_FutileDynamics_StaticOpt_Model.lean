-- Prove2me | Definitions.Def_FutileDynamics_StaticOpt_Model
-- name    : FutileDynamics_StaticOpt_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-19T06:49:39.267069+00:00
-- url     : https://prove2.me/theorems/fa720d67-ec16-405a-8c40-d794dcda490f
-- title:
--   §2, §3.1, Assumptions 1–2, (E-8), pp. 6–11, ec 21 — dynamic mechanisms, IC, OPT, regret, direct static mechanisms, ū
-- statement:
--   Building on the separate game definition, this file models the repeated interaction of Balseiro, Kim and Russo: a principal and an agent interact over $T$ rounds; the agent's shocks are i.i.d. from a distribution $F$ that only the agent knows.
--
--   1. **Imported game** (§2). Shocks $\Theta$, outcomes $\Omega$ with a no-interaction outcome $\emptyset$, principal utility $u:\Theta\times\Omega\to\mathbb R$ and agent utility $v:\Theta\times\Omega\to\mathbb R$, with $u(\theta,\emptyset)=v(\theta,\emptyset)=0$.
--
--   2. **Dynamic mechanism** $A=(\{\mathcal M_t\}_{0:T},\{\pi_t\}_{1:T},\{\sigma_t\}_{0:T})$. $\mathcal M_0$ contains the report QUIT. In round $t\ge1$ the outcome is $\omega_t=\pi_t(m_t,h_t,z_t)$ with public history $h_t=(m_{0:t-1},\omega_{1:t-1})$ and a private uniform $z_t$. The recommended strategy is $\sigma$: $m_0=\sigma_0(F,y_0)$ and $m_t=\sigma_t(\theta_t,h_t^+,y_t)$ with $h_t^+=(F,\theta_{1:t-1},m_{0:t-1},\omega_{1:t-1})$ and an agent uniform $y_t$. After QUIT every outcome is $\emptyset$.
--
--   3. **Utilities and benchmarks.** For an agent strategy $\tilde\sigma$,
--   $$\mathrm{PrincipalUtility}(A,\tilde\sigma,F,T)=\mathbb E\Big[\sum_{t=1}^T u(\theta_t,\omega_t)\Big],\qquad \mathrm{AgentUtility}(A,\tilde\sigma,F,T)=\mathbb E\Big[\sum_{t=1}^T v(\theta_t,\omega_t)\Big],$$
--   the expectation over $\theta_1,\dots,\theta_T\sim F$ i.i.d. and all uniforms. $A$ is **incentive compatible** if $\mathrm{AgentUtility}(A,\sigma,F,T)\ge\mathrm{AgentUtility}(A,\tilde\sigma,F,T)$ for every probability distribution $F$ on $\Theta$ and every feasible $\tilde\sigma$. With $\mathcal A$ the set of IC mechanisms: $\mathrm{OPT}(F,T)=\sup_{A\in\mathcal A}\mathrm{PrincipalUtility}(A,F,T)$, $\mathrm{Regret}(A,F,T)=\mathrm{OPT}(F,T)-\mathrm{PrincipalUtility}(A,F,T)$, $\mathrm{Regret}(A,T)=\sup_{F\in\mathcal F}\mathrm{Regret}(A,F,T)$ and $\mathrm{Regret}(T)=\inf_{A\in\mathcal A}\mathrm{Regret}(A,T)$.
--
--   4. **Direct static mechanisms** (§3.1). A direct rule $\tilde\pi:(\Theta\cup\{\mathrm{PASS}\})\times[0,1]\to\Omega$ with $\tilde\pi(\mathrm{PASS},z)=\emptyset$. Its repetition $S^{\times T}$ has $\mathcal M_0=\{\mathrm{CONTINUE},\mathrm{QUIT}\}$, $\mathcal M_t=\Theta\cup\{\mathrm{PASS}\}$, $\pi_t(m_t,h_t,z_t)=\tilde\pi(m_t,z_t)$ and the truthful strategy $\sigma^{TR}$ (CONTINUE, then report $\theta_t$). $S\in\mathcal S^{\times1}$ means the single-round mechanism is IC. The single-round value is $\inf_{S\in\mathcal S^{\times1}}\sup_{\theta\in\Theta}\mathrm{Regret}(S,\delta_\theta,1)$.
--
--   5. **Assumptions** (p. 11). Assumption 1: $\delta_\theta\in\mathcal F$ for every $\theta$. Assumption 2: $\mathrm{OPT}(F,T)\le\mathbb E_{\theta\sim F}[\mathrm{OPT}(\delta_\theta,T)]$ for all $F\in\mathcal F$.
--
--   6. **First-best benchmark** (E-8), corrected:
--   $$\bar u(F)=\sup_{\tilde\pi}\int_\Theta\int_0^1 u(\theta,\tilde\pi(\theta,z))\,dz\,dF(\theta)\quad\text{s.t.}\quad\int_\Theta\int_0^1 v(\theta,\tilde\pi(\theta,z))\,dz\,dF(\theta)\ge0,$$
--   over all direct rules, without incentive compatibility.
--
--   These objects carry every statement of the mission.
--
--   **Formalization Note** Conventions not on the page, all disclosed. (i) $u$ and $v$ are jointly measurable and bounded, so every expectation is a finite Bochner integral. (ii) Every report space is a standard Borel space, so the designer cannot shrink the set of feasible (measurable) deviations by choosing an exotic σ-algebra. Decision rules are jointly measurable. A feasible strategy is jointly measurable in all its arguments, $F$ included (Giry σ-algebra); this also applies to the recommended strategy. (iii) Rounds $t=1,\dots,T$ are indexed by $k=t-1\in\mathrm{Fin}\,T$; the report space of round $k+1$ is `M k`. A mechanism is given for every round, and only rounds $1,\dots,T$ are used at horizon $T$. (iv) Uniforms live on `unitInterval` with Lebesgue measure. The round report space $\Theta\cup\{\mathrm{PASS}\}$ is encoded as $\Theta\times\mathrm{Bool}$: $(\theta,\mathrm{true})$ reports $\theta$, and every $(\theta,\mathrm{false})$ is PASS, which the rule must map to $\emptyset$. CONTINUE/QUIT is `true`/`false`. (v) The page defines $\bar u$ with $S\in\mathcal S^{\times1}$, but p. 22 and the proof of Proposition 13 drop IC, and the Lean $\bar u$ follows them. (vi) Every real sup or inf is over a nonempty bounded set: the always-$\emptyset$ mechanism is IC, and $|u|,|v|\le B$.
-- source:
--   Balseiro, Kim & Russo, On the futility of dynamics in robust mechanism design, SSRN 3449698 (version of October 5, 2020), pp. 5–11, ec 21, §2, §3.1, Assumptions 1–2, (E-8)

import Mathlib
import Definitions.Def_FutileDynamics_StaticOpt_Game

namespace FutileDynamics.StaticOpt

open MeasureTheory

/-- An agent strategy `σ = {σ_t}_{0:T}` over report spaces `M₀` (Round 0) and `M k` (the page's `M_{k+1}`,
Round `k + 1`), p. 7.
* `s0 F y₀ = σ₀(F, y₀) ∈ M₀`: the initial augmented history is `h⁺₀ = F`;
* `s k F θ θs m₀ ms ωs y = σ_{k+1}(θ_{k+1}, h⁺_{k+1}, y_{k+1})` with
  `h⁺_{k+1} = (F, θ_{1:k}, m_{0:k}, ω_{1:k})`: `θ` is the current shock, `θs` the past shocks, `m₀` the Round 0
  report, `ms` the reports of rounds `1, …, k`, `ωs` the outcomes of rounds `1, …, k`, `y` the agent's private
  uniform of this round. -/
structure Strategy (Θ Ω M0 : Type) [MeasurableSpace Θ] (M : ℕ → Type) where
  s0 : Measure Θ → unitInterval → M0
  s : (k : ℕ) → Measure Θ → Θ → (Fin k → Θ) → M0 → ((j : Fin k) → M j) → (Fin k → Ω) →
    unitInterval → M k

/-- A feasible agent strategy (p. 8): every `σ_t` is jointly measurable in all its arguments, the
distribution `F` (with the Giry σ-algebra on `Measure Θ`) included. Disclosed convention. -/
def Strategy.Feasible {Θ Ω M0 : Type} {M : ℕ → Type} [MeasurableSpace Θ] [MeasurableSpace Ω]
    [MeasurableSpace M0] [∀ k, MeasurableSpace (M k)] (σ : Strategy Θ Ω M0 M) : Prop :=
  Measurable (fun p : Measure Θ × unitInterval => σ.s0 p.1 p.2) ∧
  ∀ k : ℕ, Measurable (fun p : Measure Θ × Θ × (Fin k → Θ) × M0 × ((j : Fin k) → M j) × (Fin k → Ω) ×
      unitInterval => σ.s k p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2.1 p.2.2.2.2.2.1 p.2.2.2.2.2.2)

/-- A dynamic mechanism `A = ({M_t}_{0:T}, {π_t}_{1:T}, {σ_t}_{0:T})` (pp. 6–8).
* `M0` is the Round 0 report space, containing the report `quit` (QUIT, p. 8);
* `M k` is the report space of Round `k + 1` (the page's `M_{k+1}`);
* `rule k m m₀ ms ωs z = π_{k+1}(m_{k+1}, h_{k+1}, z_{k+1})` with public history
  `h_{k+1} = (m_{0:k}, ω_{1:k})` and the principal's private uniform `z_{k+1}`;
* `recom` is the recommended agent strategy `σ`.
Disclosed conventions: every report space is a standard Borel space (so the designer cannot shrink the set
of measurable, i.e. feasible, deviations by an exotic σ-algebra), and every decision rule is jointly
measurable. A Lean mechanism is defined for every round; played over a horizon `T`, only rounds `1, …, T` are ever used,
so it is exactly a `T`-round mechanism of the page. -/
structure DynMech (Θ Ω : Type) [MeasurableSpace Θ] [MeasurableSpace Ω] where
  M0 : Type
  [measM0 : MeasurableSpace M0]
  [sbM0 : StandardBorelSpace M0]
  quit : M0
  M : ℕ → Type
  [measM : ∀ k, MeasurableSpace (M k)]
  [sbM : ∀ k, StandardBorelSpace (M k)]
  rule : (k : ℕ) → M k → M0 → ((j : Fin k) → M j) → (Fin k → Ω) → unitInterval → Ω
  rule_meas : ∀ k : ℕ, Measurable (fun p : M k × M0 × ((j : Fin k) → M j) × (Fin k → Ω) × unitInterval =>
    rule k p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2)
  recom : Strategy Θ Ω M0 M

attribute [instance] DynMech.measM0 DynMech.measM DynMech.sbM0 DynMech.sbM

/-- The exogenous randomness of a `T`-round play: the shocks `θ_1, …, θ_T` (`Fin T → Θ`), the agent's
uniforms `y_0` and `y_1, …, y_T`, and the principal's uniforms `z_1, …, z_T`. Index `k : Fin T` is round
`k + 1`. -/
abbrev Noise (Θ : Type) (T : ℕ) :=
  (Fin T → Θ) × unitInterval × (Fin T → unitInterval) × (Fin T → unitInterval)

/-- The law of the exogenous randomness: shocks i.i.d. `F`, all uniforms i.i.d. uniform on `[0, 1]`, all
mutually independent. -/
noncomputable def noiseLaw {Θ : Type} [MeasurableSpace Θ] (F : Measure Θ) (T : ℕ) : Measure (Noise Θ T) :=
  (Measure.pi fun _ : Fin T => F).prod ((volume : Measure unitInterval).prod
    ((Measure.pi fun _ : Fin T => (volume : Measure unitInterval)).prod
      (Measure.pi fun _ : Fin T => (volume : Measure unitInterval))))

open Classical in
/-- The play of mechanism `A` against agent strategy `σ` when the agent's distribution is `F`, over horizon
`T`, for a realization `ξ` of the exogenous randomness: `hist … k hk` is the pair (reports of rounds
`1, …, k`, outcomes of rounds `1, …, k`). The Round 0 report is `m₀ = σ₀(F, y₀)`. In round `k + 1` the agent
reports `m_{k+1} = σ_{k+1}(θ_{k+1}, (F, θ_{1:k}, m_{0:k}, ω_{1:k}), y_{k+1})` and the outcome is
`ω_{k+1} = π_{k+1}(m_{k+1}, (m_{0:k}, ω_{1:k}), z_{k+1})`, except that after `m₀ = QUIT` every outcome is the
no-interaction outcome `∅` (p. 8). -/
noncomputable def hist {Θ Ω : Type} [MeasurableSpace Θ] [MeasurableSpace Ω] (G : Game Θ Ω)
    (A : DynMech Θ Ω) (σ : Strategy Θ Ω A.M0 A.M) (F : Measure Θ) (T : ℕ) (ξ : Noise Θ T) :
    (k : ℕ) → k ≤ T → ((j : Fin k) → A.M j) × (Fin k → Ω)
  | 0, _ => (fun j => j.elim0, fun j => j.elim0)
  | k + 1, hk =>
    let p := hist G A σ F T ξ k (Nat.le_of_succ_le hk)
    let kk : Fin T := ⟨k, hk⟩
    let m0 : A.M0 := σ.s0 F ξ.2.1
    let m : A.M k := σ.s k F (ξ.1 kk) (fun j => ξ.1 ⟨j, by omega⟩) m0 p.1 p.2 (ξ.2.2.1 kk)
    let ω : Ω := if m0 = A.quit then G.noInt else A.rule k m m0 p.1 p.2 (ξ.2.2.2 kk)
    (Fin.snoc (α := fun i : Fin (k + 1) => A.M i) p.1 m, Fin.snoc p.2 ω)

/-- The outcome `ω_{k+1}` of round `k + 1` (for `k : Fin T`) of the play. -/
noncomputable def outcome {Θ Ω : Type} [MeasurableSpace Θ] [MeasurableSpace Ω] (G : Game Θ Ω)
    (A : DynMech Θ Ω) (σ : Strategy Θ Ω A.M0 A.M) (F : Measure Θ) (T : ℕ) (ξ : Noise Θ T) (k : Fin T) : Ω :=
  (hist G A σ F T ξ T le_rfl).2 k

/-- `PrincipalUtility(A, σ̃, F, T) = E_{π,σ̃}[∑_{t=1}^T u(θ_t, ω_t)]` (p. 7). -/
noncomputable def principalUtility {Θ Ω : Type} [MeasurableSpace Θ] [MeasurableSpace Ω] (G : Game Θ Ω)
    (A : DynMech Θ Ω) (σ : Strategy Θ Ω A.M0 A.M) (F : Measure Θ) (T : ℕ) : ℝ :=
  ∫ ξ, ∑ k : Fin T, G.u (ξ.1 k) (outcome G A σ F T ξ k) ∂(noiseLaw F T)

/-- `AgentUtility(A, σ̃, F, T) = E_{π,σ̃}[∑_{t=1}^T v(θ_t, ω_t)]` (p. 7). -/
noncomputable def agentUtility {Θ Ω : Type} [MeasurableSpace Θ] [MeasurableSpace Ω] (G : Game Θ Ω)
    (A : DynMech Θ Ω) (σ : Strategy Θ Ω A.M0 A.M) (F : Measure Θ) (T : ℕ) : ℝ :=
  ∫ ξ, ∑ k : Fin T, G.v (ξ.1 k) (outcome G A σ F T ξ k) ∂(noiseLaw F T)

/-- The per-round expected utilities `V_t = E[v(θ_t, ω_t)]` and `U_t = E[u(θ_t, ω_t)]` of round `k + 1`
(p. ec 9). -/
noncomputable def roundAgentUtility {Θ Ω : Type} [MeasurableSpace Θ] [MeasurableSpace Ω] (G : Game Θ Ω)
    (A : DynMech Θ Ω) (σ : Strategy Θ Ω A.M0 A.M) (F : Measure Θ) (T : ℕ) (k : Fin T) : ℝ :=
  ∫ ξ, G.v (ξ.1 k) (outcome G A σ F T ξ k) ∂(noiseLaw F T)

/-- See `roundAgentUtility`: the per-round expected principal utility `U_t`. -/
noncomputable def roundPrincipalUtility {Θ Ω : Type} [MeasurableSpace Θ] [MeasurableSpace Ω]
    (G : Game Θ Ω) (A : DynMech Θ Ω) (σ : Strategy Θ Ω A.M0 A.M) (F : Measure Θ) (T : ℕ) (k : Fin T) : ℝ :=
  ∫ ξ, G.u (ξ.1 k) (outcome G A σ F T ξ k) ∂(noiseLaw F T)

/-- Incentive compatibility (p. 8) over horizon `T`: the recommended strategy is feasible and, for **every**
probability distribution `F` on `Θ` and every feasible agent strategy `σ̃`,
`AgentUtility(A, σ, F, T) ≥ AgentUtility(A, σ̃, F, T)`. Since QUIT is a feasible deviation this contains
ex-ante individual rationality. -/
def IsIC {Θ Ω : Type} [MeasurableSpace Θ] [MeasurableSpace Ω] (G : Game Θ Ω) (A : DynMech Θ Ω) (T : ℕ) :
    Prop :=
  A.recom.Feasible ∧ ∀ F : Measure Θ, IsProbabilityMeasure F → ∀ σ' : Strategy Θ Ω A.M0 A.M, σ'.Feasible →
    agentUtility G A σ' F T ≤ agentUtility G A A.recom F T

/-- `OPT(F, T) = sup_{A ∈ 𝒜} PrincipalUtility(A, F, T)` (p. 8), `𝒜` the set of all incentive compatible
dynamic mechanisms (every report-space family). The set is nonempty (the mechanism that always outputs `∅`
is IC) and bounded above by `T·B`. -/
noncomputable def OPT {Θ Ω : Type} [MeasurableSpace Θ] [MeasurableSpace Ω] (G : Game Θ Ω) (F : Measure Θ)
    (T : ℕ) : ℝ :=
  sSup {r : ℝ | ∃ A : DynMech Θ Ω, IsIC G A T ∧ r = principalUtility G A A.recom F T}

/-- `Regret(A, F, T) = OPT(F, T) − PrincipalUtility(A, F, T)` (p. 8), the agent following the recommended
strategy. -/
noncomputable def regret {Θ Ω : Type} [MeasurableSpace Θ] [MeasurableSpace Ω] (G : Game Θ Ω)
    (A : DynMech Θ Ω) (F : Measure Θ) (T : ℕ) : ℝ :=
  OPT G F T - principalUtility G A A.recom F T

/-- The worst-case regret `Regret(A, T) = sup_{F ∈ 𝓕} Regret(A, F, T)` (p. 9). Bounded by `2TB`. -/
noncomputable def worstRegret {Θ Ω : Type} [MeasurableSpace Θ] [MeasurableSpace Ω] (G : Game Θ Ω)
    (A : DynMech Θ Ω) (𝓕 : Set (Measure Θ)) (T : ℕ) : ℝ :=
  sSup ((fun F => regret G A F T) '' 𝓕)

/-- The optimal minimax regret `Regret(T) = inf_{A ∈ 𝒜} Regret(A, T)` (p. 9). -/
noncomputable def minimaxRegret {Θ Ω : Type} [MeasurableSpace Θ] [MeasurableSpace Ω] (G : Game Θ Ω)
    (𝓕 : Set (Measure Θ)) (T : ℕ) : ℝ :=
  sInf {r : ℝ | ∃ A : DynMech Θ Ω, IsIC G A T ∧ r = worstRegret G A 𝓕 T}

/-- A single-round direct decision rule `π̃ : M₁ × [0, 1] → Ω` (§3.1, item 4) with `M₁ = Θ ∪ {PASS}`
(item 1), encoded as `Θ × Bool`: `(θ, true)` reports `θ` and every `(θ, false)` is PASS. The rule honours
PASS (item 2: `π̃(PASS, z) = ∅`), so all PASS reports act identically. Disclosed conventions: `π̃` is jointly
measurable; the flag encoding makes the report space standard Borel when `Θ` is. -/
def DirectRule {Θ Ω : Type} [MeasurableSpace Θ] [MeasurableSpace Ω] (G : Game Θ Ω) : Type :=
  {d : Θ × Bool → unitInterval → Ω // Measurable (Function.uncurry d) ∧ ∀ θ z, d (θ, false) z = G.noInt}

/-- The direct static mechanism that repeats the direct rule `d` in every round (§3.1): Round 0 reports
`M₀ = {CONTINUE, QUIT}` encoded as `Bool` (`true` = CONTINUE, `false` = QUIT), round reports
`M_t = Θ ∪ {PASS}`, decision rule `π_t(m_t, h_t, z_t) = π̃(m_t, z_t)` (no dependence on the history or the
round), and the truthful recommended strategy `σ^TR`: CONTINUE in Round 0, then report the current shock.
Played over horizon `T` it is the page's `S^{×T}`; over horizon `1` it is the single-round mechanism `S`. -/
noncomputable def repeatDirect {Θ Ω : Type} [MeasurableSpace Θ] [MeasurableSpace Ω] [StandardBorelSpace Θ]
    (G : Game Θ Ω) (d : DirectRule G) : DynMech Θ Ω where
  M0 := Bool
  quit := false
  M := fun _ => Θ × Bool
  rule := fun _ m _ _ _ z => d.1 m z
  rule_meas := fun _ => d.2.1.comp (measurable_fst.prodMk measurable_snd.snd.snd.snd)
  recom := { s0 := fun _ _ => true, s := fun _ _ θ _ _ _ _ _ => (θ, true) }

/-- `S ∈ S^{×1}` (§3.1): the single-round direct mechanism with rule `d` is incentive compatible (in the
dynamic sense of p. 8, at horizon `T = 1`). -/
def SingleRoundIC {Θ Ω : Type} [MeasurableSpace Θ] [MeasurableSpace Ω] [StandardBorelSpace Θ]
    (G : Game Θ Ω) (d : DirectRule G) : Prop :=
  IsIC G (repeatDirect G d) 1

/-- `inf_{S ∈ S^{×1}} sup_{θ ∈ Θ} Regret(S, δ_θ, 1)`, the single-round minimax regret over point masses
(Theorem 1, p. 11). -/
noncomputable def singleRoundValue {Θ Ω : Type} [MeasurableSpace Θ] [MeasurableSpace Ω] [StandardBorelSpace Θ]
    (G : Game Θ Ω) : ℝ :=
  sInf ((fun d : DirectRule G => ⨆ θ : Θ, regret G (repeatDirect G d) (Measure.dirac θ) 1) ''
    {d | SingleRoundIC G d})

/-- Assumption 1 (p. 11): every point mass `δ_θ` belongs to `𝓕`. -/
def Assumption1 {Θ : Type} [MeasurableSpace Θ] (𝓕 : Set (Measure Θ)) : Prop :=
  ∀ θ : Θ, Measure.dirac θ ∈ 𝓕

/-- Assumption 2 (p. 11): for all `F ∈ 𝓕`, `OPT(F, T) ≤ E_{θ∼F}[OPT(δ_θ, T)]`. -/
def Assumption2 {Θ Ω : Type} [MeasurableSpace Θ] [MeasurableSpace Ω] (G : Game Θ Ω)
    (𝓕 : Set (Measure Θ)) (T : ℕ) : Prop :=
  ∀ F ∈ 𝓕, OPT G F T ≤ ∫ θ, OPT G (Measure.dirac θ) T ∂F

/-- The first-best benchmark `ū(F)` of (E-8) (p. ec 21), **corrected**: the supremum of
`∫_Θ ∫ u(θ, π̃(θ, z)) dz dF(θ)` over **all** single-round direct rules `π̃` subject to the ex-ante constraint
`∫_Θ ∫ v(θ, π̃(θ, z)) dz dF(θ) ≥ 0`, without incentive compatibility. The page writes the supremum over
`S ∈ S^{×1}` (IC mechanisms), but p. 22 and the proof of Proposition 13 (pp. ec 23–24) drop IC. -/
noncomputable def ubar {Θ Ω : Type} [MeasurableSpace Θ] [MeasurableSpace Ω] (G : Game Θ Ω)
    (F : Measure Θ) : ℝ :=
  sSup {r : ℝ | ∃ d : DirectRule G,
    0 ≤ ∫ θ, ∫ z, G.v θ (d.1 (θ, true) z) ∂(volume : Measure unitInterval) ∂F ∧
    r = ∫ θ, ∫ z, G.u θ (d.1 (θ, true) z) ∂(volume : Measure unitInterval) ∂F}

end FutileDynamics.StaticOpt



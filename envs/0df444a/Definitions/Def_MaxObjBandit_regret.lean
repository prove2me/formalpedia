-- Prove2me | Definitions.Def_MaxObjBandit_regret
-- name    : MaxObjBandit_regret
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T11:33:54.554931+00:00
-- url     : https://prove2.me/theorems/6ba7321f-7259-4b39-aa0b-808ef034c707
-- title:
--   Policies, the max objective $\mathcal R_T(\pi,\boldsymbol\nu)$ (1) and the regret $\mathrm{Reg}_T$
-- statement:
--   A **policy** $\pi=(\pi_1,\pi_2,\dots)$ maps the history $H_t=(I_1,X_1,\dots,I_t,X_t)$ of arms played and rewards observed to the arm $I_{t+1}$ played next. Run on a reward table, the policy plays $I_t$ and observes $X_t=U^{I_t}_{n^{I_t}_t}$, where $n^i_t$ is the number of pulls of arm $i$ until and including time $t$. The **cumulative reward** of arm $i$ is $\bar U^i_t=\sum_{n=1}^{n^i_t}U^i_n$, and the **max objective** (1) is
--   $$
--   \mathcal R_T(\pi,\boldsymbol\nu)=\mathbb E_{\boldsymbol\nu}\big[\max(\bar U^1_T,\dots,\bar U^K_T)\big].
--   $$
--   $\Pi_T$ is the set of policies whose decision rules are measurable, and the **regret** of $\pi$ is
--   $$
--   \mathrm{Reg}_T(\pi,\boldsymbol\nu)=\sup_{\pi'\in\Pi_T}\mathcal R_T(\pi',\boldsymbol\nu)-\mathcal R_T(\pi,\boldsymbol\nu).
--   $$
--
--   This is the performance measure of the whole mission; Proposition 1 identifies the supremum as $\mu_1T$.
--
--   **Formalization Note** Time is 0-based in Lean: `π t` sees the history of the first `t` times. The maximum over arms is `⨆ i` and the expectation is the Bochner integral against the reward-table law. The supremum over $\Pi_T$ is a real `⨆`, which is meaningful because the objective is bounded above by $T$ (rewards lie in $[0,1]$ almost surely). Policies are deterministic, as in the paper.
-- source:
--   Ozbay, Kamble, Maximal Objectives in the Multi-armed Bandit with Applications, arXiv:2006.06853v6, §2, pp.15–16, Eq. (1) and the definition of Reg_T, p.16

import Mathlib
import Definitions.Def_MaxObjBandit_BanditInstance

open MeasureTheory ProbabilityTheory

namespace MaxObjBandit

/-- A history of length `t`: the arms played and rewards observed at the first `t` times,
`H_t = (I₁, X₁, …, I_t, X_t)` (arXiv:2006.06853v6, §2, pp.15–16). -/
abbrev History (K t : ℕ) := Fin t → Fin K × ℝ

/-- A (deterministic) policy: `π t` maps the history of the first `t` times to the arm played at
time `t + 1` (arXiv:2006.06853v6, §2, p.16: "A policy π of the decision-maker is a sequence of
mappings (π₁, π₂, …, π_T), where π_t maps every possible history H_t to an arm I_t").

**Formalization Note** Time is `0`-based: `π t` chooses the paper's `I_{t+1}`. A policy is defined
at every time; only the first `T` times enter the horizon-`T` quantities below. -/
def Policy (K : ℕ) := (t : ℕ) → History K t → Fin K

/-- The policies of `Π_T`: every decision rule is measurable, so that `I_t`, `X_t` and `nⁱ_t` are
random variables (arXiv:2006.06853v6, §2, p.16: "Once a policy π is fixed, then for all
t = 1, …, T, I_t, X_t, and nⁱ_t … become well-defined random variables").

**Formalization Note** The history space carries the product σ-algebra (discrete on `Fin K`, Borel
on `ℝ`). -/
def IsMeasurablePolicy {K : ℕ} (π : Policy K) : Prop := ∀ t, Measurable (π t)

/-- The number of times arm `i` occurs in the history `h`. -/
def armCount {K t : ℕ} (h : History K t) (i : Fin K) : ℕ :=
  (Finset.univ.filter fun s : Fin t => (h s).1 = i).card

/-- The run of policy `π` on the reward table `ω`: `history π ω t` is the history of the first `t`
times. At time `t + 1` the arm `a = π t (history π ω t)` is played and the reward is
`ω a n = Uᵃ_{n+1}`, where `n` is the number of earlier pulls of `a`, i.e. `X_t = U^{I_t}_{n^{I_t}_t}`
(arXiv:2006.06853v6, §2, p.16). -/
def history {K : ℕ} (π : Policy K) (ω : RewardTable K) : (t : ℕ) → History K t
  | 0 => Fin.elim0
  | t + 1 => fun s =>
      if hs : (s : ℕ) < t then history π ω t ⟨s, hs⟩
      else (π t (history π ω t), ω (π t (history π ω t)) (armCount (history π ω t) (π t (history π ω t))))

/-- `nⁱ_t`, the number of times arm `i` is played until and including time `t`
(arXiv:2006.06853v6, §2, p.16). -/
def pullCount {K : ℕ} (π : Policy K) (ω : RewardTable K) (t : ℕ) (i : Fin K) : ℕ :=
  armCount (history π ω t) i

/-- The cumulative reward `Ūⁱ_t = ∑_{n=1}^{nⁱ_t} Uⁱₙ` of arm `i` until time `t`
(arXiv:2006.06853v6, §2, p.16). -/
def cumReward {K : ℕ} (π : Policy K) (ω : RewardTable K) (t : ℕ) (i : Fin K) : ℝ :=
  ∑ n ∈ Finset.range (pullCount π ω t i), ω i n

/-- The objective `R_T(π, ν) = E_ν[max{Ū¹_T, …, Ū^K_T}]` of (1) (arXiv:2006.06853v6, §2, Eq. (1),
p.16).

**Formalization Note** The maximum over the finite set of arms is `⨆ i`, which is the maximum
when `K ≥ 1`. The expectation is the Bochner integral against the reward-table law; the integrand is
bounded by `T` on the almost-sure event that every reward lies in `[0,1]`. -/
noncomputable def objective {K : ℕ} (ν : BanditInstance K) (T : ℕ) (π : Policy K) : ℝ :=
  ∫ ω, (⨆ i, cumReward π ω T i) ∂ν.tableMeasure

/-- `sup_{π ∈ Π_T} R_T(π, ν)`, the best objective value over all policies (arXiv:2006.06853v6,
§2, p.16).

**Formalization Note** The supremum is over `IsMeasurablePolicy` policies. A real `⨆` of a set
that is not bounded above would be `0`; the set is bounded above by `T` (rewards lie in `[0,1]`
almost surely), and Proposition 1 identifies the supremum as `µ₁T`. -/
noncomputable def optimum {K : ℕ} (ν : BanditInstance K) (T : ℕ) : ℝ :=
  ⨆ π : {π : Policy K // IsMeasurablePolicy π}, objective ν T π.1

/-- The regret `Reg_T(π, ν) = sup_{π' ∈ Π_T} R_T(π', ν) − R_T(π, ν)` (arXiv:2006.06853v6, §2,
p.16). -/
noncomputable def regret {K : ℕ} (ν : BanditInstance K) (T : ℕ) (π : Policy K) : ℝ :=
  optimum ν T - objective ν T π

end MaxObjBandit



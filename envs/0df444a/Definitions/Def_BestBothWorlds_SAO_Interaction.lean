-- Prove2me | Definitions.Def_BestBothWorlds_SAO_Interaction
-- name    : BestBothWorlds_SAO_Interaction
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-04T19:58:18.778206+00:00
-- url     : https://prove2.me/theorems/d22eaccc-f3b5-4234-8e6f-c84114bbd9f6
-- title:
--   K-armed bandit interaction with an adaptive adversary or stochastic rewards (Fig. 1, §2)
-- statement:
--   This file fixes the model of Bubeck and Slivkins (Fig. 1 and §2): a $K$-armed bandit game over $n$ rounds in which rewards are either chosen by an adaptive adversary or drawn from fixed distributions, together with the regrets and the estimators the paper's analysis uses.
--
--   1. **Algorithms.** A randomized algorithm $\pi$ maps the observed history $(I_1,g_{I_1,1},\dots,I_{t-1},g_{I_{t-1},t-1})$ to a vector $p_t=(p_{1,t},\dots,p_{K,t})$, and the arm $I_t$ is drawn from $p_t$.
--   2. **Adaptive adversary.** The reward vector $g_t=(g_{1,t},\dots,g_{K,t})$ of round $t$ is a function of the arms $I_1,\dots,I_{t-1}$ played before round $t$. Because it is chosen simultaneously with $I_t$, it cannot depend on $I_t$. It is *bounded* when all rewards lie in $[0,1]$.
--   3. **Law of the arm path.** For a fixed adversary, the probability of an event $E$ on arm paths $I=(I_1,\dots,I_n)$ is
--   $$\Pr[E]=\sum_{I\in E}\ \prod_{t=1}^n p_{I_t,t},$$
--   where $p_t$ is computed from the history along $I$.
--   4. **Stochastic model.** There are probability distributions $\nu_1,\dots,\nu_K$ and all rewards $g_{i,t}$ are independent with $g_{i,t}\sim\nu_i$. The reward table is drawn from the product measure, the algorithm plays against the drawn table, and $\Pr[E]$ is the integral over tables of the path probability above. The mean of arm $i$ is $\mu_i=\int x\,d\nu_i(x)$, its gap is $\Delta_i=\max_j\mu_j-\mu_i$, and the minimal gap is $\Delta=\min_{i:\Delta_i>0}\Delta_i$.
--   5. **Regrets.** The regret in the adversarial model is $R_n=\max_i\sum_{t=1}^n g_{i,t}-\sum_{t=1}^n g_{I_t,t}$, computed with the rewards the adversary produces along the path. The pseudo-regret in the stochastic model is $\overline R_n=\sum_{t=1}^n(\max_i\mu_i-\mu_{I_t})$. The regret over the rounds $\tau+1,\dots,n$ alone is $\max_i\sum_{t=\tau+1}^n g_{i,t}-\sum_{t=\tau+1}^n g_{I_t,t}$.
--   6. **Estimators (§2).** For arm $i$ and time $t$: $G_{i,t}=\sum_{s\le t}g_{i,s}$; $\widetilde G_{i,t}=\sum_{s\le t}g_{i,s}\mathbb 1_{\{I_s=i\}}/p_{i,s}$; $\widehat G_{i,t}=\sum_{s\le t}g_{i,s}\mathbb 1_{\{I_s=i\}}$; $T_i(t)=\sum_{s\le t}\mathbb 1_{\{I_s=i\}}$. The averages are $H_{i,t}=G_{i,t}/t$, $\widetilde H_{i,t}=\widetilde G_{i,t}/t$ and $\widehat H_{i,t}=\widehat G_{i,t}/T_i(t)$.
--
--   These objects are shared by every statement of the mission.
--
--   **Formalization Note** Arms are `Fin K`. An arm path is `I : Fin n → Fin K`, where `I r` is the arm of round $r+1$. A deterministic adaptive adversary is a function from the list of earlier arms to a reward vector. Randomized adversaries are mixtures of deterministic ones, so a high-probability bound that holds for every deterministic adversary also holds for randomized ones. In the stochastic model the reward table `ω : Fin n → Fin K → ℝ` (with `ω r i` $=g_{i,r+1}$) is drawn from `Measure.pi (fun _ => Measure.pi ν)`, and the algorithm then faces the oblivious sequence the table defines. `probStoch` is a Bochner integral of a function with values in $[0,1]$. Every event used in the mission is a finite Boolean combination of inequalities between measurable functions of the table, so that function is measurable. Maxima over arms are `⨆ i : Fin K`, a genuine maximum because $K\ge2$ in every theorem. `minGap` is an infimum over the arms with positive gap, and every theorem that uses it assumes such an arm exists. $\widehat H_{i,t}$ is used only when $T_i(t)\ge1$.
-- source:
--   Bubeck & Slivkins, The best of both worlds: stochastic and adversarial bandits, arXiv:1202.4473v1, p. 2, Figure 1; p. 5, §2 (estimators, gaps); p. 12, §4 (adaptive adversary)

import Mathlib

open MeasureTheory

namespace BestBothWorlds.SAO

/-- An observed history of a `K`-armed bandit game: the list of pairs `(I_s, g_{I_s,s})` of
played arm and observed reward, in chronological order (the head is round `1`). -/
abbrev History (K : ℕ) := List (Fin K × ℝ)

/-- A randomized bandit algorithm (Bubeck–Slivkins, §2, p. 5): a deterministic map from the
observed history `(I_1, g_{I_1,1}, …, I_{t-1}, g_{I_{t-1},t-1})` to the sampling vector
`p_t = (p_{1,t}, …, p_{K,t})`; the arm `I_t` is then drawn from `p_t`. -/
abbrev Policy (K : ℕ) := History K → Fin K → ℝ

/-- A deterministic adaptive adversary (Fig. 1, p. 2, and §4, p. 12): the reward vector
`g_t = (g_{1,t}, …, g_{K,t})` of round `t` is a function of the arms `I_1, …, I_{t-1}` played
before round `t` (so the round index is the length of the list plus one). It is chosen
simultaneously with `I_t`, hence cannot depend on `I_t`. -/
abbrev Adversary (K : ℕ) := List (Fin K) → Fin K → ℝ

/-- The adversary's rewards lie in `[0, 1]` (Fig. 1: `g_t ∈ [0,1]^K`). -/
def Adversary.IsBounded {K : ℕ} (adv : Adversary K) : Prop :=
  ∀ l i, adv l i ∈ Set.Icc (0 : ℝ) 1

/-- The reward `g_{i,r+1}` of arm `i` on round `r + 1` (`r : Fin n` is the `0`-based round
index) along the arm path `I = (I_1, …, I_n)`, where `I r` is the arm `I_{r+1}`. -/
def reward {K n : ℕ} (adv : Adversary K) (I : Fin n → Fin K) (r : Fin n) (i : Fin K) : ℝ :=
  adv ((List.ofFn I).take r) i

/-- The full observed history `(I_1, g_{I_1,1}, …, I_n, g_{I_n,n})` along the arm path `I`. -/
def history {K n : ℕ} (adv : Adversary K) (I : Fin n → Fin K) : History K :=
  List.ofFn (fun r => (I r, reward adv I r (I r)))

/-- The sampling vector `p_t` of the algorithm `π` on round `t` (`1`-based) along the path `I`:
`π` applied to the history of rounds `1, …, t-1`. -/
def probAt {K n : ℕ} (π : Policy K) (adv : Adversary K) (I : Fin n → Fin K) (t : ℕ) :
    Fin K → ℝ :=
  π ((history adv I).take (t - 1))

/-- The probability that `π` plays exactly the arm path `I` against `adv`:
`∏_{t=1}^n p_{I_t,t}`. -/
def pathProb {K n : ℕ} (π : Policy K) (adv : Adversary K) (I : Fin n → Fin K) : ℝ :=
  ∏ r : Fin n, probAt π adv I (r + 1) (I r)

open Classical in
/-- `Pr[E]` for an event `E` on arm paths of length `n` when `π` plays against `adv`:
`∑_{I ∈ E} ∏_t p_{I_t,t}`. -/
noncomputable def probEvent {K : ℕ} (n : ℕ) (π : Policy K) (adv : Adversary K)
    (E : (Fin n → Fin K) → Prop) : ℝ :=
  ∑ I : Fin n → Fin K, if E I then pathProb π adv I else 0

/-- The regret in the adversarial model (Fig. 1):
`R_n = max_i ∑_{t=1}^n g_{i,t} - ∑_{t=1}^n g_{I_t,t}`, with the rewards the adaptive adversary
produces along the path `I`. -/
noncomputable def regret {K n : ℕ} (adv : Adversary K) (I : Fin n → Fin K) : ℝ :=
  (⨆ i : Fin K, ∑ r : Fin n, reward adv I r i) - ∑ r : Fin n, reward adv I r (I r)

/-- The regret over the rounds `τ + 1, …, n` only:
`max_i ∑_{t=τ+1}^n g_{i,t} - ∑_{t=τ+1}^n g_{I_t,t}`. -/
noncomputable def regretFrom {K n : ℕ} (adv : Adversary K) (I : Fin n → Fin K) (τ : ℕ) : ℝ :=
  (⨆ i : Fin K, ∑ r ∈ Finset.univ.filter (fun r : Fin n => τ ≤ (r : ℕ)), reward adv I r i) -
    ∑ r ∈ Finset.univ.filter (fun r : Fin n => τ ≤ (r : ℕ)), reward adv I r (I r)

/-- In the stochastic model the rewards form a table `ω`, with `ω r i = g_{i,r+1}`; with the
table fixed, the rewards are an oblivious sequence (the value past round `n` is never used). -/
def tableAdv {K n : ℕ} (ω : Fin n → Fin K → ℝ) : Adversary K :=
  fun l i => if h : l.length < n then ω ⟨l.length, h⟩ i else 0

/-- The law of the reward table in the stochastic model: all `g_{i,t}` independent, with
`g_{i,t} ∼ ν_i`. -/
noncomputable def rewardTableMeasure {K : ℕ} (n : ℕ) (ν : Fin K → Measure ℝ)
    [∀ i, SigmaFinite (ν i)] : Measure (Fin n → Fin K → ℝ) :=
  Measure.pi (fun _ : Fin n => Measure.pi ν)

/-- `Pr[E]` in the stochastic model: the reward table `ω` is drawn from
`rewardTableMeasure n ν` and the algorithm then plays against it; the event may depend on the
table and on the arm path. -/
noncomputable def probStoch {K : ℕ} (n : ℕ) (π : Policy K) (ν : Fin K → Measure ℝ)
    [∀ i, SigmaFinite (ν i)] (E : (Fin n → Fin K → ℝ) → (Fin n → Fin K) → Prop) : ℝ :=
  ∫ ω, probEvent n π (tableAdv ω) (E ω) ∂(rewardTableMeasure n ν)

/-- The mean `µ_i = ∫ x dν_i(x)` of arm `i`. -/
noncomputable def mean {K : ℕ} (ν : Fin K → Measure ℝ) (i : Fin K) : ℝ := ∫ x, x ∂(ν i)

/-- The gap `Δ_i = (max_j µ_j) - µ_i` of arm `i` (§2, p. 5). -/
noncomputable def gap {K : ℕ} (μ : Fin K → ℝ) (i : Fin K) : ℝ := (⨆ j : Fin K, μ j) - μ i

/-- The minimal gap `Δ = min_{i : Δ_i > 0} Δ_i` (§2, p. 5); meaningful when some `Δ_i > 0`. -/
noncomputable def minGap {K : ℕ} (μ : Fin K → ℝ) : ℝ := ⨅ i : {i // 0 < gap μ i}, gap μ i.1

/-- The pseudo-regret in the stochastic model (Fig. 1):
`R̄_n = ∑_{t=1}^n (max_i µ_i - µ_{I_t})`. -/
noncomputable def pseudoRegret {K n : ℕ} (μ : Fin K → ℝ) (I : Fin n → Fin K) : ℝ :=
  ∑ r : Fin n, ((⨆ j : Fin K, μ j) - μ (I r))

/-- `G_{i,t} = ∑_{s=1}^t g_{i,s}` (§2). -/
def cumReward {K n : ℕ} (adv : Adversary K) (I : Fin n → Fin K) (i : Fin K) (t : ℕ) : ℝ :=
  ∑ r ∈ Finset.univ.filter (fun r : Fin n => (r : ℕ) < t), reward adv I r i

/-- `T_i(t) = ∑_{s=1}^t 𝟙{I_s = i}` (§2). -/
def pullCount {K n : ℕ} (I : Fin n → Fin K) (i : Fin K) (t : ℕ) : ℕ :=
  (Finset.univ.filter (fun r : Fin n => (r : ℕ) < t ∧ I r = i)).card

/-- `Ĝ_{i,t} = ∑_{s=1}^t g_{i,s} 𝟙{I_s = i}` (§2). -/
def algReward {K n : ℕ} (adv : Adversary K) (I : Fin n → Fin K) (i : Fin K) (t : ℕ) : ℝ :=
  ∑ r ∈ Finset.univ.filter (fun r : Fin n => (r : ℕ) < t ∧ I r = i), reward adv I r i

/-- `G̃_{i,t} = ∑_{s=1}^t g̃_{i,s}` with `g̃_{i,s} = g_{i,s} 𝟙{I_s = i} / p_{i,s}` (§2). -/
noncomputable def estReward {K n : ℕ} (π : Policy K) (adv : Adversary K) (I : Fin n → Fin K)
    (i : Fin K) (t : ℕ) : ℝ :=
  ∑ r ∈ Finset.univ.filter (fun r : Fin n => (r : ℕ) < t ∧ I r = i),
    reward adv I r i / probAt π adv I (r + 1) i

/-- `H_{i,t} = G_{i,t} / t`. -/
noncomputable def fixedAvg {K n : ℕ} (adv : Adversary K) (I : Fin n → Fin K) (i : Fin K)
    (t : ℕ) : ℝ :=
  cumReward adv I i t / t

/-- `H̃_{i,t} = G̃_{i,t} / t`. -/
noncomputable def estAvg {K n : ℕ} (π : Policy K) (adv : Adversary K) (I : Fin n → Fin K)
    (i : Fin K) (t : ℕ) : ℝ :=
  estReward π adv I i t / t

/-- `Ĥ_{i,t} = Ĝ_{i,t} / T_i(t)` (used only when `T_i(t) ≥ 1`). -/
noncomputable def algAvg {K n : ℕ} (adv : Adversary K) (I : Fin n → Fin K) (i : Fin K)
    (t : ℕ) : ℝ :=
  algReward adv I i t / pullCount I i t

end BestBothWorlds.SAO



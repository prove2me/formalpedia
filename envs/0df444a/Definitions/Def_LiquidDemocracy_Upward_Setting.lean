-- Prove2me | Definitions.Def_LiquidDemocracy_Upward_Setting
-- name    : LiquidDemocracy_Upward_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-22T17:23:35.999333+00:00
-- url     : https://prove2.me/theorems/41271dab-8aff-45d1-a679-a30b67d00ebb
-- title:
--   §2–§3, pp. 9–12 — delegation graphs, weights, gain, models, the instance law, probabilistic do no harm / positive gain, continuous distributions, the Upward Delegation Model
-- statement:
--   This file fixes the model of liquid democracy of Berinsky et al. (§2, pp. 9–10) and the Upward Delegation Model (§3, p. 12).
--
--   1. **Voters and delegation graphs.** There are $n$ voters $[n]$. A delegation graph $G_n$ is a directed graph on $[n]$ of out-degree at most one: an edge $(i,j)$ means that $i$ delegates its vote to $j$, and a voter without an outgoing edge votes directly.
--   2. **Weights.** The weight $\mathrm{weight}_i(G_n)$ of a voter $i$ who votes directly is $\mathrm{dels}_i(G_n)+1$, where $\mathrm{dels}_i(G_n)$ is the number of voters who (transitively) delegate to $i$; a voter who delegates has weight $0$. If delegations form a cycle, the voters on the cycle and those delegating into it count for nobody. $\text{max-weight}(G_n)=\max_i \mathrm{weight}_i(G_n)$.
--   3. **Votes and gain.** Each voter $i$ has a competence $p_i\in[0,1]$; given the competence vector $\vec p_n$, the votes $V_i\sim\mathrm{Bern}(p_i)$ are independent ($V_i=1$ means correct), with law $\mathbb P_{\vec p_n}$. Direct democracy counts $X^D_n=\sum_i V_i$ correct votes and liquid democracy $X^F_{G_n}=\sum_i \mathrm{weight}_i(G_n)V_i$. The gain of the instance $(\vec p_n,G_n)$ is
--   $$\mathrm{gain}(\vec p_n,G_n)=\mathbb P_{\vec p_n}[X^F_{G_n}>n/2]-\mathbb P_{\vec p_n}[X^D_n>n/2].$$
--   4. **Models and the instance law.** A model $M=(q,\varphi)$ has $q:[0,1]\to[0,1]$ and $\varphi:[0,1]^2\to\mathbb R_{\ge0}$. Competencies are drawn i.i.d. from a distribution $\mathcal D$ supported in $[0,1]$; then each voter $i$ independently does not delegate with probability $1-q(p_i)$, and with probability $q(p_i)$ delegates to a voter $j\ne i$ chosen with probability proportional to $\varphi(p_i,p_j)$; if $\varphi(p_i,p_j)=0$ for all $j\ne i$, voter $i$ does not delegate. This defines the law $\mathbb P_{\mathcal D,M,n}$ of the instance $(\vec p_n,G_n)$.
--   5. **Definition 1 (probabilistic do no harm).** $M$ satisfies it with respect to a class $\mathfrak D$ if for every $\mathcal D\in\mathfrak D$ and all $\varepsilon,\delta>0$ there is $n_0$ with $\mathbb P_{\mathcal D,M,n}[\mathrm{gain}(\vec p_n,G_n)\ge-\varepsilon]>1-\delta$ for all $n\ge n_0$.
--   6. **Definition 2 (probabilistic positive gain).** $M$ satisfies it with respect to $\mathfrak D$ if there is $\mathcal D\in\mathfrak D$ such that for all $\varepsilon,\delta>0$ there is $n_0$ with $\mathbb P_{\mathcal D,M,n}[\mathrm{gain}(\vec p_n,G_n)\ge1-\varepsilon]>1-\delta$ for all $n\ge n_0$.
--   7. **Continuous distributions.** $\mathfrak D^C$ is the class of continuous (atomless) probability distributions on $\mathbb R$ supported in $[0,1]$.
--   8. **Upward Delegation Model.** For $p\in[0,1]$, $M^U_p=(q,\varphi)$ with $q\equiv p$ and $\varphi(x,y)=\mathbb 1\{y>x\}$: a voter delegates with probability $p$, to a more competent voter chosen uniformly at random; a most competent voter never delegates.
--   9. **Component sizes.** The multiset of the weights of the voters who vote directly.
--
--   These objects are shared by every statement of the mission.
--
--   **Formalization Note** Voters are `Fin n` (0-based); a delegation graph is a map `g : Fin n → Fin n` with `g i = i` meaning "votes directly". The weight of a direct voter `i` counts the voters `j` (including `i`) with `g^[n] j = i`; a chain that runs into a cycle never reaches a fixed point, which gives the cycle convention of p. 9. $\mathbb P_{\vec p_n}$ is the finite sum $\sum_{v\in E}\prod_i (v_i\,?\,c_i : 1-c_i)$ over vote vectors. The instance law is the finite sum over graphs `g` of the competence law $\mathcal D^{\otimes n}$ with density $\prod_i \mathrm{choiceProb}(c,i,g_i)$, placed on the slice $\{g\}$ (no push-forward along a non-measurable map). A model is a pair of real functions; only their values on $[0,1]$ matter. "Continuous distribution" is read as "continuous CDF", which for a probability measure on $\mathbb R$ means no atoms (`NullSingletonClass`). Probabilities are `Measure.real`.
-- source:
--   Berinsky et al., Tracking Truth with Liquid Democracy, arXiv:2107.11868v3, pp. 9–10 (§2, Definitions 1–2) and p. 12 (§3, M^U_p, 𝔇^C); component sizes: proof of Theorem 1, p. 16

import Mathlib

namespace LiquidDemocracy.Upward

/-! # Liquid democracy: delegation graphs, gain, delegation models and the instance law
(Berinsky et al., *Tracking Truth with Liquid Democracy*, arXiv:2107.11868v3, §2 pp. 9–10 and §3 p. 12). -/

open MeasureTheory
open scoped Classical

/-- p. 9: a delegation graph on the voters `Fin n` (out-degree at most one): `g i = i` means that voter
`i` votes directly, `g i = j ≠ i` means that `i` delegates to `j`. -/
abbrev DelegGraph (n : ℕ) := Fin n → Fin n

/-- The voter reached from `i` after following `n` delegation edges. If `i`'s delegation chain ends at a
direct voter, this is that voter; if it runs into a cycle, it is a voter on the cycle, who delegates. -/
noncomputable def root {n : ℕ} (g : DelegGraph n) (i : Fin n) : Fin n := g^[n] i

/-- p. 9: `weight_i(G_n)`. A direct voter carries itself plus every voter whose delegation chain
(transitively) ends at it, i.e. `dels_i(G_n) + 1`; a delegating voter has weight `0`. Voters on a cycle or
delegating into a cycle reach no direct voter and so are counted for nobody. -/
noncomputable def weight {n : ℕ} (g : DelegGraph n) (i : Fin n) : ℕ :=
  if g i = i then (Finset.univ.filter fun j => root g j = i).card else 0

/-- p. 9: `max-weight(G_n) = max_i weight_i(G_n)` (`0` when there are no voters). -/
noncomputable def maxWeight {n : ℕ} (g : DelegGraph n) : ℕ := Finset.univ.sup (weight g)

/-- p. 10: `ℙ_{p⃗_n}[E]` for an event `E` on the vote vector `V ∈ {0,1}^n` (`true` = correct): the votes
`V_i ∼ Bern(c_i)` are independent, so the probability is a finite sum of products. -/
noncomputable def voteProb {n : ℕ} (c : Fin n → ℝ) (E : (Fin n → Bool) → Prop) : ℝ :=
  ∑ v ∈ Finset.univ.filter E, ∏ i, (if v i then c i else 1 - c i)

/-- p. 10: `X^D_n = ∑_i V_i`, the number of correct votes under direct democracy. -/
noncomputable def XD {n : ℕ} (v : Fin n → Bool) : ℝ :=
  ((Finset.univ.filter fun i => v i = true).card : ℝ)

/-- p. 10: `X^F_{G_n} = ∑_i weight_i(G_n) · V_i`, the number of correct votes under liquid democracy. -/
noncomputable def XF {n : ℕ} (g : DelegGraph n) (v : Fin n → Bool) : ℝ :=
  ∑ i, (weight g i : ℝ) * (if v i then 1 else 0)

/-- p. 10: `gain(p⃗_n, G_n) = ℙ_{p⃗_n}[X^F_{G_n} > n/2] − ℙ_{p⃗_n}[X^D_n > n/2]`. -/
noncomputable def gain {n : ℕ} (c : Fin n → ℝ) (g : DelegGraph n) : ℝ :=
  voteProb c (fun v => (n : ℝ) / 2 < XF g v) - voteProb c (fun v => (n : ℝ) / 2 < XD v)

/-- p. 10: a delegation model `M = (q, φ)`: `q` maps a competence to the probability of delegating, `φ`
maps a pair of competencies to a nonnegative weight. Only the values on `[0,1]` matter. -/
structure Model where
  q : ℝ → ℝ
  φ : ℝ → ℝ → ℝ

/-- p. 10: the probability that voter `i`, given the competence vector `c`, ends with `g i = j`. With
`S = ∑_{k ≠ i} φ(c_i, c_k)`: if `S = 0` (degenerate case) `i` votes directly; otherwise `i` votes directly
with probability `1 − q(c_i)` and delegates to `j ≠ i` with probability `q(c_i) · φ(c_i, c_j) / S`. -/
noncomputable def choiceProb (M : Model) {n : ℕ} (c : Fin n → ℝ) (i j : Fin n) : ℝ :=
  if (∑ k ∈ Finset.univ.filter (· ≠ i), M.φ (c i) (c k)) = 0 then (if j = i then 1 else 0)
  else if j = i then 1 - M.q (c i)
  else M.q (c i) * M.φ (c i) (c j) / ∑ k ∈ Finset.univ.filter (· ≠ i), M.φ (c i) (c k)

/-- p. 10: the law `ℙ_{𝒟,M,n}` of the instance `(p⃗_n, G_n)`: competencies i.i.d. `𝒟`, then every voter
chooses independently according to `choiceProb`. Written as a finite sum over graphs `g` of the measure
with density `∏_i choiceProb M c i (g i)` with respect to `𝒟^{⊗n}`, pushed to the slice `{g}`. -/
noncomputable def instanceLaw (D : Measure ℝ) (M : Model) (n : ℕ) :
    Measure ((Fin n → ℝ) × DelegGraph n) :=
  ∑ g : DelegGraph n,
    ((Measure.pi fun _ : Fin n => D).withDensity
        (fun c => ENNReal.ofReal (∏ i, choiceProb M c i (g i)))).map (fun c => (c, g))

/-- Definition 1, p. 10 (probabilistic do no harm). -/
def ProbDNH (M : Model) (𝔇 : Set (Measure ℝ)) : Prop :=
  ∀ D ∈ 𝔇, ∀ ε > 0, ∀ δ > 0, ∃ n₀ : ℕ, ∀ n ≥ n₀,
    1 - δ < (instanceLaw D M n).real {ω | -ε ≤ gain ω.1 ω.2}

/-- Definition 2, p. 10 (probabilistic positive gain). -/
def ProbPG (M : Model) (𝔇 : Set (Measure ℝ)) : Prop :=
  ∃ D ∈ 𝔇, ∀ ε > 0, ∀ δ > 0, ∃ n₀ : ℕ, ∀ n ≥ n₀,
    1 - δ < (instanceLaw D M n).real {ω | 1 - ε ≤ gain ω.1 ω.2}

/-- `𝔇^C`, p. 12: the continuous (atomless) probability distributions with support in `[0,1]` (p. 10). -/
def ContClass : Set (Measure ℝ) :=
  {D | IsProbabilityMeasure D ∧ D (Set.Icc 0 1)ᶜ = 0 ∧ NullSingletonClass D}

/-- p. 12: the Upward Delegation Model `M^U_p`: `q ≡ p`, `φ(x, y) = 𝟙{y > x}`. -/
noncomputable def upward (p : ℝ) : Model := ⟨fun _ => p, fun x y => if x < y then 1 else 0⟩

/-- The multiset of component sizes of `g`: the weights of the voters who vote directly. -/
noncomputable def compSizes {n : ℕ} (g : DelegGraph n) : Multiset ℕ :=
  (Finset.univ.filter fun i => g i = i).val.map (weight g)

end LiquidDemocracy.Upward



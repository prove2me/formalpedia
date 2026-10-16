-- Prove2me | Definitions.Def_Fundraising_PartialCollab_Setting
-- name    : Fundraising_PartialCollab_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-16T08:02:39.120729+00:00
-- url     : https://prove2.me/theorems/a9a0538b-2d4b-4a5b-aefe-e62a91a60920
-- title:
--   §3.1, §6 — the partial-collaboration fundraising game: MNL shares, pooled reach, the lexicographic HO problem (10) with its tie-break, Nash equilibrium, α^p and k̄
-- statement:
--   This file sets up the **partial-collaboration fundraising game** of Aflaki and Pedraza-Martinez (§6), in base-utility coordinates.
--
--   There are $n$ humanitarian organizations (HOs) $i \in I = \{1, \dots, n\}$ (indexed in Lean by $\{0, \dots, n-1\}$). HO $i$ chooses a **base utility** $s_i \in [a_i, b_i]$ (how attractive its earmarking makes it to donors) and an **effort** $x_i \in [0, 1]$ (the fraction of donors it pays to contact). Each HO has a required funding $B_i$, a **unit performance** $\delta_i(s_i)$ (the fraction of each donated dollar that is usable now) and an effort cost $C_i(x_i)$. The mean donation budget is normalized to $z = 1$.
--
--   1. **Pooled reach.** The HOs pool their effort on a common platform, which reaches $\bar x = \min\left(\sum_{i \in I} x_i, 1\right)$ donors.
--   2. **Donor choice.** A contacted donor gives to HO $i$ with the multinomial-logit probability
--   $$\theta^p_i(s) = \frac{\exp(s_i)}{1 + \sum_{j \in I} \exp(s_j)},$$
--   where the $1$ is the outside option of not donating. Expected donations are $E[D^p_i(s; x)] = \bar x \, \theta^p_i(s)$.
--   3. **HO problem (10).** With the others' strategies fixed, HO $i$ evaluates a deviation $(\sigma, \xi) \in [a_i, b_i] \times [0, 1]$ by its funding gap $\left(B_i - \delta_i(\sigma) E[D^p_i]\right)^+$, its utility $\min\left(\delta_i(\sigma) E[D^p_i], B_i\right) - C_i(\xi)$, and its unconstrained total performance $\delta_i(\sigma) E[D^p_i]$, all computed at the profile in which $s_i, x_i$ are replaced by $\sigma, \xi$. A **best response** first minimizes the gap over the box, then maximizes the utility among the gap minimizers, and finally — the paper's rule for an indifferent HO — maximizes the unconstrained total performance among those.
--   4. **Nash equilibrium.** A profile $(s, x)$ in the product of the boxes at which every HO's own strategy $(s_i, x_i)$ is a best response.
--   5. **Required-funding index.** $\alpha^p_i(s) = \min\left(\dfrac{B_i}{\delta_i(s_i)\,\theta^p_i(s)}, 1\right)$, and for a vector $\alpha$, $\bar k = \#\{i : \alpha_i = \alpha_1\}$, the number of entries tied with the first.
--   6. **Standing hypotheses.** $a_i \le b_i$; $B_i > 0$; $C_i$ is nonnegative and strictly increasing on $[0, 1]$; and on some open interval containing $[a_i, b_i]$ the unit performance $\delta_i$ is positive, differentiable and concave; and $\delta_i \le 1$ on $[a_i, b_i]$.
--
--   Every statement of the mission is posed for this game.
--
--   **Formalization Note** Problem (10) as printed lets HO $i$ choose $(s_i, \bar x)$ and pay $C^p(\bar x)$; the proof of Proposition 4 ((S11): $x_i = (\alpha^p_i - \sum_{j \ne i} x_j)^+$) and the free-riding reading of part (ii) use HO $i$'s own effort $x_i$ and own cost $C_i(x_i)$, which is what is encoded. The tie-break (p. 20) is the third level of the best response. $B_i > 0$ is implicit in the paper (with $B_i = 0$ every base utility is a best response). Concavity, positivity and differentiability of $\delta_i$ are the properties the proof of Proposition 4 uses ("$\delta_i(s_i)$ is concave"); they are imposed on an open interval around $[a_i, b_i]$, not on $\mathbb R$, since a positive concave function on $\mathbb R$ is constant. The bound $\delta_i \le 1$ is the paper's range $\delta_i(\cdot) : [0,1] \to [0,1]$ (p. 9), carried over to base-utility coordinates. The paper's model in earmarking coordinates ($e_i$, $s_i(e_i, \delta_i(e_i))$) is not modelled: from (6) on the paper itself treats $s_i$ as the decision.
-- source:
--   Aflaki, Pedraza-Martinez, Competition and Collaboration on Fundraising for Short-Term Disaster Response: The Impact on Earmarking and Performance, SSRN 3705595 (version of December 2022), pp. 8–11 (§3.1, (1)–(2)), pp. 19–20 (§6, problem (10), tie-break, α^p_i and k̄ of Proposition 4)

import Mathlib

namespace Fundraising.PartialCollab

open Finset

/-- The primitives of the partial-collaboration fundraising game with `n` humanitarian
organizations (HOs) indexed by `Fin n`, written in base-utility coordinates: HO `i` chooses a
base utility `s i ∈ [a i, b i]` and an effort `x i ∈ [0, 1]`; `B i` is its required funding,
`δ i` its unit performance as a function of the base utility, `C i` its effort cost. The mean
budget of a donor is normalized to `z = 1`. -/
structure Setting (n : ℕ) where
  /-- lower end of HO `i`'s base-utility interval -/
  a : Fin n → ℝ
  /-- upper end of HO `i`'s base-utility interval -/
  b : Fin n → ℝ
  /-- required funding of HO `i` -/
  B : Fin n → ℝ
  /-- unit performance of HO `i`, as a function of its base utility -/
  δ : Fin n → ℝ → ℝ
  /-- effort cost of HO `i` -/
  C : Fin n → ℝ → ℝ

/-- Multinomial-logit share (p. 20): the probability that a contacted donor gives to HO `i`,
`θ^p_i(s) = exp(s_i) / (1 + Σ_{j ∈ I} exp(s_j))`; the `1` is the outside option. -/
noncomputable def theta {n : ℕ} (s : Fin n → ℝ) (i : Fin n) : ℝ :=
  Real.exp (s i) / (1 + ∑ j, Real.exp (s j))

/-- Platform reach (p. 19): `x̄ = min (Σ_{i ∈ I} x_i, 1)`. -/
noncomputable def reach {n : ℕ} (x : Fin n → ℝ) : ℝ :=
  min (∑ j, x j) 1

/-- Expected donations to HO `i` (p. 20): `E[D^p_i] = x̄ · θ^p_i(s)`. -/
noncomputable def expDonation {n : ℕ} (s x : Fin n → ℝ) (i : Fin n) : ℝ :=
  reach x * theta s i

/-- The number `k̄` of indices tied with the first entry of a vector `α`:
`k̄ = #{i : α_i = α_0}` (0-based; for an antitone `α` these indices are `0, …, k̄ - 1`). -/
noncomputable def kbar {n : ℕ} [NeZero n] (α : Fin n → ℝ) : ℕ :=
  (univ.filter fun i : Fin n => α i = α 0).card

namespace Setting

variable {n : ℕ} (G : Setting n)

/-- Standing hypotheses of the partial-collaboration model: `a i ≤ b i`; `B i > 0`;
`C i` is nonnegative and strictly increasing on `[0, 1]`; and on some open interval
`(l, r) ⊇ [a i, b i]` the unit performance `δ i` is positive, differentiable and concave; and
`δ i ≤ 1` on `[a i, b i]` (unit performance is a fraction of each donated dollar). -/
structure Standing : Prop where
  a_le_b : ∀ i, G.a i ≤ G.b i
  B_pos : ∀ i, 0 < G.B i
  C_nonneg : ∀ i, ∀ t ∈ Set.Icc (0 : ℝ) 1, 0 ≤ G.C i t
  C_strictMonoOn : ∀ i, StrictMonoOn (G.C i) (Set.Icc 0 1)
  δ_regular : ∀ i, ∃ l r : ℝ, l < G.a i ∧ G.b i < r ∧
    (∀ t ∈ Set.Ioo l r, 0 < G.δ i t) ∧
    DifferentiableOn ℝ (G.δ i) (Set.Ioo l r) ∧
    ConcaveOn ℝ (Set.Ioo l r) (G.δ i)
  δ_le_one : ∀ i, ∀ t ∈ Set.Icc (G.a i) (G.b i), G.δ i t ≤ 1

/-- Unconstrained total performance of HO `i` at the profile `(s, x)`:
`δ_i(s_i) · E[D^p_i(s; x)] = δ_i(s_i) · x̄ · θ^p_i(s)`. -/
noncomputable def perf (s x : Fin n → ℝ) (i : Fin n) : ℝ :=
  G.δ i (s i) * expDonation s x i

/-- Funding gap of HO `i`: `(B_i − δ_i(s_i) E[D^p_i(s; x)])^+`. -/
noncomputable def gap (s x : Fin n → ℝ) (i : Fin n) : ℝ :=
  max (G.B i - G.perf s x i) 0

/-- Utility of HO `i`: `min(δ_i(s_i) E[D^p_i(s; x)], B_i) − C_i(x_i)`, with HO `i` paying
the cost of its own effort `x_i`. -/
noncomputable def utility (s x : Fin n → ℝ) (i : Fin n) : ℝ :=
  min (G.perf s x i) (G.B i) - G.C i (x i)

/-- HO `i`'s strategy box `[a_i, b_i] × [0, 1]`. -/
def box (i : Fin n) : Set (ℝ × ℝ) :=
  Set.Icc (G.a i) (G.b i) ×ˢ Set.Icc (0 : ℝ) 1

/-- First level of HO `i`'s problem (10): the strategies `p = (σ, ξ)` in its box that minimize
its funding gap, the other HOs' strategies `(s_{-i}, x_{-i})` being fixed. -/
def gapMinimizers (s x : Fin n → ℝ) (i : Fin n) : Set (ℝ × ℝ) :=
  {p | p ∈ G.box i ∧ ∀ q ∈ G.box i,
    G.gap (Function.update s i p.1) (Function.update x i p.2) i ≤
      G.gap (Function.update s i q.1) (Function.update x i q.2) i}

/-- Second level of problem (10): the gap minimizers that maximize HO `i`'s utility among the
gap minimizers. -/
def utilityMaximizers (s x : Fin n → ℝ) (i : Fin n) : Set (ℝ × ℝ) :=
  {p | p ∈ G.gapMinimizers s x i ∧ ∀ q ∈ G.gapMinimizers s x i,
    G.utility (Function.update s i q.1) (Function.update x i q.2) i ≤
      G.utility (Function.update s i p.1) (Function.update x i p.2) i}

/-- Best responses of HO `i` (problem (10) with the tie-break of p. 20): among the
utility-maximizing gap minimizers, an indifferent HO chooses one that maximizes its
unconstrained total performance. -/
def bestResponses (s x : Fin n → ℝ) (i : Fin n) : Set (ℝ × ℝ) :=
  {p | p ∈ G.utilityMaximizers s x i ∧ ∀ q ∈ G.utilityMaximizers s x i,
    G.perf (Function.update s i q.1) (Function.update x i q.2) i ≤
      G.perf (Function.update s i p.1) (Function.update x i p.2) i}

/-- The profile `(s, x)` lies in the product of the strategy boxes. -/
def InBox (s x : Fin n → ℝ) : Prop :=
  ∀ i, s i ∈ Set.Icc (G.a i) (G.b i) ∧ x i ∈ Set.Icc (0 : ℝ) 1

/-- Pure Nash equilibrium of the partial-collaboration game: a profile in the product box at
which every HO's own strategy `(s_i, x_i)` is a best response to the others' strategies. -/
def IsNE (s x : Fin n → ℝ) : Prop :=
  G.InBox s x ∧ ∀ i, (s i, x i) ∈ G.bestResponses s x i

/-- `α^p_i(s) = min (B_i / (δ_i(s_i) θ^p_i(s)), 1)` (Proposition 4). -/
noncomputable def alpha (s : Fin n → ℝ) (i : Fin n) : ℝ :=
  min (G.B i / (G.δ i (s i) * theta s i)) 1

end Setting

end Fundraising.PartialCollab



-- Prove2me | Definitions.Def_OnlineMatchFrameworks_Supplement_ItemArrivalAlgorithm
-- name    : OnlineMatchFrameworks_Supplement_ItemArrivalAlgorithm
-- status  : Definition
-- author  : @iris
-- created : 2026-11-27T00:22:35.989478+00:00
-- url     : https://prove2.me/theorems/2ed684bf-4de4-5352-b346-171882a394ca
-- title:
--   The LARGE/SMALL algorithm for item arrivals, with the SMALL rule of its proof
-- statement:
--   Fix parameters $\phi,\rho,c$ and an optimal solution $x$ of LP (6). An item is **large** if $q_i\ge c/\theta$ and **small** otherwise.
--
--   1. If $\theta=1$, the algorithm offers, among the items that arrived, one of largest $w_ip_i$.
--   2. If $\theta\ge2$ and $\sum_{i\ \mathrm{large}}w_ix_ip_i\ge(1-\phi)\mathrm{LP}$, it uses **LARGE** at every step: select item $i$ with probability $x_i/\theta$ and, if it has arrived and was never offered, offer it with probability $\rho$.
--   3. Otherwise it uses **SMALL** at every step: each small item arriving in this step wants to be probed, independently, with probability
--
--   $$
--   a_i=\frac{x_i}{1-(1-q_i)^\theta},
--   $$
--
--   and one of those that want it is offered, uniformly at random. An item that is not offered in the step of its arrival is discarded, and large items are ignored.
--
--   The definition gives the expected reward $\mathrm{ALG}$ by the backward recursion over the steps.
--
--   **Formalization Note** This corrects two slips of pp.27–28 from the proofs: the displayed set of large items has $x_i$ where the sentence before it and the proofs have $q_i$, and the prose description of SMALL omits the coin $a_i$ that the proof of Lemma 4 uses. With either slip copied, Theorem 7 is false.
-- source:
--   Brubach, Grammel, Ma & Srinivasan, Online Matching Frameworks under Stochastic Rewards, Product Ranking, and Unknown Patience, arXiv:1907.03963v6, §5.3, pp.27–28; Appendix A, proofs of Lemmas 3 and 4, pp.47–51

import Definitions.Def_OnlineMatchFrameworks_Supplement_ItemArrivalLP

open scoped BigOperators

namespace OnlineMatchFrameworks.Supplement

namespace ItemArrivalInstance

variable {U : Type*} [Fintype U] [DecidableEq U]

/-- **Expected reward of a per-step offering rule.** arXiv:1907.03963v6, §5.3, p.27. In a step with
arrivals `N` and available, never offered items `B' = B ∪ N`, item `i ∈ B'` is offered with probability
`rule N B' i`, and nothing with the remaining probability. The rest is the process of `optFrom`. -/
noncomputable def ruleFrom (G : ItemArrivalInstance U) (rule : Finset U → Finset U → U → ℝ) :
    ℕ → Finset U → Finset U → ℝ
  | 0, _, _ => 0
  | n + 1, R, B =>
      ∑ N ∈ R.powerset, G.arrivalProb R N *
        (∑ i ∈ B ∪ N, rule N (B ∪ N) i *
            (G.p i * G.w i + (1 - G.p i) * G.ruleFrom rule n (R \ N) ((B ∪ N).erase i)) +
          (1 - ∑ i ∈ B ∪ N, rule N (B ∪ N) i) * G.ruleFrom rule n (R \ N) (B ∪ N))

/-- **The large items.** arXiv:1907.03963v6, §5.3, p.27: "We call an item large if q_i ≥ c/θ".

**Formalization Note.** The display after that sentence writes `x_i ≥ c/θ`. The proofs use `q_i`
(p.48, "for large items, q_i ≥ c/θ"; p.50, "since q_j ≤ c/θ for small j"). -/
noncomputable def largeItems (G : ItemArrivalInstance U) (c : ℝ) : Finset U :=
  Finset.univ.filter fun i => c / (G.patience : ℝ) ≤ G.q i

/-- **The LARGE strategy `π_Large`.** arXiv:1907.03963v6, §5.3, p.28: select item `i` with probability
`x_i/θ` (no item with the remaining probability); if the selected item has arrived and was never
offered, offer it with probability `ρ`. -/
noncomputable def largeRule (G : ItemArrivalInstance U) (ρ : ℝ) (x : U → ℝ)
    (_N _B : Finset U) (i : U) : ℝ :=
  x i / (G.patience : ℝ) * ρ

/-- **The probability that an arriving small item wants to be probed.** arXiv:1907.03963v6, proof of
Lemma 4, pp.49–50: `x_i / (1 - (1 - q_i)^θ)`.

**Formalization Note.** If the denominator is `0` then `q_i = 0`, the item never arrives and (6c)
gives `x_i = 0`; Lean's value `0` is never used. -/
noncomputable def wantProb (G : ItemArrivalInstance U) (x : U → ℝ) (i : U) : ℝ :=
  x i / (1 - (1 - G.q i) ^ G.patience)

/-- **The SMALL strategy `π_Small`, as analysed in the proof.** arXiv:1907.03963v6, §5.3, p.28, and proof
of Lemma 4, pp.49–50. Each small item arriving in the step wants to be probed, independently, with
probability `wantProb`; one of those that want it is offered, uniformly at random. Large items are
ignored, and a small item that is not offered in the step of its arrival is never offered.

**Formalization Note (correction).** The sentence on p.28 omits the thinning coin and offers one of
all small arrivals at random. That rule has no positive constant ratio: many small arrivals of weight
`0` crowd out the valuable one. The proof of Lemma 4 analyses the thinned rule defined here ("arrives at
time t and wants to be probed", p.49). -/
noncomputable def smallRule (G : ItemArrivalInstance U) (c : ℝ) (x : U → ℝ)
    (N _B : Finset U) (i : U) : ℝ :=
  ∑ W ∈ (N \ G.largeItems c).powerset.filter (fun W => i ∈ W),
    (∏ j ∈ W, G.wantProb x j) * (∏ j ∈ (N \ G.largeItems c) \ W, (1 - G.wantProb x j)) /
      (W.card : ℝ)

/-- **The choice for `θ = 1`.** arXiv:1907.03963v6, §5.3, p.28: offer "the item with the highest expected
reward among items that arrived". Its expected reward does not depend on how ties are broken. -/
noncomputable def bestArrivedValue (G : ItemArrivalInstance U) : ℝ :=
  ∑ N ∈ (Finset.univ : Finset U).powerset,
    G.arrivalProb Finset.univ N * N.fold max 0 (fun i => G.w i * G.p i)

/-- **The full algorithm.** arXiv:1907.03963v6, §5.3, p.28, with parameters `ϕ`, `ρ`, `c` and an optimal
solution `x` of LP (6). If `θ = 1` it offers the best arrived item. Otherwise, if
`∑_{i large} w_i x_i p_i ≥ (1 - ϕ) LP` it uses `π_Large` at every step, and else `π_Small` at every
step. -/
noncomputable def ALG (G : ItemArrivalInstance U) (ϕ ρ c : ℝ) (x : U → ℝ) : ℝ :=
  if G.patience = 1 then G.bestArrivedValue
  else if (1 - ϕ) * G.lpObjective x ≤ ∑ i ∈ G.largeItems c, G.w i * x i * G.p i then
    G.ruleFrom (G.largeRule ρ x) G.patience Finset.univ ∅
  else G.ruleFrom (G.smallRule c x) G.patience Finset.univ ∅

end ItemArrivalInstance

end OnlineMatchFrameworks.Supplement



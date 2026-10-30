-- Prove2me | Definitions.Def_CrossLayerControl_ECCA_achievable
-- name    : CrossLayerControl_ECCA_achievable
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T01:49:24.704827+00:00
-- url     : https://prove2.me/theorems/9d335b68-c28e-43e7-a141-1e19448963ec
-- title:
--   Rate–service–power triples of stationary randomized decisions
-- statement:
--   Let $\mu$ be the slot law of the pair (arrivals, state). The set $K(\mu)\subseteq\mathbb R^L\times\mathbb R^L\times\mathbb R$ consists of the triples
--   $$\Big(\big(\mathbb E\{R_i\}\big)_i,\ \big(\mathbb E\{C_i(P,s)\}\big)_i,\ \mathbb E\Big\{\sum_i P_i\Big\}\Big)$$
--   over all joint laws $\nu$ of $((a,s),(R,P))$ such that $\nu$ is a probability measure with $(a,s)$-marginal $\mu$, $\nu$-almost surely $0\le R_i\le a_i$ for all $i$ and $P$ is feasible, and $R_i$, $C_i(P,s)$ are $\nu$-integrable.
--
--   Such a $\nu$ is a stationary randomized decision that observes the current arrivals and state (the analogue for the downlink of the paper's S-only algorithms, Definition 6.1).
--
--   **Formalization Note** The integrability requirement only excludes junk values of the integral; under bounded arrivals, (3.4) and measurable rates it holds for every such $\nu$.
-- source:
--   Georgiadis, Neely, Tassiulas, Resource Allocation and Cross-Layer Control in Wireless Networks, Found. Trends Netw. 1(1) (2006), doi:10.1561/1300000001, Definition 6.1, p. 103; §6.3.1, pp. 113–114

import Mathlib
import Definitions.Def_CrossLayerControl_ECCA_Downlink
import Definitions.Def_CrossLayerControl_ECCA_IsFeasiblePower

open MeasureTheory

namespace CrossLayerControl.ECCA

/-- **The rate–service–power triples of stationary randomized decisions.**
Georgiadis, Neely, Tassiulas, *Resource Allocation and Cross-Layer Control in Wireless Networks*,
Found. Trends Netw. 1(1) (2006), Definition 6.1, p. 103: "An S-only algorithm is a stationary
randomized algorithm that chooses control variables I(t), {R(c)n(t)}, {µ(c)ab(t)} based only on the
current topology state S(t)." For the downlink of §6.3.1 (p. 113) the control variables are the
admitted data R(t), constrained by 0 ≤ Ri(t) ≤ Ai(t), and the power P(t); the decision may
therefore depend on the current pair (A(t), S(t)).

For the slot law `μ` of the pair (arrivals, state), `achievable M μ` is the set of triples
`(E[R], E[C(P, S)], E[Σᵢ Pᵢ]) ∈ ℝ^L × ℝ^L × ℝ` over all joint laws `ν` of
`((a, s), (R, P))` such that
1. `ν` is a probability measure whose `(a, s)`-marginal is `μ`;
2. `ν`-almost surely `0 ≤ Rᵢ ≤ aᵢ` for all `i` and `P` is a feasible power vector;
3. the coordinates `Rᵢ` and the rates `Cᵢ(P, s)` are `ν`-integrable.

The first two components are taken coordinatewise: `(E[Rᵢ])ᵢ` and `(E[Cᵢ(P, s)])ᵢ`.

**Formalization Note.** A joint law with `(a, s)`-marginal `μ` is the same as a stationary
randomized decision that observes the current pair: draw `(a, s) ∼ μ`, then `(R, P)` from the
conditional law. The integrability clause only excludes junk values of Lean's integral; under the
standing hypotheses (bounded arrivals, (3.4), measurable `C`) it holds for every such `ν`. -/
def achievable {L : ℕ} {𝒮 : Type*} [MeasurableSpace 𝒮] (M : Downlink L 𝒮)
    (μ : Measure ((Fin L → ℝ) × 𝒮)) : Set ((Fin L → ℝ) × (Fin L → ℝ) × ℝ) :=
  {q | ∃ ν : Measure (((Fin L → ℝ) × 𝒮) × ((Fin L → ℝ) × (Fin L → ℝ))),
      IsProbabilityMeasure ν ∧ ν.map Prod.fst = μ ∧
      (∀ᵐ x ∂ν, (∀ i, 0 ≤ x.2.1 i ∧ x.2.1 i ≤ x.1.1 i) ∧ IsFeasiblePower M x.2.2) ∧
      (∀ i, Integrable (fun x => x.2.1 i) ν ∧ Integrable (fun x => M.C i x.2.2 x.1.2) ν) ∧
      q = (fun i => ∫ x, x.2.1 i ∂ν, fun i => ∫ x, M.C i x.2.2 x.1.2 ∂ν, ∫ x, ∑ i, x.2.2 i ∂ν)}

end CrossLayerControl.ECCA



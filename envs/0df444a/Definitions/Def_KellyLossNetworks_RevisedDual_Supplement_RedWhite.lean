-- Prove2me | Definitions.Def_KellyLossNetworks_RevisedDual_Supplement_RedWhite
-- name    : KellyLossNetworks_RevisedDual_Supplement_RedWhite
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-24T02:55:40.086752+00:00
-- url     : https://prove2.me/theorems/102999f4-c3b7-436e-96cc-9e133f135205
-- title:
--   §4.6 red/white complete graph: two-white-edge fractional routing and P(K)
-- statement:
--   Choose $p\in(0,1)$ and colour each edge of the complete graph on $K$ nodes independently red with probability $p$ and white with probability $1-p$. Red edges join the pairs of stations that communicate; each such pair needs twice the capacity of one edge. It uses the whole (unit) capacity of its red edge and divides its unit of excess traffic arbitrarily over two-edge paths through tandem nodes joined to both members of the pair by white edges.
--
--   A colouring is **white-routable** if there are flows $f_{e,k}\ge0$, nonzero only for red $e$ and tandem nodes $k\notin e$ whose two connecting edges are white, with $\sum_k f_{e,k}=1$ for every red edge $e$, such that the total flow through every white edge is at most $1$. Then
--   $$P(K)=\sum_{\text{colourings } \omega\ \text{white-routable}}\ \prod_{e}p^{[\omega(e)=\text{red}]}(1-p)^{[\omega(e)=\text{white}]}.$$
--
--   This is the event whose probability Theorem 4.40 shows tends to $1$ for $p<1/3$.
--
--   **Formalization Note** Edges, two-edge routes and the load a flow family puts on an edge are the published `KellyLossNetworks.Routing.Edge`, `OnDetour` and `detourLoad`. Flows are real (traffic is divisible). The probability is the finite sum over colourings `Edge K → Bool` of the product Bernoulli weights.
-- source:
--   Kelly, Loss networks, Ann. Appl. Probab. 1(3):319–378 (1991), DOI 10.1214/aoap/1177005872, pp. 356–357, §4.6 (definition of P(K) before Theorem 4.40)

import Mathlib
import Definitions.Def_KellyLossNetworks_Routing_Model

namespace KellyLossNetworks.RevisedDual.Supplement

open KellyLossNetworks.Routing

/-- **The routing event of Theorem 4.40** for a red/white colouring `red` of the edges of the
complete graph on `K` nodes (`red e = true` means `e` is red). Every red pair uses its whole red
edge (unit capacity) and divides its unit of excess traffic among the two-edge paths through
tandem nodes joined to both ends of the pair by **white** edges, without any white edge
carrying more than its unit capacity: there are flows `f e k ≥ 0`, nonzero only when `e` is
red, `k ∉ e` and both edges of the route `e` via `k` are white, with `Σ_k f e k = 1` for every
red `e`, and with the total flow routed through each white edge at most `1`.

Kelly, Loss networks, Ann. Appl. Probab. 1(3):319–378 (1991), DOI 10.1214/aoap/1177005872,
pp. 356–357, §4.6 (definition of `P(K)` before Theorem 4.40).

**Formalization Note.** Edges, two-edge routes and the load a family of route flows puts on an
edge are the published `KellyLossNetworks.Routing.Edge`, `OnDetour` and `detourLoad`. The unit
of capacity is one edge's capacity; the communication need of a pair is twice that. The flows
are real numbers (traffic may be divided arbitrarily). Red edges carry only their own pair's
direct unit, so no two-edge flow may use a red edge. -/
def WhiteRoutable {K : ℕ} (red : Edge K → Bool) : Prop :=
  ∃ f : Edge K → Fin K → ℝ,
    (∀ e k, 0 ≤ f e k) ∧
    (∀ e k, f e k ≠ 0 → red e = true ∧ k ∉ e.1 ∧ ∀ g, OnDetour e k g → red g = false) ∧
    (∀ e, red e = true → ∑ k, f e k = 1) ∧
    (∀ g, red g = false → detourLoad f g ≤ 1)

/-- The probability `∏_e p^{[e red]} (1 − p)^{[e white]}` of a colouring when edges are
independently red with probability `p`. Kelly (1991), p. 356, §4.6. -/
noncomputable def colouringProb {K : ℕ} (p : ℝ) (red : Edge K → Bool) : ℝ :=
  ∏ e, if red e then p else 1 - p

open Classical in
/-- **`P(K)` of §4.6** (p. 357): the probability, when the edges of the complete graph on `K`
nodes are independently coloured red with probability `p` and white with probability `1 − p`,
that the routing of `WhiteRoutable` is possible simultaneously for every red edge.

Kelly (1991), pp. 356–357, §4.6.

**Formalization Note.** The colourings form the finite set `Edge K → Bool`; the probability of
the event is the finite sum of the product weights `colouringProb p` over the colourings in the
event (the product Bernoulli(`p`) measure). -/
noncomputable def whiteRoutingProb (p : ℝ) (K : ℕ) : ℝ :=
  ∑ red : Edge K → Bool, if WhiteRoutable red then colouringProb p red else 0

end KellyLossNetworks.RevisedDual.Supplement



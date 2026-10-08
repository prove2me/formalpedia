-- Prove2me | Definitions.Def_PriceOfStability_Harmonic_Model
-- name    : PriceOfStability_Harmonic_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-04T19:11:24.063374+00:00
-- url     : https://prove2.me/theorems/97cad4a7-46a8-4626-ad12-68dcce8efa05
-- title:
--   Sect. 2 — the fair (Shapley) cost-sharing game, the cost of the designed network, Rosenthal's potential and concave edge costs
-- statement:
--   This file sets up the fair connection game of Anshelevich et al. on top of the congestion games of the referenced model.
--
--   Let $N$ be a finite set of $k$ players and $E$ a finite set of edges (resources). Each player $i$ has a family $\Sigma_i$ of feasible strategies, each a set of edges. Each edge $e$ has a cost $c_e(x)$ of being built for $x\in\mathbb N$ users; for the basic game this cost is a constant $c_e\ge 0$. In a strategy vector $S=(S_1,\dots,S_k)$ let $x_e$ be the number of players whose strategy contains $e$.
--
--   1. **Fair (Shapley) cost sharing.** Every user of edge $e$ pays an equal share, so the per-user cost of $e$ is $f_e(x)=c_e(x)/x$ and player $i$ pays $C_i(S)=\sum_{e\in S_i} c_e(x_e)/x_e$. This is a congestion game with latencies $f_e$.
--   2. **Cost of the designed network.** The edges some player uses are built, each for its number of users:
--   $$\operatorname{cost}(S)=\sum_{e\in\bigcup_i S_i} c_e(x_e).$$
--   3. **Rosenthal's potential** (2.1) of a congestion game with per-user costs $f_e$:
--   $$\Phi(S)=\sum_{e\in E}\sum_{x=1}^{x_e} f_e(x).$$
--   4. **Nondecreasing concave costs** (the hypotheses of Theorem 2.3): for every edge, $c_e(0)\ge 0$, $x\mapsto c_e(x)$ is nondecreasing on $\mathbb N$, and its increments $c_e(x+1)-c_e(x)$ are nonincreasing.
--
--   These objects are used in the statements of Theorems 2.1, 2.3 and 3.1 of the paper.
--
--   **Formalization Note.** Strategy families are arbitrary families of edge sets, as in the paper's *Extensions* paragraph; the directed-graph game is the instance $\Sigma_i=\{S\subseteq E: S \text{ connects } T_i\}$. Concavity is discrete (on $\mathbb N$). The condition $c_e(0)\ge 0$ is implicit in the paper: it is needed for its claim that the per-user cost $c_e(x)/x$ decreases, and $c_e(0)$ is never charged. Lean's $c/0=0$ is reached only for unused edges, which no cost sums over.
-- source:
--   Anshelevich et al., The Price of Stability for Network Design with Fair Cost Allocation, SIAM J. Comput. 38 (2008), DOI 10.1137/070680096, p. 1603 (PDF p. 2), Sect. 1; p. 1607 (PDF p. 6), Sect. 2 and (2.1); p. 1608 (PDF p. 7), before Theorem 2.3

import Mathlib
import Definitions.Def_CongestionPoA_AsymSum_Model

open CongestionPoA.AsymSum

namespace PriceOfStability.Harmonic

variable {ι E : Type*} [Fintype ι] [DecidableEq ι] [Fintype E] [DecidableEq E]

/-- Shapley (fair) cost sharing (Anshelevich et al., SIAM J. Comput. 38 (2008), Sect. 2 and
Theorem 2.1, proof, p. 1607 (PDF p. 6); Theorem 2.3, p. 1608 (PDF p. 7)): the congestion game with
strategy families `strategies` in which every one of the `x` users of edge `e` pays `c_e(x)/x`,
where `c_e(x)` is the cost of building `e` for `x` users. For the constant costs of Theorem 2.1
take `c e x = c_e`.

**Formalization Note.** Strategy families are arbitrary families of edge sets (the paper's
*Extensions* paragraph, p. 1609: the proofs "did not rely on the graph structure"); the fair
connection game on a directed graph is the instance `Σᵢ = {S ⊆ E : S connects Tᵢ}`. Lean's
`c / 0 = 0` is only reached for an edge nobody uses, which no player cost ever sums over. -/
noncomputable def fairGame (strategies : ι → Finset (Finset E)) (c : E → ℕ → ℝ) :
    CongestionGame ι E :=
  ⟨strategies, fun e x => c e x / x⟩

/-- The total cost of the designed network (Sect. 1, p. 1603 (PDF p. 2); Sect. 2, p. 1607):
`cost(S) = Σ_{e ∈ ∪ᵢ Sᵢ} c_e(x_e)`, the cost of the edges that at least one player uses, each
built for its number of users `x_e`. Unused edges cost nothing. -/
noncomputable def designCost (c : E → ℕ → ℝ) (S : ι → Finset E) : ℝ :=
  ∑ e ∈ Finset.univ.filter (fun e => 0 < load S e), c e (load S e)

/-- Rosenthal's potential (2.1) (Theorem 2.1, proof, p. 1607 (PDF p. 6)):
`Φ(S) = Σ_{e∈E} Σ_{x=1}^{x_e} f_e(x)`, where `f_e` is the per-user cost (latency) of edge `e`. -/
noncomputable def potential (G : CongestionGame ι E) (S : ι → Finset E) : ℝ :=
  ∑ e, ∑ x ∈ Finset.Icc 1 (load S e), G.latency e x

/-- The cost hypotheses of Theorem 2.3 (p. 1608 (PDF p. 7)): every edge cost `c_e(x)`, as a
function of the number `x ∈ ℕ` of users, is nondecreasing and (discretely) concave, i.e. its
increments `c_e(x+1) − c_e(x)` are nonincreasing, and `c_e(0) ≥ 0`.

**Formalization Note.** Concavity is stated on `ℕ` (the number of users), as nonincreasing
increments. The condition `c_e(0) ≥ 0` is implicit in the paper: its claim that the cost per player
`c_e(x)/x` decreases for concave `c_e` needs it (`c(x) = 2x − 1` is concave and nondecreasing, but
`c(x)/x` increases). `c_e(0)` is never charged, since unused edges cost nothing. -/
def IsConcaveCost (c : E → ℕ → ℝ) : Prop :=
  ∀ e, 0 ≤ c e 0 ∧ Monotone (c e) ∧ ∀ x, c e (x + 2) - c e (x + 1) ≤ c e (x + 1) - c e x

end PriceOfStability.Harmonic



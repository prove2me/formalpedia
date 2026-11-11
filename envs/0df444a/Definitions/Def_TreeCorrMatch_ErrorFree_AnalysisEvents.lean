-- Prove2me | Definitions.Def_TreeCorrMatch_ErrorFree_AnalysisEvents
-- name    : TreeCorrMatch_ErrorFree_AnalysisEvents
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T16:26:41.537053+00:00
-- url     : https://prove2.me/theorems/ebfad23d-b2ba-4ba5-b4b7-fe15e5076856
-- title:
--   The events $A_1$, $A_2$, $A_{3,u}$ and the cutoff sets $B$, $\tilde B$
-- statement:
--   All three events concern TBAlign **without degree cutoff** ($\tau=\infty$), with $d$ and $\theta^*$ from (1). Write $\bar V(T)\subseteq[n]$ for the nodes of $\bar G$ representing the nodes of a local tree: $V(T)$ for a local tree of $G$, and $\pi^{-1}(V(\tilde T))$ for a local tree of $\tilde G$.
--
--   1. $A_1$ (23): there is no pair $(T^\infty_{w\setminus u},\tilde T^\infty_{\tilde x\setminus\tilde v})$, with $w\sim u$ in $G$ and $\tilde x\sim\tilde v$ in $\tilde G$, such that $\Psi=\mathbf 1\{\hat L(T,\tilde T)>\theta^*\}=1$ and $\bar V(T)\cap\bar V(\tilde T)=\emptyset$.
--   2. $A_2$: the union graph $\bar G$ has no subgraph $\bar S$ with $|V(\bar S)|<|E(\bar S)|$ and $|V(\bar S)|\le 6d+6$.
--   3. $A_{3,u}$ (25): $\mathrm{GreedyMatching}(W^\infty(u,\tilde u),\theta^*,5)=1$ with $\tilde u=\pi(u)$, for every order in which GreedyMatching examines the edges.
--
--   The **cutoff sets** (115)–(116) are
--
--   $$B=\{u: \exists v,\ \mathrm{dist}_G(u,v)\le d+1,\ \deg_G(v)>\tau\},$$
--
--   and $\tilde B$, the same set for $\tilde G$.
--
--   **Formalization Note** $A_1$ and $A_{3,u}$ depend on the outcome $(G,\tilde G,\pi)$ and on the seeds; $A_2$ on the outcome only. $A_{3,u}$ quantifies over every admissible order, which makes it the strongest form of the paper's event; `cutoffSet G d τ` is $B$ for $G$ and $\tilde B$ for $\tilde G$.
-- source:
--   Cheng, Wang, Ying, Near-Quadratic Error-Free Graph Matching above Otter's Threshold via Approximate Local Tree Correlation Testing, arXiv:2611.02281 (held copy, sha256 0dfdbedd…), p. 15, App. A.1, eqs. (23) and (25) (PDF p. 17); p. 50, eqs. (115)–(116) (PDF p. 52)

import Mathlib
import Definitions.Def_TreeCorrMatch_ErrorFree_CER
import Definitions.Def_TreeCorrMatch_ErrorFree_TBAlign

/-!
The events `A1`, `A2`, `A3,u` of the analysis of `TBAlign` without degree cutoff (`τ = ∞`), and the
sets `B`, `B̃` of nodes affected by the cutoff.

Cheng, Wang, Ying, arXiv:2611.02281 (held copy, sha256 0dfdbedd…), App. A.1, (23) and (25),
p. 15; (115)–(116), p. 50.
-/

namespace TreeCorrMatch.ErrorFree

open scoped Classical

/-- The event `A1` of (23), with `τ = ∞`: no pair of local trees
`(T^∞_{w∖u}, T̃^∞_{x̃∖ṽ}) ∈ C^∞_d × C̃^∞_d` (ordered pairs of adjacent nodes) passes the test,
`Ψ = 1{L̂ > θ*} = 1`, while being node-disjoint in the union graph, i.e.
`V̄(T^∞_{w∖u}) ∩ V̄(T̃^∞_{x̃∖ṽ}) = ∅`, where node `ỹ` of `G̃` is node `π⁻¹(ỹ)` of `Ḡ`. -/
def EventA1 {Ω₀ : Type} (App : PermApprox Ω₀) (r : OTree → OTree) (lam s : ℝ) {n : ℕ}
    (x : CEROutcome n) (ω : TBIdx n → Ω₀) : Prop :=
  ∀ w u x' v : Fin n, x.1.Adj w u → x.2.1.Adj x' v →
    thetaParam n < lhatEntry App r lam s ⊤ x.1 x.2.1 ω w u x' v →
      (localVerts x.1 (some u) w (dParam n) ⊤ ∩
        x.2.2 ⁻¹' localVerts x.2.1 (some v) x' (dParam n) ⊤).Nonempty

/-- The event `A2`: the union graph `Ḡ` has no subgraph `S̄` with `|V(S̄)| < |E(S̄)|` and
`|V(S̄)| ≤ 6d + 6`. -/
def EventA2 {n : ℕ} (x : CEROutcome n) : Prop :=
  ∀ S : (unionGraph x).Subgraph, S.verts.ncard ≤ 6 * dParam n + 6 → S.edgeSet.ncard ≤ S.verts.ncard

/-- The event `A3,u` of (25), with `τ = ∞`: `GreedyMatching(W^∞(u, ũ), θ*, 5) = 1`, `ũ = π(u)`, for
every admissible order in which `GreedyMatching` examines the edges. -/
def EventA3 {Ω₀ : Type} (App : PermApprox Ω₀) (r : OTree → OTree) (lam s : ℝ) {n : ℕ}
    (x : CEROutcome n) (ω : TBIdx n → Ω₀) (u : Fin n) : Prop :=
  ∀ order, IsWitnessOrder x.1 x.2.1 u (x.2.2 u) order →
    mTB App r lam s ⊤ x.1 x.2.1 ω u (x.2.2 u) order = true

/-- The set (115): nodes `u` whose `(d + 1)`-hop neighbourhood in `G` contains a node of degree
greater than `τ`, `B = {u : ∃ v, dist_G(u, v) ≤ d + 1, deg_G(v) > τ}`; (116) is the same set for
`G̃`. -/
def cutoffSet {n : ℕ} (G : SimpleGraph (Fin n)) (d τ : ℕ) : Set (Fin n) :=
  {u | ∃ v, G.edist u v ≤ (d + 1 : ℕ) ∧ τ < G.degree v}

end TreeCorrMatch.ErrorFree



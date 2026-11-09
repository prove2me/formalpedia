-- Prove2me | Definitions.Def_WeakGraphOracles_OneSided_testing
-- name    : WeakGraphOracles_OneSided_testing
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T10:20:10.098444+00:00
-- url     : https://prove2.me/theorems/5e98399d-28ff-450b-a1ba-7f345c333041
-- title:
--   One-sided testability with both distance normalizations
-- statement:
--   Let $F$ be a finite forbidden family and let $\epsilon>0$. A valid policy accepts every promised $F$-free graph with probability one and rejects each promised far graph with probability at least $2/3$. GEN1 uses all finite simple input graphs and edge-normalized farness. RN at fixed degeneracy $h$ uses only random-neighbor queries on $h$-degenerate graphs and vertex-normalized farness.
--
--   $$\operatorname{Test}(F)\iff
--   \forall\epsilon>0\;\exists q\in\mathbb N\;\forall n\in\mathbb N\;\exists A_n\;
--   \forall G\text{ in the promised class},\;A_n\text{ has the stated correctness on }G.$$
--
--   The bound $q$ is independent of $n$ and the hidden graph. Policies may depend nonuniformly on $n$, $F$, $\epsilon$, and on $h$ for RN. The reused degeneracy predicate requires a low-degree vertex in each nonempty vertex subset, equivalently in every nonempty subgraph. It assumes no minor or coloring condition.
--
--   For the explicit tree-discovery witness with $k\ge1$ edges, set $h=2k$, $s=\lceil4h\log h\rceil$, and $Q(k)=1+ks(s+1)^k$. The logarithm is natural. The ceiling records an integer number of oracle calls without decreasing the source's sampling rate.
-- source:
--   Oded Lachish, Amit Levi, Ilan Newman, Testability of General Graphs with Weak Query Oracles, STOC 2027 submission #274 (October 2026), p. 5 (PDF p. 6), Definition 1; pp. 5–6 (PDF pp. 6–7), Remark 2; p. 7 (PDF p. 8), Definition 4; pp. 16–18 (PDF pp. 17–19), §§7.3–7.4

import Mathlib
import Definitions.Def_HadwigerConj_Defs
import Definitions.Def_WeakGraphOracles_OneSided_oracle

set_option autoImplicit false

namespace WeakGraphOracles.OneSided

/-- Correctness holds simultaneously on every promised graph for one fixed
policy. The hidden graph is not an input to that policy. -/
def Correct {n q : ℕ} (F : Finset Pattern) (ε : ℝ) (edgeAllowed : Bool)
    (promise : SimpleGraph (Fin n) → Prop)
    (far : Finset Pattern → ℝ → SimpleGraph (Fin n) → Prop) (A : Policy n q) : Prop :=
  ValidPolicy edgeAllowed A ∧
    ∀ G, promise G →
      (Free F G → acceptProbability A G = 1) ∧
      (far F ε G → (2 : ℝ) / 3 ≤ 1 - acceptProbability A G)

/-- Query bound is outside n, and the tester is outside the hidden graph.
No computability or running-time assumption is imposed (Remark 2). -/
def GEN1Testable (F : Finset Pattern) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ q : ℕ, ∀ n : ℕ, ∃ A : Policy n q,
    Correct F ε true (fun _ => True) EdgeFar A

/-- h is fixed before epsilon, the bound, n and the hidden graph. -/
def RNTestable (F : Finset Pattern) (h : ℕ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ q : ℕ, ∀ n : ℕ, ∃ A : Policy n q,
    Correct F ε false (fun G => HadwigerConj.IsDegenerate G h) VertexFar A

/-- Theorem 7 integer implementation of the source's sample count. -/
noncomputable def treeSamples (k : ℕ) : ℕ :=
  ⌈4 * (2 * (k : ℝ)) * Real.log (2 * (k : ℝ))⌉₊

noncomputable def treeQueryBound (k : ℕ) : ℕ :=
  1 + k * treeSamples k * (treeSamples k + 1) ^ k

end WeakGraphOracles.OneSided



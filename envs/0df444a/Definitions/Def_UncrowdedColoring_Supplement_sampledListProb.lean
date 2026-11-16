-- Prove2me | Definitions.Def_UncrowdedColoring_Supplement_sampledListProb
-- name    : UncrowdedColoring_Supplement_sampledListProb
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T03:05:06.030206+00:00
-- url     : https://prove2.me/theorems/e03d0a91-a409-48f9-97f5-6426227da811
-- title:
--   Random lists — each vertex samples a uniform $q'$-subset of $[q]$
-- statement:
--   Let $H$ be a hypergraph with finite vertex set $V(H)$, and let $q, q' \in \mathbb N$. Write $[q] = \{1, \dots, q\}$ and $\binom{[q]}{q'}$ for the family of $q'$-element subsets of $[q]$. In the **random list model** of Theorem 7.1, each vertex $v \in V(H)$ independently samples a subset $L(v) \subseteq [q]$ of size $q'$ uniformly at random. The joint law of $L = (L(v))_{v \in V(H)}$ is the uniform law on the $\binom{q}{q'}^{|V(H)|}$ assignments $V(H) \to \binom{[q]}{q'}$, so for a property $P$ of list assignments
--
--   $$
--   \Pr_L[P(L)] \;=\; \frac{\#\{L : V(H) \to \tbinom{[q]}{q'} \;:\; P(L)\}}{\binom{q}{q'}^{|V(H)|}}.
--   $$
--
--   Theorem 7.1 applies this to the event that $H$ admits an $L$-coloring.
--
--   **Formalization Note** The lists are indexed by the subtype $V(H)$ and extended by $\emptyset$ outside it, so that they can be passed to the mission's published `IsListColoring`, which only reads lists on $V(H)$. Counts are `Nat.card`, the true count when $V(H)$ is finite, which every statement using the definition assumes. When $q' > q$ and $V(H) \ne \emptyset$ there are no assignments and the ratio is $0/0 = 0$; Theorem 7.1 excludes this case by $q' \le q$.
-- source:
--   Dhawan, Methuku, Vo, List Coloring Uncrowded Hypergraphs at the Shattering Threshold, STOC 2027 submission (manuscript sha256 2e7243ce…), Theorem 7.1, p.53 (PDF p.54); [q] notation §3.1, p.13

import Mathlib

namespace UncrowdedColoring

namespace Supplement

/-- The `q′`-element subsets of `[q] = {1, …, q}` (§3.1 notation `[q]`, p.13; Theorem 7.1, p.53).

Dhawan, Methuku, Vo, *List Coloring Uncrowded Hypergraphs at the Shattering Threshold*, STOC 2027
submission (manuscript sha256 2e7243ce…), §3.1, p.13 and Theorem 7.1, p.53. -/
def qSubsets (q q' : ℕ) : Finset (Finset ℕ) :=
  (Finset.Icc 1 q).powersetCard q'

open Classical in
/-- A list assignment given on the vertex set `V(H)`, extended by `∅` to the whole vertex type, so
that it can be fed to the published `IsListColoring` (which only reads lists on `V(H)`). -/
noncomputable def extendLists {V : Type*} (H : Hypergraph V) (L : H.vertexSet → Finset ℕ) :
    V → Set ℕ :=
  fun v => if h : v ∈ H.vertexSet then ((L ⟨v, h⟩ : Finset ℕ) : Set ℕ) else ∅

/-- **Random `q′`-subset lists** (the sampling model of Theorem 7.1, p.53): "For each vertex
`v ∈ V(H)`, independently sample a subset `L(v) ⊆ [q]` of size `q′` uniformly at random."

`sampledListProb H q q' P` is the probability that the random list assignment `L` has property `P`.
The joint law of independent uniform `q′`-subsets of `[q]`, one per vertex of `V(H)`, is the uniform
law on the finite set of all assignments `V(H) → ([q] choose q′)`, so the probability is the number of
assignments with property `P` divided by the number of all assignments, `C(q, q′)^{|V(H)|}`.

Dhawan, Methuku, Vo, *List Coloring Uncrowded Hypergraphs at the Shattering Threshold*, STOC 2027
submission (manuscript sha256 2e7243ce…), Theorem 7.1, p.53.

**Formalization Note.** The lists are indexed by the subtype `V(H)` and extended by `∅` outside
it (`extendLists`). `Nat.card` is the true count when `V(H)` is finite, which every statement using
this definition assumes; when `q′ > q` there are no assignments on a nonempty vertex set and the
ratio is `0/0 = 0`, a case Theorem 7.1 excludes by `q′ ≤ q`. -/
noncomputable def sampledListProb {V : Type*} (H : Hypergraph V) (q q' : ℕ)
    (P : (V → Set ℕ) → Prop) : ℝ :=
  (Nat.card {L : H.vertexSet → qSubsets q q' // P (extendLists H (fun v => (L v).1))} : ℝ) /
    (Nat.card (H.vertexSet → qSubsets q q') : ℝ)

end Supplement

end UncrowdedColoring



-- Prove2me | Definitions.Def_OAI_Combinatorics_InfiniteMatroid_DoubleRay__InfiniteMatroidCorollaries
-- name    : OAI_Combinatorics_InfiniteMatroid_DoubleRay__InfiniteMatroidCorollaries
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T05:19:29.145596+00:00
-- url     : https://prove2.me/theorems/480488e0-cf71-4469-b615-72c1940457e6
-- title:
--   Vertex assignments of subsets of the double-ray ground set $\mathbb{Z}\times\alpha$
-- statement:
--   Let $\alpha$ be a set and consider the ground set $\mathbb Z\times\alpha$, split into the *bundles* $\{k\}\times\alpha$, $k\in\mathbb Z$. The bundles are pictured as the edges of a double ray whose vertices are the integers: edge $k$ joins the vertices $k$ and $k+1$, so vertex $n$ is incident with the edges $n-1$ and $n$, and the *central edge* is $-1$. The base definitions of the project fix, for $n\in\mathbb Z$ and $b\in\{0,1\}$, the bundle
--   $$\beta(n,b)=\begin{cases} n, & n<0,\ b=0,\\ n-1, & n<0,\ b=1,\\ n-1, & n\ge 0,\ b=0,\\ n, & n\ge 0,\ b=1,\end{cases}$$
--   so that $\beta(n,0)$ is the edge at $n$ on the side of the central edge and $\beta(n,1)$ is the edge at $n$ pointing away from it. For a matroid $Q$ on $\alpha\times\{0,1\}$ and a parity $p\in\{0,1\}$, the ray matroid $M_p(Q)$ on $\mathbb Z\times\alpha$ is the direct sum of one copy of $Q$ for each vertex $v$ with $v\equiv p\pmod 2$, the copy at $v$ being placed on the two edges at $v$ by $(x,b)\mapsto(\beta(v,b),x)$.
--
--   This file adds one definition.
--
--   **Vertex assignment.** For $I\subseteq\mathbb Z\times\alpha$ and $n\in\mathbb Z$, the assignment of $I$ at $n$ is the subset of $\alpha\times\{0,1\}$
--   $$A_n(I)=\begin{cases}\{(x,b)\in\alpha\times\{0,1\}:\ (\beta(n,b),x)\in I\}, & n\ \text{even},\\ \{(x,b)\in\alpha\times\{0,1\}:\ (\beta(n,b),x)\notin I\}, & n\ \text{odd}.\end{cases}$$
--   At an even vertex, $A_n(I)$ is the trace of $I$ on the two edges at $n$, read in the coordinates of the copy of $Q$ at $n$; at an odd vertex it is the corresponding trace of the complement $(\mathbb Z\times\alpha)\setminus I$.
--
--   The assignment transfers a putative covering of $\mathbb Z\times\alpha$ by two independent sets to the vertices. If $I$ is independent in $M_0(Q)$ (copies of $Q$ at the even vertices) and its complement is independent in $M_1(Q)$ (copies at the odd vertices), then for every $n\in\mathbb Z$ the set $A_n(I)$ is the preimage of $I$ (for even $n$) or of its complement (for odd $n$) under the embedding of the copy of $Q$ at $n$, hence independent in $Q$. In the counterexamples $\alpha=D$, $Q$ is the self-dual uniform matroid on $E_0=D\times\{0,1\}$, and the two matroids on $\mathbb Z\times D$ are $M_0(Q)$ and $M_1(Q)$; following the assignments $A_n(I)$ outward along a half-ray is how one shows that $\mathbb Z\times D$ is not the union of an $M_0(Q)$-independent and an $M_1(Q)$-independent set.
--
--   **Formalization Note** `assignment I n` tests `n % 2 = 0`; since `%` on integers is the Euclidean remainder, this is exactly evenness of $n$, also for negative $n$. The map $\beta$ is `bundleAt` of the base definitions, with `false` and `true` standing for $0$ and $1$; `rayMatroid Q p` is also defined there.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/InfiniteMatroid/DoubleRay.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/InfiniteMatroid/DoubleRay.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the InfiniteMatroidCorollaries mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_InfiniteMatroidCorollaries
import Definitions.Def_OAI_Combinatorics_InfiniteMatroid_Matroid__InfiniteMatroidCorollaries

namespace OAI

section
open Set Matroid
namespace InfiniteMatroidCounterexample

/-- The independent partition is assigned to vertices by parity. -/
def assignment {α : Type*} (I : Set (ℤ × α)) (n : ℤ) : Set (α × Bool) :=
  {x | if n % 2 = 0 then (bundleAt n x.2,x.1) ∈ I else (bundleAt n x.2,x.1) ∉ I}

end InfiniteMatroidCounterexample
end

end OAI



-- Prove2me | Definitions.Def_NSWApxHard_Reduction_CubicVC
-- name    : NSWApxHard_Reduction_CubicVC
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-24T09:32:47.76778+00:00
-- url     : https://prove2.me/theorems/2dbfd5cc-821e-4118-8bfd-95e3ccfbd7e2
-- title:
--   3-regular graphs, vertex covers, and Theorem 2.1 (Chlebík–Chlebíková) as a proposition (p. 2)
-- statement:
--   Graphs have vertex set $\{0,\dots,N-1\}$. A graph is **3-regular** (cubic) when every vertex has exactly three neighbours; it then has $M=1.5N$ edges. A **vertex cover** is a set $C$ of vertices meeting every edge.
--
--   Graphs are encoded in binary as the self-delimiting code of $N$ followed by the $N^2$ bits of the adjacency matrix, row by row. For constants $c_{\min}, c_{\max}$:
--   1. a **Yes-instance** is a 3-regular graph with $N\ge1$ vertices having a vertex cover of size at most $c_{\min}N$;
--   2. a **No-instance** is a 3-regular graph with $N\ge1$ vertices every vertex cover of which has size at least $c_{\max}N$.
--
--   **Theorem 2.1** (Lee, p. 2, due to Chlebík and Chlebíková [2]) is recorded as the proposition $\mathrm{Thm21}(c_{\min},c_{\max})$: it is NP-hard to distinguish Yes-instances from No-instances, in the sense of gap NP-hardness — every NP language over every finite nonempty alphabet maps, by a polynomial-time computable function (Cook's one-tape Turing machines), to graphs so that members go to Yes-instances and non-members to No-instances. [2] proves it for $c_{\min}\approx0.5103$, $c_{\max}\approx0.5155$.
--
--   The proposition is the hypothesis of the mission's goal theorem: the paper cites Theorem 2.1 and does not prove it.
--
--   **Formalization Note** Gap NP-hardness is the published definition `GapNPHard` of `SetCoverThreshold_SetCover_Complexity`, built on `CookPvsNP_defs`. Without $N\ge1$ the empty graph would be both a Yes- and a No-instance and the proposition would be trivially false. The sentence "Therefore, it is NP-hard to approximate Vertex Cover on 3-regular graphs within factor ≈ 1.01" of Theorem 2.1 is a consequence and is not part of the proposition.
-- source:
--   Lee, APX-Hardness of Maximizing Nash Social Welfare with Indivisible Items, arXiv:1507.01159v1, p. 2, Theorem 2.1 (citing Chlebík and Chlebíková, Theoretical Computer Science 354(3), 2006)

import Mathlib
import Definitions.Def_CookPvsNP_defs
import Definitions.Def_SetCoverThreshold_SetCover_Complexity
import Definitions.Def_NSWApxHard_Reduction_Welfare

namespace NSWApxHard.Reduction

open Finset

/-- A graph on the vertex set `Fin N = {0, …, N-1}`. -/
structure GraphInput where
  N : ℕ
  G : SimpleGraph (Fin N)

/-- `G` is 3-regular: every vertex has exactly three neighbours. -/
def IsCubic {N : ℕ} (G : SimpleGraph (Fin N)) : Prop :=
  ∀ v : Fin N, (G.neighborSet v).ncard = 3

open Classical in
/-- The binary encoding of a graph: `N` by `natBits`, then the `N²` adjacency bits
`[i ~ j]`, row by row. -/
noncomputable def encGraph (I : GraphInput) : List Bool :=
  natBits I.N ++
    (List.ofFn fun i : Fin I.N => List.ofFn fun j : Fin I.N => decide (I.G.Adj i j)).flatten

/-- Yes-instances of Theorem 2.1 (Lee, p. 2): a nonempty 3-regular graph with a vertex cover of
size at most `c_min N`. -/
def vcYes (cmin : ℝ) (I : GraphInput) : Prop :=
  0 < I.N ∧ IsCubic I.G ∧
    ∃ C : Finset (Fin I.N), I.G.IsVertexCover ↑C ∧ (C.card : ℝ) ≤ cmin * I.N

/-- No-instances of Theorem 2.1 (Lee, p. 2): a nonempty 3-regular graph every vertex cover of
which has size at least `c_max N`. -/
def vcNo (cmax : ℝ) (I : GraphInput) : Prop :=
  0 < I.N ∧ IsCubic I.G ∧
    ∀ C : Finset (Fin I.N), I.G.IsVertexCover ↑C → cmax * I.N ≤ (C.card : ℝ)

/-- Theorem 2.1 of Lee (p. 2), due to Chlebík and Chlebíková, as a proposition about the
constants `c_min, c_max`: it is NP-hard to distinguish 3-regular graphs with a vertex cover of
size at most `c_min N` from 3-regular graphs all of whose vertex covers have size at least
`c_max N`. -/
def Theorem21 (cmin cmax : ℝ) : Prop :=
  SetCoverThreshold.SetCover.GapNPHard encGraph (vcYes cmin) (vcNo cmax)

end NSWApxHard.Reduction



-- Prove2me | Definitions.Def_BunkbedComplete
-- name    : BunkbedComplete
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-10-01T00:34:19.318758+00:00
-- url     : https://prove2.me/theorems/303619a1-62b5-4229-a16c-30556431a774
-- title:
--   Complete bunkbed percolation and pendant-vertex extension
-- statement:
--   For a finite graph $G=(V,E)$, form the Cartesian product $G\times K_2$: it has two horizontal copies of every base edge and one vertical edge over every vertex. The complete bunkbed connection probability is the probability of connectivity when every edge of this product, including every vertical edge, is retained independently with probability $p$.
--
--   The complete bunkbed conjecture at $p=1/2$ asserts that for all finite connected base graphs and all vertices $u,v$,
--   $$\mathbb P_{1/2}(u_0\leftrightarrow v_1)\le\mathbb P_{1/2}(u_0\leftrightarrow v_0).$$
--
--   Also defined are the probability mass of independent vertex-dependent posts, the corresponding mixture of fair horizontal bunkbed models, and the graph obtained by attaching a family of pendant vertices to specified base vertices. These provide the objects used in the proof of Theorem 6.1.
-- source:
--   N. Gladkov, I. Pak, A. Zimin, The bunkbed conjecture is false, PNAS 122 (2025), e2420725122, https://www.math.ucla.edu/~pak/papers/Bunkbed-PNAS.pdf#page=9, Section 6, Theorem 6.1.

import Definitions.Def_BunkbedPercolation

/-!
# Complete bunkbed percolation

The product graph has one copy of every base edge in each level and a vertical edge
at every base vertex. All its edges, including the vertical ones, are percolated
independently. This is the model in Section 6 of Gladkov–Pak–Zimin (2025).
-/
namespace Bunkbed
open Finset SimpleGraph
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Edge set of the Cartesian product of the base graph with `K₂`. -/
def completeEdges (E : Finset (Sym2 V)) : Finset (Sym2 (V × Fin 2)) :=
  E.image (liftLvl 0) ∪ E.image (liftLvl 1) ∪
    Finset.univ.image (fun x : V => s((x, 0), (x, 1)))

/-- Connection probability in independent `p`-percolation on the full product graph. -/
def completeProb (E : Finset (Sym2 V)) (p : ℚ) (x y : V × Fin 2) : ℚ :=
  connProbU (completeEdges E) p x y

/-- Probability mass of a set of independently retained vertical posts. -/
def postWeight (q : V → ℚ) (T : Finset V) : ℚ :=
  (∏ v ∈ T, q v) * ∏ v ∈ Finset.univ \ T, (1 - q v)

/-- Fair horizontal percolation with independent, vertex-dependent vertical probabilities. -/
def randomPostProb (E : Finset (Sym2 V)) (q : V → ℚ) (x y : V × Fin 2) : ℚ :=
  ∑ T : Finset V, postWeight q T * bbProb E (fun _ => (1 / 2 : ℚ)) T x y

/-- Attach one new pendant vertex for each index, with the specified base vertex as its parent. -/
def pendantEdges {J : Type*} [Fintype J] [DecidableEq J]
    (E : Finset (Sym2 V)) (parent : J → V) : Finset (Sym2 (V ⊕ J)) :=
  E.image (Sym2.map Sum.inl) ∪
    Finset.univ.image (fun j => s(Sum.inl (parent j), Sum.inr j))

/-- The complete bunkbed conjecture at retention probability `1/2`. -/
def CompleteBunkbedConjecture : Prop :=
  ∀ (n : ℕ) (E : Finset (Sym2 (Fin n))), (ofEdges E).Connected →
    ∀ u v : Fin n,
      completeProb E (1 / 2) (u, 0) (v, 1) ≤
        completeProb E (1 / 2) (u, 0) (v, 0)

end Bunkbed



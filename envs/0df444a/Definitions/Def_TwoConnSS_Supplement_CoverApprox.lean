-- Prove2me | Definitions.Def_TwoConnSS_Supplement_CoverApprox
-- name    : TwoConnSS_Supplement_CoverApprox
-- status  : Definition
-- author  : @iris
-- created : 2026-11-15T20:45:40.412685+00:00
-- url     : https://prove2.me/theorems/4769bac7-2f1c-48cd-b341-cff8329d5d79
-- title:
--   {3, 4}-cycle-free 2-edge-covers and their polynomial-time $\mu$-approximation
-- statement:
--   Let $G=(V,E)$ be a finite simple graph. A **2-edge-cover** of $G$ is an edge set $S\subseteq E$ in which every vertex has degree at least two. It is **$\{3,4\}$-cycle-free** if no connected component of $(V,S)$ is a triangle or a 4-cycle; such cycles may still occur inside larger components.
--
--   For a real $\mu$, the hypothesis $\mathrm{CoverApprox}(\mu)$ says that there is a **polynomial-time $\mu$-approximation algorithm for minimum $\{3,4\}$-cycle-free 2-edge-cover in 2-edge-connected graphs**: an algorithm $\mathcal A$ running in polynomial time such that, for every 2-edge-connected graph $G$ that has at least one $\{3,4\}$-cycle-free 2-edge-cover, its output $\mathcal A(G)$ is a $\{3,4\}$-cycle-free 2-edge-cover of $G$ and
--   $$
--   |\mathcal A(G)|\le \mu\cdot|C|\quad\text{for every }\{3,4\}\text{-cycle-free 2-edge-cover } C \text{ of } G .
--   $$
--
--   This is the hypothesis of the conditional Theorems 5.3 and 5.4; a PTAS for the cover problem is $\mathrm{CoverApprox}(1+\delta)$ for every $\delta>0$.
--
--   **Formalization Note** Polynomial time is Mathlib's `Turing.TM2ComputableInPolyTime` on the published encodings `encIn` (instances) and `encOut` (edge lists), as in the base mission's Theorem 5.1. The guarantee is required only on 2EC graphs that admit a $\{3,4\}$-cycle-free 2-edge-cover: the triangle and the 4-cycle are 2EC and have none, so requiring an output on every 2EC graph would make the hypothesis unsatisfiable. Every 2EC graph with at least five vertices admits one (its whole edge set). The optimum is "every feasible $C$", never an infimum.
-- source:
--   A. Jabal Ameli, Improved Approximations for Two-Edge-Connected and Two-Vertex-Connected Spanning Subgraphs, STOC 2027 submission (manuscript sha256 22d0f2a895e1fa238a27dca51f52b9f9f0c99a02bea4adcddcacca2e27e2ae6a), §5.1, pp.19–20 (PDF 20–21), Theorems 5.3 and 5.4 (hypothesis); §6, p.25 (PDF 26)

import Mathlib
import Definitions.Def_TwoConnSS_Inst
import Definitions.Def_TwoConnSS_encIn
import Definitions.Def_TwoConnSS_IsTwoEdgeCover

namespace TwoConnSS.Supplement

open TwoConnSS

variable {V : Type*} [Fintype V]

/-- **{3, 4}-cycle-free 2-edge-cover.**
Jabal Ameli, *Improved Approximations for Two-Edge-Connected and Two-Vertex-Connected Spanning
Subgraphs*, STOC 2027 submission (manuscript sha256 22d0f2a8…), §5.1, p.19: "A 2-edge-cover is a
spanning subgraph in which every vertex has degree at least two. It is {3, 4}-cycle-free if none of
its connected components is a triangle or a 4-cycle; these cycles may still occur within larger
components."

`IsCover34 G S`: `S ⊆ E(G)`, every vertex has degree at least two in `(V, S)` (published
`TwoConnSS.IsTwoEdgeCover`), and no connected component of `(V, S)` is a 3-cycle or a 4-cycle
(published `TwoConnSS.IsCycleComp`). -/
def IsCover34 (G : SimpleGraph V) (S : Finset (Sym2 V)) : Prop :=
  IsTwoEdgeCover G S ∧ ∀ C, ¬ IsCycleComp S C 3 ∧ ¬ IsCycleComp S C 4

/-- **A polynomial-time `μ`-approximation algorithm for minimum {3, 4}-cycle-free 2-edge-cover in
2-edge-connected graphs** — the hypothesis of Theorems 5.3 and 5.4.
Jabal Ameli, *Improved Approximations for Two-Edge-Connected and Two-Vertex-Connected Spanning
Subgraphs*, STOC 2027 submission (manuscript sha256 22d0f2a8…), Theorems 5.3 and 5.4, p.20:
"Suppose there is a polynomial-time μ-approximation algorithm for minimum {3, 4}-cycle-free
2-edge-cover in 2-edge-connected graphs".

`CoverApprox μ`: there is a function `A` from instances to edge lists, computed by a
polynomial-time Turing machine (`Turing.TM2ComputableInPolyTime` on the published encodings `encIn`,
`encOut`), such that on every instance whose graph `G` is 2-edge-connected and has at least one
{3, 4}-cycle-free 2-edge-cover, the output `A(G)` is a {3, 4}-cycle-free 2-edge-cover of `G` with
`|A(G)| ≤ μ·|C|` for every {3, 4}-cycle-free 2-edge-cover `C` of `G`.

**Formalization Note.** The guarantee is required only on 2EC graphs that admit a {3, 4}-cycle-free
2-edge-cover: the triangle and the 4-cycle are 2EC and have none, so asking for an output on every
2EC graph would make the hypothesis unsatisfiable. Every 2EC graph with at least five vertices
admits one (its whole edge set). The optimum is "every feasible `C`", never an infimum. -/
def CoverApprox (μ : ℝ) : Prop :=
  ∃ A : Inst → List (ℕ × ℕ), Nonempty (Turing.TM2ComputableInPolyTime encIn encOut A) ∧
    ∀ I : Inst, IsTwoEC I.graph → (∃ C, IsCover34 I.graph C) →
      IsCover34 I.graph (toEdges I.n (A I)) ∧
      ∀ C : Finset (Sym2 (Fin I.n)), IsCover34 I.graph C →
        ((toEdges I.n (A I)).card : ℝ) ≤ μ * (C.card : ℝ)

end TwoConnSS.Supplement



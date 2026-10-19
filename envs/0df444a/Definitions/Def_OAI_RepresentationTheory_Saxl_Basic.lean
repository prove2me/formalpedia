-- Prove2me | Definitions.Def_OAI_RepresentationTheory_Saxl_Basic
-- name    : OAI_RepresentationTheory_Saxl_Basic
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T22:43:56.778687+00:00
-- url     : https://prove2.me/theorems/f64b2d02-30a8-4adb-a6c0-c242c94ad8e0
-- title:
--   Membership criterion for the staircase Young diagram
-- statement:
--   For $m\in\mathbb{N}$, the staircase Young diagram $\delta_m$ is the set of cells
--   $$
--   \delta_m=\{(i,j)\in\mathbb{N}^2:\ i<m,\ j<m,\ i+j<m\},
--   $$
--   where the cell $(i,j)$ lies in row $i$ and column $j$, both counted from $0$. Its rows have lengths $m,m-1,\dots,1$, so it is the diagram of the staircase partition $(m,m-1,\dots,1)$ of $m(m+1)/2$. This file records two elementary facts about it.
--
--   1. **Membership.** For all $m,i,j\in\mathbb{N}$,
--   $$
--   (i,j)\in\delta_m\iff i+j<m ;
--   $$
--   the bounds $i<m$ and $j<m$ in the definition are redundant.
--   2. **Empty staircase.** The diagram $\delta_0$ has no cells: $|\delta_0|=0$.
--
--   The membership criterion is the form in which the staircase is handled throughout the surrounding development: the transposition $(i,j)\mapsto(j,i)$ of the self-conjugate staircase, the sub-staircase $\delta_h\subseteq\delta_{h+s}$ and the outer band of cells with $h\le i+j<h+s$ are all described through it. The staircase is the shape singled out in the target statement of the development, which asserts that for $m\ge1$ every Specht module of the symmetric group on $m(m+1)/2$ points occurs in the tensor square of the Specht module of $\delta_m$.
--
--   **Formalization Note** `staircase m` is a Mathlib `YoungDiagram` whose cells are the pairs `x` in the product of `Finset.range m` with itself satisfying `x.1 + x.2 < m`. The two facts are the simp lemmas `mem_staircase` and `staircase_card_zero`, the latter stated as `(staircase 0).card = 0`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/RepresentationTheory/Saxl/Basic.lean

-- Generated from openai/math@1581d4c lean/OAI/RepresentationTheory/Saxl/Basic.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the Saxl mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_Saxl

namespace OAI

noncomputable section

open scoped TensorProduct

universe uG uV uW

namespace Saxl

/- The genuine finite-dimensional Hom criterion; no simplicity hypothesis. -/
/- Column permutations cannot also fix the row word unless they are identity. -/
/- The coefficient of the canonical row word in its polytabloid is one. -/
@[simp] theorem mem_staircase {m i j : ℕ} :
    (i, j) ∈ staircase m ↔ i + j < m := by
  change (i, j) ∈ ((Finset.range m) ×ˢ (Finset.range m)).filter
    (fun x => x.1 + x.2 < m) ↔ _
  simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range]
  omega

@[simp] theorem staircase_card_zero : (staircase 0).card = 0 := by
  simp [staircase, YoungDiagram.card]

/- The staircase has triangular cardinality. -/
end Saxl

end

end OAI



-- Prove2me | Definitions.Def_DDNNFNeg_IsBalancedCutExpander
-- name    : DDNNFNeg_IsBalancedCutExpander
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T07:19:05.281182+00:00
-- url     : https://prove2.me/theorems/a1da449f-17ea-4840-9c10-09186df92a7c
-- title:
--   Balanced-cut $\gamma$-edge expander
-- statement:
--   For a constant $\gamma$, a graph $G = (V, E)$ is a **balanced-cut $\gamma$-edge expander** if for every cut $(A, B)$ of $V$ with $|A|, |B| \ge |V|/3$ there are at least $\gamma |V|$ edges crossing the partition.
--
--   **Formalization Note** The cut is balanced in the sense of `IsBalanced`; crossing edges are counted as unordered edges of $G$ and compared with $\gamma n$ in $\mathbb R$. The paper takes $\gamma \in (0,1)$; the theorems state that range.
-- source:
--   Arenas–Broadrick–Liew–Van den Broeck, d-DNNF is Not Polynomially Closed Under Negation, STOC 2027 submission manuscript (sha256 64e4212767c37c44…fbb68), §5.2, p.12

import Mathlib
import Definitions.Def_DDNNFNeg_IsBalanced
import Definitions.Def_DDNNFNeg_IsCrossing

namespace DDNNFNeg

/-- `G` is a balanced-cut `γ`-edge expander (Arenas–Broadrick–Liew–Van den Broeck, *d-DNNF is Not Polynomially Closed Under Negation*, STOC 2027 submission manuscript (sha256 64e42127…fbb68), §5.2, p.12): for every cut `(A, B)` of
`V = [n]` with `|A|, |B| ≥ |V|/3`, at least `γ|V|` edges of `G` cross the partition.

**Formalization Note** The cut is `(A, Aᶜ)` with `A : Finset (Fin n)`, balanced in the sense of
`IsBalanced` (`n ≤ 3|A|`, `n ≤ 3|Aᶜ|`). Crossing edges are counted as unordered edges of `G`
(elements of `G.edgeFinset`), and the comparison with `γ n` is in `ℝ`. The paper takes
`γ ∈ (0, 1)`; the theorems state that range. -/
def IsBalancedCutExpander {n : ℕ} (γ : ℝ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] :
    Prop :=
  ∀ A : Finset (Fin n), IsBalanced A →
    γ * n ≤ ((G.edgeFinset.filter (fun e => IsCrossing A e)).card : ℝ)

end DDNNFNeg



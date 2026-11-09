-- Prove2me | Definitions.Def_HierADA_Params
-- name    : HierADA_Params
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T17:57:18.15979+00:00
-- url     : https://prove2.me/theorems/e41bdcb2-5d6c-49a7-a56d-185b4b95033f
-- title:
--   Parameters $(p,\tau,\varepsilon_j,B_j,C_j,\delta,L,b)$ of the hierarchical mechanism
-- statement:
--   A record of the parameters of the hierarchical mechanism:
--
--   1. the number $p$ of sample blocks;
--   2. the disagreement threshold $\tau$;
--   3. the privacy budget $\varepsilon_j$ of each block;
--   4. the correction limit $B_j$ of each edge (an edge joins two consecutive blocks);
--   5. the number $C_j$ of private components that access block $j$, Equation (15);
--   6. the privacy slack $\delta$, the logarithmic term $L$ and the Laplace noise scale $b$.
--
--   The values used by the paper are `params`.
--
--   **Formalization Note** Blocks are indexed $0,\dots,p-1$: Lean's block $j$ is the paper's block $j+1$, the anchor is the last block, and Lean's edge $j$ (for $j+1<p$) joins blocks $j$ and $j+1$.
-- source:
--   Gribelyuk–Lin–Lyu–Majid–Woodruff–Yu–Zhou, Adaptive Data Analysis and Adversarial Robustness on Insertion-Deletion Streams, preprint (version of 2026-11-03, sha256 f220ae51…), Section 3.2, p.18, and Section 3.3, p.24

import Mathlib

set_option autoImplicit false

namespace HierADA

/-- **The parameters of the hierarchical mechanism** — Gribelyuk–Lin–Lyu–Majid–Woodruff–Yu–Zhou,
*Adaptive Data Analysis and Adversarial Robustness on Insertion-Deletion Streams*, preprint (version
of 2026-11-03, sha256 f220ae51…), Section 3.2, p.18, and Section 3.3, p.24.

A record of: the number of blocks `p`; the disagreement threshold `τ`; the privacy budgets `ε j` of
the blocks; the correction limits `B j` of the edges; the component counts `C j` of Equation (15);
the privacy slack `δ`; the logarithmic term `L`; and the Laplace noise scale `b`.

**Formalization Note.** Blocks are indexed by `Fin p`, **0-based**: Lean's block `j` is the paper's
block `j + 1`, and Lean's edge `j` (joining blocks `j` and `j + 1`, for `j + 1 < p`) is the paper's
edge `j + 1`. The anchor is the block with `j + 1 = p`. Values of `ε`, `B`, `C` at indices the paper
does not use are recorded as described in `params`. -/
structure Params where
  /-- number of blocks -/
  p : ℕ
  /-- disagreement threshold -/
  τ : ℝ
  /-- privacy budget of each block -/
  ε : Fin p → ℝ
  /-- correction limit of each edge (0 at the anchor, which has no outgoing edge) -/
  B : Fin p → ℕ
  /-- number of private components accessing each block, Equation (15) -/
  C : Fin p → ℕ
  /-- privacy slack -/
  δ : ℝ
  /-- logarithmic term of the advanced composition -/
  L : ℝ
  /-- Laplace noise scale -/
  b : ℝ

end HierADA



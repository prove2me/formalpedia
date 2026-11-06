-- Prove2me | Definitions.Def_AnytimeAdaVR_paramSeq
-- name    : AnytimeAdaVR_paramSeq
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T02:28:33.206565+00:00
-- url     : https://prove2.me/theorems/b3d86de1-c990-4e8f-8fad-a3855ca0c061
-- title:
--   Block parameters $(a_j,b_j)$ for a given count sequence
-- statement:
--   Given any sequence $m_1,m_2,\dots$ of large-estimate counts, the block parameters start at $(a_1,b_1)=(1,2)$ and follow Table 2:
--   $$
--   (a_{j+1},b_{j+1})=\text{update}\big((a_j,b_j),m_j\big).
--   $$
--   Along an S or M path, $m_j$ is the number of large estimates in block $j$; deterministic statements about the parameters are made for every count sequence.
--
--   **Formalization Note** Blocks are indexed from $0$: index $j$ is the paper's block $j+1$.
-- source:
--   Jiang–Wang–Yang–Zhang–Li, Adaptive Variance Reduction across Smoothness and Noise Conditions (preprint, 2026; held artifact sha256 6f3caf41…74006), App. C, eq. (36), p.19

import Mathlib
import Definitions.Def_AnytimeAdaVR_paramStep

namespace AnytimeAdaVR

/-- **The block parameters along a path, for a given sequence of large-estimate counts.** Jiang–Wang–Yang–Zhang–Li, *Adaptive Variance Reduction across Smoothness and Noise Conditions*
(preprint, 2026),
App. C, p.19: "Let (x_j, a_j, b_j) be the state at the start of block j, so x_1 = xinit, a_1 = 1, and
b_1 = 2. If m_j estimates in that block are large, Table 2 reads (36)."

`paramSeq k m j = (a, b)` is the scale and length at the start of block `j` (0-based: `j = 0` is the
paper's block 1) when the blocks before it had `m 0, m 1, …` large estimates.

**Formalization Note.** The sequence `m` is an arbitrary input, so statements about `paramSeq`
hold for every possible outcome of the blocks; the path's own counts are one such sequence. -/
noncomputable def paramSeq (k : SMKind) (m : ℕ → ℕ) : ℕ → ℝ × ℕ
  | 0 => (1, 2)
  | j + 1 => paramStep k (paramSeq k m j) (m j)

end AnytimeAdaVR



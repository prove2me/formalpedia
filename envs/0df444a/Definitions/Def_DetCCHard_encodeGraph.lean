-- Prove2me | Definitions.Def_DetCCHard_encodeGraph
-- name    : DetCCHard_encodeGraph
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:36:26.479181+00:00
-- url     : https://prove2.me/theorems/85cb2ed6-5490-408f-b6bc-6ed7446c4017
-- title:
--   Explicit encodings of a source graph and of the gap-table input
-- statement:
--   The **encoding of a source graph** $G$ is the block $[n]$ followed by one block $[u, v]$ per edge occurrence, in order, all numbers in binary. The **input of the gap-table algorithm** of Theorem 8.4 is the block $[k, s_g]$ followed by the blocks of the encoding of $G$.
--
--   The graph encoding is injective (verification file).
-- source:
--   Gaspers–He–Mackenzie, NP-Hardness and Additive Inapproximability of Deterministic Communication Complexity, arXiv:2508.05597 (held version, sha256 ad552d13…), Theorem 5.2, p.16; Theorem 8.4, p.36

import Mathlib
import Definitions.Def_DetCCHard_SrcGraph
import Definitions.Def_DetCCHard_CodeSym

namespace DetCCHard

/-- The **explicit encoding of a source multigraph** (Gaspers–He–Mackenzie, arXiv:2508.05597,
held version sha256 ad552d13…a4a03, Theorem 5.2, p.16; the paper fixes no format): a block `[n]`,
then one block `[u, v]` per edge occurrence, in the order of the edge list, with all numbers in
binary. -/
def encodeGraph (G : SrcGraph) : List CodeSym :=
  encodeBlocks ([G.n] :: G.edges.map fun e => [(e.1 : ℕ), (e.2 : ℕ)])

/-- The **input of the gap-table algorithm** of Theorem 8.4 (p.36): the gap `k`, the power of two
`s_g` and the source graph `G`, as a block `[k, s_g]` followed by the blocks of `encodeGraph G`. -/
def encodeGapInput (G : SrcGraph) (k sg : ℕ) : List CodeSym :=
  encodeBlocks ([k, sg] :: [G.n] :: G.edges.map fun e => [(e.1 : ℕ), (e.2 : ℕ)])

end DetCCHard



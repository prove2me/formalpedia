-- Prove2me | Definitions.Def_ValiantModel_Strategy
-- name    : ValiantModel_Strategy
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T06:35:00.559505+00:00
-- url     : https://prove2.me/theorems/d7cd2316-68e8-4570-9929-1161e7e93e90
-- title:
--   Definition 7, p.15 — deterministic adaptive query strategies, depth and transcripts
-- statement:
--   A **deterministic adaptive query strategy** $\sigma$ on $\{0,1\}^d$ is a rooted binary tree whose internal nodes are labeled by points of the domain. The root label is the first query; on response $0$ the strategy follows the left child, and on response $1$ the right child. Its **depth** is the maximum number of queries on any root-to-leaf path, whether or not any hypothesis realizes that path.
--
--   The **transcript of $\sigma$ on a hypothesis $h$** is the sequence of (query, response) pairs along the path that $h$ determines. The transcripts of this form are exactly the response transcripts of $\sigma$ realized by a hypothesis.
-- source:
--   Hanneke, Mehrotra, Velegkas, Zampetakis, What is Learnable in Valiant's Theory of the Learnable?, arXiv:2605.13840 (version held, sha256 f793f255…), p.15 (PDF p.17), Definition 7

import Mathlib
import Definitions.Def_ValiantModel_ConceptSequence

namespace ValiantModel

/-- **Definition 7 (Adaptive Query Strategy)**, arXiv:2605.13840 (version held), p.15 (PDF p.17):
a rooted binary tree whose internal nodes are labeled by points of `{0,1}^d`; on response `0` the
strategy follows the left child, on response `1` the right child. -/
inductive Strategy (d : ℕ) : Type
  | leaf : Strategy d
  | node (x : Point d) (left right : Strategy d) : Strategy d

namespace Strategy

/-- The depth: the maximum number of queries on any root-to-leaf path, realizable or not. -/
def depth {d : ℕ} : Strategy d → ℕ
  | leaf => 0
  | node _ l r => 1 + max l.depth r.depth

/-- The root-to-leaf transcript `(q(σ, r), r)` that the strategy produces on the hypothesis `h`,
as the list of (queried point, response) pairs. The transcripts of this form are exactly the
response transcripts of `σ` realized by a hypothesis (footnote 3, p.3, PDF p.5). -/
def transcript {d : ℕ} : Strategy d → Hypothesis d → List (Point d × Bool)
  | leaf, _ => []
  | node x l r, h =>
      (x, h x) ::
        match h x with
        | true => r.transcript h
        | false => l.transcript h

end Strategy

end ValiantModel



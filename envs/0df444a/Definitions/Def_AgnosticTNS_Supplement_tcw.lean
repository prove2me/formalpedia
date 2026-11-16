-- Prove2me | Definitions.Def_AgnosticTNS_Supplement_tcw
-- name    : AgnosticTNS_Supplement_tcw
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T01:38:43.82419+00:00
-- url     : https://prove2.me/theorems/4c9bd2b8-6a70-4672-846d-47e49f762840
-- title:
--   Tree-cutwidth $\mathrm{tcw}(G)$
-- statement:
--   The **tree-cutwidth** $\mathrm{tcw}(G)$ of a graph $G$ is the minimum width over all tree-cut decompositions of $G$.
-- source:
--   Caro–McHugh–Strelchuk, Efficient Agnostic Learning of Tensor Network States, STOC 2027 submission (manuscript sha256 d69077bb…abec0), Definition 6.6, p.49

import Mathlib
import Definitions.Def_AgnosticTNS_Supplement_tcWidth

namespace AgnosticTNS.Supplement

/-- **The tree-cutwidth** `tcw(G)`, Definition 6.6, p.49 (Caro–McHugh–Strelchuk, *Efficient Agnostic Learning of Tensor Network States*, STOC 2027 submission manuscript (sha256 d69077bb…abec0)): the
minimum width over all tree-cut decompositions of `G`. -/
noncomputable def tcw {n : ℕ} (G : SimpleGraph (Fin n)) : ℕ :=
  sInf {k | ∃ D : TreeCutDecomp n, tcWidth G D = k}

end AgnosticTNS.Supplement



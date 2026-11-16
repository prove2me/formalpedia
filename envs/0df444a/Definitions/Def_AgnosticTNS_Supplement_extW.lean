-- Prove2me | Definitions.Def_AgnosticTNS_Supplement_extW
-- name    : AgnosticTNS_Supplement_extW
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T01:33:39.907371+00:00
-- url     : https://prove2.me/theorems/8c9ac32e-d5aa-4ffd-9411-78b43b42bbf4
-- title:
--   Edge dimensions extended by $1$ off the edge set
-- statement:
--   Throughout Section 6, an edge-dimension function $w:E\to\mathbb N$ is extended to all unordered pairs by $w(\{u,v\})=1$ whenever $\{u,v\}\notin E$. This is a formal virtual leg of dimension one in the tensor formulas; it does not add an edge to the graph.
-- source:
--   Caro–McHugh–Strelchuk, Efficient Agnostic Learning of Tensor Network States, STOC 2027 submission (manuscript sha256 d69077bb…abec0), Section 6 convention, p.47; Theorem 6.8, p.49

import Mathlib

namespace AgnosticTNS.Supplement

/-- **Edge dimensions extended by `1` off the edge set**, Section 6 convention, p.47, and Theorem 6.8,
p.49 (Caro–McHugh–Strelchuk, *Efficient Agnostic Learning of Tensor Network States*, STOC 2027 submission manuscript (sha256 d69077bb…abec0)): `w(f) = 1` whenever `f ∉ E` (a formal virtual leg of
dimension one; no edge is added to the graph). -/
noncomputable def extW {n : ℕ} (G : SimpleGraph (Fin n)) (w : G.edgeSet → ℕ) : Sym2 (Fin n) → ℕ := by
  classical
  exact fun f => if h : f ∈ G.edgeSet then w ⟨f, h⟩ else 1

end AgnosticTNS.Supplement



-- Prove2me | Definitions.Def_AgnosticTNS_Supplement_TCIndex
-- name    : AgnosticTNS_Supplement_TCIndex
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T01:41:03.616208+00:00
-- url     : https://prove2.me/theorems/c8d9f993-7f8c-4081-a741-e64c0f4deb29
-- title:
--   Instance of the tree-cut learner (Theorem 6.18)
-- statement:
--   An instance of the learner of Theorem 6.18: the graph $G$ on $[n]$, the empty-bag-free tree-indexed partition $(\hat T,\hat{\mathcal X})$ with $m$ nodes, the width bound $k$, $d$, $\chi$, $k_\epsilon=\lceil1/\epsilon\rceil$ and $k_\delta=\lceil\log_2(1/\delta)\rceil$.
-- source:
--   Caro–McHugh–Strelchuk, Efficient Agnostic Learning of Tensor Network States, STOC 2027 submission (manuscript sha256 d69077bb…abec0), Theorem 6.18, p.60

import Mathlib

namespace AgnosticTNS.Supplement

/-- **An instance of the learner of Theorem 6.18**, p.60 (Caro–McHugh–Strelchuk, *Efficient Agnostic Learning of Tensor Network States*, STOC 2027 submission manuscript (sha256 d69077bb…abec0)):
the graph `G` on `[n]`, the empty-bag-free tree-indexed partition `(T̂, X̂)` (`T̂` on `Fin m`), the width
bound `k`, `d`, `χ`, `k_ε = ⌈1/ε⌉`, `k_δ = ⌈log₂(1/δ)⌉`. -/
structure TCIndex where
  n : ℕ
  G : SimpleGraph (Fin n)
  m : ℕ
  That : SimpleGraph (Fin m)
  Xhat : Fin m → Finset (Fin n)
  k : ℕ
  d : ℕ
  χ : ℕ
  kε : ℕ
  kδ : ℕ

end AgnosticTNS.Supplement



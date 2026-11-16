-- Prove2me | Definitions.Def_AgnosticTNS_Supplement_ContrIndex
-- name    : AgnosticTNS_Supplement_ContrIndex
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T01:29:04.336437+00:00
-- url     : https://prove2.me/theorems/378db9c6-2496-45ad-a003-2d76ddad7332
-- title:
--   Instance of the contraction-sequence learner
-- statement:
--   An instance of the learner of Theorem 1.2 consists of the graph $G$ on $[n]$, the given contraction sequence, the local dimension $d$, the bond bound $\chi$, and the accuracy and confidence through $k_\epsilon=\lceil 1/\epsilon\rceil$ and $k_\delta=\lceil\log_2(1/\delta)\rceil$.
-- source:
--   Caro–McHugh–Strelchuk, Efficient Agnostic Learning of Tensor Network States, STOC 2027 submission (manuscript sha256 d69077bb…abec0), Theorem 1.2, p.3; Corollary 5.10, p.44

import Mathlib

namespace AgnosticTNS.Supplement

/-- **An instance of the contraction-sequence learner of Theorem 1.2**, p.3 (Corollary 5.10, p.44)
(Caro–McHugh–Strelchuk, *Efficient Agnostic Learning of Tensor Network States*, STOC 2027 submission manuscript (sha256 d69077bb…abec0)): the graph `G` on `[n]`, the given contraction sequence (as the
list of merged vertex-set pairs), `d`, `χ`, and `k_ε = ⌈1/ε⌉`, `k_δ = ⌈log₂(1/δ)⌉`. -/
structure ContrIndex where
  n : ℕ
  G : SimpleGraph (Fin n)
  steps : List (Finset (Fin n) × Finset (Fin n))
  d : ℕ
  χ : ℕ
  kε : ℕ
  kδ : ℕ

end AgnosticTNS.Supplement



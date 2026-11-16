-- Prove2me | Definitions.Def_AgnosticTNS_Supplement_OrdIndex
-- name    : AgnosticTNS_Supplement_OrdIndex
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T01:40:13.889195+00:00
-- url     : https://prove2.me/theorems/7e98de3c-a6cf-464a-bf13-b7d16e720aad
-- title:
--   Instance of the MPS-representation learner (Theorem 6.16)
-- statement:
--   An instance of the learner of Theorem 6.16: the graph $G$ on $[n]$, a linear ordering $\pi$ of its vertices, $d$, $\chi$, $k_\epsilon=\lceil1/\epsilon\rceil$ and $k_\delta=\lceil\log_2(1/\delta)\rceil$.
-- source:
--   Caro–McHugh–Strelchuk, Efficient Agnostic Learning of Tensor Network States, STOC 2027 submission (manuscript sha256 d69077bb…abec0), Theorem 6.16, p.59

import Mathlib

namespace AgnosticTNS.Supplement

/-- **An instance of the learner of Theorem 6.16**, p.59 (Caro–McHugh–Strelchuk, *Efficient Agnostic Learning of Tensor Network States*, STOC 2027 submission manuscript (sha256 d69077bb…abec0)):
the graph `G` on `[n]`, a linear ordering `π`, `d`, `χ`, `k_ε = ⌈1/ε⌉`, `k_δ = ⌈log₂(1/δ)⌉`. -/
structure OrdIndex where
  n : ℕ
  G : SimpleGraph (Fin n)
  π : Equiv.Perm (Fin n)
  d : ℕ
  χ : ℕ
  kε : ℕ
  kδ : ℕ

end AgnosticTNS.Supplement



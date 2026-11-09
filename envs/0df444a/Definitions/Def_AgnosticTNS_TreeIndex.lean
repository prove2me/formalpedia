-- Prove2me | Definitions.Def_AgnosticTNS_TreeIndex
-- name    : AgnosticTNS_TreeIndex
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T16:33:22.133198+00:00
-- url     : https://prove2.me/theorems/11fc4f85-3b8d-43f0-adbd-7fc8b94ff168
-- title:
--   Instance of the tree learner of Corollary 5.2
-- statement:
--   An instance of Corollary 5.2: the number of vertices $n$, the tree $T$, the local dimension $d$, the bond dimension bound $\chi$, $k_\epsilon=\lceil1/\epsilon\rceil$ and $k_\delta=\lceil\log_2(1/\delta)\rceil$.
-- source:
--   Caro–McHugh–Strelchuk, Efficient Agnostic Learning of Tensor Network States, STOC 2027 submission (manuscript sha256 d69077bb…abec0), Corollary 5.2, p.40

import Mathlib

namespace AgnosticTNS

/-- **An instance of the tree learner of Corollary 5.2**, p.40 (Caro–McHugh–Strelchuk, *Efficient Agnostic Learning of Tensor Network States*, STOC 2027 submission manuscript (sha256 d69077bb…abec0)): `n`, the tree `T`, the local
dimension `d`, the bond bound `χ`, and the accuracy and confidence as `k_ε = ⌈1/ε⌉`,
`k_δ = ⌈log₂(1/δ)⌉`. -/
structure TreeIndex where
  n : ℕ
  T : SimpleGraph (Fin n)
  d : ℕ
  χ : ℕ
  kε : ℕ
  kδ : ℕ

end AgnosticTNS



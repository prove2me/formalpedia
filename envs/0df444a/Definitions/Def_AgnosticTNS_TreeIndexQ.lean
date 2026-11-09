-- Prove2me | Definitions.Def_AgnosticTNS_TreeIndexQ
-- name    : AgnosticTNS_TreeIndexQ
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T16:33:23.592581+00:00
-- url     : https://prove2.me/theorems/e007bb45-e752-440f-bf76-7bbde3d00c3e
-- title:
--   Instance of the tree learner of Corollary 5.1
-- statement:
--   An instance of Corollary 5.1: $n$, the tree $T$, $d$, $\chi$, the accuracy $\epsilon$ and the overlap bound $\vartheta$ as exact rationals, and $k_\delta=\lceil\log_2(1/\delta)\rceil$.
--
--   **Formalization Note** $\epsilon,\vartheta$ are exact because the copy bound (5.2) runs through the step function $p_T$.
-- source:
--   Caro–McHugh–Strelchuk, Efficient Agnostic Learning of Tensor Network States, STOC 2027 submission (manuscript sha256 d69077bb…abec0), Corollary 5.1, p.39

import Mathlib

namespace AgnosticTNS

/-- **An instance of the tree learner of Corollary 5.1**, p.39 (Caro–McHugh–Strelchuk, *Efficient Agnostic Learning of Tensor Network States*, STOC 2027 submission manuscript (sha256 d69077bb…abec0)): `n`, the tree `T`, `d`, `χ`,
the accuracy `ε` and overlap bound `ϑ` as exact rationals, and `k_δ = ⌈log₂(1/δ)⌉`.

**Formalization Note** `ε, ϑ` are exact because the copy bound (5.2) runs through the step function
`p_T`, which rounding would change. -/
structure TreeIndexQ where
  n : ℕ
  T : SimpleGraph (Fin n)
  d : ℕ
  χ : ℕ
  ε : ℚ
  ϑ : ℚ
  kδ : ℕ

end AgnosticTNS



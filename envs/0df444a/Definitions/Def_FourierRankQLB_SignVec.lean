-- Prove2me | Definitions.Def_FourierRankQLB_SignVec
-- name    : FourierRankQLB_SignVec
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T00:38:13.536244+00:00
-- url     : https://prove2.me/theorems/89322372-bd42-4df0-ae3a-9e3bbb1b3469
-- title:
--   Sign vectors $\sigma\in\{-1,+1\}^d$
-- statement:
--   The set $\{-1,+1\}^d$ of sign vectors, which index the objectives of the main theorem.
--
--   **Formalization Note** A sign is coded by a Boolean, with `true` for $+1$ and `false` for $-1$ (see `boolSign`).
-- source:
--   Augustino et al., Near-Optimal Quantum Lower Bounds for Convex Optimization via Fourier Rank, arXiv:2609.09035, §4.3, p.28 and Theorem 5.1, p.31

import Mathlib

namespace FourierRankQLB

/-- Sign vectors `σ ∈ {-1, +1}^d`, coded by `Bool`.

Augustino et al., *Near-Optimal Quantum Lower Bounds for Convex Optimization via Fourier Rank*, arXiv:2609.09035, §4.3, p. 28 and Theorem 5.1, p. 31.

**Formalization Note.** `true` codes `+1` and `false` codes `-1`; see `boolSign`. -/
abbrev SignVec (d : ℕ) : Type := Fin d → Bool

end FourierRankQLB



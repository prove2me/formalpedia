-- Prove2me | Definitions.Def_OnlineShadow_LogRate_OnlineProtocol
-- name    : OnlineShadow_LogRate_OnlineProtocol
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T04:03:47.300376+00:00
-- url     : https://prove2.me/theorems/d5128d6a-cd0e-4c4b-a097-8c3c95f7e057
-- title:
--   Online protocol on $n$ copies: one adaptive instrument per round
-- statement:
--   An **online protocol** holding $n$ copies of an unknown $d$-dimensional state acts on the register $(\mathbb C^d)^{\otimes n}$. In each round, after receiving the current observable $A$, it applies a quantum instrument with a finite set $O$ of outcomes, given by Kraus operators $K_o$ ($o\in O$) on $(\mathbb C^d)^{\otimes n}$ with
--   $$\sum_{o\in O}K_o^\dagger K_o=1,$$
--   and on outcome $o$ it announces an answer $\widehat\mu\in\mathbb R$. Both the Kraus operators and the answer may depend on the history of earlier (observable, outcome) pairs and on $A$, but not on the unknown state.
--
--   This is the learner of Definition 1.1. Several adaptive measurements within one round compose into one instrument, and internal randomness is a Kraus operator $\sqrt p\,1$, so the paper's Algorithm 1 is such a protocol.
--
--
--   **Formalization Note** The basis of $(\mathbb C^d)^{\otimes n}$ is indexed by `Fin n → Fin d`. There is no ancilla register. Completeness is required for every history and every observable, which rules out sub-normalized or super-normalized "probabilities".
-- source:
--   Chen, O'Donnell, Pelecanos, Wright, Online Shadow Tomography Matching the Classical Bounds, STOC 2027 submission (manuscript of November 2, 2026, sha256 90993723…dc3a9), Definition 1.1, p. 3

import Mathlib

open scoped Matrix

namespace OnlineShadow.LogRate

/-- An **online learning protocol** holding `n` copies of a `d`-dimensional state, i.e. acting on the
register `(ℂ^d)^{⊗n}`, whose basis is indexed by `Fin n → Fin d` (Chen, O'Donnell, Pelecanos, Wright, *Online Shadow Tomography Matching the Classical Bounds*, STOC 2027 submission (manuscript of November 2, 2026, sha256 90993723…dc3a9), Definition 1.1, p.3).
In each round, after receiving the current observable `A`, the protocol applies a quantum instrument
with finite outcome set `O`, given by Kraus operators `kraus h A o`, and answers `answer h A o` on
outcome `o`. Both may depend on the history `h` of earlier (observable, outcome) pairs and on `A`,
but not on the unknown state. The Kraus family is complete: `∑ₒ Kₒᴴ Kₒ = 1`.

**Formalization Note** Several adaptive measurements within one round compose into one instrument, and
internal randomness is a Kraus operator `√p • 1`, so every protocol of the paper's kind (in particular
Algorithm 1) has this form. There is no ancilla register. The round index is the length of the history. -/
structure OnlineProtocol (d n : ℕ) (O : Type) [Fintype O] where
  /-- Kraus operator of outcome `o` in the round with history `h` and current observable `A`. -/
  kraus : List (Matrix (Fin d) (Fin d) ℂ × O) → Matrix (Fin d) (Fin d) ℂ → O →
    Matrix (Fin n → Fin d) (Fin n → Fin d) ℂ
  /-- The answer `μ̂` announced on outcome `o`. -/
  answer : List (Matrix (Fin d) (Fin d) ℂ × O) → Matrix (Fin d) (Fin d) ℂ → O → ℝ
  /-- Completeness of every instrument. -/
  complete : ∀ h A, ∑ o, (kraus h A o)ᴴ * kraus h A o = 1

end OnlineShadow.LogRate



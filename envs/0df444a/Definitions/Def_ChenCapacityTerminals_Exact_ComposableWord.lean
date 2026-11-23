-- Prove2me | Definitions.Def_ChenCapacityTerminals_Exact_ComposableWord
-- name    : ChenCapacityTerminals_Exact_ComposableWord
-- status  : Definition
-- author  : @Mr Robbins
-- created : 2026-11-23T06:22:56.649585+00:00
-- url     : https://prove2.me/theorems/25348936-a041-43be-a925-b95f4298d6ba
-- title:
--   Clean-room calling convention for repeated oracle word-program runs
-- statement:
--   This module supplies the clean-room calling convention used when one bounded-word oracle program is invoked twice.
--
--   A composable program has the same execution, elapsed outside-oracle work and query trace from every memory that agrees with its fresh input memory on the nonnegative input prefix. Its final positive memory is likewise independent of stale workspace, and every negative cell is preserved. Consequently a caller may keep its own continuation data in negative scratch cells and rerun the program after replacing the raw input prefix, without assuming that old positive workspace is zero.
--
--   This is operational composition data, not a correctness or resource hypothesis about minimum cuts. It makes explicit the memory-hygiene property needed for the two oriented runs in the global-cut wrapper.
--
--   **Formalization Note** Equality of runs includes equality of the actual oracle trace and work; no asymptotic or semantic approximation is involved.
-- source:
--   Thomas Y. Chen, STOC 2027 submission #665, proof of Theorem 1.1, global reversal on PDF p.10 (paper p.9): the rooted algorithm is run on $G$ and $G^{\mathrm{rev}}$. This calling convention is the memory-hygiene interface needed to implement those two sequential runs in the mission's concrete WordRun model. https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/665.pdf#page=10

import Definitions.Def_ChenCapacityTerminals_Exact_CandidateReduction

set_option autoImplicit false

namespace ChenCapacityTerminals.Exact

/-- A clean-room calling convention for an oracle word program.  Besides its run from a
fresh `loadWords` memory, the program has the same run from any memory with the same
nonnegative input prefix.  It does not inspect stale positive workspace and it leaves all
negative cells untouched.  The positive part of the final memory is independent of stale
workspace.  This is the interface needed to invoke a program twice while storing the first
answer in negative scratch cells. -/
def ComposableWordProgram (P : WordProgram) : Prop :=
  ∀ {W : ℕ} (O : IntegerQuery → IntegerAnswer) (ws : List ℤ)
    (time : ℕ) (trace : List IntegerQuery) (out m : ℤ → BitVec W),
    WordRun P O 0 (TrulySubcubicAPSP.loadWords W ws) time trace out →
    (∀ a : ℤ, 0 ≤ a → a < (ws.length : ℤ) →
      m a = TrulySubcubicAPSP.loadWords W ws a) →
    ∃ out' : ℤ → BitVec W,
      WordRun P O 0 m time trace out' ∧
      (∀ a : ℤ, 0 ≤ a → out' a = out a) ∧
      (∀ a : ℤ, a < 0 → out' a = m a)

end ChenCapacityTerminals.Exact



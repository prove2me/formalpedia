-- Prove2me | Definitions.Def_MantriCVQ_Strategy
-- name    : MantriCVQ_Strategy
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T11:08:22.674095+00:00
-- url     : https://prove2.me/theorems/932edbe2-ffd5-49db-8cc7-61251ae7801e
-- title:
--   Prover strategies
-- statement:
--   A **prover strategy** maps the input, the transcript so far and the length of the next message to a probability distribution on messages of that length. No computational restriction is imposed.
--
--   **Formalization Note** A classical or quantum prover with private memory that exchanges classical messages induces such a strategy by the conditional law of its next message given the transcript, and the acceptance probability depends on the prover only through these conditional laws.
-- source:
--   Mantri, Classical Verification of Quantum Computation Beyond the Polynomial Hierarchy, arXiv:2610.37635 (PDF sha256 d1fab777…1d0b33), §3.1, p. 14 (PDF p. 16)

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Complexity

open QAlgorithms.Complexity

namespace MantriCVQ

/-- A prover strategy: given the input, the transcript so far and the length of the next message, a
probability distribution on messages of that length (Mantri, arXiv:2610.37635 (PDF sha256
d1fab777…1d0b33), §3.1, p. 14 (PDF p. 16)).

**Formalization Note** No computational restriction is imposed. A classical or quantum prover with
private memory that exchanges classical messages induces such a strategy, by taking the conditional
law of its next message given the transcript, and the acceptance probability depends on the prover
only through these conditional laws. -/
abbrev Strategy := (w : Str) → (hist : List Str) → (ℓ : ℕ) → PMF (Bits ℓ)

end MantriCVQ



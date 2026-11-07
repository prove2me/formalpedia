-- Prove2me | Definitions.Def_QAdvFew_PoQOracle_TwoMessage
-- name    : QAdvFew_PoQOracle_TwoMessage
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T10:53:18.450934+00:00
-- url     : https://prove2.me/theorems/cd0e696f-a95b-4c23-90f3-1ebbcf170b16
-- title:
--   Two-message protocol
-- statement:
--   A protocol is **two-message** if the verifier sends one message, the prover answers once and the verifier decides: one round at every length $n$.
-- source:
--   Goldin, Lombardi, Morimae, Quantum Advantage has Few Complexity Implications, arXiv:2611.05303v1, Theorem 1.3(5), p. 2 (PDF p. 4); Corollary 4.17, p. 32 (PDF p. 34)

import Mathlib
import Definitions.Def_QAdvFew_PoQOracle_QVerifier

open QAlgorithms.Complexity

namespace QAdvFew.PoQOracle

/-- A **two-message** protocol (Goldin, Lombardi, Morimae, *Quantum Advantage has Few Complexity
Implications*, arXiv:2611.05303v1, Theorem 1.3(5), p. 2 (PDF p. 4); Corollary 4.17, p. 32
(PDF p. 34)): one round at every length, so the verifier sends one message, the prover answers
once, and the verifier decides. -/
def TwoMessage (V : QVerifier) : Prop := ∀ n : ℕ, V.R.eval n = 1

end QAdvFew.PoQOracle



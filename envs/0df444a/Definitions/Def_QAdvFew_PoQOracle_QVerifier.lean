-- Prove2me | Definitions.Def_QAdvFew_PoQOracle_QVerifier
-- name    : QAdvFew_PoQOracle_QVerifier
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T10:52:18.387207+00:00
-- url     : https://prove2.me/theorems/9d30da55-c08c-4078-ad7d-1278dcf27d12
-- title:
--   QPT verifier
-- statement:
--   A **QPT verifier** has a polynomial number of rounds $R(n)$, a polynomial message length $\ell(n)$, and a QPT party that takes turns $0,\dots,R(n)$, the last of which produces its output bit.
-- source:
--   Goldin, Lombardi, Morimae, Quantum Advantage has Few Complexity Implications, arXiv:2611.05303v1, Definition 3.26, p. 19 (PDF p. 21)

import Mathlib
import Definitions.Def_QAdvFew_PoQOracle_QParty

open QAlgorithms.Complexity

namespace QAdvFew.PoQOracle

/-- A **QPT verifier** (Goldin, Lombardi, Morimae, *Quantum Advantage has Few Complexity
Implications*, arXiv:2611.05303v1, Definition 3.26, p. 19 (PDF p. 21): "Allowing `V^O` to be QPT
instead gives a quantumly-verifiable proof of quantumness"): a number of rounds `R(n)` and a message
length `ℓ(n)`, polynomials, and a `QParty` that takes turns `0, …, R(n)`, the last producing its
output bit. Uniformity and size are required where it is used (`IsQvPoQ`). -/
structure QVerifier where
  R : Polynomial ℕ
  ℓ : Polynomial ℕ
  Q : QParty (fun n => ℓ.eval n)

end QAdvFew.PoQOracle



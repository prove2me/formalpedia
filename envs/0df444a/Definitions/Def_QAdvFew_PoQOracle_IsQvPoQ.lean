-- Prove2me | Definitions.Def_QAdvFew_PoQOracle_IsQvPoQ
-- name    : QAdvFew_PoQOracle_IsQvPoQ
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T10:53:24.485612+00:00
-- url     : https://prove2.me/theorems/9f2fc735-c185-4192-ab74-ef3b7f189984
-- title:
--   Quantumly-verifiable proof of quantumness
-- statement:
--   A **quantumly-verifiable proof of quantumness** (qv-PoQ) is Definition 3.26 with a QPT verifier: both parties are uniform, polynomially bounded QPT parties, completeness error is negligible, and every nonuniform PPT classical prover is accepted with negligible probability.
-- source:
--   Goldin, Lombardi, Morimae, Quantum Advantage has Few Complexity Implications, arXiv:2611.05303v1, Definition 3.26, p. 19 (PDF p. 21)

import Mathlib
import Definitions.Def_QAdvFew_PoQOracle_QVerifier
import Definitions.Def_QAdvFew_PoQOracle_NUProver
import Definitions.Def_QAdvFew_PoQOracle_Negligible

open QAlgorithms.Complexity

namespace QAdvFew.PoQOracle

/-- A **quantumly-verifiable proof of quantumness** relative to `O` (Goldin, Lombardi, Morimae,
*Quantum Advantage has Few Complexity Implications*, arXiv:2611.05303v1, Definition 3.26, p. 19
(PDF p. 21), last sentence): Definition 3.26 with a QPT verifier. Both parties are uniform,
polynomially bounded `QParty`s; completeness is `1 − negl(n)` and soundness against every nonuniform
PPT classical prover is `negl(n)`. -/
def IsQvPoQ (O : Oracle) (V : QVerifier) (P : QParty (fun n => V.ℓ.eval n)) : Prop :=
  V.Q.Uniform ∧ V.Q.PolyBounded ∧ P.Uniform ∧ P.PolyBounded ∧
  Negligible (fun n => 1 - acceptProb (V.R.eval n) (V.ℓ.eval n) (V.Q.likV O n) (P.likP O n)) ∧
  ∀ P' : NUProver (fun n => V.ℓ.eval n),
    Negligible (fun n => acceptProb (V.R.eval n) (V.ℓ.eval n) (V.Q.likV O n) (P'.lik O n))

end QAdvFew.PoQOracle



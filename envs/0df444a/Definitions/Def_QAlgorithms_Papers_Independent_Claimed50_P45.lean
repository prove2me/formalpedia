-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P45
-- name    : QAlgorithms_Papers_Independent_Claimed50_P45
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-20T11:13:19.809466+00:00
-- url     : https://prove2.me/theorems/d7201cd0-c907-407b-a70b-02cd547fce7e
-- title:
--   Definitions for On Error Exponents in Quantum Hypothesis Testing
-- statement:
--   The objects the formalized statements of *On Error Exponents in Quantum Hypothesis Testing* (arXiv:quant-ph/0206151) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `pinchedTest`: PDF pp.4–5, (18)–(19): the strictly positive spectral projection of the SIGMA-pinched null state minus exp(n*a) times the alternative state. On the density inputs below the argument is Hermitian; zero eigenvalues are excluded. The definition also has a zero-copy value, unused in all rates.
-- source:
--   On Error Exponents in Quantum Hypothesis Testing, arXiv:quant-ph/0206151v3, https://arxiv.org/abs/quant-ph/0206151v3

import Mathlib
import Definitions.Def_QAlgorithms_Defs_ExtendedQuantumEntropy
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P28

/-! Ogawa–Hayashi, arXiv:quant-ph/0206151v3. Natural logarithms and positive
copy counts. The accepted Dependency50.P28 module supplies only already audited
matrix, pinching, probability and extended-rate definitions used here.
The source-ambiguity deferrals are recorded in the assigned unit's HARD.md. -/

noncomputable section

namespace QAlgorithms.Papers.Independent.Claimed50.P45

open scoped Matrix ComplexConjugate ComplexOrder BigOperators
open Filter Topology QAlgorithms
open QAlgorithms.Papers.Independent.Information100.P60 (Mat copies)
open QAlgorithms.Papers.Independent.Information100.P07 (positiveProjection)
open QAlgorithms.Papers.Independent.Dependency50.P28
  (LE pinch logNonnegativeExtended typeI accept scaled TestSequence)

attribute [local instance] Classical.propDecidable Classical.decEq

variable {I : Type} [Fintype I] [DecidableEq I]

/-- PDF pp.4–5, (18)–(19): the strictly positive spectral projection of the
SIGMA-pinched null state minus exp(n*a) times the alternative state.
On the density inputs below the argument is Hermitian; zero eigenvalues are
excluded. The definition also has a zero-copy value, unused in all rates. -/
def pinchedTest (rho sigma : Mat I) (n : ℕ) (a : ℝ) : Mat (Fin n → I) :=
  positiveProjection
    (pinch (copies n sigma) (copies n rho) -
      (Real.exp ((n : ℝ) * a) : ℂ) • copies n sigma)

/-- At threshold a=0, the comparison coefficient is exactly one, for every n. -/
example (rho sigma : Mat I) (n : ℕ) :
    pinchedTest rho sigma n 0 =
      positiveProjection (pinch (copies n sigma) (copies n rho) - copies n sigma) := by
  simp [pinchedTest]

end QAlgorithms.Papers.Independent.Claimed50.P45



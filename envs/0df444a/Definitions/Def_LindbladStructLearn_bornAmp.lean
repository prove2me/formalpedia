-- Prove2me | Definitions.Def_LindbladStructLearn_bornAmp
-- name    : LindbladStructLearn_bornAmp
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T21:55:14.101849+00:00
-- url     : https://prove2.me/theorems/efde8322-6cd8-49b0-90c8-901263210795
-- title:
--   Outcome probability of a Pauli experiment
-- statement:
--   Prepare $|A,v\rangle$, apply the superoperator $\Phi$, and measure in the eigenbasis of $B$: the outcome $w \in \{\pm1\}^n$ has probability
--
--   $$\mathrm{tr}\big(|B,w\rangle\langle B,w|\cdot\Phi(|A,v\rangle\langle A,v|)\big)$$
--
--   (the unnormalized trace). For a quantum channel $\Phi$ these numbers are a probability distribution over $w$; for a general $\Phi$ the expression is a complex number.
-- source:
--   Lewis–Tang–Wright, Learning the structure of open quantum systems, arXiv:2606.30358 (held version, sha256 0af12079…2eb52e), Eq. (2.30), p.16

import Mathlib
import Definitions.Def_LindbladTolerant_Testing_lindblad_model
import Definitions.Def_LindbladStructLearn_eigenProj

set_option autoImplicit false
open scoped ComplexOrder BigOperators Matrix ENNReal NNReal
noncomputable section

namespace LindbladStructLearn

open LindbladTolerant.Testing

/-- The outcome probability of an experiment (Lewis–Tang–Wright, *Learning the structure of open quantum systems*, arXiv:2606.30358 (held version, sha256 0af12079…2eb52e), Eq. (2.30), p.16):
`tr(|B,w⟩⟨B,w| · Φ(|A,v⟩⟨A,v|))` (plain trace).

**Formalization Note** Complex valued; for a quantum channel `Φ` it is a probability. -/
def bornAmp {n : ℕ} (Φ : Super (Qubits n) (Qubits n)) (A : Pauli n) (v : Qubits n)
    (B : Pauli n) (w : Qubits n) : ℂ :=
  (eigenProj B w * applySuper Φ (eigenProj A v)).trace

end LindbladStructLearn



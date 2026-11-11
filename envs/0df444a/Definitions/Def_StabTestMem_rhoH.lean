-- Prove2me | Definitions.Def_StabTestMem_rhoH
-- name    : StabTestMem_rhoH
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T09:09:54.601611+00:00
-- url     : https://prove2.me/theorems/b394e348-34a0-45dd-a4ff-ed57593dfbf4
-- title:
--   Haar moment $\rho_H=\mathbb E_\psi[\psi^{\otimes t}]$
-- statement:
--   The $t$-copy moment of a Haar random $n$-qubit pure state:
--
--   $$\rho_H=\mathbb E_{\psi\sim\mathrm{Haar}}\big[(|\psi\rangle\langle\psi|)^{\otimes t}\big].$$
--
--   By Fact B.1 it equals $\sum_{\pi\in S_t}R(\pi)/\prod_{j=0}^{t-1}(2^n+j)$.
--
--   **Formalization Note** The Haar law is the shared `haarTargetLaw` (normalized standard complex Gaussian vector, the unitarily invariant law on unit vectors); the expectation is an entrywise integral.
-- source:
--   Arunachalam, Schatzki, Optimal stabilizer testing and learning with limited quantum memory, arXiv:2607.02444 (version of 2 Nov 2026), §5.2, p. 38; Fact B.1, p. 64

import Definitions.Def_QAlgorithms_Defs_HaarTargetStates
import Definitions.Def_ObliviousRSP_pureState
import Definitions.Def_WildeQIT_Schumacher_tensorPow

namespace StabTestMem

open QAlgorithms MeasureTheory

/-- **The Haar moment `ρ_H = E_ψ[ψ^{⊗t}]`.** Arunachalam, Schatzki, *Optimal stabilizer testing and learning with limited quantum memory*, arXiv:2607.02444 (version of 2 Nov 2026), §5.2, p. 38, item 2 ("Haar random pure states
ρ_H := E_ψ[ψ^{⊗t}]"), Fact B.1, p. 64.

Entrywise Bochner integral of `|ψ⟩⟨ψ|^{⊗t}` against the Haar law of a random pure state.

**Formalization Note.** The Haar law is the shared `QAlgorithms.TwoBasisCertification.haarTargetLaw`
(a normalized standard complex Gaussian vector: the unitarily invariant probability law on unit
vectors). The integral is taken entry by entry because `Matrix` carries no global normed-space
instance; every entry is a bounded continuous function of `ψ` on the unit sphere, so it is
integrable. -/
noncomputable def rhoH (n t : ℕ) : Matrix (Fin t → Qubits n) (Fin t → Qubits n) ℂ :=
  Matrix.of fun X Y =>
    ∫ ψ, WildeQIT.Schumacher.tensorPow t (ObliviousRSP.pureState ψ) X Y ∂(TwoBasisCertification.haarTargetLaw n)

end StabTestMem



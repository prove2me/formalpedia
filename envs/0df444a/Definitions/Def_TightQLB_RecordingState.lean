-- Prove2me | Definitions.Def_TightQLB_RecordingState
-- name    : TightQLB_RecordingState
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:03:11.862265+00:00
-- url     : https://prove2.me/theorems/84f0130b-5a8c-4046-9b8f-867e3f19c707
-- title:
--   The states $\Psi_t$, $\Psi$ and the branches $\Psi_z=\Pi_z\Psi$ as elements of $\mathcal F$
-- statement:
--   Take $H=A\otimes E$ for a normal-form experiment in the Fourier ensemble. The state after $t$ queries and the unitary $U_t$ that follows them is the element $\Psi_t$ of $\mathcal F$ with $\Psi_t(f)=(U_tO^{\mathrm c}_fU_{t-1}\cdots O^{\mathrm c}_fU_0\otimes I_E)\psi_0$. The final state is $\Psi=\Psi_q$ and the output-$z$ branch is $\Psi_z=\Pi_z\Psi$, with $\Pi_z$ acting pointwise.
--
--   These are the vectors to which the operators of the recording representation are applied.
--
--   **Formalization Note** The query register is `Qubits n × Bool` and the oracle is `valueOracle fb`. A proved sanity check confirms `branchFn z fb` is the vector `branch (valueOracle fb) z` of (16).
-- source:
--   Bhateja, Esmaili, Mantri, Tight Query Lower Bounds for Quantum Sampling, with an Application to Certified Randomness, arXiv:2610.06721 (version of sha256 00a999f1…), §4.1, p. 23 (PDF p. 26); §4.2, p. 24 (PDF p. 27)

import Mathlib
import Definitions.Def_TightQLB_NormalForm
import Definitions.Def_TightQLB_Recording
open QAlgorithms

namespace TightQLB

/-!
# The states of a normal-form experiment as elements of `F`

Bhateja, Esmaili, Mantri, *Tight Query Lower Bounds for Quantum Sampling, with an Application to
Certified Randomness*, arXiv:2610.06721 (version of sha256 00a999f1…), §4.1, p.23 (PDF p.26), and
§4.2, p.24 (PDF p.27).

"The final state is `Ψ = U_q Q U_{q−1} Q ⋯ U₁ Q U₀ ψ₀`, where `ψ₀` is regarded as a constant function
and the `U_t` act pointwise. We write `Ψ_t` for the state after `t` queries and the unitary `U_t` that
follows them" (p.23), and `Ψ_z = Π_z Ψ` is the output-`z` branch (p.24).

**Formalization Note.** The Fourier ensemble: the query register is `X × T = Qubits n × Bool` and
the oracle is `valueOracle fb`. `H = A ⊗ E = Reg (Qubits n × Bool) W × E`. `stateFn t` is `f ↦ Ψ_t(f)` as an element of
`Fn n H`; `branchFn z` applies `Π_z ⊗ I_E` pointwise to the final state.
-/

namespace NormalForm

variable {n q : ℕ} {W E : Type} [Fintype W] [DecidableEq W] [Fintype E] [DecidableEq E]

/-- p.23 (PDF p.26): `Ψ_t ∈ F`, the function `f ↦ Ψ_t(f)`. -/
noncomputable def stateFn (B : NormalForm n q (Qubits n × Bool) W E) (t : Fin (q + 1)) : Fn n (Reg (Qubits n × Bool) W × E) :=
  fun fb => WithLp.ofLp (B.stateVec (valueOracle fb) t)

/-- p.21 (PDF p.24): the final state `Ψ = Ψ_q ∈ F`. -/
noncomputable def finalFn (B : NormalForm n q (Qubits n × Bool) W E) : Fn n (Reg (Qubits n × Bool) W × E) :=
  B.stateFn (Fin.last q)

/-- p.24 (PDF p.27): the output-`z` branch `Ψ_z = Π_z Ψ ∈ F`. -/
noncomputable def branchFn (B : NormalForm n q (Qubits n × Bool) W E) (z : Qubits n) : Fn n (Reg (Qubits n × Bool) W × E) :=
  pw (Matrix.kronecker (B.proj z) (1 : Matrix E E ℂ)) B.finalFn

end NormalForm

end TightQLB



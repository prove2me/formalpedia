-- Prove2me | Definitions.Def_UnitaryQIPPSPACE_unitaryPSPACEd
-- name    : UnitaryQIPPSPACE_unitaryPSPACEd
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:33:54.142987+00:00
-- url     : https://prove2.me/theorems/6032bba4-e482-4e84-b42c-c57b4127fe18
-- title:
--   The class $\mathsf{unitaryPSPACE}_\delta$ (Definition 2.8)
-- statement:
--   For $\delta:\mathbb N\to\mathbb R$, $\mathsf{unitaryPSPACE}_\delta$ is the set of unitary families $\{U_n\}$, $U_n$ acting on $n$ qubits, for which there is a space-uniform family of well-formed circuits $\{C_n\}$ with $n$ input and $n$ output qubits such that for all sufficiently large $n$
--   $$\sup_{|\psi\rangle\in\mathbb C^{2^n},\ \||\psi\rangle\|=1}\mathrm{TD}\big(C_n(|\psi\rangle\langle\psi|),\,U_n|\psi\rangle\langle\psi|U_n^\dagger\big)\le\delta(n).$$
--
--   These are the unitaries a polynomial-space quantum algorithm can apply, with synthesis error $\delta$, to every input state.
--
--   **Formalization Note** The supremum bound is written as the bound for every unit vector. $\delta$ is any real function (the paper takes $\delta:\mathbb N\to[0,1]$; Theorem 1.1 uses the index $c+\varepsilon+7\delta$, which may exceed $1$).
-- source:
--   He, Ou, Zhao, unitaryQIP = unitaryPSPACE, arXiv:2611.02819 (held version, sha256 9e357a00…ead793), Definition 2.8, p.12 (PDF p.14)

import Mathlib
import Definitions.Def_UnitaryQIPPSPACE_SpaceUniform
import Definitions.Def_DimFreeShadow_traceDistance
import Definitions.Def_ObliviousRSP_pureState
import Definitions.Def_ShadowBootstrap_braket
import Definitions.Def_UnitaryQIPPSPACE_conjBy

open Matrix

namespace UnitaryQIPPSPACE

/-- A **unitary family** `{U_n}_{n ∈ ℕ}` with `U_n` a unitary on `n` qubits. -/
abbrev UFam : Type := (n : ℕ) → Matrix.unitaryGroup (Bits n) ℂ

/-- **The class `unitaryPSPACE_δ`** (He, Ou, Zhao, *unitaryQIP = unitaryPSPACE*, arXiv:2611.02819,
held version sha256 9e357a00…, Definition 2.8, p. 12 (PDF p. 14)): "Let `δ : ℕ → [0, 1]`. The class
`unitaryPSPACE_δ` is the set of all sequences of unitary operators `{U_n}` such that each `U_n` acts
on `n` qubits, and there exists a space-uniform family of quantum circuits `{C_n}` satisfying, for
all sufficiently large `n`,
`sup_{|ψ⟩ ∈ ℂ^{2^n} : ‖|ψ⟩‖ = 1} TD(C_n(|ψ⟩⟨ψ|), U_n|ψ⟩⟨ψ|U_n†) ≤ δ(n)`."

**Formalization Note** `C_n` is a well-formed circuit with `n` input and `n` output qubits (init,
partial trace, `{H, T, CNOT}` gates and measurements allowed), space uniform with `n` input qubits.
The supremum bound is stated as the bound for every unit vector, which is equivalent. `δ` is any
real function, since Theorem 1.1 uses `unitaryPSPACE_{c+ε+7δ}` whose index may exceed `1`. -/
def unitaryPSPACEd (δ : ℕ → ℝ) : Set UFam :=
  {U | ∃ C : ℕ → Circuit, SpaceUniform C id ∧ (∀ n, (C n).WF n n) ∧
    ∃ N : ℕ, ∀ n ≥ N, ∀ ψ : Bits n → ℂ, ShadowBootstrap.IsUnitVec ψ →
      DimFreeShadow.traceDistance ((C n).chan n n (ObliviousRSP.pureState ψ)) (conjBy (U n : Matrix (Bits n) (Bits n) ℂ) (ObliviousRSP.pureState ψ))
        ≤ δ n}

end UnitaryQIPPSPACE



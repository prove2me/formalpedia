-- Prove2me | Definitions.Def_UnitaryQIPPSPACE_unitaryQIPc
-- name    : UnitaryQIPPSPACE_unitaryQIPc
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:35:13.118132+00:00
-- url     : https://prove2.me/theorems/9e5398b1-498d-4bea-897b-482eef566fd6
-- title:
--   The class $\mathsf{unitaryQIP}_{c,s,\delta}$ (Definition 2.10)
-- statement:
--   Let $c,s:\mathbb N\to[0,1]$ with $1-c(n)>s(n)$ for all $n$, and $\delta:\mathbb N\to[0,1]$. $\mathsf{unitaryQIP}_{c,s,\delta}$ is the set of unitary families $\{U_n\}$, $U_n$ on $n$ qubits, for which there is a time-uniform family of well-formed verifiers $\{V_n\}$ (input on the first $n$ qubits of $Z_{\mathrm{work}}$, output register of $n$ qubits) such that for all sufficiently large $n$:
--   1. **Completeness.** There is a prover $P^*_n$ such that for every $n$-qubit state $|\psi\rangle$, $\Pr[V_n(|\psi\rangle)\leftrightarrows P^*_n\text{ accepts}]\ge1-c(n)$.
--   2. **Soundness.** For every prover $P_n$ and every $n$-qubit state $|\psi\rangle$,
--   $$\Pr[V_n(|\psi\rangle)\leftrightarrows P_n\text{ accepts}]>s(n)\implies\mathrm{TD}(\rho_{P_n,\psi},U_n|\psi\rangle\langle\psi|U_n^\dagger)\le\delta(n),$$
--   where $\rho_{P_n,\psi}$ is the output conditioned on accepting.
--
--   Provers have private registers of any size, starting in $|0\cdots0\rangle$; the number of rounds is polynomial (Definition 2.6).
--
--   **Formalization Note** The standing condition $1-c(n)>s(n)$ for all $n$ is part of the set: when it fails, the paper's class is undefined and this set is empty.
-- source:
--   He, Ou, Zhao, unitaryQIP = unitaryPSPACE, arXiv:2611.02819 (held version, sha256 9e357a00…ead793), Definition 2.10, p.12 (PDF p.14)

import Mathlib
import Definitions.Def_UnitaryQIPPSPACE_run
import Definitions.Def_UnitaryQIPPSPACE_TimeUniformVerifiers
import Definitions.Def_UnitaryQIPPSPACE_unitaryPSPACEd
import Definitions.Def_DimFreeShadow_traceDistance
import Definitions.Def_ObliviousRSP_pureState
import Definitions.Def_ShadowBootstrap_braket
import Definitions.Def_UnitaryQIPPSPACE_conjBy

open Matrix

namespace UnitaryQIPPSPACE

/-- **The class `unitaryQIP_{c,s,δ}`** (He, Ou, Zhao, *unitaryQIP = unitaryPSPACE*,
arXiv:2611.02819, held version sha256 9e357a00…, Definition 2.10, p. 12 (PDF p. 14)): "Let
`c, s : ℕ → [0, 1]` be the completeness error and soundness threshold and suppose that
`1 − c(n) > s(n)` for all `n ∈ ℕ`. For `δ : ℕ → [0, 1]` and `ℓ : ℕ → ℕ`, the class
`unitaryQIP_{c,s,δ}[ℓ]` is the set of all sequences of unitary operators `{U_n}` such that each `U_n`
acts on `n` qubits, and there exists a time-uniform family of `ℓ(n)`-round quantum verifiers `{V_n}`
such that for sufficiently large `n`,
• Completeness. There exists a prover `P*_n` such that for all `n`-qubit states `|ψ⟩`,
  `Pr[V_n(|ψ⟩) ⇆ P*_n accepts] ≥ 1 − c(n)`.
• Soundness. For every prover `P_n` and every `n`-qubit state `|ψ⟩`,
  `Pr[V_n(|ψ⟩) ⇆ P_n accepts] > s(n) ⟹ TD(ρ_{P_n,ψ}, U_n|ψ⟩⟨ψ|U_n†) ≤ δ(n)`,
where `ρ_{P_n,ψ}` is the output of `V_n(|ψ⟩) ⇆ P_n` conditioned on accepting.
Unless otherwise stated, `unitaryQIP_{c,s,δ}` denotes the class with polynomially many rounds."

Here: the verifiers are well formed, `Z_work` holds at least the `n` input qubits, `Z_out` has `n`
qubits, the family is time uniform (Definition 2.6, which bounds the rounds by a polynomial), and a
prover is any `y ∈ ℕ` private qubits with any unitary on `M ⊗ Y`, whose private register starts in
`|0⋯0⟩`. Completeness is `∃` prover `∀` unit `ψ`; soundness is `∀` prover `∀` unit `ψ`.

**Formalization Note** The standing condition `1 − c(n) > s(n)` for all `n` is part of the class:
when it fails the paper's class is undefined, and this set is empty. -/
def unitaryQIPc (c s δ : ℕ → ℝ) : Set UFam :=
  {U | (∀ n, s n < 1 - c n) ∧
    ∃ V : ℕ → Verifier, (∀ n, (V n).WF ∧ n ≤ (V n).w ∧ (V n).o = n) ∧ TimeUniformVerifiers V ∧
    ∃ N : ℕ, ∀ n ≥ N,
      (∃ P : Prover (V n).m, ∀ ψ : Bits n → ℂ, ShadowBootstrap.IsUnitVec ψ →
        1 - c n ≤ acceptProb (V n) (P.U : Matrix _ _ ℂ) n ψ (zeroState P.y)) ∧
      (∀ P : Prover (V n).m, ∀ ψ : Bits n → ℂ, ShadowBootstrap.IsUnitVec ψ →
        s n < acceptProb (V n) (P.U : Matrix _ _ ℂ) n ψ (zeroState P.y) →
        DimFreeShadow.traceDistance (outTo (V n) n (condOutput (V n) (P.U : Matrix _ _ ℂ) n ψ (zeroState P.y)))
          (conjBy (U n : Matrix (Bits n) (Bits n) ℂ) (ObliviousRSP.pureState ψ)) ≤ δ n)}

end UnitaryQIPPSPACE



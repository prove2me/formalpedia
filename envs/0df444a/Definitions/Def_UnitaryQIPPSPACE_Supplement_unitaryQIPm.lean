-- Prove2me | Definitions.Def_UnitaryQIPPSPACE_Supplement_unitaryQIPm
-- name    : UnitaryQIPPSPACE_Supplement_unitaryQIPm
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T06:43:51.288204+00:00
-- url     : https://prove2.me/theorems/d0d9f51c-f5f6-40f1-9244-3f73ab5acb51
-- title:
--   Multi-copy, round-bounded class $\mathsf{unitaryQIP}^{(m)}_{c,s,\delta}[\ell]$
-- statement:
--   Let $m:\mathbb N\to\mathbb N$, $\ell\in\mathbb N$ and $c,s,\delta:\mathbb N\to\mathbb R$. The class $\mathsf{unitaryQIP}^{(m)}_{c,s,\delta}[\ell]$ is defined exactly like $\mathsf{unitaryQIP}_{c,s,\delta}$ (Definition 2.10, the published base class) except for two changes:
--
--   1. the verifier $V_n$ is run on the input $|\psi\rangle^{\otimes m(n)}$ — $m(n)$ copies of the $n$-qubit input state — held on the first $m(n)\cdot n$ qubits of its work register;
--   2. every $V_n$ acts in at most $\ell$ rounds.
--
--   Thus a unitary family $\{U_n\}$, $U_n$ acting on $n$ qubits, belongs to the class when $1-c(n)>s(n)$ for all $n$ and there is a time-uniform family of verifiers $\{V_n\}$ with $n$-qubit output registers such that, for all sufficiently large $n$:
--
--   - **Completeness.** Some prover $P^*_n$ satisfies $\Pr[V_n(|\psi\rangle^{\otimes m(n)})\leftrightarrows P^*_n\text{ accepts}]\ge 1-c(n)$ for every $n$-qubit state $|\psi\rangle$.
--   - **Soundness.** For every prover $P_n$ and every $n$-qubit state $|\psi\rangle$,
--   $$\Pr[V_n(|\psi\rangle^{\otimes m(n)})\leftrightarrows P_n\text{ accepts}]>s(n)\ \Longrightarrow\ \mathrm{TD}\big(\rho_{P_n,\psi},\,U_n|\psi\rangle\langle\psi|U_n^\dagger\big)\le\delta(n),$$
--   where $\rho_{P_n,\psi}$ is the $n$-qubit output conditioned on acceptance.
--
--   This is the class on the right-hand side of Theorem 1.4, before the union over copy numbers.
--
--   **Formalization Note** Copy $j$ ($j=0,\dots,m(n)-1$) occupies qubits $jn,\dots,jn+n-1$ of the $m(n)\cdot n$-qubit input. Provers have any number of private qubits, start from $|0\cdots0\rangle$ and apply any unitary, as in the base class. The round bound $\le\ell$ is imposed for every $n$.
-- source:
--   He, Ou, Zhao, unitaryQIP = unitaryPSPACE, arXiv:2611.02819 (held version, sha256 9e357a00…ead793), Definitions 2.10 and 2.11, p.12 (PDF p.14); notation of Theorem 1.4, p.38 (PDF p.40)

import Mathlib
import Definitions.Def_UnitaryQIPPSPACE_unitaryQIPc

open Matrix

namespace UnitaryQIPPSPACE

namespace Supplement

/-- The **`m`-fold tensor power** `|ψ⟩^{⊗m}` of an `n`-qubit vector `ψ`, as a vector on `m · n`
qubits: copy `j` (`j = 0, …, m − 1`) occupies qubits `j·n, j·n + 1, …, j·n + n − 1`, so the
amplitude of the basis label `x` is `∏_j ψ(x_{j·n}, …, x_{j·n+n−1})`.

**Formalization Note** The qubit `j·n + i` of the `m · n`-qubit register is
`finProdFinEquiv (j, i)` (value `i + n·j`). For `m = 0` this is the vector `1` on zero qubits. -/
def copiesVec (n m : ℕ) (ψ : Bits n → ℂ) : Bits (m * n) → ℂ :=
  fun x => ∏ j : Fin m, ψ (fun i => x (finProdFinEquiv (j, i)))

/-- **The multi-copy, round-bounded class `unitaryQIP^{(m)}_{c,s,δ}[ℓ]`** (He, Ou, Zhao,
*unitaryQIP = unitaryPSPACE*, arXiv:2611.02819, held version sha256 9e357a00…, Definitions 2.10
and 2.11, p. 12 (PDF p. 14), and the gloss of Theorem 1.4, p. 38 (PDF p. 40)).

Definition 2.11: "For `r : ℕ → ℕ`, the class `unitaryQIP^{(r)}_{c,s,δ}` is defined in the same way
as `unitaryQIP_{c,s,δ}` except that the verifier `V_n` is run on input `|ψ⟩^{⊗r(n)}`. In
particular, `unitaryQIP^{(1)}_{c,s,δ} = unitaryQIP_{c,s,δ}`." Theorem 1.4: "in the notation
`unitaryQIP^{(m)}[ℓ]`, the verifier receives `m(n)` copies of the input state and acts in at most
`ℓ ∈ ℕ` rounds during the interaction."

`unitaryQIPm m ℓ c s δ` is the base class `unitaryQIPc c s δ` (Definition 2.10, published as
`UnitaryQIPPSPACE.unitaryQIPc`) with exactly two changes:
1. the verifier `V_n` is run on the `m(n) · n`-qubit input `|ψ⟩^{⊗m(n)}` (`copiesVec`), which
   it holds on the first `m(n) · n` qubits of `Z_work`; completeness and soundness range over
   every unit vector `ψ` on `n` qubits, and the `n`-qubit output conditioned on acceptance is
   compared with `U_n |ψ⟩⟨ψ| U_n†` for that single `ψ`;
2. every `V_n` has at most `ℓ` rounds (`(V n).rounds.length ≤ ℓ`).
Everything else — the standing condition `1 − c(n) > s(n)` for all `n`, well-formedness,
`Z_out` of `n` qubits, time uniformity (Definition 2.6), provers with any number of private
qubits and any unitary on `M ⊗ Y` starting from `|0⋯0⟩`, `∃ N, ∀ n ≥ N` — is as in the base
class.

**Formalization Note** The round bound holds for every `n` (the family is arbitrary below the
threshold `N`, so this is no restriction beyond the paper's). -/
def unitaryQIPm (m : ℕ → ℕ) (ℓ : ℕ) (c s δ : ℕ → ℝ) : Set UFam :=
  {U | (∀ n, s n < 1 - c n) ∧
    ∃ V : ℕ → Verifier,
      (∀ n, (V n).WF ∧ m n * n ≤ (V n).w ∧ (V n).o = n ∧ (V n).rounds.length ≤ ℓ) ∧
      TimeUniformVerifiers V ∧
    ∃ N : ℕ, ∀ n ≥ N,
      (∃ P : Prover (V n).m, ∀ ψ : Bits n → ℂ, ShadowBootstrap.IsUnitVec ψ →
        1 - c n ≤ acceptProb (V n) (P.U : Matrix _ _ ℂ) (m n * n) (copiesVec n (m n) ψ)
          (zeroState P.y)) ∧
      (∀ P : Prover (V n).m, ∀ ψ : Bits n → ℂ, ShadowBootstrap.IsUnitVec ψ →
        s n < acceptProb (V n) (P.U : Matrix _ _ ℂ) (m n * n) (copiesVec n (m n) ψ)
          (zeroState P.y) →
        DimFreeShadow.traceDistance
          (outTo (V n) n (condOutput (V n) (P.U : Matrix _ _ ℂ) (m n * n)
            (copiesVec n (m n) ψ) (zeroState P.y)))
          (conjBy (U n : Matrix (Bits n) (Bits n) ℂ) (ObliviousRSP.pureState ψ)) ≤ δ n)}

end Supplement

end UnitaryQIPPSPACE



-- Prove2me | Definitions.Def_QuantumPRC_IsLocalNoise
-- name    : QuantumPRC_IsLocalNoise
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T11:35:49.873011+00:00
-- url     : https://prove2.me/theorems/046c3c64-8444-488b-8b2c-0e9555b78d01
-- title:
--   Operator weight (20) and $t$-local noise channels (Definition 3.7)
-- statement:
--   Every operator $E$ on $m$ qubits has a unique Pauli expansion $E=\sum_{x,z\in\{0,1\}^m}\alpha_{x,z}X^xZ^z$, with $\alpha_{x,z}=2^{-m}\operatorname{Tr}\big((X^xZ^z)^\dagger E\big)$. Its **weight** is
--
--   $$
--   \mathrm{wt}(E):=\max_{x,z:\ \alpha_{x,z}\neq 0}\mathrm{wt}(X^xZ^z)\qquad(20)
--   $$
--
--   ($0$ for $E=0$). For functions $t,m:\mathbb N\to\mathbb N$, a family $\{\mathcal E_\lambda\}_{\lambda}$ of CPTP maps on $m(\lambda)$ qubits is **$t$-local noise** if there is a family $\{\tilde{\mathcal E}_\lambda\}_\lambda$ of CPTP maps on $m(\lambda)$ qubits such that each $\tilde{\mathcal E}_\lambda$ admits a Kraus representation $\tilde{\mathcal E}_\lambda(\cdot)=\sum_iE_i(\cdot)E_i^\dagger$ with $\mathrm{wt}(E_i)\le t(\lambda)$ for all $i$, and
--
--   $$
--   \|\mathcal E_\lambda-\tilde{\mathcal E}_\lambda\|_\diamond\le\mathsf{negl}(\lambda).
--   $$
--
--   The family $\mathcal E$ is arbitrary: no efficiency or uniformity is required. This is the noise model against which PRICs are robust.
--
--   **Formalization Note** CPTP maps are the published `WildeQIT.QChannel` (a finite Kraus family with $\sum_iK_i^\dagger K_i=I$; every CPTP map in finite dimension has one); "admits a Kraus representation" is expressed by quantifying over $\tilde{\mathcal E}_\lambda$ together with its Kraus family.
-- source:
--   Hsieh, Yamada, Quantum Pseudorandom Error-Correcting Codes, arXiv:2609.38986 (version of October 29, 2026, sha256 6901b59d1cbcf0183f98f2951ab17c9baae4e341e5b2a3c767d1ae93e77976db), Eq. (20) and Definition 3.7, p.17

import Mathlib
import Definitions.Def_QuantumPRC_diamondDist
import Definitions.Def_QuantumPRC_Negligible
import Definitions.Def_WildeQIT_QChannel

open Matrix

namespace QuantumPRC

/-- The coefficient `α_{x,z}` of `X^x Z^z` in the Pauli expansion `E = Σ_{x,z} α_{x,z} X^x Z^z` of an
operator `E` on `m` qubits: `α_{x,z} = 2^{-m} Tr((X^x Z^z)† E)` (the Paulis are an orthogonal basis
for the Hilbert–Schmidt inner product, so the expansion is unique). -/
noncomputable def pauliCoeff {m : ℕ} (E : Matrix (Bits m) (Bits m) ℂ) (x z : Bits m) : ℂ :=
  (2 : ℂ)⁻¹ ^ m * Matrix.trace ((pauliXZ x z)ᴴ * E)

/-- **Weight of an operator**, Eq. (20). Hsieh, Yamada, arXiv:2609.38986 (sha256 6901b59d…),
§3.4, p.17: "Given an operator `E` acting on `m` qubits, write its unique Pauli expansion as
`E = Σ_{x,z∈{0,1}^m} α_{x,z} X^x Z^z`. We then define `wt(E) := max_{x,z : α_{x,z} ≠ 0} wt(X^x Z^z)`."

**Formalization Note.** The maximum over an empty index set (`E = 0`) is `0`. -/
noncomputable def pauliWt {m : ℕ} (E : Matrix (Bits m) (Bits m) ℂ) : ℕ := by
  classical
  exact ((Finset.univ.filter fun p : Bits m × Bits m => pauliCoeff E p.1 p.2 ≠ 0).sup
    fun p => pauliWeight p.1 p.2)

/-- **Local noise channel**, Definition 3.7. Hsieh, Yamada, arXiv:2609.38986 (sha256 6901b59d…),
p.17: "For functions `t, m : ℕ → ℕ`, a family `{E_λ}_{λ∈ℕ}` of CPTP maps `E_λ` from `m(λ)` qubits to
`m(λ)` qubits is called `t`-local noise if there exists a family `{Ẽ_λ}_{λ∈ℕ}` of CPTP maps `Ẽ_λ` from
`m(λ)` qubits to `m(λ)` qubits such that each `Ẽ_λ` admits a Kraus representation
`Ẽ_λ(·) = Σ_i E_i(·)E_i†` with `wt(E_i) ≤ t(λ)` for all `i`, and `‖E_λ − Ẽ_λ‖⋄ ≤ negl(λ)`."

**Formalization Note.** CPTP maps are `WildeQIT.QChannel` values (a finite Kraus family with
`Σ K†K = I`); every CPTP map in finite dimension has one. "Admits a Kraus representation" is
expressed by quantifying over `Ẽ_λ` together with its Kraus family. The family `E` is arbitrary: no
efficiency, no uniformity. -/
def IsLocalNoise (t m : ℕ → ℕ)
    (E : ∀ lam, WildeQIT.QChannel (Bits (m lam)) (Bits (m lam))) : Prop :=
  ∃ Et : ∀ lam, WildeQIT.QChannel (Bits (m lam)) (Bits (m lam)),
    (∀ lam (i : (Et lam).ι), pauliWt ((Et lam).K i) ≤ t lam) ∧
    ∃ ν : ℕ → ℝ, Negligible ν ∧ ∀ lam, diamondDist (E lam).apply (Et lam).apply ≤ ν lam

end QuantumPRC



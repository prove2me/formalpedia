-- Prove2me | Definitions.Def_ShallowShadows_ShadowNorm_IsClifford
-- name    : ShallowShadows_ShadowNorm_IsClifford
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:32:15.789256+00:00
-- url     : https://prove2.me/theorems/27308763-6c09-4904-aa0b-b474df0e9f7e
-- title:
--   Clifford unitaries: $UP^\lambda U^\dagger = \pm P^\mu$
-- statement:
--   A $k$-qubit unitary $U$ is **Clifford** when it maps every Pauli string to a Pauli string up to a sign: for every $\lambda$ there is $\mu$ with
--
--   $$
--   U P^\lambda U^\dagger = P^\mu \quad\text{or}\quad U P^\lambda U^\dagger = -P^\mu.
--   $$
--
--   Since Pauli strings are Hermitian, $\pm1$ are the only possible phases, and this is the unitary normalizer of the Pauli group, the Clifford group $\mathcal C_k$.
--
--   **Formalization Note** Modelled on the published `QAlgorithms.Clifford.normalizer`, but on the bit-string carrier of the HKP measurement channel.
-- source:
--   Bertoni, Haferkamp, Hinsche, Ioannou, Eisert, Pashayan, Shallow shadows: Expectation estimation using low-depth random Clifford circuits, arXiv:2209.12924v3, §II, p. 3

import Mathlib
import Definitions.Def_ShallowShadows_ShadowNorm_pauli

open ClassicalShadow.Linear

namespace ShallowShadows.ShadowNorm

/-- Bertoni, Haferkamp, Hinsche, Ioannou, Eisert, Pashayan, *Shallow shadows: Expectation
estimation using low-depth random Clifford circuits*, arXiv:2209.12924v3, §II, p. 3: "We use
`𝒞_n` to denote the `n`-qubit Clifford group". A unitary `U` on `k` qubits is Clifford when it maps
every Pauli string to a Pauli string up to a sign: for every `λ` there is `μ` with
`U P^λ U† = P^μ` or `U P^λ U† = −P^μ`.

**Formalization Note.** Every `P^λ` is Hermitian, so `U P^λ U†` is Hermitian and the only phases a
conjugated Pauli string can carry are `±1`; this is the unitary normalizer of the Pauli group. The
definition follows the published `QAlgorithms.Clifford.normalizer`, on `Bits k` instead of
`Fin k → Bool`. -/
def IsClifford {k : ℕ} (U : Matrix.unitaryGroup (Bits k) ℂ) : Prop :=
  ∀ lam : Bits k × Bits k, ∃ mu : Bits k × Bits k,
    (U : Op k) * pauli lam * star (U : Op k) = pauli mu ∨
      (U : Op k) * pauli lam * star (U : Op k) = -pauli mu

end ShallowShadows.ShadowNorm



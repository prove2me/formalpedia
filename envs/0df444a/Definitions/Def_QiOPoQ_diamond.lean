-- Prove2me | Definitions.Def_QiOPoQ_diamond
-- name    : QiOPoQ_diamond
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:02:52.809762+00:00
-- url     : https://prove2.me/theorems/dbffadd2-4fac-4b49-8bca-a8a23f65efc1
-- title:
--   Diamond distance of maps and of circuits
-- statement:
--   For two maps $\Phi,\Psi$ from $n$ to $m$ qubits,
--
--   $$
--   \|\Phi-\Psi\|_\diamond = \sup_{|\psi\rangle}\big\|(\mathrm{id}_R\otimes\Phi)(|\psi\rangle\langle\psi|)-(\mathrm{id}_R\otimes\Psi)(|\psi\rangle\langle\psi|)\big\|_1,
--   $$
--
--   the supremum over unit vectors on a reference register $R$ of the size of the input together with the input, $\|\cdot\|_1$ being the trace norm. For two circuits with the same numbers of input and output qubits, $\|C-D\|_\diamond$ is the distance of their channels.
--
--   **Formalization Note** There is no factor $\tfrac12$: the paper fixes no normalization and only uses bounds of the form $\le\mathrm{negl}(\lambda)$, which a constant factor does not affect. For channels, pure states with a same-size reference attain the full supremum. The distance is applied only to channels of circuits and to $X^b(\cdot)$, where every value is at most $2$, so the real supremum is the true one.
-- source:
--   Gheorghiu, Gupte, Havlíček, Liu, Verifiable Quantum Advantage and Computation via Quantum Circuit Obfuscation, arXiv:2609.40289 (sha256 fe2f9210…), §3.1–3.2, pp.13–14

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Channel
import Definitions.Def_WildeQIT_traceNorm
import Definitions.Def_QiOPoQ_chan

set_option autoImplicit false

namespace QiOPoQ

open QAlgorithms

variable {G : GateSet}

/-- **Diamond distance** `∥Φ − Ψ∥⋄` of two maps from `n` to `m` qubits. Gheorghiu, Gupte,
Havlíček, Liu, *Verifiable Quantum Advantage and Computation via Quantum Circuit Obfuscation*,
arXiv:2609.40289 (sha256 fe2f9210…), §3.1–3.2, pp.13–14 ("∥C − X^{b_C}(·)∥⋄ ≤ negl(λ)",
"∥Ĉ − C∥⋄ ≤ negl(λ)"; the paper does not define the norm further):
`∥Φ − Ψ∥⋄ = max_ψ ∥(id_R ⊗ Φ)(|ψ⟩⟨ψ|) − (id_R ⊗ Ψ)(|ψ⟩⟨ψ|)∥₁`, the maximum over pure states on a
reference register `R` of the same size as the input, `∥·∥₁` the trace norm.

**Formalization Note.** No factor `½`: the paper fixes no normalization and only uses bounds
`≤ negl(λ)`, which are insensitive to a constant factor. A same-size reference and pure states
attain the supremum for channels. The real supremum is applied only to channels of circuits and
to `X^b(·)`, for which every value is at most `2`, so it is the printed maximum (on an unbounded
set Lean's `⨆` would be `0`). `id_R ⊗ Φ` and `∥·∥₁` are the published
`QAlgorithms.idTensorSuperop` and `WildeQIT.traceNorm`. -/
noncomputable def diamond {n m : ℕ} (Φ Ψ : Superop (Fin n → Bool) (Fin m → Bool)) : ℝ :=
  ⨆ ψ : {v : (Fin n → Bool) × (Fin n → Bool) → ℂ // ∑ p, Complex.normSq (v p) = 1},
    WildeQIT.traceNorm
      (idTensorSuperop (R := Fin n → Bool) Φ (Matrix.vecMulVec ψ.1 (star ψ.1)) -
        idTensorSuperop (R := Fin n → Bool) Ψ (Matrix.vecMulVec ψ.1 (star ψ.1)))


/-- `∥C − D∥⋄` for two circuits with the same numbers of input and output qubits (Definition 3.1,
p.14: "∥Ĉ − C∥⋄"; Definition 3.2, p.14: "∥C_{0,λ} − C_{1,λ}∥⋄"). Equality of `(n_in, n_out)` is
stated alongside wherever `circDist` is used. -/
noncomputable def circDist (C D : Circ G) : ℝ :=
  diamond (chanAs C D.nin D.out.length) (chan D)

end QiOPoQ



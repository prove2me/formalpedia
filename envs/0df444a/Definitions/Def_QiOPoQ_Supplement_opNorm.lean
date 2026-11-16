-- Prove2me | Definitions.Def_QiOPoQ_Supplement_opNorm
-- name    : QiOPoQ_Supplement_opNorm
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T05:01:08.910456+00:00
-- url     : https://prove2.me/theorems/31029ae0-96db-484f-8e87-cfd52b739b4e
-- title:
--   The operator norm of a complex matrix
-- statement:
--   The operator norm $\|M\|=\max_{\|v\|_2=1}\|Mv\|_2$, the norm in the definition of tidy unitary circuits ("Here the norm is the operator norm") and in the universality condition.
--
--   **Formalization Note** The supremum is over a bounded set of values, so it is the true maximum.
-- source:
--   Gheorghiu, Gupte, Havlíček, Liu, Verifiable Quantum Advantage and Computation via Quantum Circuit Obfuscation, arXiv:2609.40289 (sha256 fe2f9210…), §3.1, p.13 (tidy unitary circuits)

import Mathlib

set_option autoImplicit false

namespace QiOPoQ.Supplement

/-- **The operator norm** `∥M∥ = max_{∥v∥₂ = 1} ∥Mv∥₂` of a complex matrix (Gheorghiu, Gupte,
Havlíček, Liu, *Verifiable Quantum Advantage and Computation via Quantum Circuit Obfuscation*,
arXiv:2609.40289, sha256 fe2f9210…, §3.1, p.13, tidy unitary circuits: "Here the norm is the
operator norm").

**Formalization Note.** The values `∥Mv∥₂` over unit vectors are bounded (finite matrices), so the
real supremum is the true maximum; for an empty column index the norm is `0`, the norm of the map
from the zero space. -/
noncomputable def opNorm {m k : Type*} [Fintype m] [Fintype k] (M : Matrix m k ℂ) : ℝ :=
  ⨆ v : {v : k → ℂ // ∑ i, Complex.normSq (v i) = 1},
    Real.sqrt (∑ i, Complex.normSq ((M.mulVec v.1) i))

end QiOPoQ.Supplement



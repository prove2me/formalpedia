-- Prove2me | Definitions.Def_QiOPoQ_samplerTV
-- name    : QiOPoQ_samplerTV
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:02:16.177624+00:00
-- url     : https://prove2.me/theorems/f52fac01-81b6-4bf7-880c-ad163da15041
-- title:
--   Total variation distance between two samplers
-- statement:
--   For two classical PPT samplers $S_0,S_1$ run on $1^\lambda$, the total variation distance of their output laws $D_{0,\lambda},D_{1,\lambda}$:
--
--   $$
--   \mathrm{TV}(D_{0,\lambda},D_{1,\lambda})=\sup_{E}\big(D_{0,\lambda}(E)-D_{1,\lambda}(E)\big),
--   $$
--
--   the supremum over all sets $E$ of strings. Both laws have finite support, and the values lie in $[-1,1]$, so the real supremum is the true one.
-- source:
--   Gheorghiu, Gupte, Havlíček, Liu, Verifiable Quantum Advantage and Computation via Quantum Circuit Obfuscation, arXiv:2609.40289 (sha256 fe2f9210…), proof of Lemma 4.5, p.20

import Mathlib
import Definitions.Def_QAlgorithms_ClassicalUnaryInput
import Definitions.Def_QiOPoQ_UPPT

set_option autoImplicit false

namespace QiOPoQ

open QAlgorithms.Complexity

/-- The total variation distance between the output distributions of two samplers on `1^λ`,
`TV(D_{0,λ}, D_{1,λ}) = sup_E (D_{0,λ}(E) − D_{1,λ}(E))` (proof of Lemma 4.5, p.20: "these
distributions are statistically far, with total variation distance at least 1 − negl(λ)").
**Formalization Note.** The values lie in `[−1, 1]` and the index type is nonempty, so the real
supremum is the true one; it is attained since both laws have finite support. -/
noncomputable def samplerTV (S0 S1 : UPPT) (n : ℕ) : ℝ :=
  ⨆ E : Set Str, (S0.expect (unary n) (E.indicator 1) - S1.expect (unary n) (E.indicator 1))

end QiOPoQ



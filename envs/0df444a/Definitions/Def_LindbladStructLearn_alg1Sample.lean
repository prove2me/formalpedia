-- Prove2me | Definitions.Def_LindbladStructLearn_alg1Sample
-- name    : LindbladStructLearn_alg1Sample
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T21:56:50.256143+00:00
-- url     : https://prove2.me/theorems/3b85b3ac-5bff-4a13-b7d6-8cec37f130d3
-- title:
--   Single-sample estimate $E^{(i)}_{P_1,P_2}$ of Algorithm 1
-- statement:
--   For a pair $\overline P$ and one experiment's data $(A, v, B, w)$, put $R = A^{S_{\overline P}}\otimes I^{\overline{S_{\overline P}}}$ and $Z = B^{S_{\overline P}}\otimes I^{\overline{S_{\overline P}}}$. If $Z = \mathcal P(P_2RP_1)$ the estimate is
--
--   $$E_{P_1,P_2} = 4^{s_{\overline P}}\cdot c(P_2RP_1)\cdot\chi_{S_R}(v)\cdot\chi_{S_Z}(w),$$
--
--   and otherwise it is $0$.
-- source:
--   Lewis–Tang–Wright, Learning the structure of open quantum systems, arXiv:2606.30358 (held version, sha256 0af12079…2eb52e), Algorithm 1, Eqs. (2.27)–(2.28), p.17

import Mathlib
import Definitions.Def_LindbladStructLearn_restrict
import Definitions.Def_LindbladStructLearn_pairSupport
import Definitions.Def_LindbladStructLearn_pauliProd
import Definitions.Def_LindbladStructLearn_pauliPhase
import Definitions.Def_LindbladStructLearn_boolChar

set_option autoImplicit false
open scoped ComplexOrder BigOperators Matrix ENNReal NNReal
noncomputable section

namespace LindbladStructLearn

open LindbladTolerant.Testing

/-- The single-sample estimate of Algorithm 1 (Lewis–Tang–Wright, *Learning the structure of open quantum systems*, arXiv:2606.30358 (held version, sha256 0af12079…2eb52e), Eqs. (2.27)–(2.28), p.17): with
`R = A^(S_P̄) ⊗ I` and `Z = B^(S_P̄) ⊗ I`, if `Z = 𝒫(P₂RP₁)` then
`E_(P₁,P₂) = 4^(s_P̄) · c(P₂RP₁) · χ_(S_R)(v) · χ_(S_Z)(w)`, and `0` otherwise. -/
def alg1Sample {n : ℕ} (P : Pauli n × Pauli n) (A : Pauli n) (v : Qubits n) (B : Pauli n)
    (w : Qubits n) : ℂ :=
  let S := pairSupport P
  let R := restrict S A
  let Z := restrict S B
  if Z = pauliProd (pauliProd P.2 R) P.1 then
    (4 : ℂ) ^ S.card * (pauliPhase P.2 R * pauliPhase (pauliProd P.2 R) P.1) *
      boolChar (support R) v * boolChar (support Z) w
  else 0

end LindbladStructLearn



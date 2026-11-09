-- Prove2me | Definitions.Def_LindbladStructLearn_pauliAvg
-- name    : LindbladStructLearn_pauliAvg
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T21:48:14.760845+00:00
-- url     : https://prove2.me/theorems/ac972320-bd77-40bd-9255-b84432498df3
-- title:
--   Average over a uniformly random Pauli $R \sim \mathcal P_S$
-- statement:
--   For $S \subseteq [n]$ and a function $f$ on $n$-qubit Paulis,
--
--   $$\mathbb E_{R\sim\mathcal P_S} f(R) = \frac{1}{4^{|S|}} \sum_{R \in \mathcal P_S} f(R).$$
--
--   With $S = [n]$ this is the uniform average over all $4^n$ Paulis.
-- source:
--   Lewis–Tang–Wright, Learning the structure of open quantum systems, arXiv:2606.30358 (held version, sha256 0af12079…2eb52e), §2.2, p.15

import Mathlib
import Definitions.Def_LindbladStructLearn_paulisOn

set_option autoImplicit false
open scoped ComplexOrder BigOperators Matrix ENNReal NNReal
noncomputable section

namespace LindbladStructLearn

open LindbladTolerant.Testing

/-- Expectation over a uniformly random Pauli supported in a set (Lewis–Tang–Wright, *Learning the structure of open quantum systems*, arXiv:2606.30358 (held version, sha256 0af12079…2eb52e), §2.2, p.15):
`E_(R∼𝒫_S) f(R) = 4^(−|S|) Σ_(R ∈ 𝒫_S) f(R)`. -/
def pauliAvg {n : ℕ} (S : Finset (Fin n)) (f : Pauli n → ℂ) : ℂ :=
  (∑ R ∈ paulisOn S, f R) / (4 : ℂ) ^ S.card

end LindbladStructLearn



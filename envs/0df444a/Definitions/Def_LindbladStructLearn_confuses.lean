-- Prove2me | Definitions.Def_LindbladStructLearn_confuses
-- name    : LindbladStructLearn_confuses
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T21:49:01.868969+00:00
-- url     : https://prove2.me/theorems/77236579-ea3e-4b89-8245-6614a530e034
-- title:
--   Confusion relation $\overline Q \succeq \overline P$
-- statement:
--   For pairs of $n$-qubit Paulis, $\overline Q \succeq \overline P$ ("$\overline Q$ can be confused with $\overline P$") holds when
--
--   $$Q_1^{S_{\overline P}} = P_1,\qquad Q_2^{S_{\overline P}} = P_2,\qquad Q_1^{\overline{S_{\overline P}}} = Q_2^{\overline{S_{\overline P}}},$$
--
--   i.e. $\overline Q$ agrees with $\overline P$ on $S_{\overline P}$ and its two components coincide off $S_{\overline P}$. The local Fourier coefficients of a superoperator are sums of its Fourier coefficients over the confusable pairs.
-- source:
--   Lewis–Tang–Wright, Learning the structure of open quantum systems, arXiv:2606.30358 (held version, sha256 0af12079…2eb52e), §2.2.1, Eq. (2.21), p.16

import Mathlib
import Definitions.Def_LindbladStructLearn_restrict
import Definitions.Def_LindbladStructLearn_pairSupport

set_option autoImplicit false
open scoped ComplexOrder BigOperators Matrix ENNReal NNReal
noncomputable section

namespace LindbladStructLearn

open LindbladTolerant.Testing

/-- The confusion relation (Lewis–Tang–Wright, *Learning the structure of open quantum systems*, arXiv:2606.30358 (held version, sha256 0af12079…2eb52e), §2.2.1, Eq. (2.21), p.16): `Q̄ ⪰ P̄` iff
`Q₁^(S_P̄) = P₁`, `Q₂^(S_P̄) = P₂` and `Q₁^(S̄_P̄) = Q₂^(S̄_P̄)` (`S̄` the complement).

**Formalization Note** `confuses Q P` is `Q̄ ⪰ P̄`; the complement bars are lost in the text
layer and checked on the rendered page. -/
def confuses {n : ℕ} (Q P : Pauli n × Pauli n) : Prop :=
  restrict (pairSupport P) Q.1 = P.1 ∧ restrict (pairSupport P) Q.2 = P.2 ∧
    restrict (pairSupport P)ᶜ Q.1 = restrict (pairSupport P)ᶜ Q.2

end LindbladStructLearn



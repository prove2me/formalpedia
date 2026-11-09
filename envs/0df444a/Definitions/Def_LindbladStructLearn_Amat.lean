-- Prove2me | Definitions.Def_LindbladStructLearn_Amat
-- name    : LindbladStructLearn_Amat
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T21:56:56.253123+00:00
-- url     : https://prove2.me/theorems/ae1d5444-0974-43f7-b237-4dd04b431cff
-- title:
--   The matrix $A_k$
-- statement:
--   $A_k$ is the square matrix indexed by the $k$-local pairs with $P_1 \ne I$ defined by
--
--   $$(A_k x)_{\overline P} = \mathbb E_{R\sim\mathcal P_{S_{\overline P}}}\big[\overline{\mathrm{tr}}\big(\chi_{\overline P}(R)^\dagger\,\mathcal L_x(R)\big)\big],$$
--
--   the local Fourier coefficients of $\mathcal L_x$ itself, which is the first-order term $E(x) \approx tA_kx$ of the expectation values. Equation (3.14) gives it explicitly in terms of the confusion relation.
--
--   **Formalization Note** The column of $\overline Q$ is the vector of local Fourier coefficients of $\mathcal L_{e_{\overline Q}}$.
-- source:
--   Lewis–Tang–Wright, Learning the structure of open quantum systems, arXiv:2606.30358 (held version, sha256 0af12079…2eb52e), Notation 3.2, Eq. (3.13), p.19

import Mathlib
import Definitions.Def_LindbladStructLearn_ext
import Definitions.Def_LindbladStructLearn_lindbladSuper
import Definitions.Def_LindbladStructLearn_locFourier

set_option autoImplicit false
open scoped ComplexOrder BigOperators Matrix ENNReal NNReal
noncomputable section

namespace LindbladStructLearn

open LindbladTolerant.Testing

/-- The matrix `A_k` (Lewis–Tang–Wright, *Learning the structure of open quantum systems*, arXiv:2606.30358 (held version, sha256 0af12079…2eb52e), Notation 3.2, Eq. (3.13), p.19): rows and columns are the
`k`-local pairs with `P₁ ≠ I`, and `(A_k x)_P̄ = E_(R∼𝒫_(S_P̄)) [tr̄(χ_P̄(R)† · L_x(R))]`.

**Formalization Note** Defined by Eq. (3.13), the paper's definition: the column of `Q̄` is
`L_x` at `x = e_Q̄`; Eq. (3.14) is its explicit form (with `c̄(PQ)`, the bar lost in the text
layer). -/
def Amat (n k : ℕ) : Matrix (Idx n k) (Idx n k) ℂ := fun a b =>
  locFourier (lindbladSuper (ext (Pi.single b (1 : ℂ)))) a.1

end LindbladStructLearn



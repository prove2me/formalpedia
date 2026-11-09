-- Prove2me | Definitions.Def_LindbladStructLearn_expVec
-- name    : LindbladStructLearn_expVec
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T21:57:00.865206+00:00
-- url     : https://prove2.me/theorems/89c13b05-6c53-4d95-ace3-263fcbe9394c
-- title:
--   Vector of expectation values $E(x)$
-- statement:
--   For a time $t$ and $x \in \mathbb C^m$,
--
--   $$E(x)_{\overline P} = \mathbb E_{R\sim\mathcal P_{S_{\overline P}}}\big[\overline{\mathrm{tr}}\big(\chi_{P_1,P_2}(R)^\dagger\, e^{\mathcal L_x t}(R)\big)\big]$$
--
--   for every $k$-local pair $\overline P$ with $P_1\ne I$: the local Fourier coefficients of the time evolution $e^{\mathcal L_x t}$. At the true parameters these are the quantities measured in experiments.
--
--   **Formalization Note** $e^{\mathcal L_x t}$ is the reused `LindbladTolerant.Testing.evolution`, the matrix exponential of $t\,\mathcal L_x$.
-- source:
--   Lewis–Tang–Wright, Learning the structure of open quantum systems, arXiv:2606.30358 (held version, sha256 0af12079…2eb52e), Definition 3.1, Eq. (3.1), p.18; Eq. (5.2), p.32

import Mathlib
import Definitions.Def_LindbladTolerant_Testing_lindblad_model
import Definitions.Def_LindbladStructLearn_ext
import Definitions.Def_LindbladStructLearn_lindbladSuper
import Definitions.Def_LindbladStructLearn_locFourier

set_option autoImplicit false
open scoped ComplexOrder BigOperators Matrix ENNReal NNReal
noncomputable section

namespace LindbladStructLearn

open LindbladTolerant.Testing

/-- The vector of expectation values (Lewis–Tang–Wright, *Learning the structure of open quantum systems*, arXiv:2606.30358 (held version, sha256 0af12079…2eb52e), Definition 3.1, Eq. (3.1), p.18, and Eq. (5.2),
p.32): `E(x)_P̄ = E_(R∼𝒫_(S_P̄)) [tr̄(χ_P̄(R)† · e^(L_x t)(R))]` for `P̄` a `k`-local pair with
`P₁ ≠ I`; i.e. the local Fourier coefficients of `e^(L_x t)`.

**Formalization Note** `e^(L_x t)` is the reused `LindbladTolerant.Testing.evolution` (the matrix
exponential of `t • L_x`). -/
def expVec {n k : ℕ} (t : ℝ) (x : Idx n k → ℂ) : Idx n k → ℂ := fun a =>
  locFourier (evolution (lindbladSuper (ext x)) t) a.1

end LindbladStructLearn



-- Prove2me | Definitions.Def_SpencerEight_Supplement_discmat
-- name    : SpencerEight_Supplement_discmat
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T23:48:02.675168+00:00
-- url     : https://prove2.me/theorems/ec2ca3e5-5954-4be6-88b4-ab45c9eafa22
-- title:
--   Matrix signing discrepancy $\mathrm{disc}_{\mathrm{mat}}(A_1,\dots,A_n)$
-- statement:
--   For real symmetric matrices $A_1,\dots,A_n\in\mathbb R^{d\times d}$, the **matrix signing discrepancy** is the operator norm of the best signing:
--   $$
--   \mathrm{disc}_{\mathrm{mat}}(A_1,\dots,A_n):=\min_{\varepsilon\in\{-1,1\}^n}\Bigl\|\sum_{i=1}^n\varepsilon_iA_i\Bigr\|.
--   $$
--
--   It is the quantity the lower-bound families of Section 15 compute or bound, and the inner term of the constant $D^{\mathrm{mat}}_n$.
--
--   **Formalization Note** The minimum is a real infimum over the finite, nonempty set of real sign vectors ($\varepsilon_i=\pm1$); the norms are nonnegative, so it is attained. The family's index type and the matrix size are arbitrary finite types; Definition 15.1 uses $[n]$ and $d\le n$.
-- source:
--   Song, Zhang, Matrix Spencer: Eight Standard Deviations Suffice and an Almost-Linear Time Algorithm for Dense Input, arXiv:2609.15025 (held version, sha256 9ccbcdb8…), Definition 15.1, pp.288-289 (PDF pp.288-289)

import Mathlib
import Definitions.Def_SpencerEight_signedSum
open scoped Matrix.Norms.L2Operator

namespace SpencerEight.Supplement

/-- The matrix signing discrepancy (Definition 15.1, Song, Zhang, *Matrix Spencer: Eight Standard Deviations Suffice and an Almost-Linear Time Algorithm for Dense Input*, arXiv:2609.15025 (held version, sha256 9ccbcdb8…), pp.288-289 (PDF pp.288-289)):
`discmat(A₁, …, A_n) := min_{ε ∈ {−1,1}ⁿ} ‖∑ᵢ εᵢ Aᵢ‖`, the norm of the best signing.

**Formalization Note** `‖·‖` is Mathlib's L2 operator norm. A signing is a real vector `ε` with
`ε i = 1 ∨ ε i = -1` for every `i`. The minimum is written as a real infimum over this finite set of
signings; the set is nonempty (the all-ones signing) and the norms are nonnegative, so the infimum is a
genuine minimum. The index type `ι` of the family and the index type `d` of the rows are arbitrary
finite types; the source's `ι = [n]`, `d ≤ n` is the case used by `Dmat`. -/
noncomputable def discmat {ι d : Type*} [Fintype ι] [Fintype d] [DecidableEq d]
    (A : ι → Matrix d d ℝ) : ℝ :=
  ⨅ ε : {ε : ι → ℝ // ∀ i, ε i = 1 ∨ ε i = -1}, ‖signedSum A ε.1‖

end SpencerEight.Supplement



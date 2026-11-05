-- Prove2me | Definitions.Def_LoPopescuCC_Dilution_IsSchmidtDegenerate
-- name    : LoPopescuCC_Dilution_IsSchmidtDegenerate
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:41:48.061117+00:00
-- url     : https://prove2.me/theorems/53ecb397-91a8-42fb-bab9-9fc78042808a
-- title:
--   $D$-fold degenerate Schmidt coefficients
-- statement:
--   Let $M$ be the coefficient matrix of a bipartite vector $v$ and let $D$ be a natural number. The Schmidt coefficients of $v$ are $D$-fold degenerate if every nonzero eigenvalue of $MM^\dagger$, counted with multiplicity, occurs a multiple of $D$ times.
--
--   These eigenvalues are the squared Schmidt coefficients, so this says that every value taken by a Schmidt coefficient is taken a multiple of $D$ times. This is the sense of the paper's sentence "The degeneracies of its Schmidt coefficients are multiples of" (p. 5).
--
--   **Formalization Note** The eigenvalue $0$ is excluded because it is not a Schmidt coefficient.
-- source:
--   Lo, Popescu, The classical communication cost of entanglement manipulation, arXiv:quant-ph/9902045v2, Lemma, p. 4; Theorem, pp. 4-5; Proof of the Theorem, p. 5

import Mathlib
import Definitions.Def_LoPopescuCC_Dilution_coeffMatrix

namespace LoPopescuCC.Dilution

/-- **`D`-fold degenerate Schmidt coefficients** (Lo, Popescu, arXiv:quant-ph/9902045v2, Lemma, p. 4:
"the Schmidt coefficients … be 2^r-fold degenerate"; Theorem, pp. 4–5: "D = 2^d … degeneracies in
its Schmidt decomposition"; proof of the Theorem, p. 5: "The degeneracies of its Schmidt
coefficients are multiples of"): every nonzero eigenvalue of `M Mᴴ`, where `M` is the coefficient
matrix of `v`, has multiplicity divisible by `D`.

**Formalization Note** These eigenvalues are the squared Schmidt coefficients, and two Schmidt
coefficients agree exactly when their squares do. The value `0` is excluded because it is not a
Schmidt coefficient: its multiplicity on Alice's side is `|a|` minus the Schmidt rank. Exactly
`D`-fold degeneracy is the special case of multiplicity `D`; the divisibility form is what the
proof of the Theorem applies to `u₁`. -/
def IsSchmidtDegenerate {a b : Type} [Fintype a] [DecidableEq a] [Fintype b] (D : ℕ)
    (v : EuclideanSpace ℂ (a × b)) : Prop :=
  ∀ μ : ℝ, μ ≠ 0 →
    D ∣ (Finset.univ.filter fun i =>
      (Matrix.isHermitian_mul_conjTranspose_self (coeffMatrix v)).eigenvalues i = μ).card

end LoPopescuCC.Dilution



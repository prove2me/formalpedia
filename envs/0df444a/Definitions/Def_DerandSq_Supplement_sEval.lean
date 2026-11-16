-- Prove2me | Definitions.Def_DerandSq_Supplement_sEval
-- name    : DerandSq_Supplement_sEval
-- status  : Definition
-- author  : @iris
-- created : 2026-11-15T20:05:36.233209+00:00
-- url     : https://prove2.me/theorems/af01c6d9-b262-4e18-8931-79c51f8e1bc9
-- title:
--   Scalar ∗-polynomial evaluated at operators
-- statement:
--   A **non-commutative ∗-polynomial** with complex coefficients in the variables $x_i$ ($i \in \iota$) is a finite sum $P = \sum_w \alpha_w\, w$ over words $w$ in the letters $x_i, x_i^*$. Its evaluation at a tuple $u = (u_i)$ of bounded operators on a Hilbert space $E$ is
--
--   $$
--   P(u) = \sum_w \alpha_w\, w(u),
--   $$
--
--   where $w(u)$ replaces $x_i$ by $u_i$ and $x_i^*$ by $u_i^*$ and multiplies in order. This is the evaluation in the definition (2.8) of weak convergence, $|\operatorname{tr} P(X^N) - \tau(P(x))|$.
--
--   **Formalization Note** The polynomial is the published `DerandSq.NCPoly 1 ι` (scalars as $1 \times 1$ matrices, $\alpha_w$ = the entry of the coefficient); the result is an operator on $E$ itself, so traces apply to it directly.
-- source:
--   Alev–Rao, Rotating Walks, Derandomized Squares, and Permutation Conjugated Walks, STOC 2027 submission (manuscript sha256 2549f907…376941e0), §2.4, (2.8), p.12

import Mathlib
import Definitions.Def_DerandSq_NCPoly
import Definitions.Def_DerandSq_wordOp

namespace DerandSq.Supplement

/-- A scalar non-commutative ∗-polynomial `P = ∑_w α_w w ∈ ℂ*⟨x_i : i ∈ ι⟩` evaluated at a tuple
`u` of bounded operators on a Hilbert space `E`: `P(u) = ∑_w α_w w(u)`, an operator on `E`
(Alev–Rao, *Rotating Walks, Derandomized Squares, and Permutation Conjugated Walks*, STOC 2027 submission manuscript (sha256 2549f907…376941e0), §2.4, p.12, (2.8)).

**Formalization Note** The polynomial is the published `DerandSq.NCPoly 1 ι` (`1 × 1` matrix
coefficients, i.e. scalars `α_w = P w 0 0`); `w(u)` is the published `DerandSq.wordOp` (letters
`x_i ↦ u_i`, `x_i^* ↦ u_i^*`). This evaluation lands in the operators on `E` itself, so the
normalized trace and the canonical trace `τ` apply to it directly; it agrees with
`DerandSq.NCPoly.eval` on the single copy `PiLp 2 (fun _ : Fin 1 => E)` of `E`. -/
noncomputable def sEval {ι : Type*} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] (P : DerandSq.NCPoly 1 ι) (u : ι → E →L[ℂ] E) : E →L[ℂ] E :=
  ∑ w ∈ P.support, (P w 0 0) • DerandSq.wordOp u w

end DerandSq.Supplement



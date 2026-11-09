-- Prove2me | Definitions.Def_LindbladStructLearn_alg4Iter
-- name    : LindbladStructLearn_alg4Iter
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T22:00:59.528338+00:00
-- url     : https://prove2.me/theorems/0bf55cfb-c7bb-4368-9fde-2100c99c7246
-- title:
--   Iterates of the simplified Algorithm 4
-- statement:
--   Given estimates $\widehat{\mathcal F}_j$ (one per round), the simplified Algorithm 4 starts from $x^{(0)} = 0$ and sets
--
--   $$x^{(j+1)} = \mathrm{Round}_{\varepsilon_j/(4d)}\Big(x^{(j)} - A^{-1}\,\mathrm{Round}_{\tau_j}\big(\widehat{\mathcal F}_j(x^{(j)})\big)\Big),\qquad \varepsilon_j = 2^{-j}g,\quad \tau_j = \frac{\varepsilon_j}{800\cdot16^k d},$$
--
--   with $A = A_k$; the output is $\widehat\lambda = x^{(T)}$ with $T = \lceil\log_2(g/\varepsilon)\rceil$.
--
--   **Formalization Note** $A^{-1}$ is the matrix inverse of $A_k$; the estimates may depend on the round.
-- source:
--   Lewis–Tang–Wright, Learning the structure of open quantum systems, arXiv:2606.30358 (held version, sha256 0af12079…2eb52e), Algorithm 4, Eq. (5.10), p.34

import Mathlib
import Definitions.Def_LindbladStructLearn_Amat
import Definitions.Def_LindbladStructLearn_roundVec

set_option autoImplicit false
open scoped ComplexOrder BigOperators Matrix ENNReal NNReal
noncomputable section

namespace LindbladStructLearn

open LindbladTolerant.Testing

/-- The simplified Algorithm 4 (Lewis–Tang–Wright, *Learning the structure of open quantum systems*, arXiv:2606.30358 (held version, sha256 0af12079…2eb52e), p.34, Eq. (5.10)): `x^(0) = 0` and
`x^(j+1) = Round_(ε_j/(4d))(x^(j) − A⁻¹ Round_(τ_j)(F̂(x^(j))))`, with `ε_j = 2^(−j) g` and
`τ_j = ε_j/(800 · 16^k d)`.

**Formalization Note** The estimates may depend on the round: `F̂ j` is used in round `j`. `A⁻¹` is
Mathlib's matrix inverse of `A_k`. -/
def alg4Iter (n k d : ℕ) (g : ℝ) (Fhat : ℕ → (Idx n k → ℂ) → (Idx n k → ℂ)) :
    ℕ → Idx n k → ℂ
  | 0 => 0
  | j + 1 =>
    let x := alg4Iter n k d g Fhat j
    let εj : ℝ := g / 2 ^ j
    let τj : ℝ := εj / (800 * 16 ^ k * d)
    roundVec (εj / (4 * d)) (x - Matrix.mulVec (Amat n k)⁻¹ (roundVec τj (Fhat j x)))

end LindbladStructLearn



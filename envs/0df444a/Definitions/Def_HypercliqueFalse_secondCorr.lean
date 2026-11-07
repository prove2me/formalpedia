-- Prove2me | Definitions.Def_HypercliqueFalse_secondCorr
-- name    : HypercliqueFalse_secondCorr
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T17:30:58.186519+00:00
-- url     : https://prove2.me/theorems/3de4f68f-782d-4fb8-8c3d-317cf3ef1e86
-- title:
--   Lemma 4.1, second reduction: the correction children, of size $(N, M/q, a, b, 2c)$
-- statement:
--   With the digit split of the second reduction ($x_1 = q y_1 + i$, $x_4 = q y_4 + j$, $M = M'q$), the **$(i,j)$-th correction child** has size $(N, M', a, b, 2c)$ and consists of the block matrices
--   $$
--   \bar A = \begin{bmatrix} A^{i} & A^{j}\end{bmatrix},\quad
--   \bar B = \begin{bmatrix} B^{ij} \\ -B^{ji}\end{bmatrix},\quad
--   \bar C = \begin{bmatrix} C^{ij} & -C^{ji}\end{bmatrix},\quad
--   \bar D = \begin{bmatrix} D^{j} \\ D^{i}\end{bmatrix},
--   $$
--   and $\bar E_\ell[\alpha,\beta,(1,\gamma)] = E^{ij}_\ell[\alpha,\beta,\gamma]$, $\bar E_\ell[\alpha,\beta,(2,\gamma)] = E^{ji}_\ell[\alpha,\beta,\gamma]$. Then $\bar A\bar B = A^iB^{ij} - A^jB^{ji}$ and the $C$–$D$–$E$ part is $U_{ij} - U_{ji}$ in the notation of the main children.
--
--   The paper says only "The correction terms are handled as before"; these are the arrays that description determines.
--
--   **Formalization Note** $[2]\times[c]\cong[2c]$ by `finProdFinEquiv`; block $1$ is $t=0$, block $2$ is $t=1$. Defined for every pair $(i,j)$.
-- source:
--   Fischer, The Hyperclique Hypothesis is False, arXiv:2611.03880 (held version, sha256 6bd5cf5d…7730), proof of Lemma 4.1, p.11

import Mathlib
import Definitions.Def_HypercliqueFalse_TData

set_option autoImplicit false

namespace HypercliqueFalse

/-- **Lemma 4.1, second reduction: the `(i, j)`-th correction child, of size `(N, M/q, a, b, 2c)`.**
Fischer, *The Hyperclique Hypothesis is False*, arXiv:2611.03880 (held version, sha256
6bd5cf5d…7730), proof of Lemma 4.1, p.11 ("The correction terms are handled as before").

With the digit split and the matrices `V_{ij} = A^i B^{ij}`, `U_{ij}` of `secondMain`, the correction
term `tr((V_{ij} − V_{ji})(U_{ij} − U_{ji}))` is `T_h` of
`Ā[α, (1, κ)] = A^i[α, κ]`, `Ā[α, (2, κ)] = A^j[α, κ]`; `B̄[(1, κ), β] = B^{ij}`, `B̄[(2, κ), β] = −B^{ji}`;
`C̄[β, (1, γ)] = C^{ij}`, `C̄[β, (2, γ)] = −C^{ji}`; `D̄[(1, γ), α] = D^j`, `D̄[(2, γ), α] = D^i`;
`Ē_ℓ[α, β, (1, γ)] = E^{ij}_ℓ`, `Ē_ℓ[α, β, (2, γ)] = E^{ji}_ℓ`.

**Formalization Note.** The paper gives no formulas for this reduction; these are the formulas its
description determines. `M = M' · q`; `[2] × [c] ≅ [2c]` by `finProdFinEquiv`, block `1` is `t = 0`
and block `2` is `t = 1`. -/
def secondCorr {h N M' q a b c n : ℕ} (T : TData h N (M' * q) a b c n) (i j : Fin q) :
    TData h N M' a b (2 * c) n where
  A y₁ x₂ x₃ r := Matrix.of fun α p =>
    if (finProdFinEquiv.symm p).1 = 0 then
      T.A (finProdFinEquiv (y₁, i)) x₂ x₃ r α (finProdFinEquiv.symm p).2
    else
      T.A (finProdFinEquiv (y₁, j)) x₂ x₃ r α (finProdFinEquiv.symm p).2
  B y₁ x₂ y₄ r := Matrix.of fun p β =>
    if (finProdFinEquiv.symm p).1 = 0 then
      T.B (finProdFinEquiv (y₁, i)) x₂ (finProdFinEquiv (y₄, j)) r (finProdFinEquiv.symm p).2 β
    else
      -T.B (finProdFinEquiv (y₁, j)) x₂ (finProdFinEquiv (y₄, i)) r (finProdFinEquiv.symm p).2 β
  C y₁ x₃ y₄ r := Matrix.of fun β p =>
    if (finProdFinEquiv.symm p).1 = 0 then
      T.C (finProdFinEquiv (y₁, i)) x₃ (finProdFinEquiv (y₄, j)) r β (finProdFinEquiv.symm p).2
    else
      -T.C (finProdFinEquiv (y₁, j)) x₃ (finProdFinEquiv (y₄, i)) r β (finProdFinEquiv.symm p).2
  D x₂ x₃ y₄ r := Matrix.of fun p α =>
    if (finProdFinEquiv.symm p).1 = 0 then
      T.D x₂ x₃ (finProdFinEquiv (y₄, j)) r (finProdFinEquiv.symm p).2 α
    else
      T.D x₂ x₃ (finProdFinEquiv (y₄, i)) r (finProdFinEquiv.symm p).2 α
  E ℓ y₁ x₂ x₃ y₄ r α β p :=
    if (finProdFinEquiv.symm p).1 = 0 then
      T.E ℓ (finProdFinEquiv (y₁, i)) x₂ x₃ (finProdFinEquiv (y₄, j)) r α β (finProdFinEquiv.symm p).2
    else
      T.E ℓ (finProdFinEquiv (y₁, j)) x₂ x₃ (finProdFinEquiv (y₄, i)) r α β (finProdFinEquiv.symm p).2

end HypercliqueFalse



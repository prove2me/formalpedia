-- Prove2me | Definitions.Def_HypercliqueFalse_firstCorr
-- name    : HypercliqueFalse_firstCorr
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T17:30:55.264126+00:00
-- url     : https://prove2.me/theorems/728bbbde-9c9b-4dc3-bd70-6a2b1c98988b
-- title:
--   Lemma 4.1, first reduction: the correction children $(\bar A^{ij},\bar B^{ij},\bar C^{ij},\bar D^{ij},\bar E^{ij})$
-- statement:
--   With the digit split of the first reduction ($x_2 = q y_2 + i$, $x_3 = q y_3 + j$, $N = N'q$), the **$(i,j)$-th correction child** has size $(N', M, a, b, 2c)$ and consists of the block matrices
--   $$
--   \bar A^{ij} = \begin{bmatrix} A^{ij} & -A^{ji}\end{bmatrix},\quad
--   \bar B^{ij} = \begin{bmatrix} B^{i} \\ B^{j}\end{bmatrix},\quad
--   \bar C^{ij} = \begin{bmatrix} C^{j} & C^{i}\end{bmatrix},\quad
--   \bar D^{ij} = \begin{bmatrix} D^{ij} \\ -D^{ji}\end{bmatrix},
--   $$
--   and $\bar E^{ij}_\ell[\alpha,\beta,(1,\gamma)] = E^{ij}_\ell[\alpha,\beta,\gamma]$, $\bar E^{ij}_\ell[\alpha,\beta,(2,\gamma)] = E^{ji}_\ell[\alpha,\beta,\gamma]$.
--
--   These are the correction terms of the proof of Lemma 4.1, used for $1 \le i < j \le q$.
--
--   **Formalization Note** $[2]\times[c]$ is identified with $[2c]$ by `finProdFinEquiv`, $(t,\gamma)\mapsto c t+\gamma$; the paper's block $1$ is $t = 0$ and block $2$ is $t = 1$. The child is defined for every pair $(i, j)$.
-- source:
--   Fischer, The Hyperclique Hypothesis is False, arXiv:2611.03880 (held version, sha256 6bd5cf5d…7730), proof of Lemma 4.1, pp.10–11; proof of Lemma 3.2, p.7

import Mathlib
import Definitions.Def_HypercliqueFalse_TData

set_option autoImplicit false

namespace HypercliqueFalse

/-- **Lemma 4.1, first reduction: the `(i, j)`-th correction child
`(Ā^{ij}, B̄^{ij}, C̄^{ij}, D̄^{ij}, Ē^{ij})`, of size `(N/q, M, a, b, 2c)`.** Fischer, *The
Hyperclique Hypothesis is False*, arXiv:2611.03880 (held version, sha256 6bd5cf5d…7730), proof of
Lemma 4.1, pp.10–11, with the block matrices of the proof of Lemma 3.2, p.7.

With the digit split of `firstMain` (`x₂ = q·y₂ + i`, `x₃ = q·y₃ + j`):
`Ā^{ij} = [A^{ij}  −A^{ji}]`, `B̄^{ij} = [B^i; B^j]`, `C̄^{ij} = [C^j  C^i]`, `D̄^{ij} = [D^{ij}; −D^{ji}]`,
and `Ē^{ij}_ℓ[α, β, (1, γ)] = E^{ij}_ℓ[α, β, γ]`, `Ē^{ij}_ℓ[α, β, (2, γ)] = E^{ji}_ℓ[α, β, γ]`
("where we identify [2] × [c] with [2c] as for the columns of C̄^{ij}").

**Formalization Note.** `N = N' · q`; `[2] × [c]` is identified with `[2c]` by `finProdFinEquiv`
(`(t, γ) ↦ c·t + γ`), the paper's block `1` being `t = 0` and block `2` being `t = 1`. The child is
defined for every pair `(i, j)`; Lemma 4.1 uses it for `i < j`. -/
def firstCorr {h N' q M a b c n : ℕ} (T : TData h (N' * q) M a b c n) (i j : Fin q) :
    TData h N' M a b (2 * c) n where
  A x₁ y₂ y₃ r := Matrix.of fun α p =>
    if (finProdFinEquiv.symm p).1 = 0 then
      T.A x₁ (finProdFinEquiv (y₂, i)) (finProdFinEquiv (y₃, j)) r α (finProdFinEquiv.symm p).2
    else
      -T.A x₁ (finProdFinEquiv (y₂, j)) (finProdFinEquiv (y₃, i)) r α (finProdFinEquiv.symm p).2
  B x₁ y₂ x₄ r := Matrix.of fun p β =>
    if (finProdFinEquiv.symm p).1 = 0 then
      T.B x₁ (finProdFinEquiv (y₂, i)) x₄ r (finProdFinEquiv.symm p).2 β
    else
      T.B x₁ (finProdFinEquiv (y₂, j)) x₄ r (finProdFinEquiv.symm p).2 β
  C x₁ y₃ x₄ r := Matrix.of fun β p =>
    if (finProdFinEquiv.symm p).1 = 0 then
      T.C x₁ (finProdFinEquiv (y₃, j)) x₄ r β (finProdFinEquiv.symm p).2
    else
      T.C x₁ (finProdFinEquiv (y₃, i)) x₄ r β (finProdFinEquiv.symm p).2
  D y₂ y₃ x₄ r := Matrix.of fun p α =>
    if (finProdFinEquiv.symm p).1 = 0 then
      T.D (finProdFinEquiv (y₂, i)) (finProdFinEquiv (y₃, j)) x₄ r (finProdFinEquiv.symm p).2 α
    else
      -T.D (finProdFinEquiv (y₂, j)) (finProdFinEquiv (y₃, i)) x₄ r (finProdFinEquiv.symm p).2 α
  E ℓ x₁ y₂ y₃ x₄ r α β p :=
    if (finProdFinEquiv.symm p).1 = 0 then
      T.E ℓ x₁ (finProdFinEquiv (y₂, i)) (finProdFinEquiv (y₃, j)) x₄ r α β (finProdFinEquiv.symm p).2
    else
      T.E ℓ x₁ (finProdFinEquiv (y₂, j)) (finProdFinEquiv (y₃, i)) x₄ r α β (finProdFinEquiv.symm p).2

end HypercliqueFalse



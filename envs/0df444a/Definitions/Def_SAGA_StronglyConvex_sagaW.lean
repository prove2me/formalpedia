-- Prove2me | Definitions.Def_SAGA_StronglyConvex_sagaW
-- name    : SAGA_StronglyConvex_sagaW
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-04T12:53:57.416607+00:00
-- url     : https://prove2.me/theorems/b9e8175b-c41f-4220-8cfc-492f763b5828
-- title:
--   The SAGA gradient step $w^{k+1}$ (eq. (1))
-- statement:
--   Let $f_1',\dots,f_n':E\to E$ be the component gradients of a finite sum, $\gamma\in\mathbb R$ a step size, $x\in E$ the current iterate and $\phi_1,\dots,\phi_n\in E$ the points at which the stored gradient table was evaluated. For an index $j$, the **SAGA gradient step** is
--
--   $$
--   w \;=\; x-\gamma\Big[f_j'(x)-f_j'(\phi_j)+\frac1n\sum_{i=1}^n f_i'(\phi_i)\Big].
--   $$
--
--   This is $w^{k+1}$ of eq. (1) of Defazio, Bach and Lacoste-Julien with $x=x^k$, $\phi_i=\phi_i^k$ and $f_j'(\phi_j^{k+1})=f_j'(x^k)$. The table average uses the table **before** entry $j$ is overwritten. The next iterate is the proximal point of $h$ at $w$.
--
--   **Formalization Note** The indices run over `Fin n` (0-based). The gradient table is represented by the points $\phi_i$ rather than by the stored vectors $f_i'(\phi_i)$, which is equivalent and also gives access to $f_i(\phi_i)$, needed by the Lyapunov function. For $n=0$ the average is $0$; every theorem assumes $n>0$.
-- source:
--   Defazio, Bach & Lacoste-Julien, SAGA, arXiv:1407.0202v3, p. 2, Section 2, eq. (1)

import Mathlib

namespace SAGA.StronglyConvex

/-- The SAGA gradient step `w^{k+1}` of eq. (1), p. 2, from the state `(x, φ)` with index `j`:
`w = x - γ (f'_j(x) - f'_j(φ_j) + (1/n) Σ_i f'_i(φ_i))`. The table average uses the old table `φ`. -/
noncomputable def sagaW {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {n : ℕ}
    (f' : Fin n → E → E) (γ : ℝ) (x : E) (φ : Fin n → E) (j : Fin n) : E :=
  x - γ • (f' j x - f' j (φ j) + (1 / (n : ℝ)) • ∑ i, f' i (φ i))

end SAGA.StronglyConvex



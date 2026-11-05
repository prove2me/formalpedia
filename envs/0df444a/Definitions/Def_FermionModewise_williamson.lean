-- Prove2me | Definitions.Def_FermionModewise_williamson
-- name    : FermionModewise_williamson
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:32:10.330869+00:00
-- url     : https://prove2.me/theorems/b6c730d6-16e2-431f-b164-4af6bd290141
-- title:
--   Fermion Williamson form $\bigoplus_i\lambda_iJ_2$
-- statement:
--   For real numbers $(\lambda_i)_{i\in\mu}$, the **fermion Williamson form** is the block-diagonal real matrix on the quadrature index $\mu\times\{0,1\}$
--   $$W=\bigoplus_{i\in\mu}\lambda_i J_2,\qquad W_{(i,a),(i',a')}=\begin{cases}\lambda_i\,(J_2)_{aa'}&i=i',\\0&i\ne i'.\end{cases}$$
--   With all $\lambda_i=1$ it is the matrix $J_{2g}=\bigoplus_{i=1}^gJ_2$ of (19).
--
--   Every real antisymmetric matrix is orthogonally equivalent to such a form with $\lambda_i\ge0$ (milestone `williamson_form`).
--
--   **Formalization Note.** No sign condition is built in; statements that need $\lambda_i\ge0$ assume it.
-- source:
--   Botero–Reznik, arXiv:quant-ph/0404176v3, eq. (9), p.5; J_{2g} in eq. (19), p.7

import Mathlib
import Definitions.Def_FermionModewise_J2

open Matrix

namespace FermionModewise

/-- **Fermion Williamson form** (Botero–Reznik, arXiv:quant-ph/0404176v3, eq. (9), p.5): the block
diagonal matrix `W = ⊕_i λ_i J₂` on the quadrature index `μ × Fin 2`.

**Formalization Note.** Entry `((i, a), (i', a'))` is `λ_i · J₂ a a'` if `i = i'` and `0` otherwise.
With all `λ_i = 1` this is the matrix `J_{2g} = ⊕ J₂` of eq. (19), p.7. No sign condition is built
in; the statements that need `λ_i ≥ 0` assume it. -/
def williamson {μ : Type} [DecidableEq μ] (lam : μ → ℝ) : Matrix (μ × Fin 2) (μ × Fin 2) ℝ :=
  Matrix.of fun p q => if p.1 = q.1 then lam p.1 * J2 p.2 q.2 else 0

end FermionModewise



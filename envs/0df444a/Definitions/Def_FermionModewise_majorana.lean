-- Prove2me | Definitions.Def_FermionModewise_majorana
-- name    : FermionModewise_majorana
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:31:25.199498+00:00
-- url     : https://prove2.me/theorems/53ea9d19-41ca-41c1-a5ef-e58ebb3da158
-- title:
--   Fermion quadratures $\gamma_{2i-1}=b_i+b_i^\dagger$, $\gamma_{2i}=i(b_i-b_i^\dagger)$
-- statement:
--   For a family of modes $(b_i)_{i\in\mu}$, the $2|\mu|$ **fermion quadratures** (Majorana operators) are
--   $$\gamma_{(i,0)}=b_i+b_i^\dagger,\qquad \gamma_{(i,1)}=i\,(b_i-b_i^\dagger).$$
--   They are Hermitian, and $b_i=\tfrac12(\gamma_{(i,0)}-i\gamma_{(i,1)})$.
--
--   Quadratures turn the anticommutation relations into a Clifford algebra, on which canonical transformations act by real orthogonal matrices.
--
--   **Formalization Note.** The paper's labels $2i-1$ and $2i$ are $(i,0)$ and $(i,1)$, so quadratures are indexed by $\mu\times\{0,1\}$.
-- source:
--   Botero–Reznik, arXiv:quant-ph/0404176v3, eq. (5), p.3

import Mathlib

open Matrix

namespace FermionModewise

/-- **Fermion quadratures** (Botero–Reznik, arXiv:quant-ph/0404176v3, eq. (5), p.3): for a family
of modes `b : μ → Matrix ι ι ℂ`, the `2|μ|` Hermitian combinations
`γ_(i,0) = b_i + b_i†` and `γ_(i,1) = i (b_i - b_i†)`.

**Formalization Note.** The page indexes quadratures by `2i − 1` and `2i`; here they are indexed by
`μ × Fin 2`, with `(i, 0)` for `γ_{2i−1}` and `(i, 1)` for `γ_{2i}`. Then
`b_i = (γ_(i,0) − i γ_(i,1)) / 2`. -/
noncomputable def majorana {ι μ : Type} (b : μ → Matrix ι ι ℂ) : μ × Fin 2 → Matrix ι ι ℂ :=
  fun p => if p.2 = 0 then b p.1 + (b p.1)ᴴ else Complex.I • (b p.1 - (b p.1)ᴴ)

end FermionModewise



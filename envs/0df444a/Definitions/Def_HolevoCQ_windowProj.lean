-- Prove2me | Definitions.Def_HolevoCQ_windowProj
-- name    : HolevoCQ_windowProj
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T03:14:42.526333+00:00
-- url     : https://prove2.me/theorems/092efc4d-f188-4183-ac73-8f4a0c53c622
-- title:
--   Spectral projector onto an open eigenvalue window
-- statement:
--   For a Hermitian operator $M$ with spectral decomposition $M=\sum_J\lambda_J|e_J\rangle\langle e_J|$ and reals $lo<hi$, the window projector is
--
--   $$
--   \sum_{J:\ lo<\lambda_J<hi}|e_J\rangle\langle e_J| ,
--   $$
--
--   the spectral projector of $M$ for the open interval $(lo,hi)$. Holevo's typical projectors (6) and (8) are of this form.
--
--   **Formalization Note** Computed by the continuous functional calculus as $\mathbf 1_{(lo,hi)}(M)$, which is independent of the choice of eigenbasis.
-- source:
--   Holevo, The Capacity of Quantum Channel with General Signal States, arXiv:quant-ph/9611023v1, eqs. (6) and (8), pp.3–4

import Mathlib

namespace HolevoCQ

/-- Holevo, *The Capacity of Quantum Channel with General Signal States*,
arXiv:quant-ph/9611023v1, eqs. (6) and (8), pp.3–4: the spectral projector of a Hermitian
operator `M` onto the span of its eigenvectors whose eigenvalue lies in the open window
`lo < λ < hi`, i.e. `Σ_{J : lo < λ_J < hi} |e_J⟩⟨e_J|`.

**Formalization Note.** Computed by the continuous functional calculus as
`1_{(lo, hi)}(M)`; for a Hermitian matrix this equals the sum of the rank-one eigenprojectors
with eigenvalue in the open interval, for every choice of orthonormal eigenbasis. (`cfc` is `0`
on a non-Hermitian argument; it is only applied to density matrices here.) -/
noncomputable def windowProj {ι : Type} [Fintype ι] [DecidableEq ι] (M : Matrix ι ι ℂ)
    (lo hi : ℝ) : Matrix ι ι ℂ :=
  cfc (Set.indicator (Set.Ioo lo hi) (fun _ => (1 : ℝ))) M

end HolevoCQ



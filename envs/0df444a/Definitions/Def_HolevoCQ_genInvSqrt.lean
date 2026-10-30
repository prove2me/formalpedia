-- Prove2me | Definitions.Def_HolevoCQ_genInvSqrt
-- name    : HolevoCQ_genInvSqrt
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T03:14:46.576031+00:00
-- url     : https://prove2.me/theorems/0e0faef2-9b05-44f7-a6e8-8bee16ea31fd
-- title:
--   Generalized inverse square root $X^{-1/2}$
-- statement:
--   For a positive operator $X$ on a finite-dimensional space, $X^{-1/2}$ denotes the generalized inverse of $X^{1/2}$: the operator equal to $0$ on $\mathrm{Ker}\,X$ and to $(X^{1/2})^{-1}$ on $(\mathrm{Ker}\,X)^\perp$.
--
--   **Formalization Note** Computed by the continuous functional calculus as $f(X)$ with $f(x)=(\sqrt x)^{-1}$; Lean's convention $(\sqrt0)^{-1}=0$ makes $f(X)$ vanish on the kernel, which is the paper's definition.
-- source:
--   Holevo, The Capacity of Quantum Channel with General Signal States, arXiv:quant-ph/9611023v1, §4, p.4

import Mathlib

namespace HolevoCQ

/-- Holevo, *The Capacity of Quantum Channel with General Signal States*,
arXiv:quant-ph/9611023v1, §4, p.4: `X^{−1/2}`, the generalized inverse of `X^{1/2}`, i.e. the
operator equal to `0` on `Ker X` and to `(X^{1/2})^{−1}` on `(Ker X)^⊥`.

**Formalization Note.** Computed by the continuous functional calculus as `f(X)` with
`f(x) = (√x)⁻¹`; since `(√0)⁻¹ = 0` in Lean, `f(X)` vanishes on `Ker X` and inverts `X^{1/2}` on
its orthogonal complement, which is the paper's definition for positive `X`. (`cfc` is `0` on a
non-Hermitian argument; it is only applied to positive operators here.) -/
noncomputable def genInvSqrt {ι : Type} [Fintype ι] [DecidableEq ι] (G : Matrix ι ι ℂ) :
    Matrix ι ι ℂ :=
  cfc (fun x : ℝ => (Real.sqrt x)⁻¹) G

end HolevoCQ



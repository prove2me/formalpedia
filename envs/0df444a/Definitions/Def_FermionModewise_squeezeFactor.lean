-- Prove2me | Definitions.Def_FermionModewise_squeezeFactor
-- name    : FermionModewise_squeezeFactor
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:31:23.963674+00:00
-- url     : https://prove2.me/theorems/9f389b35-0060-443d-a01d-1b8de0902e3b
-- title:
--   Two-mode squeezing factor $\cos\theta-\sin\theta\,a^\dagger b^\dagger$
-- statement:
--   For two modes $a,b$ and an angle $\theta$, the operator
--   $$S_\theta(a,b)=\cos\theta\,\mathbb 1-\sin\theta\,a^\dagger b^\dagger .$$
--   Applied to a joint vacuum $|00\rangle$ of $a$ and $b$ it gives the two-mode fermion squeezed state of (3),
--   $$S_\theta(a,b)|00\rangle=\cos\theta|00\rangle-\sin\theta|11\rangle,\qquad |11\rangle=a^\dagger b^\dagger|00\rangle .$$
--
--   **Formalization Note.** The convention $|11\rangle=a^\dagger b^\dagger|00\rangle$ is the one under which the entangling unitary $T$ of (15) produces the minus sign of (3).
-- source:
--   Botero–Reznik, arXiv:quant-ph/0404176v3, eq. (3), p.2; eq. (15), p.6

import Mathlib

open Matrix

namespace FermionModewise

/-- **Two-mode squeezing factor** (Botero–Reznik, arXiv:quant-ph/0404176v3, eq. (3), p.2): the
operator `cos θ · 1 − sin θ · a† b†`. Applied to a joint vacuum `|00⟩` of the modes `a, b` it gives
`cos θ |00⟩ − sin θ |11⟩`, the two-mode squeezed state (3).

**Formalization Note.** The convention is `|11⟩ = a† b† |00⟩` (the creation operator of the first
mode acts last). Under this convention `T|00⟩` of eq. (15) carries the minus sign of (3). -/
noncomputable def squeezeFactor {ι : Type} [Fintype ι] [DecidableEq ι]
    (a b : Matrix ι ι ℂ) (θ : ℝ) : Matrix ι ι ℂ :=
  (Real.cos θ : ℂ) • 1 - (Real.sin θ : ℂ) • (aᴴ * bᴴ)

end FermionModewise



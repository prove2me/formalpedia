-- Prove2me | Definitions.Def_FermionModewise_squeezeT
-- name    : FermionModewise_squeezeT
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:31:27.30068+00:00
-- url     : https://prove2.me/theorems/c9cb577c-8385-49cf-b20d-19e882553034
-- title:
--   Entangling unitary $T=\exp[-(a^\dagger b^\dagger+ab)\theta]$
-- statement:
--   For two modes $a,b$ and an angle $\theta$, the operator of (15)
--   $$T=\exp\big[-\big(a^\dagger b^\dagger+ab\big)\theta\big].$$
--   For modes satisfying the anticommutation relations it is unitary and rotates $|00\rangle$ into $|11\rangle$ (milestone `two_mode_squeezed`).
--
--   **Formalization Note.** The exponential is the matrix exponential. The relation $\tan2\theta=\kappa/\lambda$ of (15) is not part of the definition; it is stated in `two_mode_squeezed` as $\lambda=\cos2\theta$, $\kappa=\sin2\theta$.
-- source:
--   Botero–Reznik, arXiv:quant-ph/0404176v3, eq. (15), p.6

import Mathlib

open Matrix

namespace FermionModewise

/-- **Entangling unitary `T`** (Botero–Reznik, arXiv:quant-ph/0404176v3, eq. (15), p.6):
`T = exp[−(a† b† + a b) θ]` for two modes `a, b`.

**Formalization Note.** `NormedSpace.exp` on the matrix algebra `Matrix ι ι ℂ` (with its product
topology). The relation `tan 2θ = κ/λ` of (15) is not part of the definition; milestone
`two_mode_squeezed` states it as `λ = cos 2θ`, `κ = sin 2θ`. -/
noncomputable def squeezeT {ι : Type} [Fintype ι] [DecidableEq ι]
    (a b : Matrix ι ι ℂ) (θ : ℝ) : Matrix ι ι ℂ :=
  NormedSpace.exp (-(θ : ℂ) • (aᴴ * bᴴ + a * b))

end FermionModewise



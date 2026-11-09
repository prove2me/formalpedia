-- Prove2me | Definitions.Def_ResultantVNP_SupportedOnGrid
-- name    : ResultantVNP_SupportedOnGrid
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T22:29:25.49421+00:00
-- url     : https://prove2.me/theorems/ccf7d9aa-1789-40b9-a3bd-c76506899a32
-- title:
--   Symmetric tensor supported on the grid triangles
-- statement:
--   A symmetric tensor $A$ is **supported on the grid triangles** (for given index classes $\Omega_{ij}$) if its only possibly nonzero entries, up to permutation of their indices, are $a_{\alpha\beta\gamma}$ with $\alpha\in\Omega_{ij}$, $\beta\in\Omega_{i+1,j}$, $\gamma\in\Omega_{i,j+1}$ for some position $(i,j)$.
-- source:
--   Bhargav–Curticapean–Jindal–Shukla, Multivariate Resultants: Complexity and Applications to Real Feasibility, STOC 2027 submission (manuscript sha256 8827709b…7f8271), Section 3.2, p.14

import Mathlib
import Definitions.Def_ResultantVNP_gridSum

namespace ResultantVNP

/-- A symmetric tensor `A` is **supported on the grid triangles** for the index classes `Ω_p` (the
fibres of `cls`): its only possibly nonzero entries, up to permutation of their indices, are
`a_{αβγ}` with `α ∈ Ω_{ij}`, `β ∈ Ω_{i+1,j}`, `γ ∈ Ω_{i,j+1}`.

Bhargav–Curticapean–Jindal–Shukla, *Multivariate Resultants: Complexity and Applications to Real Feasibility*, STOC 2027 submission manuscript (sha256 8827709b…7f8271), Section 3.2, p.14.

**Formalization Note** "Up to permutation of their indices" is built in: `A` is a function of the
unordered triple `Sym ι 3`. -/
def SupportedOnGrid {m : ℕ} {ι : Type} {S : Type} [Zero S] (cls : ι → ZMod m × ZMod m)
    (A : Sym ι 3 → S) : Prop :=
  ∀ T, A T ≠ 0 → ∃ (p : ZMod m × ZMod m) (α β γ : ι), cls α = p ∧ cls β = gridRight p ∧
    cls γ = gridDown p ∧ T = α ::ₛ β ::ₛ γ ::ₛ Sym.nil

end ResultantVNP



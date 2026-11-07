-- Prove2me | Definitions.Def_EllipsoidFitting_Fits
-- name    : EllipsoidFitting_Fits
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T10:41:14.945203+00:00
-- url     : https://prove2.me/theorems/0fdddf5f-e43e-4dc8-9fe7-b7686106610f
-- title:
--   Points lying on a centered, possibly degenerate ellipsoid
-- statement:
--   Let $v_1,\dots,v_m\in\mathbb R^d$. The points **lie on a centered ellipsoid** if there is a positive semidefinite matrix $\Lambda\in\mathbb R^{d\times d}$ with
--   $$
--   v_i^\top\Lambda v_i=1\qquad(i=1,\dots,m).
--   $$
--   Degenerate ellipsoids ($\Lambda$ singular) are allowed. This is the ellipsoid fitting problem of the paper's introduction: "a positive semidefinite matrix $\Lambda\succeq0$ such that $v_i^\top\Lambda v_i=1$ for all $i\in[m]$".
--
--   This predicate is the event whose probability the main theorems control.
--
--   **Formalization Note** Points are `Fin d → ℝ`; the constraints are equalities and $\Lambda$ is `PosSemidef` (not positive definite).
-- source:
--   de la Cerda, Potechin, Tulsiani, Xu, Sharp Phase Transition for Ellipsoid Fitting, arXiv:2608.12415 (version of Nov 3, 2026, sha256 e4268312ca36b47de9467896061e7747d1efb1efe9677b7f14bd1b0647e093bc), §1, p.2 (PDF p.4)

import Mathlib

set_option autoImplicit false

namespace EllipsoidFitting

open Matrix

/-- **Ellipsoid fitting.** de la Cerda, Potechin, Tulsiani, Xu, *Sharp Phase Transition for
Ellipsoid Fitting*, arXiv:2608.12415 (version of Nov 3, 2026), §1, p.2: "when does there exist an
(origin-centered, possibly degenerate) ellipsoid passing through all of them? Equivalently, … a
positive semidefinite matrix Λ ⪰ 0 such that v⊤_i Λ v_i = 1 for all i ∈ [m]?"

`Fits v` holds when the points `v 0, …, v (m-1)` of `ℝ^d` all lie on one origin-centered,
possibly degenerate ellipsoid: some positive semidefinite `d × d` matrix `Λ` has
`v iᵀ Λ v i = 1` for every `i`.

**Formalization Note** `Λ` is positive *semi*definite (degenerate ellipsoids allowed), exactly as
on p.2, and the constraints are equalities. Points are `Fin d → ℝ`, `⬝ᵥ` is the dot product. -/
def Fits {m d : ℕ} (v : Fin m → Fin d → ℝ) : Prop :=
  ∃ Λ : Matrix (Fin d) (Fin d) ℝ, Λ.PosSemidef ∧ ∀ i, v i ⬝ᵥ (Λ *ᵥ v i) = 1

end EllipsoidFitting



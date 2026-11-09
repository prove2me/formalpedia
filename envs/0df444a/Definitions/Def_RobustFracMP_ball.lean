-- Prove2me | Definitions.Def_RobustFracMP_ball
-- name    : RobustFracMP_ball
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T17:56:51.435164+00:00
-- url     : https://prove2.me/theorems/0751a3b9-2140-4c99-b91d-ef3367ca030c
-- title:
--   The $\beta$-scaled power-$z$ ball $B^{(\beta)}_p(r)$
-- statement:
--   Let $(P,\mathrm{dist})$ be a finite metric space, $z\ge1$ and $\beta>0$. For a point $p$ and a radius $r\ge0$,
--
--   $$B^{(\beta)}_p(r)=\{q\in P:\ \beta\cdot\mathrm{dist}^z(p,q)\le r\}.\qquad(10)$$
--
--   The radius is measured in the scaled power distance $\beta\,\mathrm{dist}^z$, the scale of the radii $r^{(\beta)}_p$. Balls of radius proportional to $r^{(\beta)}_p$ carry the size bound (Lemma 3.5) and the local-density bound (Lemma 3.9).
-- source:
--   Czumaj–Jiang–Jin–Lou–Wang, Fully Scalable MPC Algorithms for Euclidean Clustering, arXiv:2604.00954 (version of November 3, 2026; manuscript sha256 c65896fe…51d8), Section 3.1, eq. (10), p.15 (PDF p.17)

import Mathlib

set_option autoImplicit false

namespace RobustFracMP

/-- **The β-scaled power-z ball B^{(β)}_p(r).**

Czumaj–Jiang–Jin–Lou–Wang, *Fully Scalable MPC Algorithms for Euclidean Clustering:
Constant Approximation in Constant Rounds*, arXiv:2604.00954 (version of November 3, 2026;
manuscript sha256 c65896fe6f32051527c00d1bcd269746784374658ddefb707cff5f35bd3551d8), Section 3.1, "Additional Notations: Balls and Rings", eq. (10), p.15 (PDF p.17):
"B^{(β)}_p(r) := {q ∈ P : β · dist^z(p, q) ≤ r}."

**Formalization Note.** A finite set of points of the finite metric space `P`, in the true metric
`dist`. Its radius is measured in the scaled power distance `β·dist^z`, not in `dist`. -/
noncomputable def ball {P : Type*} [Fintype P] [MetricSpace P] (z : ℕ) (β : ℝ) (p : P) (r : ℝ) :
    Finset P :=
  Finset.univ.filter (fun q => β * dist p q ^ z ≤ r)

end RobustFracMP



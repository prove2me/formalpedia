-- Prove2me | Definitions.Def_RobustFracMP_xBeta
-- name    : RobustFracMP_xBeta
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T17:57:43.946653+00:00
-- url     : https://prove2.me/theorems/b585ae58-1738-4c6b-b2f1-2093fcf929c7
-- title:
--   The concrete assignment $x^{(\beta)}$ of the proof of Lemma 3.12
-- statement:
--   Let $(P,\mathrm{dist})$ be a finite metric space, $z\ge1$, $\beta>0$, $\lambda>0$, and let $r^{(\beta)}$ be the radii of Algorithm 1 on $(P,\mathrm{dist})$. The fractional assignment $x^{(\beta)}$ is
--
--   $$x^{(\beta)}_{p,q}=\frac1\lambda\bigl[r^{(\beta)}_p-\beta\cdot\mathrm{dist}^z(p,q)\bigr]_+\qquad(p,q\in P).\qquad(15)$$
--
--   By (8) each row of $x^{(\beta)}$ sums to $1$. It need not be feasible for $y^{(\beta)}$ when $z\ge2$ (Example 3.19), and it is the bridge between $\mathrm{cost}_z(y^{(\beta)})$ and the LMP benchmark in Lemmas 3.14 and 3.16.
-- source:
--   Czumaj–Jiang–Jin–Lou–Wang, Fully Scalable MPC Algorithms for Euclidean Clustering, arXiv:2604.00954 (version of November 3, 2026; manuscript sha256 c65896fe…51d8), proof of Lemma 3.12, eq. (15), p.21 (PDF p.23)

import Mathlib
import Definitions.Def_RobustFracMP_mpRadius

set_option autoImplicit false

namespace RobustFracMP

/-- **The concrete fractional assignment x^{(β)} of the proof of Lemma 3.12.**

Czumaj–Jiang–Jin–Lou–Wang, *Fully Scalable MPC Algorithms for Euclidean Clustering:
Constant Approximation in Constant Rounds*, arXiv:2604.00954 (version of November 3, 2026;
manuscript sha256 c65896fe6f32051527c00d1bcd269746784374658ddefb707cff5f35bd3551d8), proof of Lemma 3.12, eq. (15), p.21 (PDF p.23):
"x^{(β)}_{p,q} := (1/λ) · [r^{(β)}_p − β · dist^z(p, q)]_+, ∀p, q ∈ P."

**Formalization Note.** `r^{(β)}` is `mpRadius z dist β lam`, computed on the true metric `dist`
(Sections 3.1–3.2 fix `(P, dist)`, p.14). -/
noncomputable def xBeta {P : Type*} [Fintype P] [MetricSpace P] (z : ℕ) (β lam : ℝ) :
    P → P → ℝ :=
  fun p q => (1 / lam) * max (mpRadius z dist β lam p - β * dist p q ^ z) 0

end RobustFracMP



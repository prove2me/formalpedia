-- Prove2me | Definitions.Def_RobustFracMP_ring
-- name    : RobustFracMP_ring
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T17:58:22.477203+00:00
-- url     : https://prove2.me/theorems/79a0d81f-1e39-46c6-aa37-ae615162a509
-- title:
--   The $\beta$-scaled power-$z$ ring $R^{(\beta)}_p(r)$
-- statement:
--   Let $(P,\mathrm{dist})$ be a finite metric space, $z\ge1$ and $\beta>0$. For a point $p$ and a radius $r\ge0$, the ring with inner radius $r$ and outer radius $2r$ is
--
--   $$R^{(\beta)}_p(r)=B^{(\beta)}_p(2r)\setminus B^{(\beta)}_p(r)=\{q\in P:\ r<\beta\cdot\mathrm{dist}^z(p,q)\le2r\}.\qquad(11)$$
--
--   It appears in the additive smoothness bound of Lemma 3.8.
--
--   **Formalization Note** Defined by the explicit second form of (11).
-- source:
--   Czumaj–Jiang–Jin–Lou–Wang, Fully Scalable MPC Algorithms for Euclidean Clustering, arXiv:2604.00954 (version of November 3, 2026; manuscript sha256 c65896fe…51d8), Section 3.1, eq. (11), p.15 (PDF p.17)

import Mathlib

set_option autoImplicit false

namespace RobustFracMP

/-- **The β-scaled power-z ring R^{(β)}_p(r).**

Czumaj–Jiang–Jin–Lou–Wang, *Fully Scalable MPC Algorithms for Euclidean Clustering:
Constant Approximation in Constant Rounds*, arXiv:2604.00954 (version of November 3, 2026;
manuscript sha256 c65896fe6f32051527c00d1bcd269746784374658ddefb707cff5f35bd3551d8), Section 3.1, eq. (11), p.15 (PDF p.17):
"R^{(β)}_p(r) := B^{(β)}_p(2r) \ B^{(β)}_p(r) = {q ∈ P : r < β · dist^z(p, q) ≤ 2r}."

**Formalization Note.** Defined by the second (explicit) form of (11), which equals the set
difference of the two balls `RobustFracMP.ball z β p (2 * r)` and `RobustFracMP.ball z β p r`. -/
noncomputable def ring {P : Type*} [Fintype P] [MetricSpace P] (z : ℕ) (β : ℝ) (p : P) (r : ℝ) :
    Finset P :=
  Finset.univ.filter (fun q => r < β * dist p q ^ z ∧ β * dist p q ^ z ≤ 2 * r)

end RobustFracMP



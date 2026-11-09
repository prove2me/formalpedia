-- Prove2me | Definitions.Def_RobustFracMP_mpOutput
-- name    : RobustFracMP_mpOutput
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T17:57:44.826197+00:00
-- url     : https://prove2.me/theorems/e0c98579-3703-4be5-a438-e1d61e75185c
-- title:
--   The output $y^{(\beta)}$ of Algorithm 1 ($\mathrm{MP}_\beta$)
-- statement:
--   For a finite set $P$, a distance function $D$, $z\ge1$, $\beta>0$ and $\lambda>0$, Algorithm 1 returns the fractional center set
--
--   $$y^{(\beta)}=\bigl(r^{(\beta)}_p/\lambda\bigr)_{p\in P}\in\mathbb R^P_{\ge0},$$
--
--   opening each point $p$ by the amount $r^{(\beta)}_p/\lambda$, where $r^{(\beta)}_p$ solves (8) for $D$. Run on the true metric it is $y^{(\beta)}$ of Sections 3.1–3.2; run on a distorted distance $\widetilde{\mathrm{dist}}$ it is the vector $\tilde y$ of Lemma 3.1.
-- source:
--   Czumaj–Jiang–Jin–Lou–Wang, Fully Scalable MPC Algorithms for Euclidean Clustering, arXiv:2604.00954 (version of November 3, 2026; manuscript sha256 c65896fe…51d8), Algorithm 1, line 2, p.12 (PDF p.14)

import Mathlib
import Definitions.Def_RobustFracMP_mpRadius

set_option autoImplicit false

namespace RobustFracMP

/-- **The output y^{(β)} of Algorithm 1 (MP_β).**

Czumaj–Jiang–Jin–Lou–Wang, *Fully Scalable MPC Algorithms for Euclidean Clustering:
Constant Approximation in Constant Rounds*, arXiv:2604.00954 (version of November 3, 2026;
manuscript sha256 c65896fe6f32051527c00d1bcd269746784374658ddefb707cff5f35bd3551d8), Algorithm 1, line 2, p.12 (PDF p.14): "return y^{(β)} := (r^{(β)}_p / λ)_{p∈P} ∈ ℝ^P_{≥0}".

**Formalization Note.** As for `mpRadius`, the distance function `D` is an argument:
`mpOutput z dist β lam` is the output of MP_β on `(P, dist)`, and `mpOutput z distT β lam` is the
output on the distorted input `(P, \tilde{dist})` of Lemma 3.1. -/
noncomputable def mpOutput {P : Type*} [Fintype P] (z : ℕ) (D : P → P → ℝ) (β lam : ℝ) : P → ℝ :=
  fun p => mpRadius z D β lam p / lam

end RobustFracMP



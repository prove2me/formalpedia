-- Prove2me | Definitions.Def_RobustFracMP_mpRadius
-- name    : RobustFracMP_mpRadius
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T17:56:53.400656+00:00
-- url     : https://prove2.me/theorems/98302cad-14e4-4f14-a68f-12424b99e99b
-- title:
--   The radius $r^{(\beta)}_p$ of the scaled Mettu–Plaxton algorithm $\mathrm{MP}_\beta$
-- statement:
--   Let $P$ be a finite set, $D:P\times P\to\mathbb R$ a distance function, $z\ge1$, a scale factor $\beta>0$ and an opening cost $\lambda>0$. Line 1 of Algorithm 1 ($\mathrm{MP}_\beta$) computes, for every point $p$, the value $r^{(\beta)}_p>0$ solving
--
--   $$\sum_{q\in P}\bigl[r^{(\beta)}_p-\beta\cdot D(p,q)^z\bigr]_+=\lambda.\qquad(8)$$
--
--   This definition takes $r^{(\beta)}_p$ to be the largest $r\ge0$ with $\sum_q[r-\beta D(p,q)^z]_+\le\lambda$. When $D\ge0$ and $D(p,p)=0$ the left side of (8) is continuous, vanishes at $r=0$ and is strictly increasing in $r\ge0$, so this is the unique positive root of (8), and it lies in $(0,\lambda]$ (milestone *Algorithm 1 is well defined*).
--
--   The distance is an argument so that one definition serves the true metric ($D=\mathrm{dist}$, Sections 3.1–3.2) and the distorted distance $\widetilde{\mathrm{dist}}$ on which the algorithm is run in Lemma 3.1; the sum in (8) is over the second argument of $D$.
--
--   **Formalization Note** The value is the supremum of $\{r\ge0:\sum_q\max(r-\beta D(p,q)^z,0)\le\lambda\}$. Outside the range above it is a junk value: for $\lambda<0$ the set is empty and the value is $0$, and if the set is unbounded (for instance $\beta\le0$) the value is $0$.
-- source:
--   Czumaj–Jiang–Jin–Lou–Wang, Fully Scalable MPC Algorithms for Euclidean Clustering, arXiv:2604.00954 (version of November 3, 2026; manuscript sha256 c65896fe…51d8), Algorithm 1, line 1, eq. (8), p.12 (PDF p.14)

import Mathlib

set_option autoImplicit false

namespace RobustFracMP

/-- **The Mettu–Plaxton radius r^{(β)}_p of Algorithm 1, for an arbitrary distance function.**

Czumaj–Jiang–Jin–Lou–Wang, *Fully Scalable MPC Algorithms for Euclidean Clustering:
Constant Approximation in Constant Rounds*, arXiv:2604.00954 (version of November 3, 2026;
manuscript sha256 c65896fe6f32051527c00d1bcd269746784374658ddefb707cff5f35bd3551d8), Algorithm 1 (MP_β), line 1, eq. (8), p.12 (PDF p.14): "For each point p ∈ P, compute a value
r^{(β)}_p > 0 such that Σ_{q∈P} [r^{(β)}_p − β · dist^z(p, q)]_+ = λ." (`[a]_+ := max{a, 0}`, p.10.)

The function takes the distance `D : P → P → ℝ` as an argument, so that the same definition serves
the true metric (`D = dist`, Sections 3.1–3.2) and the distorted distance `\tilde{dist}` on which the
algorithm is run in Lemma 3.1 (`D = distT`); `D p q` is `D(p, q)` with `p` the centre and the sum
over the second argument `q`, as printed in (8) and in the proof of Lemma 3.1 (p.24).

**Formalization Note.** `mpRadius z D β lam p` is the supremum of
`{r ≥ 0 | Σ_q [r − β·D(p,q)^z]_+ ≤ λ}`. When `z ≥ 1`, `β > 0`, `λ > 0`, `D ≥ 0` and `D p p = 0`,
the map `r ↦ Σ_q [r − β·D(p,q)^z]_+` is continuous, vanishes at `0`, and is strictly increasing on
`[0, ∞)` (its `q = p` term is `r`), so the set is the interval `[0, r*]` and the supremum is the
unique positive root `r*` of (8), which lies in `(0, λ]`; this is milestone
`RobustFracMP.algorithm_1_well_defined`. Outside that range the value is junk: for `λ < 0` the set
is empty and the value is `0`; if the set is unbounded above (e.g. `β ≤ 0` with `D ≥ 0`) the
value is `0` as well. -/
noncomputable def mpRadius {P : Type*} [Fintype P] (z : ℕ) (D : P → P → ℝ) (β lam : ℝ) (p : P) :
    ℝ :=
  sSup {r : ℝ | 0 ≤ r ∧ ∑ q, max (r - β * D p q ^ z) 0 ≤ lam}

end RobustFracMP



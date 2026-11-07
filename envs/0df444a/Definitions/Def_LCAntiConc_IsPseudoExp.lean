-- Prove2me | Definitions.Def_LCAntiConc_IsPseudoExp
-- name    : LCAntiConc_IsPseudoExp
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:47:55.665548+00:00
-- url     : https://prove2.me/theorems/3bf449ad-1c09-49a8-8a47-90b8f4e119db
-- title:
--   Definition 3.2 — degree-$D$ pseudo-expectation on the sphere
-- statement:
--   For an even integer $D$, a **degree-$D$ pseudo-expectation satisfying $\{\|v\|^2=1\}$** is a linear functional $\tilde{\mathbb E}$ on polynomials of degree at most $D$ such that
--
--   1. $\tilde{\mathbb E}\,1=1$;
--   2. $\tilde{\mathbb E}\,p^2\ge0$ whenever $\deg p\le D/2$;
--   3. $\tilde{\mathbb E}\,[(\|v\|_2^2-1)h]=0$ whenever $\deg h\le D-2$.
--
--   Pseudo-expectations are the dual objects of sum-of-squares proofs on the sphere: evaluation at a unit vector is one, and by duality a bound valid for all of them yields a sum-of-squares certificate.
--
--   **Formalization Note** Lean takes a linear functional on all of $\mathbb R[v]$ constrained only on polynomials of degree at most $D$; its restriction to $\mathbb R[v]_{\le D}$ is the page's object, and every statement applies it only in that range. $\deg p\le D/2$ is written $2\deg p\le D$ and $\deg h\le D-2$ is written $\deg h+2\le D$.
-- source:
--   Tiegel, Dimension-Independent Anti-Concentration Certificates for Log-Concave Distributions, STOC 2027 submission (manuscript sha256 7164444e…), Definition 3.2, p.16 (PDF p.18)

import Mathlib
import Definitions.Def_LCAntiConc_sphereConstraint

namespace LCAntiConc

/-- **Definition 3.2** (pseudo-expectation): for an even integer `D`, a degree-`D`
pseudo-expectation satisfying `{‖v‖² = 1}` is a linear functional `Ẽ` with `Ẽ 1 = 1`,
`Ẽ p² ≥ 0` whenever `deg p ≤ D/2`, and `Ẽ[(‖v‖₂² - 1) h] = 0` whenever `deg h ≤ D - 2`.

Tiegel, *Dimension-Independent Anti-Concentration Certificates for Log-Concave Distributions*,
STOC 2027 submission (manuscript sha256 7164444e…), Definition 3.2, p.16 (PDF p.18).

**Formalization Note** `Ẽ` is a linear functional on all of `ℝ[v]` that is constrained only on
polynomials of degree at most `D`; its restriction to `ℝ[v]_{≤D}` is the page's object, and every
statement applies it only to polynomials of degree at most `D`. `deg p ≤ D/2` is written
`2 deg p ≤ D` and `deg h ≤ D - 2` is written `deg h + 2 ≤ D` (no natural-number subtraction). -/
def IsPseudoExp {n : ℕ} (D : ℕ) (L : MvPolynomial (Fin n) ℝ →ₗ[ℝ] ℝ) : Prop :=
  Even D ∧ L 1 = 1 ∧ (∀ p : MvPolynomial (Fin n) ℝ, 2 * p.totalDegree ≤ D → 0 ≤ L (p ^ 2)) ∧
    ∀ h : MvPolynomial (Fin n) ℝ, h.totalDegree + 2 ≤ D → L (sphereConstraint n * h) = 0

end LCAntiConc



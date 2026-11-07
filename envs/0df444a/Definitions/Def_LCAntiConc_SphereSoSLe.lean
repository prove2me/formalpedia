-- Prove2me | Definitions.Def_LCAntiConc_SphereSoSLe
-- name    : LCAntiConc_SphereSoSLe
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:47:50.497728+00:00
-- url     : https://prove2.me/theorems/a0ec9982-d780-4cd2-8beb-f0009c43205b
-- title:
--   Degree-$D$ sum-of-squares proof on the sphere, $\{\|v\|_2^2=1\}\vdash_D p(v)\le B$
-- statement:
--   Let $p\in\mathbb R[v]$, $B\in\mathbb R$ and $D\in\mathbb N$. We write $\{\|v\|_2^2=1\}\vdash_D p(v)\le B$ if there are finitely many polynomials $p_1,\dots,p_m$ and a polynomial $h$ with
--
--   $$B-p(v)=\sum_{j=1}^m p_j(v)^2+(\|v\|_2^2-1)\,h(v),$$
--
--   where every summand, each $p_j^2$ and $(\|v\|_2^2-1)h$, has degree at most $D$.
--
--   Evaluating the identity at a unit vector $u$ shows $p(u)\le B$. The degree bound on every summand is what makes the degree of a certificate meaningful.
--
--   **Formalization Note** The squares are indexed by `Fin m`. The page's preamble "for a polynomial $p$ of degree at most $D$" is not a separate clause, since it follows from the identity.
-- source:
--   Tiegel, Dimension-Independent Anti-Concentration Certificates for Log-Concave Distributions, STOC 2027 submission (manuscript sha256 7164444e…), §1.1, p.2 (PDF p.4); (3.1), p.15 (PDF p.17)

import Mathlib
import Definitions.Def_LCAntiConc_sphereConstraint

namespace LCAntiConc

/-- A degree-`D` sum-of-squares proof on the sphere, `{‖v‖₂² = 1} ⊢_D f(v) ≤ B`: there are
polynomials `p₁, …, p_m` and `h` with
`B - f = ∑ⱼ pⱼ² + (‖v‖₂² - 1) h`, every summand of degree at most `D`.

Tiegel, *Dimension-Independent Anti-Concentration Certificates for Log-Concave Distributions*,
STOC 2027 submission (manuscript sha256 7164444e…), §1.1, p.2 (PDF p.4); (3.1), p.15 (PDF p.17).

**Formalization Note** The finite family of squares is indexed by `Fin m`. "All summands have
degree at most `D`" bounds both `pⱼ²` and `(‖v‖₂² - 1) h`. The page's preamble "for a polynomial
of degree at most `D`" is not a separate clause: it follows from the identity. -/
def SphereSoSLe {d : ℕ} (D : ℕ) (f : MvPolynomial (Fin d) ℝ) (B : ℝ) : Prop :=
  ∃ (m : ℕ) (p : Fin m → MvPolynomial (Fin d) ℝ) (h : MvPolynomial (Fin d) ℝ),
    MvPolynomial.C B - f = ∑ j, p j ^ 2 + sphereConstraint d * h ∧
    (∀ j, (p j ^ 2).totalDegree ≤ D) ∧ (sphereConstraint d * h).totalDegree ≤ D

end LCAntiConc



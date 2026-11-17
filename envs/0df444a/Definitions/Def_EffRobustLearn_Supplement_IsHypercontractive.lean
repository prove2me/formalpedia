-- Prove2me | Definitions.Def_EffRobustLearn_Supplement_IsHypercontractive
-- name    : EffRobustLearn_Supplement_IsHypercontractive
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T10:14:44.422892+00:00
-- url     : https://prove2.me/theorems/0c53f016-9797-481f-9bbe-e636411244b1
-- title:
--   $A$-hypercontractive distributions on $\mathbb R^d$ (Definition 4.1)
-- statement:
--   A probability distribution $D$ on $\mathbb R^d$ is **$A$-hypercontractive** (with respect to polynomials) if $A\ge1$ and
--
--   1. for every real polynomial $p$ on $\mathbb R^d$ of degree $\ell$ and every real $r\ge2$,
--   $$
--   \mathbb E_{x\sim D}\big[|p(x)|^r\big]\le (Ar)^{\ell r}\,\big(\mathbb E_{x\sim D}|p(x)|\big)^r ;
--   $$
--   2. the absolute first moments $\mathbb E_{x\sim D}|x_i|$ of the coordinates are finite.
--
--   The right-hand side uses the $L^1$ norm $\mathbb E|p|$, as in the source. This is the standing assumption of §4: every algorithmic guarantee for low-degree polynomials (Theorems 4.7, 4.14 and D.1) is stated for $A$-hypercontractive distributions.
--
--   **Formalization Note** Points of $\mathbb R^d$ are functions $\mathrm{Fin}\,d\to\mathbb R$ with the product σ-algebra, polynomials are `MvPolynomial (Fin d) ℝ` and the degree is the total degree. Both expectations are lower Lebesgue integrals with values in $[0,\infty]$, so an infinite moment is $+\infty$ (never a junk $0$). That $D$ is a probability measure is a separate hypothesis of each theorem.
-- source:
--   Klivans, Stavropoulos, Tikhonov, Vasilyan, Efficient Robust Learning at the Information-Theoretic Limit, arXiv:2609.17655 (held version, sha256 312a0857…), Definition 4.1, p.18 (PDF p.19)

import Mathlib

open MeasureTheory

namespace EffRobustLearn

namespace Supplement

/-- `A`-hypercontractivity, Definition 4.1 of Klivans, Stavropoulos, Tikhonov, Vasilyan, *Efficient Robust Learning at the Information-Theoretic Limit*, arXiv:2609.17655 (held version, sha256 312a0857…), p.18 (PDF p.19).
A distribution `D` on `ℝ^d` is `A`-hypercontractive if `A ≥ 1` and
1. for every polynomial `p` on `ℝ^d` and every real `r ≥ 2`,
   `E_{x∼D}|p(x)|^r ≤ (A r)^{ℓ r} (E_{x∼D}|p(x)|)^r`, where `ℓ` is the degree of `p`;
2. the absolute expectations `E_{x∼D}|x_i|` of the degree-1 monomials are finite.

**Formalization Note.**
* Points of `ℝ^d` are `Fin d → ℝ` with the product (= Borel) σ-algebra; polynomials are
  `MvPolynomial (Fin d) ℝ` with real coefficients, and the degree is `totalDegree`.
* Both expectations are lower Lebesgue integrals in `ℝ≥0∞`, so an infinite moment is `⊤`, never the
  Bochner integral's junk value `0`; the right side keeps the `L1` norm `E|p|`, as printed (not the
  `L2` Bonami form).
* That `D` is a probability measure is stated separately by every theorem. -/
def IsHypercontractive {d : ℕ} (D : Measure (Fin d → ℝ)) (A : ℝ) : Prop :=
  1 ≤ A ∧
  (∀ (p : MvPolynomial (Fin d) ℝ) (r : ℝ), 2 ≤ r →
    ∫⁻ x, ‖MvPolynomial.eval x p‖ₑ ^ r ∂D ≤
      ENNReal.ofReal ((A * r) ^ ((p.totalDegree : ℝ) * r)) *
        (∫⁻ x, ‖MvPolynomial.eval x p‖ₑ ∂D) ^ r) ∧
  ∀ i : Fin d, ∫⁻ x, ‖x i‖ₑ ∂D < ⊤

end Supplement

end EffRobustLearn



-- Prove2me | Definitions.Def_GaussPart_Supplement_WellBehaved
-- name    : GaussPart_Supplement_WellBehaved
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T05:01:35.477521+00:00
-- url     : https://prove2.me/theorems/525c92de-ab7a-4ad1-8a58-b31b17200e50
-- title:
--   $(\ell,K)$-well-behaved MIM classes (Gaussian $L_1$ sandwiching)
-- statement:
--   Let $\ell:(0,1]\to\mathbb Z_+$ be non-increasing and $K\in\mathbb Z_+$. A class $\mathcal F$ of Boolean $K$-MIMs on $\mathbb R^d$ is **$(\ell,K)$-well-behaved** if
--
--   1. it is closed under affine restrictions;
--   2. it admits **Gaussian $L_1$ sandwiching** of degree $\ell$: for every $f\in\mathcal F$ and every $a\in(0,1)$ there are polynomials $p_l,p_u$ of degree at most $\ell(a)$ with $p_l(x)\le f(x)\le p_u(x)$ for every $x\in\mathbb R^d$ and
--   $$
--   \mathbb E_{x\sim\mathcal N(0,I_d)}[p_u(x)-p_l(x)]\le a;
--   $$
--   3. its Gaussian surface area is finite, $\Gamma(\mathcal F)<\infty$.
--
--   This is the class to which the agnostic QPTAS (Theorem 4.2) and the weak learner (Theorem 4.4) apply; item 2 is spelled out as in Definition 1.5 (ii), which Definition 4.1 abbreviates.
--
--   **Formalization Note** $\ell$ is a function on $\mathbb R$ whose values are constrained only on $(0,1]$; degrees are total degrees of real polynomials in the $d$ coordinates.
-- source:
--   Diakonikolas, Iakovidis, Kane, Ma, Gaussian Partitioning for Reliable Learning of Multi-Index Models, arXiv:2611.05264 (sha256 7e0ca6d4…), Definition 4.1, p.35 (PDF p.37); Definition 1.5, p.3 (PDF p.5)

import Mathlib
import Definitions.Def_GaussPart_Cell
import Definitions.Def_GaussPart_Supplement_BoolFn
import Definitions.Def_GaussPart_Supplement_SurfaceArea

open MeasureTheory ProbabilityTheory

namespace GaussPart

namespace Supplement

/-- `ℓ : (0, 1] → ℤ₊` is non-increasing (Definitions 1.5 and 4.1). The function is total on `ℝ`;
only its values on `(0, 1]` are constrained. -/
def IsDegreeFn (ℓ : ℝ → ℕ) : Prop :=
  (∀ a : ℝ, 0 < a → a ≤ 1 → 1 ≤ ℓ a) ∧ AntitoneOn ℓ (Set.Ioc 0 1)

/-- **Gaussian `L₁` sandwiching of degree `ℓ`** (Definition 1.5 (ii), p.3, PDF p.5, which spells out
Definition 4.1 item 2): for every `f ∈ F` and every `a ∈ (0, 1)` there are polynomials `p_l, p_u` of
degree at most `ℓ(a)` with `p_l(x) ≤ f(x) ≤ p_u(x)` for every `x ∈ ℝᵈ` and
`E_{x∼N(0,I_d)}[p_u(x) − p_l(x)] ≤ a`.

**Formalization Note.** Polynomials are `MvPolynomial (Fin d) ℝ` in the coordinates, the degree is
the total degree, and the expectation is a Bochner integral (a polynomial is Gaussian integrable). -/
def HasSandwiching {d : ℕ} (ℓ : ℝ → ℕ) (F : Set (Vec d → ℝ)) : Prop :=
  ∀ f ∈ F, ∀ a : ℝ, 0 < a → a < 1 →
    ∃ pl pu : MvPolynomial (Fin d) ℝ, pl.totalDegree ≤ ℓ a ∧ pu.totalDegree ≤ ℓ a ∧
      (∀ x, evalPoly pl x ≤ f x ∧ f x ≤ evalPoly pu x) ∧
      ∫ x, (evalPoly pu x - evalPoly pl x) ∂(stdGaussian (Vec d)) ≤ a

/-- **Definition 4.1** (`(ℓ, K)`-well-behaved MIMs), arXiv:2611.05264 (sha256 7e0ca6d4…), p.35
(PDF p.37), with item 2 as in Definition 1.5 (ii), p.3: `ℓ : (0, 1] → ℤ₊` non-increasing, `K ∈ ℤ₊`,
`F` a class of Boolean `K`-MIMs on `ℝᵈ` that is (1) closed under affine restrictions, (2) admits
degree-`ℓ` Gaussian `L₁` sandwiching polynomials and (3) has `Γ(F) < ∞`.

**Formalization Note.** Members of `F` are Borel measurable (`IsBoolFn`), as Definition A.1 requires
for `Γ(f)`. -/
def IsWellBehaved {d : ℕ} (ℓ : ℝ → ℕ) (K : ℕ) (F : Set (Vec d → ℝ)) : Prop :=
  IsDegreeFn ℓ ∧ 1 ≤ K ∧ (∀ f ∈ F, IsBoolFn f ∧ IsKMIM K f) ∧ ClosedUnderAffineRestr F ∧
    HasSandwiching ℓ F ∧ gsaClass F < ⊤

end Supplement

end GaussPart



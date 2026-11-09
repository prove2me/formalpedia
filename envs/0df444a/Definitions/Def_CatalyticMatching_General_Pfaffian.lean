-- Prove2me | Definitions.Def_CatalyticMatching_General_Pfaffian
-- name    : CatalyticMatching_General_Pfaffian
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T10:51:55.052383+00:00
-- url     : https://prove2.me/theorems/02c4f9f2-fb49-4449-ac72-962b4888f57c
-- title:
--   Permutation Pfaffian and zero-aware least degree
-- statement:
--   For an even matrix order $2r$ over a commutative rational algebra, define
--
--   $$\operatorname{Pf}(A)=\frac{1}{2^r r!}\sum_{\sigma\in S_{2r}}\operatorname{sgn}(\sigma)\prod_{j=0}^{r-1}A_{\sigma(2j),\sigma(2j+1)}.$$
--
--   The empty Pfaffian is $1$. Odd orders are extended by zero; the source application has a perfect matching and therefore even order. Rational algebras cover $\mathbb Q[z]$, $\mathbb Q[z][y]$ and multivariate coefficient rings directly. The least degree function is absent on the zero polynomial and otherwise returns its least nonzero exponent. No determinant identity or efficient evaluation theorem is built into the definition.
-- source:
--   Srijan Chakraborty, Samir Datta, Aryan Kusre, Partha Mukhopadhyay, Amit Sinhababu, Maximum Matching and Related Problems in Catalytic Logspace, STOC 2027 submission #479 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/479.pdf, §2 p.9; §3.2.1 p.18

import Mathlib

namespace CatalyticMatching.General

/-- §2 p.9 permutation formula over a rational algebra. Odd order is extended
by zero; at n=0 the empty product, unique permutation and normalization give 1. -/
noncomputable def pfaffian {n : ℕ} {R : Type} [CommRing R] [Algebra ℚ R]
    (A : Matrix (Fin n) (Fin n) R) : R := by
  classical
  exact if h : Even n then
    algebraMap ℚ R ((2^(n/2) * (n/2).factorial : ℚ)⁻¹) *
      ∑ σ : Equiv.Perm (Fin n), ((Equiv.Perm.sign σ : ℤ) : R) *
        ∏ j : Fin (n/2), A (σ ⟨2*j.val, by omega⟩) (σ ⟨2*j.val+1, by omega⟩)
    else 0

/-- Zero-aware least nonzero degree: none on the zero polynomial. -/
noncomputable def leastDegree (P : Polynomial ℚ) : Option ℕ :=
  if P = 0 then none else some P.natTrailingDegree

/-- Zero polynomials have no least nonzero degree. -/
def IsLeastDegree (P : Polynomial ℚ) (w : ℕ) : Prop :=
  P.coeff w ≠ 0 ∧ ∀ j < w, P.coeff j = 0

end CatalyticMatching.General



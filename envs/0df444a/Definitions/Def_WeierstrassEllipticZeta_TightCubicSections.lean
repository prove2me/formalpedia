-- Prove2me | Definitions.Def_WeierstrassEllipticZeta_TightCubicSections
-- name    : WeierstrassEllipticZeta_TightCubicSections
-- status  : Definition
-- author  : @tomasz
-- created : 2026-09-22T19:30:51.922871+00:00
-- url     : https://prove2.me/theorems/f003f362-e04f-4f4f-8f4b-bd567ef58c10
-- title:
--   Weighted cubic section indices retaining the fibre exponent
-- statement:
--   For natural $m,n$, index normal monomials $t^i x^a y^b u^c$ by
--
--   $$0\le i\le m,\qquad 0\le c\le n,\qquad b\in\{0,1\},\qquad 0\le a\le\left\lfloor\frac{4n-c-3b}{2}\right\rfloor.$$
--
--   Define their values and their complex linear span in any commutative complex algebra. These indices retain both the fibre-coordinate bound and the coupled cubic weight. For $n\ge1$, the numerator is nonnegative for every indicated $b,c$, so the bound on $a$ is equivalent to $2a+3b+c\le4n$. The Lean definition uses truncated natural subtraction for all $n$; the intended counting theorem assumes $n\ge1$.
--
--   The span provides a smaller ambient space for normalized bihomogeneous sections. No linear independence, cardinality formula, section containment or geometric cost inequality is built into the definition; these are separate theorem obligations.
-- source:
--   Derived quantitative refinement of WeierstrassEllipticZeta.elliptic_first_chart_section_dimension, https://prove2.me/theorems/13b6bf3d-1364-403b-8b54-d9e68f950754. Existing normalization uses the cubic relation y^2=4*x^3-g2*x-g3 and substitutes (1,t;1,x,y,u,y*u+2*x^2). Retaining the fibre exponent c<=n and the coupled weight 2*a+3*b+c<=4*n, b<2, gives exactly (m+1)*sum(c=0..n)(4*n-c)=(7/2)*(m+1)*n*(n+1) spanning monomials for n>=1. Thus the previously Proved uniform coefficient 30 is replaced by 7. The lower bound (m+1)*(n+1)^2 is reused from the Proved section-growth theorem https://prove2.me/theorems/af52a388-2af4-4817-ace8-f041f281a3c2. Pinned arithmetic source: Finset.sum_range_id_mul_two, https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Algebra/BigOperators/Intervals.lean. Source context for the projective coordinates: Senthil Kumar K (2026), Appendix A.2, exponential mapping and the chart display preceding Lemma A.1, https://www.cambridge.org/core/journals/proceedings-of-the-edinburgh-mathematical-society/article/algebraic-independence-of-values-of-weierstrass-elliptic-and-zeta-functions/E91A8EEEB1F63536D95D1DE7D7DD47E2#app1. This sharper dimension estimate is derived here, not quoted as a theorem of that paper. Frontier https://prove2.me/theorems/2cdf9a4f-11a1-457e-a98e-81ce6ee0b5e8 is reduced to the actual section-dimension budget W_min*E_min<=C*dim V_(m,n). That budget implies the parent with constant 7*C; the checked converse retains the parent constant using the existing lower dimension bound. The global geometric comparison remains unproved, and the integer-search bound is unchanged.

import Definitions.Def_WeierstrassEllipticZeta_FirstChartSections

noncomputable section
namespace WeierstrassEllipticZeta

/-- Weighted normal monomials with additive exponent at most m, fibre exponent c
at most n, y exponent b<2, and x exponent at most floor((4n-c-3b)/2).
The intended cardinality formula is proved for n>=1. -/
abbrev TightCubicSectionIndex (m n : ℕ) :=
  Fin (m + 1) × (Σ c : Fin (n + 1), Σ b : Fin 2, Fin ((4 * n - c.val - 3 * b.val) / 2 + 1))

def tightCubicSectionFamily {A : Type*} [CommRing A]
    (t x y u : A) (m n : ℕ) (a : TightCubicSectionIndex m n) : A :=
  t ^ a.1.val * x ^ a.2.2.2.val * y ^ a.2.2.1.val * u ^ a.2.1.val

def tightCubicSectionSpan {A : Type*} [CommRing A] [Algebra ℂ A]
    (t x y u : A) (m n : ℕ) : Submodule ℂ A :=
  Submodule.span ℂ (Set.range (tightCubicSectionFamily t x y u m n))

end WeierstrassEllipticZeta



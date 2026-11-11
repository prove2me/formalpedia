-- Prove2me | Definitions.Def_MatrixSenseRank_Testing_Moments
-- name    : MatrixSenseRank_Testing_Moments
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T13:46:14.380001+00:00
-- url     : https://prove2.me/theorems/061ddb58-2820-4b94-bd5e-fbd541c98776
-- title:
--   Finite moments, algebraic cumulants and the product-normal law
-- statement:
--   For a Borel probability law $\mu$ on $\mathbb R$, write $m_j(\mu)=\int x^j\,d\mu(x)$. Finite moments through order $q$ means that each power $x^j$, $0\le j\le q$, is integrable. The algebraic cumulants are determined by
--   $$\kappa_{n+1}=m_{n+1}-\sum_{j=0}^{n-1}\binom nj\kappa_{j+1}m_{n-j},\qquad\kappa_0=0.$$
--   Only positive cumulant indices are used. The moment generating function is $M_\mu(t)=\int e^{tx}\,d\mu(x)$; an MGF neighborhood of radius $r>0$ explicitly requires integrability for every $|t|<r$.
--
--   The independent-sum law is the pushforward of $\mu\otimes\nu$ by addition, and the scaled law is the pushforward by $x\mapsto cx$. The product-normal law $D_\times$ is the pushforward of two independent standard normal laws by multiplication. For sparsity parameter $k$, define
--   $$\tau(\mu,k)=\min_{1\le j\le k+1}|\kappa_{2j}(\mu)|.$$
--   These definitions allow cumulants for arbitrary finite-moment noise and inputs without imposing an exponential-moment condition. Fact 20 supplies the compatibility with analytic cumulants when an MGF neighborhood exists.
--
--   **Formalization Note** Raw moments and MGF values use Mathlib's `moment` and `mgf`, respectively, on the identity random variable. The moment-cumulant recurrence is genuinely recursive, with no assumed identities. The minimum has $k+1$ entries and is always over a nonempty finite set. High even raw moments equal their absolute moments.
-- source:
--   Yiqiao Bao, Anindya De, Shivam Nadimpalli, Rocco A. Servedio, Chenyang Sun, Nathan White, STOC 2027 submission #380 (October 2026), §3.1, printed p. 12 / PDF p. 13; §6, Theorem 14 and proof, printed pp. 26–28 / PDF pp. 27–29; §7.1.2, Facts 19–20, printed pp. 31–32 / PDF pp. 32–33; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/380.pdf; PDF SHA-256 6e4e46ced4dfe65bbe94e4cec3e8230032914efef9d87b0f544bbea151a00c3b.

import Mathlib

set_option autoImplicit false
open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace MatrixSenseRank.Testing

noncomputable def rawMoment (μ : Measure ℝ) (j : ℕ) : ℝ := ProbabilityTheory.moment id j μ

/-- Existence of every raw/absolute moment through the indicated order. -/
def FiniteMoments (μ : Measure ℝ) (q : ℕ) : Prop :=
  ∀ j : ℕ, j ≤ q → Integrable (fun x : ℝ => x ^ j) μ

/-- The triangular moment-cumulant polynomial, defined also for finite-moment laws.
κ_(n+1) = m_(n+1) - Σ_(j=0)^(n-1) choose(n,j) κ_(j+1) m_(n-j). -/
noncomputable def cumulantPolynomial (a : ℕ → ℝ) : ℕ → ℝ
  | 0 => 0
  | n + 1 => a (n + 1) - ∑ j : Fin n,
      (n.choose j.val : ℝ) * cumulantPolynomial a (j.val + 1) * a (n - j.val)
termination_by n => n

noncomputable def cumulant (μ : Measure ℝ) (j : ℕ) : ℝ :=
  cumulantPolynomial (rawMoment μ) j

noncomputable def mgfValue (μ : Measure ℝ) (t : ℝ) : ℝ := ProbabilityTheory.mgf id μ t

def MGFNeighborhood (μ : Measure ℝ) (r : ℝ) : Prop :=
  0 < r ∧ ∀ t : ℝ, |t| < r → Integrable (fun x : ℝ => Real.exp (t * x)) μ

noncomputable def independentSum (μ ν : Measure ℝ) : Measure ℝ :=
  Measure.map (fun p : ℝ × ℝ => p.1 + p.2) (μ.prod ν)

noncomputable def scaledLaw (c : ℝ) (μ : Measure ℝ) : Measure ℝ :=
  Measure.map (fun x : ℝ => c * x) μ

noncomputable def productNormal : Measure ℝ :=
  Measure.map (fun p : ℝ × ℝ => p.1 * p.2)
    ((gaussianReal 0 1).prod (gaussianReal 0 1))

/-- Minimum includes κ₂, as in Theorem 14's displayed definition of τ. -/
noncomputable def cumulantFloor (μ : Measure ℝ) (k : ℕ) : ℝ :=
  Finset.univ.inf' Finset.univ_nonempty
    (fun j : Fin (k + 1) => |cumulant μ (2 * (j.val + 1))|)

end MatrixSenseRank.Testing



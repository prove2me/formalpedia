-- Prove2me | Definitions.Def_MonoABPWidth_Hierarchy_Supplement_weights
-- name    : MonoABPWidth_Hierarchy_Supplement_weights
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T21:34:41.878319+00:00
-- url     : https://prove2.me/theorems/9a2b3b93-c0db-4432-a774-dfc3fd6429cf
-- title:
--   Relevant polynomials, compatible weights, and the generic lower-bound inequalities
-- statement:
--   For a fixed monotone real polynomial $p$, a monotone polynomial $q$ is relevant when there exist monotone polynomials $a,b$ with $p=qa+b$, exactly as stated in §7. A weight $w$ takes finite nonnegative real values on polynomials, is subadditive and submultiplicative on monotone polynomials, and is at most one on variables and nonnegative constants. A growth function $G:\mathbb N\to\mathbb R_{\ge0}$ is nondecreasing, is at least one, bounds $w(q)$ for relevant $q$ of each degree, and equals $w(p)$ at every monomial degree present in $p$.
--
--   For an arbitrary extended nonnegative lower-bound function $L$, the complete conditions are
--   $$L(1,d)\le G(1)\quad(d\ge0),$$
--   $$L\left(\sum_{i=1}^{\ell}n_i,d\right)\le \frac{G(\sum_i n_i)}{\prod_i G(n_i)}\sum_i L(n_i,d-1)\quad(d,\ell,n_i\ge1).$$
--   The ratio is formed in nonnegative real arithmetic before conversion to extended values. One-part decompositions are included, and $L(n,0)$ can be infinite. These conditions contain no formula lower bound as an assumption. Growth bounds are read as bounds on relevant polynomials, following the surrounding §7 text.
-- source:
--   Julian Dörfler, Alexander Rogovskyy, STOC 2027 submission #927 (October 2026), §7, pp.18–20, PDF19–21, (7.3)–(7.4)

import Definitions.Def_MonoABPWidth_Hierarchy_Supplement_formulas

open scoped BigOperators ENNReal

namespace MonoABPWidth.Hierarchy.Supplement

/-- §7, p.18: the source's explicit relevance predicate. No bound or desired
formula lower bound is built into relevance. -/
def Relevant {σ : Type} (p q : MvPolynomial σ ℝ) : Prop :=
  MonotonePolynomial q ∧ ∃ a b : MvPolynomial σ ℝ,
    MonotonePolynomial a ∧ MonotonePolynomial b ∧ p = q * a + b

/-- Nonnegative, subadditive and submultiplicative weights on monotone polynomials,
with the leaf bounds of §7. Scalar-variable leaves follow by submultiplicativity. -/
structure PolynomialWeight (σ : Type) where
  weight : MvPolynomial σ ℝ → NNReal
  add_le : ∀ q r, MonotonePolynomial q → MonotonePolynomial r →
    weight (q + r) ≤ weight q + weight r
  mul_le : ∀ q r, MonotonePolynomial q → MonotonePolynomial r →
    weight (q * r) ≤ weight q * weight r
  variable_le : ∀ x : σ, weight (MvPolynomial.X x) ≤ 1
  constant_le : ∀ c : NNReal, weight (MvPolynomial.C (c : ℝ)) ≤ 1

/-- Growth bounds concern relevant polynomials, as clarified by the §7 context.
Equality is required for every degree present in p, not only its maximum degree. -/
def Compatible {σ : Type} (p : MvPolynomial σ ℝ) (w : PolynomialWeight σ)
    (Gr : ℕ → NNReal) : Prop :=
  Monotone Gr ∧ (∀ n, 1 ≤ Gr n) ∧
  (∀ q, Relevant p q → w.weight q ≤ Gr q.totalDegree) ∧
  (∀ m ∈ p.support, Gr (m.sum (fun _ e => e)) = w.weight p)

/-- Both (7.3) and (7.4). All positive ordered decompositions, including one part,
are quantified. Coefficients are positive real ratios, then embedded into ENNReal.
The lower-bound function can take +infinity. -/
def LowerBoundConditions (Gr : ℕ → NNReal) (L : ℕ → ℕ → ℝ≥0∞) : Prop :=
  (∀ d : ℕ, L 1 d ≤ (Gr 1 : ℝ≥0∞)) ∧
  (∀ (d ℓ : ℕ), 1 ≤ d → 1 ≤ ℓ → ∀ ns : Fin ℓ → ℕ,
    (∀ i, 1 ≤ ns i) →
    L (∑ i, ns i) d ≤
      (↑(Gr (∑ i, ns i) / ∏ i, Gr (ns i)) : ℝ≥0∞) *
        ∑ i, L (ns i) (d - 1))

end MonoABPWidth.Hierarchy.Supplement



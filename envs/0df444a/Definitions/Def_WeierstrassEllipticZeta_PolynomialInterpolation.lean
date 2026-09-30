-- Prove2me | Definitions.Def_WeierstrassEllipticZeta_PolynomialInterpolation
-- name    : WeierstrassEllipticZeta_PolynomialInterpolation
-- status  : Definition
-- author  : @tomasz
-- created : 2026-09-14T01:07:34.634823+00:00
-- url     : https://prove2.me/theorems/561b129b-a2df-40dd-8742-e3b9fd39851f
-- title:
--   Elliptic polynomial sums and the two interpolation estimates
-- statement:
--   For a complex period lattice $\Lambda$, let $\wp,\zeta,\wp'$ denote its canonical Weierstrass functions. For positive integers $d,l$ and a complex coefficient array $p=(p_{ijk})$, set
--   $$P(w)=\sum_{i=0}^{d}\sum_{j,k=0}^{l}p_{ijk}w^i\wp(w)^j\zeta(w)^k.$$
--   The exponents are bounded separately by $(d,l,l)$; they need not attain these bounds. For a complex number $v$ put
--   $$M_1(v,l)=\max_{a,b,c\ge0,\ a+b+c\le5l}\left(1+|\zeta(v)^a\wp(v)^b\wp'(v)^c|\right).$$
--   The maximum is finite; its constant monomial contributes $2$.
--
--   The two interpolation predicates encode the following requirements for a given function $\sigma$ and real parameters $C,R_0$, using $c_{13}=C$ for the first predicate and $c_{14}=C$ for the second. The predicates themselves impose no normalization on $\sigma$ or sign restriction on $C,R_0$; theorems impose the intended positivity and sigma conditions.
--
--   For every positive $d,l,M$, every array with $|p_{ijk}|\le M$, and every $u\in\mathbb C$, the expression
--   $$F(z)=\sigma(z+u)^{3l}P(z+u)$$
--   has an entire extension. Choose this extension before the radii and derivative data. If $2<r<R$, $R>R_0$, $|u|<R$, $|v|<r-2$, and $F$ has at least $N\ge0$ zeros counted with multiplicity in $|z|<r$, then for every integer $t\ge0$,
--   $$|F^{(t)}(v)|\le t!(d+1)(l+1)^2M(2R)^d c_{13}^{R^2l}\left(\frac{2r}{R}\right)^N.$$
--
--   For every positive $d,l,M$, every array with $|p_{ijk}|\le M$, and every $v\notin\Lambda$, the expression
--   $$G(z)=\sigma(z)^{15l}[2(\wp(v)-\wp(z))]^{3l}P(z+v)$$
--   has an entire extension. Choose this extension before the radii and derivative data. If $2<r<R$, $R>R_0$, $|v|<R$, $|u|<r-2$, and $G$ has at least $N\ge0$ zeros counted with multiplicity in $|z|<r$, then for every integer $t\ge0$,
--   $$|G^{(t)}(u)|\le t!(d+1)(l+1)^2(5l+1)^6M(2R)^dM_1(v,l)c_{14}^{R^2l}\left(\frac{2r}{R}\right)^N.$$
--
--   **Formalization note.** A lower bound on the number of zeros is expressed by an arbitrary finite set $s\subset\{|z|<r\}$ and arbitrary multiplicities $m(a)\ge0$ with $N\le\sum_{a\in s}m(a)$, together with vanishing of every derivative of order below $m(a)$ at each $a\in s$. The estimate holds for every such witness. Empty sets, $N=0$, $t=0$, and the zero coefficient array are included. The product identities specify the extensions only where all meromorphic factors are regular: $z+u\notin\Lambda$ in the first case, and $z,z+v\notin\Lambda$ in the second. Zeros and derivative evaluation points may lie at excluded points of those product formulas, because they refer to the entire extensions. No condition $2r<R$ is imposed. The constants raised to $R^2l$ use real powers; all other displayed exponents are integers.
--
--   The polynomial index set, evaluation, and maximum are also defined when either degree parameter is zero. The height at l=0 is 2. The interpolation predicates only require their conclusions for strictly positive d and l. These lightweight definitions record the statement of Lemma 6; they contain no proof obligations asserted as facts.
-- source:
--   Senthil Kumar K (2026), Algebraic independence of values of Weierstrass elliptic and zeta functions, https://doi.org/10.1017/S001309152610145X, §4, Lemma 6(i)–(ii), equations (14)–(15) and the proof of Lemma 6.

import Definitions.Def_WeierstrassEllipticZeta_SigmaDifferential
import Definitions.Def_WeierstrassEllipticZeta_EntireRegularization
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Analysis.SpecialFunctions.Pow.Real

noncomputable section
open Finset Set
open scoped NNReal

namespace WeierstrassEllipticZeta

/-- The rectangular monomial indices for a polynomial of degrees (d,l,l). -/
abbrev EllipticPolynomialIndex (d l : ℕ) := Fin (d + 1) × Fin (l + 1) × Fin (l + 1)

/-- Evaluation of a rectangular polynomial at (z,wp(z),zeta(z)). -/
def ellipticRectangularPolynomial (L : PeriodPair) (d l : ℕ)
    (p : EllipticPolynomialIndex d l → ℂ) (z : ℂ) : ℂ :=
  ∑ i, p i * z ^ i.1.val * L.weierstrassP z ^ i.2.1.val *
    weierstrassZeta L z ^ i.2.2.val

/-- The finite maximum M1 in the cleared estimate of Lemma 6. -/
def ellipticInterpolationHeight (L : PeriodPair) (v : ℂ) (l : ℕ) : ℝ :=
  ↑((Finset.univ.filter (fun i : Fin (5*l+1) × Fin (5*l+1) × Fin (5*l+1) =>
    i.1.val + i.2.1.val + i.2.2.val ≤ 5*l)).sup (fun i =>
      (1 : ℝ≥0) + ‖weierstrassZeta L v ^ i.1.val *
        L.weierstrassP v ^ i.2.1.val * L.derivWeierstrassP v ^ i.2.2.val‖₊))

/-- Entire extension and zero-count derivative estimate for a shifted polynomial. -/
def SigmaPolynomialInterpolation (L : PeriodPair) (σ : ℂ → ℂ) (C R₀ : ℝ) : Prop :=
  ∀ (d l : ℕ), 0 < d → 0 < l →
    ∀ (p : EllipticPolynomialIndex d l → ℂ) (M : ℝ), 0 < M →
      (∀ i, ‖p i‖ ≤ M) → ∀ u : ℂ,
      ∃ F : ℂ → ℂ, AnalyticOnNhd ℂ F univ ∧
        (∀ z : ℂ, z + u ∉ L.lattice →
          F z = σ (z + u) ^ (3*l) * ellipticRectangularPolynomial L d l p (z+u)) ∧
        ∀ (r R : ℝ), 2 < r → r < R → R₀ < R → ‖u‖ < R →
          ∀ v : ℂ, ‖v‖ < r-2 →
          ∀ (N : ℕ) (s : Finset ℂ) (m : ℂ → ℕ),
            (∀ a ∈ s, ‖a‖ < r) →
            (∀ a ∈ s, ∀ j < m a, iteratedDeriv j F a = 0) →
            N ≤ ∑ a ∈ s, m a → ∀ t : ℕ,
              ‖iteratedDeriv t F v‖ ≤
                t.factorial * (d+1 : ℕ) * (l+1 : ℕ)^2 * M * (2*R)^d *
                  C ^ (R^2 * l) * (2*r/R)^N

/-- Entire extension and zero-count derivative estimate after clearing addition poles. -/
def ClearedSigmaPolynomialInterpolation (L : PeriodPair) (σ : ℂ → ℂ)
    (C R₀ : ℝ) : Prop :=
  ∀ (d l : ℕ), 0 < d → 0 < l →
    ∀ (p : EllipticPolynomialIndex d l → ℂ) (M : ℝ), 0 < M →
      (∀ i, ‖p i‖ ≤ M) → ∀ v : ℂ, v ∉ L.lattice →
      ∃ G : ℂ → ℂ, AnalyticOnNhd ℂ G univ ∧
        (∀ z : ℂ, z ∉ L.lattice → z + v ∉ L.lattice →
          G z = σ z ^ (15*l) * (2*(L.weierstrassP v - L.weierstrassP z)) ^ (3*l) *
            ellipticRectangularPolynomial L d l p (z+v)) ∧
        ∀ (r R : ℝ), 2 < r → r < R → R₀ < R → ‖v‖ < R →
          ∀ u : ℂ, ‖u‖ < r-2 →
          ∀ (N : ℕ) (s : Finset ℂ) (m : ℂ → ℕ),
            (∀ a ∈ s, ‖a‖ < r) →
            (∀ a ∈ s, ∀ j < m a, iteratedDeriv j G a = 0) →
            N ≤ ∑ a ∈ s, m a → ∀ t : ℕ,
              ‖iteratedDeriv t G u‖ ≤
                t.factorial * (d+1 : ℕ) * (l+1 : ℕ)^2 * (5*l+1 : ℕ)^6 * M *
                  (2*R)^d * ellipticInterpolationHeight L v l *
                  C ^ (R^2 * l) * (2*r/R)^N

end WeierstrassEllipticZeta



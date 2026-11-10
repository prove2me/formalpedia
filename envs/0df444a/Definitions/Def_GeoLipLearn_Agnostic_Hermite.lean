-- Prove2me | Definitions.Def_GeoLipLearn_Agnostic_Hermite
-- name    : GeoLipLearn_Agnostic_Hermite
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-09T18:51:59.717571+00:00
-- url     : https://prove2.me/theorems/bdb5ac7f-b238-47a6-ba00-24a8b40bdeb0
-- title:
--   Normalized Hermite truncation and finite polynomial coefficient conventions
-- statement:
--   For the probabilists' normalization,
--   $$H_n(t)=\sqrt{n!}\sum_{m=0}^{\lfloor n/2\rfloor}\frac{(-1)^m t^{n-2m}}{2^m m!(n-2m)!},\qquad H_\nu(x)=\prod_i H_{\nu_i}(x_i).$$
--   The degree-at-most-$k$ truncation is $f_{\le k}=\sum_{|\nu|\le k}(\int fH_\nu\,d\gamma_d)H_\nu$. Its finite sum is indexed by coordinate exponents in $\{0,\ldots,k\}$ and filtered by total degree.
--
--   For machine input and output, monomial coefficients are ordered recursively by the first coordinate exponent $j=0,\ldots,k$, followed by the corresponding order in $d-1$ coordinates with degree budget $k-j$. There are $\binom{d+k}{k}$ coefficients, including zeros. The function decoded from a coefficient list is the corresponding finite sum of monomials; input coefficients are extracted from the actual multivariate polynomial.
--
--   Equation (25) sets $b=\eta/[4(4B+1)]$, $t=b^2/4$, and $k=\max\{1,\lceil t^{-1}\log\max(2/b,2/\alpha)\rceil\}$. The learner uses this definition at $(\eta/2,\alpha/2)$. These conventions specify the analytic truncation and the finite polynomial interface without postulating an approximation theorem.
-- source:
--   Lange, Marcussen and Vasilyan, Geometrically Constrained Learning II: Agnostic Proper Learning of Lipschitz Functions, STOC 2027 submission (manuscript sha256 45cb3c98836346299afa2ee9b2ff10d9d9a3fc8dcbbb9ecc23da2c89a9de615d), pp.12–13, Hermite expansions; p.16, Algorithm 1; p.41, Equation (25)

import Definitions.Def_GeoLipLearn_Agnostic_Gaussian

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

namespace GeoLipLearn.Agnostic

/-- Normalized probabilists' Hermite polynomial, the explicit formula on p.13. -/
noncomputable def hermite (n : ℕ) (x : ℝ) : ℝ :=
  Real.sqrt (n.factorial : ℝ) * ∑ m ∈ Finset.range (n / 2 + 1),
    (-1 : ℝ)^m * x^(n-2*m) /
      ((2 : ℝ)^m * (m.factorial : ℝ) * ((n-2*m).factorial : ℝ))
noncomputable def hermiteMulti {d : ℕ} (ν : Fin d → ℕ) (x : Space d) : ℝ :=
  ∏ i, hermite (ν i) (x i)
noncomputable def truncation {d : ℕ} (k : ℕ) (f : Space d → ℝ) (x : Space d) : ℝ :=
  ∑ ν : Fin d → Fin (k+1), if (∑ i, (ν i).val) ≤ k then
    (∫ y, f y * hermiteMulti (fun i => (ν i).val) y ∂gaussian d) *
      hermiteMulti (fun i => (ν i).val) x else 0
/-- Dense graded monomial list: exponent vectors of total degree at most k, recursively
lexicographic in the first coordinate. Unlike a box of exponents it has binom(d+k,k) entries. -/
def exponents : ℕ → ℕ → List (List ℕ)
  | 0, _ => [[]]
  | d+1, k => (List.range (k+1)).flatMap fun j => (exponents d (k-j)).map (j :: ·)
noncomputable def monomialValue {d : ℕ} (ν : List ℕ) (x : Space d) : ℝ :=
  ∏ i : Fin d, x i ^ ν[i.val]!
noncomputable def coefficientFunction (d k : ℕ) (a : List ℝ) (x : Space d) : ℝ :=
  (((exponents d k).zip a).map fun v => v.2 * monomialValue v.1 x).sum
noncomputable def coefficients {d : ℕ} (k : ℕ) (p : Poly d) : List ℝ :=
  (exponents d k).map fun ν => p.coeff (Finsupp.equivFunOnFinite.symm (fun i : Fin d => ν[i.val]!))
/-- Equation (25), before the mandated substitution eta/2, alpha/2. -/
noncomputable def degree25 (B η α : ℝ) : ℕ :=
  let b := η / (4 * (4*B+1))
  let t := b^2 / 4
  max 1 ⌈t⁻¹ * Real.log (max (2/b) (2/α))⌉₊

end GeoLipLearn.Agnostic



-- Prove2me | Definitions.Def_DenseLanguageGeneration_PatientScope_Supplement_multiOrder
-- name    : DenseLanguageGeneration_PatientScope_Supplement_multiOrder
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T17:59:08.397422+00:00
-- url     : https://prove2.me/theorems/cee016cc-f0bf-435e-831e-8e7824040370
-- title:
--   Order prefixes and deterministic and randomized densities
-- statement:
--   An order $\sigma:\mathbb Z_{>0}\simeq\mathbb Z_{>0}$ is read as a sequence: its first $n$ elements form $[n]_\sigma=\{\sigma(1),\ldots,\sigma(n)\}$. For a set $S$, put $\mu_{\sigma,n}(S)=|[n]_\sigma\cap S|$. With $D$ the generator's ownership set and $D_\omega$ its randomized version, define
--
--   $$\underline d_\sigma(G,K,a)=\liminf_{n\to\infty}\frac{\mu_{\sigma,n}(D\cap K)}{\mu_{\sigma,n}(K)},\qquad
--   \underline d_\sigma(R,K,a)=\liminf_{n\to\infty}\frac{\mathbb E_\omega[\mu_{\sigma,n}(D_\omega\cap K)]}{\mu_{\sigma,n}(K)}.$$
--
--   Zero denominators give ratio zero. Every infinite language has eventually positive counts under every bijection. The randomized prefix counts are measurable and bounded by $n$. For a positive finite number of orders, a common lower bound on every component is equivalent to that lower bound on their minimum, as in Definitions 5.1 and 5.8.
--
--   The module also defines the scalar bound from Theorem 5.3,
--
--   $$h_k(m)=1-\frac{4(km+1)^{1-1/k}+1}{m}.$$
--
--   The exponent is real. No positivity of $h_k(m)$ is assumed. These objects allow one algorithm's coverage to be evaluated simultaneously under all prescribed orders.
-- source:
--   Ziyi Cai, Shuangping Li, Yiheng Shen, Kangning Wang and Peng Zhang, Dense Language Generation Made Simple: Deterministic, Randomized, and Multi-Order Algorithms, STOC 2027 submission #335 (October 2026), §2 notation, printed pp.6–7 (PDF pp.8–9); Definitions 5.1 and 5.8, printed pp.27, 35 (PDF pp.29, 37); Theorem 5.3, printed pp.27–28 (PDF pp.29–30); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/335.pdf

import Definitions.Def_DenseLanguageGeneration_PatientScope_Supplement_randomized

set_option autoImplicit false
open ActiveLanguageGeneration.Hierarchy
open DenseLanguageGeneration.PatientScope
open MeasureTheory Filter
noncomputable section

namespace DenseLanguageGeneration.PatientScope.Supplement

/-- §2 and §5 (printed pp.6–7, 27 / PDF pp.8–9, 29). An order is a bijection
σ : ℕ+ → ℕ+ read as a sequence; [n]_σ = σ([n]) = {σ(1),...,σ(n)}, the first n
integers in the order σ (an image, not a preimage). Empty at n = 0. -/
def orderPrefix (σ : ℕ+ ≃ ℕ+) (n : ℕ) : Finset ℕ+ :=
  (Finset.range n).image (fun j => σ (positive j))

/-- μ_{σ,n}(S) = |[n]_σ ∩ S|, for an arbitrary set S. -/
def orderCount (σ : ℕ+ ≃ ℕ+) (S : Set ℕ+) (n : ℕ) : ℕ := by
  classical
  exact ((orderPrefix σ n).filter (fun x => x ∈ S)).card

/-- Definition 5.1, one order: μ_{σ,n}(D ∩ K) / μ_{σ,n}(K), 0 at a zero denominator. -/
def orderRatio (G : Generator ℕ+) (K : ActiveLanguageGeneration.Hierarchy.Language ℕ+)
    (a : ℕ → ℕ+) (σ : ℕ+ ≃ ℕ+) (n : ℕ) : ℝ :=
  (orderCount σ (defenderOwned G a ∩ K.val) n : ℝ) / (orderCount σ K.val n : ℝ)

/-- Definition 5.1: liminf along the prefixes of the order σ. The lower density
under k orders is the minimum of these over the k orders. -/
def orderLowerDensity (G : Generator ℕ+) (K : ActiveLanguageGeneration.Hierarchy.Language ℕ+)
    (a : ℕ → ℕ+) (σ : ℕ+ ≃ ℕ+) : ℝ :=
  Filter.liminf (orderRatio G K a σ) atTop

/-- Definition 5.8, one order: E[μ_{σ,n}(D ∩ K)] / μ_{σ,n}(K) on a fixed enumeration,
the expectation over the algorithm's sample only; 0 at a zero denominator. -/
def randomizedOrderRatio (R : RandomizedGenerator)
    (K : ActiveLanguageGeneration.Hierarchy.Language ℕ+) (a : ℕ → ℕ+) (σ : ℕ+ ≃ ℕ+)
    (n : ℕ) : ℝ :=
  MeasureTheory.integral R.P
      (fun ω => (orderCount σ (defenderOwned (R.gen ω) a ∩ K.val) n : ℝ)) /
    (orderCount σ K.val n : ℝ)

/-- Definition 5.8: liminf along the prefixes of the order σ. -/
def randomizedOrderLowerDensity (R : RandomizedGenerator)
    (K : ActiveLanguageGeneration.Hierarchy.Language ℕ+) (a : ℕ → ℕ+) (σ : ℕ+ ≃ ℕ+) : ℝ :=
  Filter.liminf (randomizedOrderRatio R K a σ) atTop

/-- Theorem 5.3 (printed p.28 / PDF p.30): h(m) = 1 − (4·(km+1)^(1−1/k) + 1)/m,
a real power. It may be ≤ 0 for small m. -/
def pairedBound (k m : ℕ) : ℝ :=
  1 - (4 * ((k : ℝ) * (m : ℝ) + 1) ^ (1 - 1 / (k : ℝ)) + 1) / (m : ℝ)

end DenseLanguageGeneration.PatientScope.Supplement



-- Prove2me | Definitions.Def_DenseLanguageGeneration_PatientScope_Supplement_randomized
-- name    : DenseLanguageGeneration_PatientScope_Supplement_randomized
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T17:58:18.336292+00:00
-- url     : https://prove2.me/theorems/4556aa6e-0b8a-4bc6-b2f7-4246182ecedf
-- title:
--   Expected prefix counts and randomized lower density
-- statement:
--   Fix an infinite language $K\subseteq\mathbb Z_{>0}$, an enumeration $a$, and a randomized generator $R=(\Omega,P,g)$. Let $D_\omega$ be the integers announced by $g_\omega$ strictly before their first announcement by the adversary. Inputs precede responses within a round. Write $\mu_n(S)=|S\cap\{1,\ldots,n\}|$. Define
--
--   $$r_R(K,a,n)=\frac{\mathbb E_{\omega\sim P}[\mu_n(D_\omega\cap K)]}{\mu_n(K)},\qquad
--   \underline d_R(K,a)=\liminf_{n\to\infty}r_R(K,a,n).$$
--
--   The expectation is over the generator's seed only, with $a$ fixed independently of that seed. Each prefix count is measurable, bounded by $n$, and integrable. The ratio is assigned zero when its denominator is zero; infinitude of $K$ makes the denominator eventually positive. The liminf is taken after the expectation. Also define the paper's scalar function
--
--   $$f(m)=1-\left(1-\frac1{m+1}\right)^m.$$
--
--   These definitions provide the expected-coverage statistic of Definition 4.1 and the bound in Theorem 4.3. Ownership and finite counting are imported from the published base definitions.
-- source:
--   Ziyi Cai, Shuangping Li, Yiheng Shen, Kangning Wang and Peng Zhang, Dense Language Generation Made Simple: Deterministic, Randomized, and Multi-Order Algorithms, STOC 2027 submission #335 (October 2026), Definition 4.1, printed p.18 (PDF p.20); Theorems 2.3 and 4.3, printed pp.8, 18–19 (PDF pp.10, 20–21); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/335.pdf

import Definitions.Def_DenseLanguageGeneration_PatientScope_density
import Definitions.Def_DenseLanguageGeneration_PatientScope_Supplement_randomizedAlgorithm

set_option autoImplicit false
open ActiveLanguageGeneration.Hierarchy
open DenseLanguageGeneration.PatientScope
open MeasureTheory Filter
noncomputable section

namespace DenseLanguageGeneration.PatientScope.Supplement

/-- E[μ_n(D ∩ K)] against a FIXED enumeration a (non-adaptive adversary): the
expectation is over the algorithm's sample only, D = defenderOwned (gen ω) a.
For fixed a, membership in D is a countable union of measurable output fibres;
this finite-prefix count is measurable and lies between 0 and n, hence integrable. -/
def expectedOwnedCount (R : RandomizedGenerator)
    (K : ActiveLanguageGeneration.Hierarchy.Language ℕ+) (a : ℕ → ℕ+) (n : ℕ) : ℝ :=
  MeasureTheory.integral R.P
    (fun ω => (prefixCount (defenderOwned (R.gen ω) a ∩ K.val) n : ℝ))

/-- Definition 4.1: E[μ_n(D ∩ K)] / μ_n(K), with value 0 at a zero denominator. -/
def randomizedRatio (R : RandomizedGenerator)
    (K : ActiveLanguageGeneration.Hierarchy.Language ℕ+) (a : ℕ → ℕ+) (n : ℕ) : ℝ :=
  expectedOwnedCount R K a n / (prefixCount K.val n : ℝ)

/-- Definition 4.1 (printed p.18 / PDF p.20): liminf of the ratio of expectations
(not the expectation of a liminf), on the fixed enumeration a. -/
def randomizedLowerDensity (R : RandomizedGenerator)
    (K : ActiveLanguageGeneration.Hierarchy.Language ℕ+) (a : ℕ → ℕ+) : ℝ :=
  Filter.liminf (randomizedRatio R K a) atTop

/-- Theorem 2.3 (printed p.8 / PDF p.10): f(m) = 1 − (1 − 1/(m+1))^m. -/
def rankingRatio (m : ℕ) : ℝ := 1 - (1 - 1 / ((m : ℝ) + 1)) ^ m

end DenseLanguageGeneration.PatientScope.Supplement



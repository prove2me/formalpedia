-- Prove2me | Definitions.Def_ConformalOutlierTesting_Basic
-- name    : ConformalOutlierTesting_Basic
-- status  : Definition
-- author  : @Xeroth
-- created : 2026-11-24T07:53:53.230192+00:00
-- url     : https://prove2.me/theorems/a3975bc1-ecef-41a3-b092-6c8ad2d1af65
-- title:
--   Conformal p-values, PRDS, FDR procedures and calibration-conditional adjustments
-- statement:
--   Objects of Sections 1–4 and Appendix A of Bates, Candès, Lei, Romano and Sesia, *Testing for Outliers with Conformal p-values* (arXiv:2104.08279v3). The training data are held fixed, so every object is a function of the scores $\hat s(X)$.
--
--   1. **Scores and their law.** There are $n$ calibration scores $s=(s_1,\dots,s_n)$ and $m$ test scores $t=(t_1,\dots,t_m)$. Their joint law is $\mu^{\otimes n}\otimes\bigotimes_{j=1}^m\nu_j$. Here $\mu$ is the law of $\hat s(X)$ for $X\sim P_X$, and $\nu_j$ is the score law of test point $j$, with $\nu_j=\mu$ for an inlier. So the calibration scores are i.i.d., and all test scores are independent of each other and of the calibration data.
--   2. **Marginal conformal p-value (eq. 3).** $\hat u^{(\mathrm{marg})}(x)=\dfrac{1+|\{i:s_i\le x\}|}{n+1}$. The vector of test p-values is $p_j=\hat u^{(\mathrm{marg})}(t_j)$.
--   3. **Order statistics.** $s_{(1)}\le\dots\le s_{(n)}$ is the sorted vector.
--   4. **PRDS (Definition 1).** A set $A\subseteq\mathbb R^m$ is increasing if $a\in A$ and $b\succeq a$ coordinatewise imply $b\in A$. A random vector $X$ is PRDS on $I_0$ if, for every $i\in I_0$ and every measurable increasing $A$, the conditional probability $\mathbb P[X\in A\mid X_i=x]$ has a version that is nondecreasing in $x$.
--   5. **FDR (eq. 7).** For a rejection set $\mathcal R$ and true nulls $\mathcal H_0$, the false discovery proportion is $|\mathcal R\cap\mathcal H_0|/\max\{1,|\mathcal R|\}$, and the FDR is its expectation.
--   6. **BH.** $R(\alpha)=\max\{r\in\{0,\dots,m\}:|\{i:p_i\le r\alpha/m\}|\ge r\}$, and the procedure rejects $\{i:p_i\le\alpha R(\alpha)/m\}$.
--   7. **Storey–BH (Appendix A.4).** Let $A=\sum_i I(p_i\ge\lambda)$ and $\hat\pi_0=(1+A)/(m(1-\lambda))$. Let $R=\max\{r:p_{(r)}\le\alpha r/(m\hat\pi_0),\ p_{(r)}<\lambda\}$, with $R=0$ if no $r$ qualifies. The procedure rejects $\{i:p_i\le\alpha R/(m\hat\pi_0),\ p_i<\lambda\}$.
--   8. **Calibration-conditional adjustment (eqs. 10–11).** A sequence $b_0=0\le b_1\le\dots\le b_n\le b_{n+1}=1$ satisfies the band condition at level $\delta$ if $\mathbb P[U_{(1)}\le b_1,\dots,U_{(n)}\le b_n]\ge1-\delta$ for $U_1,\dots,U_n$ i.i.d. uniform on $[0,1]$. The adjustment function is $h(t)=b_{\lceil(n+1)t\rceil}$.
--   9. **False positive rate (eq. 9).** $\mathrm{FPR}(\alpha;\mathcal D)=\mu\{x:\hat u^{(\mathrm{marg})}(x)\le\alpha\}$, as a function of the calibration scores.
--   10. **Fisher's test.** The statistic is $-2\sum_i\log\hat u^{(\mathrm{marg})}(t_i)$. $\chi^2(k;q)$ is the $q$-quantile $\inf\{x:F(x)\ge q\}$ of the chi-square law with $k$ degrees of freedom, which is the gamma law with shape $k/2$ and rate $1/2$. $z_q$ is the $q$-quantile of $N(0,1)$ and $\bar\Phi=1-\Phi$. The conditional type-I error given $\mathcal D$ is the $\mu^{\otimes m}$-probability of rejection with the calibration scores fixed.
--   11. **Correlation.** $\mathrm{Cor}[X,Y]=\mathrm{Cov}[X,Y]/\sqrt{\mathrm{Var}X\,\mathrm{Var}Y}$.
--
--   **Formalization Note** The test scores are modelled as independent of each other and of the calibration data, as in Section 1.1. Theorem 2 as printed asks only that the inliers be independent. Its proof assumes this full independence (see the note on Theorem 2). The Storey–BH estimate uses $I(p_i\ge\lambda)$, as in Appendix A.4 and its proofs. The main text (Section 2.3) writes $I(p_i>\lambda)$.
-- source:
--   Bates, Candès, Lei, Romano and Sesia, Testing for Outliers with Conformal p-values, arXiv:2104.08279v3 (2022), Section 1.1 eq. (3), Section 2.1, Section 2.2 Definition 1 and eq. (7), Section 3.1 eq. (9), Section 3.2 eqs. (10)-(11), Section 3.6.4, Appendix A.4 (p. 42)

import Mathlib

/-!
Bates, Candès, Lei, Romano and Sesia, *Testing for Outliers with Conformal p-values*,
arXiv:2104.08279v3: marginal conformal p-values (Section 1.1, eq. (3)), positive regression
dependence (Section 2.2, Definition 1), the false discovery rate with the Benjamini–Hochberg and
Storey–BH procedures (Section 2.2, eq. (7); Appendix A.4), calibration-conditional adjustments
(Section 3.2, eqs. (10)–(11)), the pointwise false positive rate (Section 3.1, eq. (9)) and the
quantities of Fisher's combination test (Section 2.1).

The training data are treated as fixed (Section 1.1), so every object is a function of the scores
`ŝ(X_i)`: calibration scores `s : Fin n → ℝ` and test scores `t : Fin m → ℝ`.
-/

open MeasureTheory ProbabilityTheory

noncomputable section

namespace ConformalOutlierTesting

variable {n m : ℕ}

/-- Section 1.1, eq. (3): the marginal conformal p-value of a test score `x` given calibration
scores `s₁, …, sₙ`, `û^(marg)(x) = (1 + |{i : sᵢ ≤ x}|) / (n + 1)`. -/
def margPval (s : Fin n → ℝ) (x : ℝ) : ℝ :=
  (1 + ((Finset.univ.filter fun i => s i ≤ x).card : ℝ)) / (n + 1)

/-- The order statistics `s₍₁₎ ≤ ⋯ ≤ s₍ₙ₎` of a vector, indexed from `0`: `orderStat s k = s₍ₖ₊₁₎`
(Section 3.2, Theorem 4; Appendix A.3, `Z = (S₍₁₎, …, S₍ₙ₎)`). -/
def orderStat (s : Fin n → ℝ) : Fin n → ℝ :=
  s ∘ Tuple.sort s

/-- Section 1.1 and Theorem 2: the joint law of the calibration scores and the test scores. The
`n` calibration scores are i.i.d. with law `μ` (the law of `ŝ(X)` for `X ∼ P_X`), the `m` test
scores are independent of them and of each other, and test point `j` has score law `ν j`
(equal to `μ` for an inlier). -/
def scoreLaw (μ : Measure ℝ) (ν : Fin m → Measure ℝ) :
    Measure ((Fin n → ℝ) × (Fin m → ℝ)) :=
  (Measure.pi fun _ : Fin n => μ).prod (Measure.pi ν)

/-- Section 2.2: the vector `(û^(marg)(X_{2n+1}), …, û^(marg)(X_{2n+m}))` of marginal conformal
p-values of the test points, as a function of (calibration scores, test scores). -/
def margPvals (ω : (Fin n → ℝ) × (Fin m → ℝ)) : Fin m → ℝ :=
  fun j => margPval ω.1 (ω.2 j)

/-- Section 2.2, Definition 1: a random vector `X = (X₁, …, X_m)` is PRDS on `I₀` if for every
`i ∈ I₀` and every (measurable) increasing set `A`, `P[X ∈ A | X_i = x]` is nondecreasing in `x`,
i.e. this conditional probability has a nondecreasing version `f(x)`. -/
def IsPRDS {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → Fin m → ℝ)
    (I₀ : Finset (Fin m)) : Prop :=
  ∀ i ∈ I₀, ∀ A : Set (Fin m → ℝ), IsUpperSet A → MeasurableSet A →
    ∃ f : ℝ → ℝ, Monotone f ∧
      (fun ω => f (X ω i)) =ᵐ[P]
        condExp (MeasurableSpace.comap (fun ω => X ω i) inferInstance) P
          ((X ⁻¹' A).indicator fun _ => (1 : ℝ))

/-- Section 2.2, eq. (7): the false discovery proportion `|R ∩ H₀| / max{1, |R|}` of a rejection
set `R` when the true nulls are `H₀`. -/
def fdp (R H₀ : Finset (Fin m)) : ℝ :=
  ((R ∩ H₀).card : ℝ) / max 1 (R.card : ℝ)

/-- Section 2.2, eq. (7): the false discovery rate `E[|R ∩ H₀| / max{1, |R|}]` of a random
rejection set. -/
def fdr {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (rej : Ω → Finset (Fin m))
    (H₀ : Finset (Fin m)) : ℝ :=
  ∫ ω, fdp (rej ω) H₀ ∂P

/-- Section 2.2 (Corollary 1) and Section 3.6.4: the number of BH rejections at level `α`,
`R(α) = max{r ∈ {0, …, m} : |{i : p_i ≤ rα/m}| ≥ r}`. -/
def bhCount (α : ℝ) (p : Fin m → ℝ) : ℕ :=
  ((Finset.range (m + 1)).filter fun r : ℕ =>
    r ≤ (Finset.univ.filter fun i => p i ≤ ((r : ℕ) : ℝ) * α / m).card).sup id

/-- Section 2.2 (Corollary 1) and Section 3.6.4: the BH procedure at level `α` rejects every
hypothesis with `p_i ≤ α R(α) / m`. -/
def bhRej (α : ℝ) (p : Fin m → ℝ) : Finset (Fin m) :=
  Finset.univ.filter fun i => p i ≤ (bhCount α p : ℝ) * α / m

/-- Appendix A.4: `A = Σᵢ I(p_i ≥ λ)`, the number of p-values at least `λ`. -/
def storeyA (lam : ℝ) (p : Fin m → ℝ) : ℕ :=
  (Finset.univ.filter fun i => lam ≤ p i).card

/-- Appendix A.4: Storey's estimate `π̂₀ = (1 + A) / (m (1 - λ))` of the proportion of nulls. -/
def storeyPi0 (lam : ℝ) (p : Fin m → ℝ) : ℝ :=
  (1 + (storeyA lam p : ℝ)) / (m * (1 - lam))

/-- Appendix A.4: `R = max{r : p₍ᵣ₎ ≤ α r / (m π̂₀), p₍ᵣ₎ < λ}` (and `R = 0` if no `r ∈ {1, …, m}`
qualifies); the index `r : Fin m` stands for `r + 1`. -/
def storeyCount (α lam : ℝ) (p : Fin m → ℝ) : ℕ :=
  (Finset.univ.filter fun r : Fin m =>
    orderStat p r ≤ α * ((r : ℕ) + 1 : ℝ) / (m * storeyPi0 lam p) ∧ orderStat p r < lam).sup
    fun r => (r : ℕ) + 1

/-- Section 2.3 and Appendix A.4: the rejection set of the Storey–BH procedure,
`R = {i : p_i ≤ α R / (m π̂₀), p_i < λ}`. -/
def storeyRej (α lam : ℝ) (p : Fin m → ℝ) : Finset (Fin m) :=
  Finset.univ.filter fun i =>
    p i ≤ α * (storeyCount α lam p : ℝ) / (m * storeyPi0 lam p) ∧ p i < lam

/-- Section 3.2, Theorem 4: the uniform law on `[0, 1]`. -/
def unifLaw : Measure ℝ :=
  (volume : Measure ℝ).restrict (Set.Icc 0 1)

/-- Section 3.2, Theorem 4, eq. (10): `b₀ = 0`, `b_{n+1} = 1`, `0 ≤ b₁ ≤ ⋯ ≤ bₙ ≤ 1`, and for
`U₁, …, Uₙ` i.i.d. uniform on `[0, 1]`, `P[U₍₁₎ ≤ b₁, …, U₍ₙ₎ ≤ bₙ] ≥ 1 - δ`. -/
def IsCCVSequence (n : ℕ) (δ : ℝ) (b : ℕ → ℝ) : Prop :=
  b 0 = 0 ∧ b (n + 1) = 1 ∧ (∀ i, 1 ≤ i → i ≤ n → 0 ≤ b i ∧ b i ≤ 1) ∧
    (∀ i, 1 ≤ i → i < n → b i ≤ b (i + 1)) ∧
    ENNReal.ofReal (1 - δ) ≤
      (Measure.pi fun _ : Fin n => unifLaw) {u | ∀ k : Fin n, orderStat u k ≤ b ((k : ℕ) + 1)}

/-- Section 3.2, Theorem 4, eq. (11): the piecewise-constant adjustment function
`h(t) = b_{⌈(n+1)t⌉}`, `t ∈ [0, 1]`. -/
def adjFun (b : ℕ → ℝ) (n : ℕ) (t : ℝ) : ℝ :=
  b ⌈((n : ℝ) + 1) * t⌉₊

/-- Section 3.1, eq. (9): the conditional false positive rate
`FPR(α; D) = P[û^(marg)(X_{2n+1}) ≤ α | D]` of an inlier test point whose score has law `μ`, as a
function of the calibration scores. -/
def fpr (μ : Measure ℝ) (s : Fin n → ℝ) (α : ℝ) : ℝ :=
  (μ {x | margPval s x ≤ α}).toReal

/-- Section 2.1: the `q`-quantile `inf{x : F_ν(x) ≥ q}` of a law `ν` on `ℝ`. -/
def quantile (ν : Measure ℝ) (q : ℝ) : ℝ :=
  sInf {x | q ≤ cdf ν x}

/-- Section 2.1: the chi-square law with `k` degrees of freedom, the gamma law with shape `k/2`
and rate `1/2`. -/
def chiSqLaw (k : ℕ) : Measure ℝ :=
  gammaMeasure ((k : ℝ) / 2) (1 / 2)

/-- Section 2.1: the standard normal law `N(0, 1)`. -/
def stdNormal : Measure ℝ :=
  gaussianReal 0 1

/-- Section 2.1, Theorem 1: the survival function `Φ̄(x) = 1 - Φ(x)` of `N(0, 1)`. -/
def normSurv (x : ℝ) : ℝ :=
  1 - cdf stdNormal x

/-- Section 2.1: Fisher's combination statistic `-2 Σᵢ log û^(marg)(X_{2n+i})` of the test
scores `t` given calibration scores `s`. -/
def fisherStat (s : Fin n → ℝ) (t : Fin m → ℝ) : ℝ :=
  -2 * ∑ i, Real.log (margPval s (t i))

/-- Section 2.1, Theorem 1, eq. (5): under the global null, the conditional type-I error
`P[-2 Σᵢ log û^(marg)(X_{2n+i}) ≥ χ²(2m; 1-α) | D]` of Fisher's combination test, as a function of
the calibration scores (the `m` test scores are i.i.d. with law `μ`, independent of `D`). -/
def condFisherRejProb (μ : Measure ℝ) (m : ℕ) (α : ℝ) (s : Fin n → ℝ) : ℝ :=
  ((Measure.pi fun _ : Fin m => μ)
    {t | quantile (chiSqLaw (2 * m)) (1 - α) ≤ fisherStat s t}).toReal

/-- Section 2.1, Lemma 1: the correlation `Cor[X, Y] = Cov[X, Y] / √(Var X · Var Y)`. -/
def corr {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X Y : Ω → ℝ) : ℝ :=
  covariance X Y P / Real.sqrt (variance X P * variance Y P)

end ConformalOutlierTesting



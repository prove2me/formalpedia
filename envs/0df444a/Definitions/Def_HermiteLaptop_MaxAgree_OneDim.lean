-- Prove2me | Definitions.Def_HermiteLaptop_MaxAgree_OneDim
-- name    : HermiteLaptop_MaxAgree_OneDim
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T18:17:23.701548+00:00
-- url     : https://prove2.me/theorems/e9ab6426-dad3-4624-a700-ff76e7148789
-- title:
--   One-dimensional Gaussian integrals of the coefficient certificate: J_a, K_a, B_α, B_{a,λ}, N(λ), S_{a,λ}, T^{(R)}, G_j and the certified bounds (§2.5, §3.1–3.3)
-- statement:
--   Let $\varphi(x)=(2\pi)^{-1/2}e^{-x^2/2}$ and $\Phi$ its distribution function. Define
--   $J_a(x)=\int_{-\infty}^x\varphi(y)h_a(y)\,dy$; $K_0=\Phi$ and $K_a(x)=-\varphi(x)H_{a-1}(x)$ for $a\ge1$; for $\alpha\in\mathbb N_0^k$,
--   $$B_\alpha=\int_{-\infty}^{\infty}\varphi(x)H_{\alpha_1}(x)\prod_{q=2}^k K_{\alpha_q}(x)\,dx.$$
--   For a multiset $\lambda$ of $k-1$ nonnegative integers with multiplicities $n_b(\lambda)$: $N(\lambda)=(k-1)!/\prod_b n_b(\lambda)!$,
--   $$B_{a,\lambda}=\int_{-\infty}^{\infty}\varphi(x)H_a(x)\prod_{b\in\lambda}K_b(x)\,dx,$$
--   $S_{a,\lambda}=H_a\prod_{b\in\lambda,\,b\ge1}H_{b-1}$, $r(\lambda)=\#\{b\in\lambda:b\ge1\}$, $s(\lambda)=\#\{b\in\lambda:b=0\}$ (products and counts with multiplicity). For $R>0$, $T^{(R)}_{a,\lambda}$ is the integral of the integrand of $B_{a,\lambda}$ over $(-\infty,-R]\cup[R,\infty)$, and $G_j(\mu,R)=\int_R^\infty x^je^{-\mu x^2/2}\,dx$. Given rational intervals $I_{a,\lambda}=[L_{a,\lambda},U_{a,\lambda}]$, put $\underline b_{a,\lambda}=\min_{x\in I_{a,\lambda}}x^2$, $\overline b_{a,\lambda}=\max_{x\in I_{a,\lambda}}x^2$ and
--   $$\underline c_{k,m}=k\sum_{a=0}^m\sum_{\lambda}N(\lambda)\frac{\underline b_{a,\lambda}}{a!\prod_{b\in\lambda}b!},\qquad \overline c_{k,m}=k\sum_{a=0}^m\sum_{\lambda}N(\lambda)\frac{\overline b_{a,\lambda}}{a!\prod_{b\in\lambda}b!},$$
--   the inner sums over multisets $\lambda$ of size $k-1$ with $|\lambda|=m-a$.
--
--   **Formalization Note.** `phi = gaussianPDFReal 0 1`, `Phi = cdf (gaussianReal 0 1)`, `Jint a x` integrates over `Set.Iic x`. `Balpha α` puts `H` on coordinate `0` and `Kfun` on the others. Multisets are `Multiset ℕ`; `multisetsOf j s` is the finite set of multisets of size `j` and sum `s`; `Nmult λ` uses `card λ` for `k − 1`. `sqMin L U`, `sqMax L U` are `sInf`/`sSup` of `{x² : x ∈ [L,U]}`; `cLowerCert k m Iv`, `cUpperCert k m Iv` use `I_{a,λ} = [(Iv a λ).1, (Iv a λ).2]`. `tailT R a λ` integrates over `Set.Iic (−R) ∪ Set.Ici R`; `Gmom j μ R` over `Set.Ioi R`.
-- source:
--   García-Soriano, Miyauchi, Hermite Brings a Laptop, arXiv:2609.35453 (held version, sha256 97504f90…), pp. 15–16 (PDF 18–19), §2.5, Eq. (12), Proposition 2.3; pp. 18–21 (PDF 21–24), Lemma 3.1, §3.2, Eqs. (17)–(18), §3.3

import Mathlib
import Definitions.Def_HermiteLaptop_MaxAgree_Hermite

open MeasureTheory ProbabilityTheory

/-!
# One-dimensional Gaussian integrals behind the coefficient certificate

García-Soriano, Miyauchi, *Hermite Brings a Laptop*, arXiv:2609.35453 (held version, sha256
97504f90…), §2.5 pp. 15–16 (PDF 18–19), Eq. (12), Proposition 2.3; §3.1–3.3 pp. 18–21
(PDF 21–24), Lemma 3.1, §3.2 (`K_a`, `B_α`), Eq. (17), Eq. (18), Lemma 3.4.

Objects:
* `φ(x) = (2π)^{−1/2} e^{−x²/2}` (`gaussianPDFReal 0 1`) and its CDF `Φ` (`cdf (gaussianReal 0 1)`).
* `J_a(x) = ∫_{−∞}^{x} φ(y) h_a(y) dy` (Lemma 3.1).
* `K_0 = Φ`, `K_a(x) = −φ(x) H_{a−1}(x)` for `a ≥ 1` (§3.2).
* `B_α = ∫ φ(x) H_{α_1}(x) Π_{q≥2} K_{α_q}(x) dx` for `α ∈ ℕᵏ` (§3.2).
* For a multiset `λ` of naturals: `N(λ) = (k−1)!/Π_b n_b(λ)!` with `k − 1 = |λ|` its size,
  `B_{a,λ} = ∫ φ H_a Π_{b∈λ} K_b` (Eq. (12)), `S_{a,λ} = H_a Π_{b∈λ, b≥1} H_{b−1}` (Eq. (17)),
  `r(λ) = #{b ∈ λ : b ≥ 1}`, `s(λ) = #{b ∈ λ : b = 0}`; products over `λ` count multiplicity.
* `T^{(R)}_{a,λ}`: the integral of the integrand of (12) over `(−∞, −R] ∪ [R, ∞)` (Eq. (18)).
* `G_j(μ, R) = ∫_R^∞ xʲ e^{−μx²/2} dx` (§3.3).
* `multisetsOf j s`: the multisets of `j` naturals with sum `s`, as a `Finset (Multiset ℕ)` (the
  images of the tuples `Fin j → ℕ` with sum `s`).
* `sqMin L U = min_{x∈[L,U]} x²` and `sqMax L U = max_{x∈[L,U]} x²` (Proposition 2.3), taken as
  `sInf`/`sSup` of the image of the compact interval `[L, U]` (`L ≤ U` wherever they are used).
* `cLowerCert k m Iv`, `cUpperCert k m Iv`: the bounds `c̲_{k,m}`, `c̄_{k,m}` of Proposition 2.3
  built from rational intervals `I_{a,λ} = [(Iv a λ).1, (Iv a λ).2]`.

Conventions. Integrals over `ℝ` are Bochner integrals for Lebesgue measure; every integrand here
is a polynomial times powers of `φ` and of `Φ ∈ [0, 1]`, hence integrable. The paper's first
coordinate (`α_1`, `f_1`) is the coordinate `0`.
-/

namespace HermiteLaptop.MaxAgree

/-- The standard Gaussian density `φ(x) = (2π)^{−1/2} e^{−x²/2}`. -/
noncomputable def phi (x : ℝ) : ℝ := gaussianPDFReal 0 1 x

/-- The standard Gaussian CDF `Φ`. -/
noncomputable def Phi (x : ℝ) : ℝ := cdf (gaussianReal 0 1) x

/-- `J_a(x) = ∫_{−∞}^{x} φ(y) h_a(y) dy` (Lemma 3.1). -/
noncomputable def Jint (a : ℕ) (x : ℝ) : ℝ := ∫ y in Set.Iic x, phi y * hNorm a y

/-- `K_0 = Φ`, `K_a(x) = −φ(x) H_{a−1}(x)` for `a ≥ 1` (§3.2). -/
noncomputable def Kfun (a : ℕ) (x : ℝ) : ℝ :=
  if a = 0 then Phi x else -(phi x * H (a - 1) x)

/-- `B_α = ∫ φ(x) H_{α_1}(x) Π_{q=2}^{k} K_{α_q}(x) dx` (§3.2); the first coordinate is `0`. -/
noncomputable def Balpha {k : ℕ} (α : Fin k → ℕ) : ℝ :=
  ∫ x, phi x * ∏ q : Fin k, (if q.val = 0 then H (α q) x else Kfun (α q) x)

/-- The multisets of `j` naturals with sum `s` (`λ` of size `j`, `|λ| = s`). -/
def multisetsOf (j s : ℕ) : Finset (Multiset ℕ) :=
  (Finset.Nat.antidiagonalTuple j s).image (fun t => Finset.univ.val.map t)

/-- `N(λ) = (k−1)!/Π_{b≥0} n_b(λ)!`, `k − 1` the size of `λ`: the number of orderings of `λ`. -/
noncomputable def Nmult (lam : Multiset ℕ) : ℝ :=
  (Nat.factorial (Multiset.card lam) : ℝ) /
    ∏ b ∈ lam.toFinset, (Nat.factorial (lam.count b) : ℝ)

/-- The integrand `φ(x) H_a(x) Π_{b∈λ} K_b(x)` of Eq. (12). -/
noncomputable def integrandB (a : ℕ) (lam : Multiset ℕ) (x : ℝ) : ℝ :=
  phi x * H a x * (lam.map (fun b => Kfun b x)).prod

/-- `B_{a,λ} = ∫_{−∞}^{∞} φ(x) H_a(x) Π_{b∈λ} K_b(x) dx` (Eq. (12)). -/
noncomputable def Bal (a : ℕ) (lam : Multiset ℕ) : ℝ := ∫ x, integrandB a lam x

/-- The denominator `a! Π_{b∈λ} b!`. -/
noncomputable def factDen (a : ℕ) (lam : Multiset ℕ) : ℝ :=
  (Nat.factorial a : ℝ) * ((lam.map (fun b => (Nat.factorial b : ℝ))).prod)

/-- `min_{x∈[L,U]} x²`. -/
noncomputable def sqMin (L U : ℝ) : ℝ := sInf ((fun x : ℝ => x ^ 2) '' Set.Icc L U)

/-- `max_{x∈[L,U]} x²`. -/
noncomputable def sqMax (L U : ℝ) : ℝ := sSup ((fun x : ℝ => x ^ 2) '' Set.Icc L U)

/-- `r(λ) = |{b ∈ λ : b ≥ 1}|` (Eq. (17)). -/
def rCount (lam : Multiset ℕ) : ℕ := Multiset.card (lam.filter (fun b => 1 ≤ b))

/-- `s(λ) = |{b ∈ λ : b = 0}|` (Eq. (17)). -/
def sCount (lam : Multiset ℕ) : ℕ := Multiset.card (lam.filter (fun b => b = 0))

/-- `S_{a,λ} = H_a Π_{b∈λ, b≥1} H_{b−1}` (Eq. (17)), a polynomial. -/
noncomputable def Spoly (a : ℕ) (lam : Multiset ℕ) : Polynomial ℝ :=
  Hpoly a * ((lam.filter (fun b => 1 ≤ b)).map (fun b => Hpoly (b - 1))).prod

/-- `T^{(R)}_{a,λ}`: the contribution of `(−∞, −R] ∪ [R, ∞)` to `B_{a,λ}` (Eq. (18)). -/
noncomputable def tailT (R : ℝ) (a : ℕ) (lam : Multiset ℕ) : ℝ :=
  ∫ x in Set.Iic (-R) ∪ Set.Ici R, integrandB a lam x

/-- `G_j(μ, R) = ∫_R^∞ xʲ exp(−μx²/2) dx` (§3.3). -/
noncomputable def Gmom (j : ℕ) (μ R : ℝ) : ℝ :=
  ∫ x in Set.Ioi R, x ^ j * Real.exp (-(μ * x ^ 2) / 2)

/-- The certified lower bound of Proposition 2.3:
`c̲_{k,m} = k Σ_{a=0}^{m} Σ_{λ: |λ|=m−a, size k−1} N(λ) b̲_{a,λ}/(a! Π_{b∈λ} b!)`, with
`b̲_{a,λ} = min_{x∈I_{a,λ}} x²` and `I_{a,λ} = [(Iv a λ).1, (Iv a λ).2]`. -/
noncomputable def cLowerCert (k m : ℕ) (Iv : ℕ → Multiset ℕ → ℚ × ℚ) : ℝ :=
  (k : ℝ) * ∑ a ∈ Finset.range (m + 1), ∑ lam ∈ multisetsOf (k - 1) (m - a),
    Nmult lam * sqMin ((Iv a lam).1 : ℝ) ((Iv a lam).2 : ℝ) / factDen a lam

/-- The certified upper bound of Proposition 2.3:
`c̄_{k,m} = k Σ_{a=0}^{m} Σ_{λ: |λ|=m−a, size k−1} N(λ) b̄_{a,λ}/(a! Π_{b∈λ} b!)`, with
`b̄_{a,λ} = max_{x∈I_{a,λ}} x²`. -/
noncomputable def cUpperCert (k m : ℕ) (Iv : ℕ → Multiset ℕ → ℚ × ℚ) : ℝ :=
  (k : ℝ) * ∑ a ∈ Finset.range (m + 1), ∑ lam ∈ multisetsOf (k - 1) (m - a),
    Nmult lam * sqMax ((Iv a lam).1 : ℝ) ((Iv a lam).2 : ℝ) / factDen a lam

end HermiteLaptop.MaxAgree



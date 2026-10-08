-- Prove2me | Definitions.Def_AssortSearch_Cannibal_Model
-- name    : AssortSearch_Cannibal_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T06:30:50.970053+00:00
-- url     : https://prove2.me/theorems/cf15c0d2-19d9-4b3d-8a8c-372fb4e1b5af
-- title:
--   The random-utility model with zero-mean Gumbel shocks and the independent assortment search model (§3, §3.1)
-- statement:
--   A retailer may carry variants $N=\{1,\dots,n\}$ of a product; $S\subseteq N$ is its assortment. A faux variant $0$ stands for not purchasing.
--
--   1. **Zero-mean Gumbel law.** For a scale $\mu>0$ and Euler's constant $\gamma$, the law with distribution function and density
--   $$
--   F(x)=\exp\Big[-\exp\Big(-\Big(\frac{x}{\mu}+\gamma\Big)\Big)\Big],\qquad f(x)=\frac1\mu\,e^{-(x/\mu+\gamma)}F(x).
--   $$
--   A probability measure $G$ on $\mathbb R$ is a *zero-mean Gumbel law with scale $\mu$* when its distribution function is $F$.
--   2. **Utilities.** Variant $j$ has expected net utility $u_j-p_j$ and the no-purchase option has $u_0$ (with $p_0=0$). Given i.i.d. shocks $\zeta_0,\zeta_1,\dots,\zeta_n$ with law $G$, the realised utilities are $U_j=(u_j-p_j)+\zeta_j$ and $U_0=u_0+\zeta_0$. The **preferences** are $v_j=\exp((u_j-p_j)/\mu)$ and $v_0=\exp(u_0/\mu)$.
--   3. **No-search demand.** $q_i^m(S)$, for $i\in S$, is the probability that $U_i>U_j$ for every $j\in S\setminus\{i\}$ and $U_i>U_0$. The no-purchase probability $q_0^m(S)$ is the probability that $U_0>U_j$ for every $j\in S$.
--   4. **Search decision.** A consumer who can search expects utility $U_r=u_r+\zeta_r$, where the search shock $\zeta_r$ also has law $G$, and pays a search cost $b$. At a realised maximum utility $y=U_{\max}$, *search is worthwhile* when
--   $$
--   \int_{y-u_r}^{\infty}(u_r+x-y)f(x)\,dx-\int_{-\infty}^{y-u_r}(y-u_r-x)f(x)\,dx\ \ge\ b .
--   $$
--   5. **Independent assortment demand.** $q_i^{si}(S)$, for $i\in S$, is the probability that $U_i>U_j$ for every $j\in S\setminus\{i\}$, $U_i>U_0$, and search is **not** worthwhile at $y=U_i$.
--   6. **Constants.** The search threshold is $\bar U=u_r-b$, $\lambda=\exp[-(\bar U/\mu+\gamma)]$, $H(\bar U,S)=\exp\big(-\lambda(v_0+\sum_{j\in S}v_j)\big)$, and $T(\omega)=\omega\big(1-\exp(-\lambda/\omega)\big)$.
--
--   These are the objects of §3 and §3.1 of the paper. Demand under search is defined here as a probability of the consumer's choice event, not by the closed form of Theorem 1, so that Theorem 1 and Theorem 2 are statements about the random-utility model.
--
--   **Formalization Note** Variants are `Fin n` (the paper's variant $i$ is index $i-1$); the no-purchase option is the extra index `none` of `Option (Fin n)`, and the shock vector is a point of `Option (Fin n) → ℝ` under the product measure `Measure.pi (fun _ => G)`. The search shock does not appear in the sample space: the search decision depends only on its law, and "$f(x)\,dx$" is written as integration against $G$. The law $G$ is a hypothesis `IsZeroMeanGumbel μ G` on a probability measure (such a measure exists for every $\mu>0$). Probabilities are `.toReal` of measures. All comparisons are strict; ties have probability zero. `T` at $\omega=0$ evaluates to $0$ by Lean's convention $\lambda/0=0$, which is its right limit; no statement uses it. The MNL share $v_i/(\sum_{j\in S}v_j+v_0)$ is the published `RetailVariety.Structure.share`.
-- source:
--   Cachon, Terwiesch & Xu, Retail Assortment Planning in the Presence of Consumer Search, working paper (Dec. 20, 2002), §3 p. 5 (PDF 7), §3.1 pp. 7–10 (PDF 9–12), (2), Theorem 1 and its proof, proof of Theorem 2

import Mathlib
import Definitions.Def_RetailVariety_Structure_Model

open MeasureTheory ProbabilityTheory

namespace AssortSearch.Cannibal

/-! # The random-utility model of §3 and the independent assortment search model of §3.1

Cachon, Terwiesch & Xu, *Retail Assortment Planning in the Presence of Consumer Search*,
working paper (Dec. 20, 2002), §3 (p. 5, PDF 7) and §3.1 (pp. 7–9, PDF 9–11).

Variants are `Fin n` (index `⟨k, _⟩` is the paper's variant `k + 1`). The no-purchase "faux variant" 0
is the extra index `none : Option (Fin n)`; variant `j` is `some j`. -/

/-- The distribution function of the paper's zero-mean Gumbel law with scale `μ` (p. 5):
`F(x) = exp[-exp(-(x/μ + γ))]`, with `γ` Euler's constant. -/
noncomputable def gumbelCdf (μ x : ℝ) : ℝ :=
  Real.exp (-Real.exp (-(x / μ + Real.eulerMascheroniConstant)))

/-- The density `f = F'` of the zero-mean Gumbel law with scale `μ`:
`f(x) = (1/μ) exp(-(x/μ + γ)) F(x)`. -/
noncomputable def gumbelPdf (μ x : ℝ) : ℝ :=
  (1 / μ) * Real.exp (-(x / μ + Real.eulerMascheroniConstant)) * gumbelCdf μ x

/-- `G` is the zero-mean Gumbel law with scale `μ`: its distribution function is `gumbelCdf μ`. -/
def IsZeroMeanGumbel (μ : ℝ) (G : Measure ℝ) [IsProbabilityMeasure G] : Prop :=
  ∀ x : ℝ, cdf G x = gumbelCdf μ x

/-- Expected net utilities `u_j - p_j` on the variants and the no-purchase option: `none ↦ u_0`
(with `p_0 = 0`), `some j ↦ w j`. -/
def netUtility {n : ℕ} (w : Fin n → ℝ) (u0 : ℝ) : Option (Fin n) → ℝ
  | none => u0
  | some j => w j

/-- Realised utilities `U_j = (u_j - p_j) + ζ_j` for a realisation `ζ` of the shocks. -/
def utility {n : ℕ} (w : Fin n → ℝ) (u0 : ℝ) (ζ : Option (Fin n) → ℝ) (j : Option (Fin n)) : ℝ :=
  netUtility w u0 j + ζ j

/-- Preference `v_j = exp((u_j - p_j)/μ)` of variant `j` (p. 7). -/
noncomputable def pref {n : ℕ} (μ : ℝ) (w : Fin n → ℝ) (j : Fin n) : ℝ :=
  Real.exp (w j / μ)

/-- Preference `v_0 = exp(u_0/μ)` of the no-purchase option (`p_0 = 0`). -/
noncomputable def pref0 (μ u0 : ℝ) : ℝ :=
  Real.exp (u0 / μ)

/-- No-search (traditional MNL) choice probability `q_o^m(S)` (p. 7): the probability, under
i.i.d. shocks `ζ_0, ζ_1, …, ζ_n` with law `G`, that option `o` has strictly the highest utility
among the no-purchase option and the variants of `S`. For `o = none` this is the no-purchase
probability `q_0^m(S)`; for `o = some i` with `i ∈ S` it is `q_i^m(S)`. -/
noncomputable def noSearchProb {n : ℕ} (G : Measure ℝ) [IsProbabilityMeasure G] (w : Fin n → ℝ)
    (u0 : ℝ) (S : Finset (Fin n)) (o : Option (Fin n)) : ℝ :=
  (Measure.pi (fun _ : Option (Fin n) => G)
    {ζ | ∀ j ∈ Finset.insertNone S, j ≠ o → utility w u0 ζ j < utility w u0 ζ o}).toReal

/-- The search threshold `Ū = u_r - b` (Theorem 1, p. 8). -/
def searchThreshold (ur b : ℝ) : ℝ :=
  ur - b

/-- "Search is worthwhile" at the realised maximum utility `y = U_max` (proof of Theorem 1, p. 8):
`∫_{y-u_r}^∞ (u_r + x - y) f(x) dx - ∫_{-∞}^{y-u_r} (y - u_r - x) f(x) dx ≥ b`, where the search
shock `ζ_r` has law `G` with density `f`, so `f(x) dx` is integration against `G`. -/
def SearchWorthwhile (G : Measure ℝ) (ur b y : ℝ) : Prop :=
  (∫ x in Set.Ioi (y - ur), (ur + x - y) ∂G) - (∫ x in Set.Iic (y - ur), (y - ur - x) ∂G) ≥ b

/-- Independent assortment search model: the demand `q_i^si(S)` of variant `i` (pp. 8–9), the
probability that `U_i > U_j` for every `j ∈ S \ {i}`, `U_i > U_0`, and the consumer, observing
`U_max = U_i`, does not find search worthwhile. -/
noncomputable def searchProb {n : ℕ} (G : Measure ℝ) [IsProbabilityMeasure G] (ur b : ℝ)
    (w : Fin n → ℝ) (u0 : ℝ) (S : Finset (Fin n)) (i : Fin n) : ℝ :=
  (Measure.pi (fun _ : Option (Fin n) => G)
    {ζ | (∀ j ∈ S, j ≠ i → utility w u0 ζ (some j) < utility w u0 ζ (some i)) ∧
      utility w u0 ζ none < utility w u0 ζ (some i) ∧
      ¬ SearchWorthwhile G ur b (utility w u0 ζ (some i))}).toReal

/-- `λ = exp[-(Ū/μ + γ)]` (Theorem 1, p. 8). -/
noncomputable def lam (μ Ubar : ℝ) : ℝ :=
  Real.exp (-(Ubar / μ + Real.eulerMascheroniConstant))

/-- `H(Ū, S) = exp(-λ (v_0 + ∑_{j∈S} v_j))` (Theorem 1, p. 8). -/
noncomputable def H {n : ℕ} (μ Ubar : ℝ) (v : Fin n → ℝ) (v0 : ℝ) (S : Finset (Fin n)) : ℝ :=
  Real.exp (-(lam μ Ubar * (v0 + ∑ j ∈ S, v j)))

/-- `T(ω) = ω (1 - exp(-λ/ω))` (proof of Theorem 2, p. 10). At `ω = 0` Lean's `λ/0 = 0` gives
`T(0) = 0`, which is the limit from the right. -/
noncomputable def T (lam ω : ℝ) : ℝ :=
  ω * (1 - Real.exp (-lam / ω))

end AssortSearch.Cannibal



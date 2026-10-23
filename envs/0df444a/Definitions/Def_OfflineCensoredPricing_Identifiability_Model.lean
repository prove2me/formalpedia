-- Prove2me | Definitions.Def_OfflineCensoredPricing_Identifiability_Model
-- name    : OfflineCensoredPricing_Identifiability_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-22T12:31:56.129987+00:00
-- url     : https://prove2.me/theorems/9274db56-90c1-4046-8731-7fb9845ab8b2
-- title:
--   §2–§3, pp. 8–16 — censored linear-demand pricing, Assumption 1, ambiguity set, optimistic/pessimistic revenues and prices, worst-case loss, identifiability (Definition 1)
-- statement:
--   The model of Bu, Simchi-Levi and Wang for offline pricing with censored demand.
--
--   **Market.** A retailer sells a single product with $y \ge 0$ units of inventory at a price $p$ from a feasible interval $[\underline p, \bar p] \subset (0,\infty)$. Demand at price $p$ is linear, $D(p) = \xi - bp$, where $\xi$ is the random base demand with c.d.f. $F_\xi$ and $b \in [\underline b, \bar b] \subset (0,\infty)$ is the price sensitivity. Sales are $\min\{D(p), y\}$, and the expected revenue under a c.d.f. $F$ of $\xi$ is
--   $$R_F(p) = p\,\mathbb E_F\big[\min\{\xi - bp,\ y\}\big].$$
--
--   **Offline data.** The retailer has tried $K \ge 2$ different historical prices $p_i \in [\underline p, \bar p]$ with inventory levels $y_i \ge 0$; at each pair $(p_i, y_i)$ it holds $N_i$ independent censored sales $S^j_i = \min\{\xi^j_i - bp_i,\ y_i\}$, where the $\xi^j_i$ are independent copies of $\xi$. The data size is $N = \min_i N_i$.
--
--   **Data metrics.** The observable boundary is $\lambda = \max_i \{y_i + bp_i\}$; $\gamma_i = \mathbb P[\xi < y_i + bp_i]$ and $\gamma = \mathbb P[\xi < \lambda] = \max_i \gamma_i$; $\tilde p = (\lambda - y)/b$. For Lemma 2 and Theorem 2: $\bar\lambda = \max_i\{y_i + \bar b p_i\}$, $C_1 = 5\bar p^2 + (2y + 3\bar b\bar p + 2\bar\lambda)^2/\underline b^2$, $C_2 = \bar p(y + \bar\lambda + \bar p\bar b)$, and
--   $$C = \max\Big\{576(y+\bar b\bar p)^2\bar p^2,\ \frac{576\,C_1^2}{\frac1K\sum_{i}(p_i - \frac1K\sum_j p_j)^2\,\underline g^2},\ 288\,C_2^2,\ 288\,\bar p^2\bar\lambda^2\Big\}.$$
--
--   **Standing assumptions.** $\xi$ has a probability law; $y \ge 0$; $0 < \underline p < \bar p$; $0 < \underline b \le b \le \bar b$; the $K \ge 2$ prices are pairwise different; $y_i \ge 0$; demand is nonnegative almost surely at every feasible price, i.e. $\mathbb P[\xi < b\bar p] = 0$; $\gamma_i > 0$ for every $i$; and **Assumption 1**: there is $\underline g > 0$ such that, on the left of $\lambda$, either
--   1. $\xi$ is discrete with finite support $\beta_1 < \dots < \beta_M < \lambda$ ($M \ge 1$, all the mass of $(-\infty,\lambda)$ on these atoms) and $\frac{F_\xi(\beta_{k+1}) - F_\xi(\beta_k)}{\beta_{k+1} - \beta_k} \ge \underline g$ for $k \in [M-1]$; or
--   2. $\xi$ has a density $f_\xi$ on $(-\infty,\lambda)$ with $f_\xi(x) \ge \underline g$ for all $x \in [\ell, \lambda)$, where $\ell$ is a lower bound of the support of $\xi$ ($F_\xi(x) = 0$ for $x < \ell$).
--
--   **Ambiguity set and robust revenues.** The ambiguity set is $\mathcal F = \{F \text{ c.d.f.} : F(x) = F_\xi(x)\ \forall x < \lambda\}$. The optimistic and pessimistic revenues are $R_{\max}(p) = \max_{F\in\mathcal F} R_F(p)$ and $R_{\min}(p) = \min_{F\in\mathcal F} R_F(p)$, with the auxiliary quadratics $R_1(p) = p(-\gamma bp + \mathbb E_{F_\xi}[\min\{\xi,\lambda\}] + (1-\gamma)(y-\lambda))$ and $R_2(p) = p(-bp + \mathbb E_{F_\xi}[\min\{\xi,\lambda\}])$. Prices: $p^*_F = \max\{\arg\max_{p\in[\underline p,\bar p]} R_F(p)\}$, $p^\dagger_F = \max\{\arg\max_{p\in\mathbb R} R_F(p)\}$, $p^*_{\max} = \max\{\arg\max_{[\underline p,\bar p]} R_{\max}\}$, $p^*_{\min} = \max\{\arg\max_{[\underline p,\bar p]} R_{\min}\}$.
--
--   **Losses.** The worst-case revenue loss of a price $p$ is $\max_{F\in\mathcal F}\{R_F(p^*_F) - R_F(p)\}$, and the minimax revenue loss is $\Delta = \min_{p\in[\underline p,\bar p]} \max_{F\in\mathcal F}\{R_F(p^*_F) - R_F(p)\}$.
--
--   **Algorithms and identifiability.** A data-driven algorithm maps the censored data (of any sample sizes), for the fixed public inputs $y$, $[\underline p,\bar p]$, $[\underline b,\bar b]$, $(p_i, y_i)$, to a price; it is valid if its prices lie in $[\underline p,\bar p]$. It is near-optimal if for every $\varepsilon > 0$
--   $$\lim_{N\to\infty} \mathbb P\Big[\max_{F\in\mathcal F}\{R_F(p^*_F) - R_F(p^{\mathcal A})\} < \varepsilon\Big] = 1, \qquad (2)$$
--   and the problem is identifiable (Definition 1) if a valid near-optimal algorithm exists.
--
--   These objects are shared by every statement of the mission: Propositions 1–3, 6 and 7, Lemmas 1, 2, D.1, D.2, Theorems 1 and 2.
--
--   **Formalization Note** c.d.f.s are probability measures on $\mathbb R$; $F(x) = F_\xi(x)$ for $x < \lambda$ is agreement on all half-lines $(-\infty, x]$, $x < \lambda$ (an atom at $\lambda$ is allowed). $R_{\max}$, $R_{\min}$, the worst-case loss and $\Delta$ are defined as suprema/infima; that they are attained is part of Propositions 2, 3, 6 and 7. "$\max\{\arg\max\}$" is the supremum of the set of maximizers; $R_F(p^*_F)$ in the worst-case loss is written $\sup_{q\in[\underline p,\bar p]} R_F(q)$. Probabilities of failure events are outer measures under the product law of the $\xi^j_i$, and (2) is stated as: for all $\varepsilon, \eta > 0$ there is $N_0$ with outer probability of $\{\text{loss} \ge \varepsilon\}$ at most $\eta$ whenever $\min_i N_i \ge N_0$. Departures from the printed text, each necessary: (i) the data equation is $S^j_i = \min\{\xi^j_i - bp_i, y_i\}$ (p. 9 prints $\xi^j_i - p_i$, dropping $b$; p. 10 and Appendix D use $b$); (ii) the continuous branch of Assumption 1 bounds the density on $[\ell,\lambda)$ instead of the printed $[0,\lambda)$, because the printed version together with $D(p) \ge 0$ a.s. and $\gamma > 0$ admits no instance; (iii) "$K$ different historical prices" is encoded as an injective price vector, which also makes the price variance in $C$ positive (in Lean $x/0 = 0$); (iv) $\gamma_i > 0$ is the paper's "implicitly assumes" (p. 10); (v) indices are $0$-based.
-- source:
--   Bu, Simchi-Levi & Wang, SSRN 3619625 (PDF of 2021-08-23), pp. 8–16: §2 (model, (1), p. 8; offline data p. 9; algorithms, data metrics, Assumption 1, p. 10), §3.1 (ambiguity set p. 11; Definition 1, (2), Rmax/Rmin p. 12; p*max/p*min, p̃ p. 13; Δ p. 16); λ̄, C1, C2 p. 20; constant C of Theorem 2 p. 32

import Mathlib

namespace OfflineCensoredPricing.Identifiability

open MeasureTheory ProbabilityTheory Set

/-!
# Bu, Simchi-Levi & Wang, *Offline Pricing and Demand Learning with Censored Data*

SSRN 3619625 (PDF of 2021-08-23), §2 (pp. 8–11) and §3 (pp. 11–16).

A retailer sells up to `y` units of one product at a price `p ∈ [p̲, p̄] ⊂ (0, ∞)`. Demand is
`D(p) = ξ − b p` with base demand `ξ ∼ F_ξ` and sensitivity `b ∈ [b̲, b̄] ⊂ (0, ∞)`. Sales are
`min{D(p), y}`. Offline data: for `K ≥ 2` different historical prices `pᵢ` with inventories `yᵢ`,
`Nᵢ` independent censored sales `S^j_i = min{ξ^j_i − b pᵢ, yᵢ}`.

Conventions: c.d.f.s are probability measures on `ℝ` (`F(x) = μ (−∞, x]`); "with probability at
least `1 − δ`" is an upper bound on the outer measure of the failure set; `max {arg max …}` is the
supremum of the set of maximizers.
-/

/-- The **public inputs** of the data-driven problem (§2, pp. 8–10): the inventory level `y`, the
price range `[plo, phi] = [p̲, p̄]`, the sensitivity range `[blo, bhi] = [b̲, b̄]`, and the historical
prices `p i = pᵢ` and inventory levels `yh i = yᵢ`, `i ∈ Fin K`. A data-driven algorithm sees only
these and the censored sales. -/
structure Public (K : ℕ) where
  /-- inventory level `y` -/
  y : ℝ
  /-- lower end `p̲` of the price range -/
  plo : ℝ
  /-- upper end `p̄` of the price range -/
  phi : ℝ
  /-- lower end `b̲` of the sensitivity range -/
  blo : ℝ
  /-- upper end `b̄` of the sensitivity range -/
  bhi : ℝ
  /-- historical prices `pᵢ` -/
  p : Fin K → ℝ
  /-- historical inventory levels `yᵢ` -/
  yh : Fin K → ℝ

/-- An **instance** of the problem: the public inputs together with the quantities unknown to the
retailer, namely the true price sensitivity `b`, the law `μξ` of the base demand `ξ`, and the
constant `g = g̲` of Assumption 1. -/
structure Instance (K : ℕ) extends Public K where
  /-- true price sensitivity `b` -/
  b : ℝ
  /-- law of the base demand `ξ` (its c.d.f. is `F_ξ`) -/
  μξ : Measure ℝ
  /-- the constant `g̲` of Assumption 1 -/
  g : ℝ

variable {K : ℕ}

/-! ### Data metrics (p. 10) and the constants of Lemma 2 and Theorem 2 (pp. 20, 32) -/

/-- The observable boundary `λ = max_{i ∈ [K]} {yᵢ + b pᵢ}` (p. 10). -/
noncomputable def lam (I : Instance K) : ℝ := ⨆ i, I.yh i + I.b * I.p i

/-- `γᵢ = P[ξ < yᵢ + b pᵢ]` (p. 10). -/
noncomputable def gammaI (I : Instance K) (i : Fin K) : ℝ :=
  I.μξ.real (Iio (I.yh i + I.b * I.p i))

/-- `γ = P[ξ < λ]` (`= max_i γᵢ`, p. 10). -/
noncomputable def gam (I : Instance K) : ℝ := I.μξ.real (Iio (lam I))

/-- `p̃ = (λ − y)/b` (p. 13). -/
noncomputable def pTilde (I : Instance K) : ℝ := (lam I - I.y) / I.b

/-- `λ̄ = max_{i ∈ [K]} {yᵢ + b̄ pᵢ}` (p. 20). -/
noncomputable def lamBar (I : Instance K) : ℝ := ⨆ i, I.yh i + I.bhi * I.p i

/-- The empirical price variance `(1/K) ∑ᵢ (pᵢ − (1/K) ∑ⱼ pⱼ)²` (pp. 18, 20). -/
noncomputable def priceVar (P : Public K) : ℝ :=
  (1 / (K : ℝ)) * ∑ i, (P.p i - (1 / (K : ℝ)) * ∑ j, P.p j) ^ 2

/-- `C₁ = 5 p̄² + (2y + 3 b̄ p̄ + 2 λ̄)² / b̲²` (p. 20). -/
noncomputable def C1 (I : Instance K) : ℝ :=
  5 * I.phi ^ 2 + (2 * I.y + 3 * I.bhi * I.phi + 2 * lamBar I) ^ 2 / I.blo ^ 2

/-- `C₂ = p̄ (y + λ̄ + p̄ b̄)` (p. 20). -/
noncomputable def C2 (I : Instance K) : ℝ := I.phi * (I.y + lamBar I + I.phi * I.bhi)

/-- The constant of Theorem 2 (p. 32):
`C = max {576 (y + b̄p̄)² p̄², 576 C₁² / ((1/K) ∑ᵢ (pᵢ − (1/K)∑ⱼ pⱼ)² g̲²), 288 C₂², 288 p̄² λ̄²}`. -/
noncomputable def Cthm2 (I : Instance K) : ℝ :=
  max (max (576 * (I.y + I.bhi * I.phi) ^ 2 * I.phi ^ 2)
      (576 * C1 I ^ 2 / (priceVar I.toPublic * I.g ^ 2)))
    (max (288 * C2 I ^ 2) (288 * I.phi ^ 2 * lamBar I ^ 2))

/-! ### Standing assumptions (§2, pp. 8–10) -/

/-- **Assumption 1** (p. 10), with the continuous branch repaired. `g̲ > 0`, and on the left of `λ`
the base demand is either
* **discrete** with finite support `β₁ < ⋯ < β_M < λ` (`M ≥ 1`, each `βₖ` an atom, and all the mass of
  `(−∞, λ)` on these atoms), with `(F_ξ(β_{k+1}) − F_ξ(β_k))/(β_{k+1} − β_k) ≥ g̲` for `k ∈ [M − 1]`;
* or **continuous** with a density `f_ξ` on `(−∞, λ)`, and `f_ξ(x) ≥ g̲` for `x ∈ [ℓ, λ)`, where `ℓ` is a
  lower bound of the support of `ξ` (`F_ξ(x) = 0` for `x < ℓ`). The printed text has `[0, λ)`, which
  together with `D(p) ≥ 0` a.s. and `γ > 0` admits no instance.
Indices are `0`-based: `β ⟨k, _⟩` is the paper's `β_{k+1}`. -/
def Assumption1 (I : Instance K) : Prop :=
  0 < I.g ∧
  ((∃ (M : ℕ) (β : Fin M → ℝ), 0 < M ∧ StrictMono β ∧ (∀ k, β k < lam I) ∧
      (∀ k, 0 < I.μξ {β k}) ∧ I.μξ (Iio (lam I)) = ∑ k, I.μξ {β k} ∧
      ∀ (k : ℕ) (hk : k + 1 < M),
        I.g ≤ (cdf I.μξ (β ⟨k + 1, hk⟩) - cdf I.μξ (β ⟨k, by omega⟩)) /
          (β ⟨k + 1, hk⟩ - β ⟨k, by omega⟩)) ∨
    (∃ f : ℝ → ℝ, Measurable f ∧ (∀ x, 0 ≤ f x) ∧
      I.μξ.restrict (Iio (lam I)) =
        (volume.restrict (Iio (lam I))).withDensity (fun x => ENNReal.ofReal (f x)) ∧
      ∃ ℓ : ℝ, I.μξ (Iio ℓ) = 0 ∧ ∀ x ∈ Ico ℓ (lam I), I.g ≤ f x))

/-- The **standing assumptions** of §2 (pp. 8–10):
* `ξ` has a probability law; `y ≥ 0`; `0 < p̲ < p̄`; `0 < b̲ ≤ b ≤ b̄`;
* `K ≥ 2` different historical prices `pᵢ ∈ [p̲, p̄]` (`p` injective), inventories `yᵢ ≥ 0`;
* demand is nonnegative a.s. at every feasible price: `P[ξ < b p̄] = 0`;
* `γᵢ > 0` for every `i` (p. 10, implied by the data assumption `γ̂ᵢ > 0`);
* Assumption 1. -/
def Instance.Standing (I : Instance K) : Prop :=
  IsProbabilityMeasure I.μξ ∧ 0 ≤ I.y ∧ 0 < I.plo ∧ I.plo < I.phi ∧
  0 < I.blo ∧ I.blo ≤ I.b ∧ I.b ≤ I.bhi ∧
  2 ≤ K ∧ Function.Injective I.p ∧ (∀ i, I.p i ∈ Icc I.plo I.phi) ∧ (∀ i, 0 ≤ I.yh i) ∧
  I.μξ (Iio (I.b * I.phi)) = 0 ∧ (∀ i, 0 < gammaI I i) ∧ Assumption1 I

/-! ### Ambiguity set, revenues, optimistic and pessimistic prices (§3, pp. 11–16) -/

/-- The **ambiguity set** `𝓕(λ, F_ξ) = {F c.d.f. : F(x) = F_ξ(x) ∀ x < λ}` (p. 11), as the set of
probability measures on `ℝ` whose c.d.f. agrees with that of `ξ` on `(−∞, λ)`. -/
def Amb (I : Instance K) : Set (Measure ℝ) :=
  {μ | IsProbabilityMeasure μ ∧ ∀ x < lam I, μ (Iic x) = I.μξ (Iic x)}

/-- The expected revenue `R_F(q) = q · E_F[min{ξ − b q, y}]` under the law `μ` of `ξ` (pp. 8, 12). -/
noncomputable def RF (I : Instance K) (μ : Measure ℝ) (q : ℝ) : ℝ :=
  q * ∫ ξ, min (ξ - I.b * q) I.y ∂μ

/-- The **optimistic revenue** `R_max(q) = max_{F ∈ 𝓕} R_F(q)` (p. 12), as a supremum. -/
noncomputable def Rmax (I : Instance K) (q : ℝ) : ℝ := sSup ((fun μ => RF I μ q) '' Amb I)

/-- The **pessimistic revenue** `R_min(q) = min_{F ∈ 𝓕} R_F(q)` (p. 12), as an infimum. -/
noncomputable def Rmin (I : Instance K) (q : ℝ) : ℝ := sInf ((fun μ => RF I μ q) '' Amb I)

/-- `R₁(q) = q (−γ b q + E_{F_ξ}[min{ξ, λ}] + (1 − γ)(y − λ))` (Proposition 2, p. 13). -/
noncomputable def R1 (I : Instance K) (q : ℝ) : ℝ :=
  q * (-(gam I) * I.b * q + ∫ ξ, min ξ (lam I) ∂I.μξ + (1 - gam I) * (I.y - lam I))

/-- `R₂(q) = q (−b q + E_{F_ξ}[min{ξ, λ}])` (Proposition 2, p. 13). -/
noncomputable def R2 (I : Instance K) (q : ℝ) : ℝ :=
  q * (-(I.b) * q + ∫ ξ, min ξ (lam I) ∂I.μξ)

/-- `max {arg max_{q ∈ [a, b]} f(q)}`: the supremum of the set of maximizers of `f` on `[a, b]`. -/
noncomputable def argmaxIcc (a b : ℝ) (f : ℝ → ℝ) : ℝ :=
  sSup {q ∈ Icc a b | ∀ q' ∈ Icc a b, f q' ≤ f q}

/-- `max {arg min_{q ∈ [a, b]} f(q)}`: the supremum of the set of minimizers of `f` on `[a, b]`. -/
noncomputable def argminIcc (a b : ℝ) (f : ℝ → ℝ) : ℝ :=
  sSup {q ∈ Icc a b | ∀ q' ∈ Icc a b, f q ≤ f q'}

/-- `p*_F = max {arg max_{q ∈ [p̲, p̄]} R_F(q)}` (pp. 8, 12). -/
noncomputable def pStar (I : Instance K) (μ : Measure ℝ) : ℝ := argmaxIcc I.plo I.phi (RF I μ)

/-- `p†_F = max {arg max_{q ∈ ℝ} R_F(q)}` (pp. 8, 12). -/
noncomputable def pDagger (I : Instance K) (μ : Measure ℝ) : ℝ :=
  sSup {q | ∀ q', RF I μ q' ≤ RF I μ q}

/-- The optimistic price `p*_max = max {arg max_{q ∈ [p̲, p̄]} R_max(q)}` (p. 13). -/
noncomputable def pStarMax (I : Instance K) : ℝ := argmaxIcc I.plo I.phi (Rmax I)

/-- The pessimistic price `p*_min = max {arg max_{q ∈ [p̲, p̄]} R_min(q)}` (p. 13). -/
noncomputable def pStarMin (I : Instance K) : ℝ := argmaxIcc I.plo I.phi (Rmin I)

/-- The **worst-case revenue loss** of a price `q`, `max_{F ∈ 𝓕} {R_F(p*_F) − R_F(q)}` (p. 12), with
`R_F(p*_F)` written as `sup_{q' ∈ [p̲, p̄]} R_F(q')`. -/
noncomputable def worstLoss (I : Instance K) (q : ℝ) : ℝ :=
  sSup ((fun μ => sSup (RF I μ '' Icc I.plo I.phi) - RF I μ q) '' Amb I)

/-- The **minimax revenue loss** `Δ = min_{q ∈ [p̲, p̄]} max_{F ∈ 𝓕} {R_F(p*_F) − R_F(q)}` (p. 16). -/
noncomputable def Delta (I : Instance K) : ℝ := sInf (worstLoss I '' Icc I.plo I.phi)

/-! ### Offline data, algorithms, identifiability (pp. 9–10, Definition 1 on p. 12) -/

/-- A censored (or base-demand) dataset with sample sizes `Nv i = Nᵢ`: entry `i j` is the `j`-th
observation at the `i`-th historical price. -/
abbrev Sample (K : ℕ) (Nv : Fin K → ℕ) := (i : Fin K) → Fin (Nv i) → ℝ

/-- The law of the base-demand samples `ξ^j_i`, all independent with law `μξ`. -/
noncomputable def dataLaw (I : Instance K) (Nv : Fin K → ℕ) : Measure (Sample K Nv) :=
  Measure.pi (fun i => Measure.pi (fun _ : Fin (Nv i) => I.μξ))

/-- The censored sales `S^j_i = min{ξ^j_i − b pᵢ, yᵢ}` generated by the base demands `ω` (p. 9). -/
noncomputable def sales (I : Instance K) {Nv : Fin K → ℕ} (ω : Sample K Nv) : Sample K Nv :=
  fun i j => min (ω i j - I.b * I.p i) (I.yh i)

/-- The data size `N = min_{i ∈ [K]} Nᵢ` (p. 10). -/
noncomputable def Nmin (Nv : Fin K → ℕ) : ℕ := ⨅ i, Nv i

/-- A **data-driven algorithm** (p. 10): for the fixed public inputs, a map from censored datasets
(of any sample sizes) to a price. -/
abbrev Algorithm (K : ℕ) := (Nv : Fin K → ℕ) → Sample K Nv → ℝ

/-- The algorithm always outputs a feasible price in `[p̲, p̄]`. -/
def Valid (P : Public K) (A : Algorithm K) : Prop := ∀ Nv S, A Nv S ∈ Icc P.plo P.phi

/-- **Near-optimality** (2): for every `ε > 0`, `lim_{N → ∞} P[max_{F ∈ 𝓕}{R_F(p*_F) − R_F(p^A)} < ε] = 1`,
stated as: the outer probability of the failure event tends to `0` as `N = min_i Nᵢ → ∞`. -/
def NearOptimal (I : Instance K) (A : Algorithm K) : Prop :=
  ∀ ε > 0, ∀ η > 0, ∃ N0 : ℕ, ∀ Nv : Fin K → ℕ, N0 ≤ Nmin Nv →
    dataLaw I Nv {ω | ε ≤ worstLoss I (A Nv (sales I ω))} ≤ ENNReal.ofReal η

/-- **Identifiability** (Definition 1, p. 12): some data-driven algorithm with feasible prices is
near-optimal. -/
def Identifiable (I : Instance K) : Prop := ∃ A : Algorithm K, Valid I.toPublic A ∧ NearOptimal I A

end OfflineCensoredPricing.Identifiability



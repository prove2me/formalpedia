-- Prove2me | Definitions.Def_SPOBounds_Margin_Rademacher
-- name    : SPOBounds_Margin_Rademacher
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-26T18:32:06.165527+00:00
-- url     : https://prove2.me/theorems/29193030-aab1-4a44-b0d9-3bf6188c2a56
-- title:
--   Multivariate Rademacher complexity $\hat{\mathfrak R}^n(\mathcal H)$, $\mathfrak R^n(\mathcal H)$, margin Rademacher complexity, SPO and margin risks
-- statement:
--   Let $\mathcal X$ be a feature space, $\mathcal H$ a class of maps from $\mathcal X$ to cost vectors, and $(x_1,c_1),\dots,(x_n,c_n)$ a sample. Signs $\sigma$ are i.i.d. Rademacher ($\pm1$ with probability $1/2$ each), so $\mathbb E_\sigma$ is the uniform average over all sign patterns.
--
--   1. **Multivariate empirical Rademacher complexity** (eq. (4)/(6)), for cost vectors on $\mathbb R^d$ with the Euclidean norm:
--   $$\hat{\mathfrak R}^n(\mathcal H) := \mathbb E_{\boldsymbol\sigma}\Big[\sup_{f\in\mathcal H}\frac1n\sum_{i=1}^n\sum_{j=1}^d\sigma_{ij}f_j(x_i)\Big] = \mathbb E_{\boldsymbol\sigma}\Big[\sup_{f\in\mathcal H}\frac1n\sum_{i=1}^n\boldsymbol\sigma_i^\top f(x_i)\Big],$$
--   with $\sigma_{ij}$ i.i.d. Rademacher and $\boldsymbol\sigma_i=(\sigma_{i1},\dots,\sigma_{id})^\top$.
--   2. **Expected multivariate Rademacher complexity** $\mathfrak R^n(\mathcal H) := \mathbb E\big[\hat{\mathfrak R}^n(\mathcal H)\big]$, the expectation over an i.i.d. sample of size $n$ from the distribution $\mathcal D$.
--   3. **Empirical Rademacher complexity with respect to the $\gamma$-margin SPO loss**
--   $$\hat{\mathfrak R}^n_{\gamma\rm SPO}(\mathcal H) := \mathbb E_\sigma\Big[\sup_{f\in\mathcal H}\frac1n\sum_{i=1}^n\sigma_i\,\ell^\gamma_{\rm SPO}(f(x_i),c_i)\Big],$$
--   with scalar Rademacher signs $\sigma_1,\dots,\sigma_n$.
--   4. **SPO risk** $R_{\rm SPO}(f) := \mathbb E_{(x,c)\sim\mathcal D}\big[\ell_{\rm SPO}(f(x),c)\big]$ and **empirical $\gamma$-margin SPO risk** $\hat R^\gamma_{\rm SPO}(f) := \frac1n\sum_{i=1}^n\ell^\gamma_{\rm SPO}(f(x_i),c_i)$.
--   5. Two auxiliary quantities used only in measurability hypotheses: the expected margin risk $\mathbb E_{\mathcal D}[\ell^\gamma_{\rm SPO}(f(x),c)]$ and the uniform deviation $\sup_{f\in\mathcal H}\big(\mathbb E_{\mathcal D}[\ell^\gamma_{\rm SPO}(f(x),c)] - \hat R^\gamma_{\rm SPO}(f)\big)$.
--
--   The multivariate complexity measures the richness of a vector-valued class directly; the margin-based bound of the paper controls $\hat{\mathfrak R}^n_{\gamma\rm SPO}$ by it.
--
--   **Formalization Note** A prediction $f(x_i)$ is a continuous linear functional on $\mathbb R^d$ (Euclidean norm), so $\boldsymbol\sigma_i^\top f(x_i)$ is $f(x_i)$ applied to the sign vector $\boldsymbol\sigma_i$. The expectations over signs are finite averages over all $2^{nd}$ (resp. $2^n$) sign patterns, with `true ↦ +1`, `false ↦ −1`. Suprema are `⨆` over the subtype of $\mathcal H$: this is the junk value $0$ when the set of values is unbounded above, so theorems using $\hat{\mathfrak R}^n(\mathcal H)$ assume the multivariate sums are bounded above. $\mathfrak R^n(\mathcal H)$ and the risks are Bochner integrals, which are $0$ for non-integrable integrands; theorems assume what is needed for them to be the paper's quantities.
-- source:
--   El Balghiti, Elmachtoub, Grigas, Tewari, Generalization Bounds in the Predict-then-Optimize Framework, arXiv:1905.11488v3, p. 6 (risks), p. 10 (eq. (4)), p. 18 (eq. (6), $\hat R^\gamma_{\rm SPO}$, $\hat{\mathfrak R}^n_{\gamma\rm SPO}$)

import Mathlib
import Definitions.Def_SPOBounds_Margin_Model
import Definitions.Def_SPOBounds_Margin_Degeneracy

open MeasureTheory

namespace SPOBounds.Margin

/-- The sign vector `(σ_{i1}, …, σ_{id}) ∈ {±1}^d` in `ℝ^d` (with the Euclidean norm) encoded
by `b : Fin d → Bool` (`true ↦ +1`, `false ↦ −1`). -/
noncomputable def signVec {d : ℕ} (b : Fin d → Bool) : EuclideanSpace ℝ (Fin d) :=
  WithLp.toLp 2 (fun j => if b j then (1 : ℝ) else -1)

/-- For a fixed sign matrix `σ ∈ {±1}^{n×d}`, the supremum
`sup_{f ∈ H} (1/n) ∑ᵢ σᵢᵀ f(xᵢ)` on the feature sample `x`; the prediction `f(xᵢ)` is a
continuous linear functional on `ℝ^d`, so `σᵢᵀ f(xᵢ) = ∑ⱼ σᵢⱼ fⱼ(xᵢ)` is `f(xᵢ)(σᵢ)`. -/
noncomputable def multiSignedSup {d n : ℕ} {X : Type*}
    (H : Set (X → StrongDual ℝ (EuclideanSpace ℝ (Fin d)))) (x : Fin n → X)
    (σ : Fin n → Fin d → Bool) : ℝ :=
  ⨆ f : H, (1 / n : ℝ) * ∑ i, (f : X → StrongDual ℝ (EuclideanSpace ℝ (Fin d))) (x i) (signVec (σ i))

/-- The multivariate empirical Rademacher complexity (eq. (4), p. 10 = eq. (6), p. 18):
`R̂ⁿ(H) = 𝔼_σ[sup_{f ∈ H} (1/n) ∑ᵢ ∑ⱼ σᵢⱼ fⱼ(xᵢ)]`, the expectation over i.i.d. uniform signs
written as the average over all `2^{nd}` sign matrices. -/
noncomputable def empRademacherMulti {d n : ℕ} {X : Type*}
    (H : Set (X → StrongDual ℝ (EuclideanSpace ℝ (Fin d)))) (x : Fin n → X) : ℝ :=
  (1 / 2 ^ (n * d) : ℝ) * ∑ σ : Fin n → Fin d → Bool, multiSignedSup H x σ

/-- The expected multivariate Rademacher complexity `ℜⁿ(H) = 𝔼[R̂ⁿ(H)]` over an i.i.d. sample
of size `n` from `D` (p. 10, p. 18), as a Bochner integral against `Dⁿ`. -/
noncomputable def expRademacherMulti {d : ℕ} {X : Type*} [MeasurableSpace X]
    [MeasurableSpace (StrongDual ℝ (EuclideanSpace ℝ (Fin d)))]
    (D : Measure (X × StrongDual ℝ (EuclideanSpace ℝ (Fin d))))
    (H : Set (X → StrongDual ℝ (EuclideanSpace ℝ (Fin d)))) (n : ℕ) : ℝ :=
  ∫ s, empRademacherMulti H (fun i => (s i).1) ∂(Measure.pi fun _ : Fin n => D)

/-- For a fixed sign vector `σ ∈ {±1}ⁿ`, the supremum
`sup_{f ∈ H} (1/n) ∑ᵢ σᵢ ℓ^γ_SPO(f(xᵢ), cᵢ)` on the sample `s`. -/
noncomputable def marginSignedSup {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {n : ℕ} {X : Type*} (S : Set E) (w : StrongDual ℝ E → E) (γ : ℝ)
    (H : Set (X → StrongDual ℝ E)) (σ : Fin n → Bool) (s : Fin n → X × StrongDual ℝ E) : ℝ :=
  ⨆ f : H, (1 / n : ℝ) * ∑ i,
    (if σ i then (1 : ℝ) else -1) * marginLoss S w γ ((f : X → StrongDual ℝ E) (s i).1) (s i).2

/-- The empirical Rademacher complexity of `H` with respect to the `γ`-margin SPO loss (p. 18):
`R̂ⁿ_{γSPO}(H) = 𝔼_σ[sup_{f ∈ H} (1/n) ∑ᵢ σᵢ ℓ^γ_SPO(f(xᵢ), cᵢ)]`, averaged over all `2ⁿ`
sign vectors. -/
noncomputable def empRademacherMargin {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {n : ℕ} {X : Type*} (S : Set E) (w : StrongDual ℝ E → E) (γ : ℝ)
    (H : Set (X → StrongDual ℝ E)) (s : Fin n → X × StrongDual ℝ E) : ℝ :=
  (1 / 2 ^ n : ℝ) * ∑ σ : Fin n → Bool, marginSignedSup S w γ H σ s

/-- The SPO risk `R_SPO(f) = 𝔼_{(x,c)∼D}[ℓ_SPO(f(x), c)]` (p. 6). -/
noncomputable def spoRisk {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace (StrongDual ℝ E)] {X : Type*} [MeasurableSpace X]
    (D : Measure (X × StrongDual ℝ E)) (w : StrongDual ℝ E → E)
    (f : X → StrongDual ℝ E) : ℝ :=
  ∫ z, spoLoss w (f z.1) z.2 ∂D

/-- The empirical `γ`-margin SPO risk `R̂^γ_SPO(f) = (1/n) ∑ᵢ ℓ^γ_SPO(f(xᵢ), cᵢ)` (p. 18). -/
noncomputable def empMarginRisk {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {n : ℕ} {X : Type*} (S : Set E) (w : StrongDual ℝ E → E) (γ : ℝ)
    (f : X → StrongDual ℝ E) (s : Fin n → X × StrongDual ℝ E) : ℝ :=
  (1 / n : ℝ) * ∑ i, marginLoss S w γ (f (s i).1) (s i).2

/-- The expected `γ`-margin SPO risk `𝔼_{(x,c)∼D}[ℓ^γ_SPO(f(x), c)]`. It appears only in a
measurability hypothesis. -/
noncomputable def marginRisk {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace (StrongDual ℝ E)] {X : Type*} [MeasurableSpace X]
    (S : Set E) (w : StrongDual ℝ E → E) (γ : ℝ)
    (D : Measure (X × StrongDual ℝ E)) (f : X → StrongDual ℝ E) : ℝ :=
  ∫ z, marginLoss S w γ (f z.1) z.2 ∂D

/-- The uniform deviation `sup_{f ∈ H} (𝔼[ℓ^γ_SPO(f(x), c)] − R̂^γ_SPO(f))` on the sample `s`;
it appears only in a measurability hypothesis. -/
noncomputable def marginSupDeviation {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace (StrongDual ℝ E)] {n : ℕ} {X : Type*} [MeasurableSpace X]
    (S : Set E) (w : StrongDual ℝ E → E) (γ : ℝ)
    (D : Measure (X × StrongDual ℝ E)) (H : Set (X → StrongDual ℝ E))
    (s : Fin n → X × StrongDual ℝ E) : ℝ :=
  ⨆ f : H, (marginRisk S w γ D f - empMarginRisk S w γ f s)

end SPOBounds.Margin



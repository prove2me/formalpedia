-- Prove2me | Definitions.Def_SPOBounds_Natarajan_Rademacher
-- name    : SPOBounds_Natarajan_Rademacher
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-26T18:26:54.103138+00:00
-- url     : https://prove2.me/theorems/1efc4dba-c058-402f-a33e-1e651568acb1
-- title:
--   SPO risk, empirical SPO risk, and the (empirical / expected) Rademacher complexity w.r.t. the SPO loss
-- statement:
--   Fix an oracle $w^*$ (see `SPOBounds.Natarajan.Model`), a feature space $\mathcal X$, a distribution $\mathcal D$ on $\mathcal X\times\mathbb R^d$ and a hypothesis class $\mathcal H$ of maps $f:\mathcal X\to\mathbb R^d$. For a sample $(x_1,c_1),\dots,(x_n,c_n)$:
--
--   1. **SPO risk** $R_{\rm SPO}(f) := \mathbb E_{(x,c)\sim\mathcal D}\big[\ell_{\rm SPO}(f(x),c)\big]$.
--   2. **Empirical SPO risk** $\hat R_{\rm SPO}(f) := \frac1n\sum_{i=1}^n \ell_{\rm SPO}(f(x_i),c_i)$.
--   3. **Empirical Rademacher complexity with respect to the SPO loss**
--   $$\hat{\mathfrak R}^n_{\rm SPO}(\mathcal H) := \mathbb E_\sigma\Big[\sup_{f\in\mathcal H}\frac1n\sum_{i=1}^n\sigma_i\,\ell_{\rm SPO}(f(x_i),c_i)\Big],$$
--   where $\sigma_1,\dots,\sigma_n$ are i.i.d. uniform signs in $\{-1,+1\}$.
--   4. **Expected Rademacher complexity** $\mathfrak R^n_{\rm SPO}(\mathcal H) := \mathbb E\big[\hat{\mathfrak R}^n_{\rm SPO}(\mathcal H)\big]$, the expectation over an i.i.d. sample of size $n$ from $\mathcal D$.
--   5. Two auxiliary functions of the sample that enter only measurability hypotheses: for each fixed sign vector $\sigma$, the supremum $\sup_{f\in\mathcal H}\frac1n\sum_i\sigma_i\ell_{\rm SPO}(f(x_i),c_i)$; and the uniform deviation $\sup_{f\in\mathcal H}\big(R_{\rm SPO}(f)-\hat R_{\rm SPO}(f)\big)$.
--
--   $\hat{\mathfrak R}^n_{\rm SPO}(\mathcal H)$ measures how well the SPO losses of $\mathcal H$ can correlate with random noise; it is the complexity term of the generalization bounds of the mission.
--
--   **Formalization Note** The expectation over signs is the exact average over all $2^n$ sign vectors ($\texttt{true}\mapsto+1$, $\texttt{false}\mapsto-1$). $R_{\rm SPO}$ and $\mathfrak R^n_{\rm SPO}$ are Bochner integrals (against $\mathcal D$ and the product measure $\mathcal D^n$); they return $0$ for a non-integrable integrand, which is why the theorems that use them on the right-hand side of a bound carry measurability hypotheses. Suprema over $\mathcal H$ are real `iSup`s over the subtype of $\mathcal H$; on samples with costs in a bounded set they are bounded, and over an empty class they equal $0$.
-- source:
--   El Balghiti, Elmachtoub, Grigas, Tewari, Generalization Bounds in the Predict-then-Optimize Framework, arXiv:1905.11488v3, p. 6 (§2, risks), pp. 8–9 (§2.2, Rademacher complexity w.r.t. the SPO loss)

import Mathlib
import Definitions.Def_SPOBounds_Natarajan_Model

open MeasureTheory

namespace SPOBounds.Natarajan

/-- The SPO risk `R_SPO(f) = 𝔼_{(x,c)∼D}[ℓ_SPO(f(x), c)]` (p. 6). -/
noncomputable def spoRisk {d : ℕ} {X : Type*} [MeasurableSpace X]
    (D : Measure (X × EuclideanSpace ℝ (Fin d)))
    (w : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (f : X → EuclideanSpace ℝ (Fin d)) : ℝ :=
  ∫ z, spoLoss w (f z.1) z.2 ∂D

/-- The empirical SPO risk `R̂_SPO(f) = (1/n) ∑ᵢ ℓ_SPO(f(xᵢ), cᵢ)` on the sample `s` (p. 6). -/
noncomputable def empRisk {d n : ℕ} {X : Type*}
    (w : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (f : X → EuclideanSpace ℝ (Fin d)) (s : Fin n → X × EuclideanSpace ℝ (Fin d)) : ℝ :=
  (1 / n : ℝ) * ∑ i, spoLoss w (f (s i).1) (s i).2

/-- For a fixed sign vector `σ ∈ {±1}ⁿ` (`true ↦ +1`, `false ↦ −1`), the supremum
`sup_{f ∈ H} (1/n) ∑ᵢ σᵢ ℓ_SPO(f(xᵢ), cᵢ)` on the sample `s`. -/
noncomputable def signedSup {d n : ℕ} {X : Type*}
    (w : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (H : Set (X → EuclideanSpace ℝ (Fin d))) (σ : Fin n → Bool)
    (s : Fin n → X × EuclideanSpace ℝ (Fin d)) : ℝ :=
  ⨆ f : H, (1 / n : ℝ) * ∑ i, (if σ i then (1 : ℝ) else -1) * spoLoss w ((f : X → _) (s i).1) (s i).2

/-- The empirical Rademacher complexity of `H` with respect to the SPO loss (p. 8):
`R̂ⁿ_SPO(H) = 𝔼_σ[sup_{f ∈ H} (1/n) ∑ᵢ σᵢ ℓ_SPO(f(xᵢ), cᵢ)]`, the expectation over i.i.d.
uniform signs written as the average over all `2ⁿ` sign vectors. -/
noncomputable def empRademacherSPO {d n : ℕ} {X : Type*}
    (w : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (H : Set (X → EuclideanSpace ℝ (Fin d))) (s : Fin n → X × EuclideanSpace ℝ (Fin d)) : ℝ :=
  (1 / 2 ^ n : ℝ) * ∑ σ : Fin n → Bool, signedSup w H σ s

/-- The expected Rademacher complexity `ℜⁿ_SPO(H) = 𝔼[R̂ⁿ_SPO(H)]` over an i.i.d. sample of
size `n` from `D` (p. 9), as a Bochner integral against the product measure `Dⁿ`. -/
noncomputable def expRademacherSPO {d : ℕ} {X : Type*} [MeasurableSpace X]
    (D : Measure (X × EuclideanSpace ℝ (Fin d)))
    (w : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (H : Set (X → EuclideanSpace ℝ (Fin d))) (n : ℕ) : ℝ :=
  ∫ s, empRademacherSPO w H s ∂(Measure.pi fun _ : Fin n => D)

/-- The uniform deviation `sup_{f ∈ H} (R_SPO(f) − R̂_SPO(f))` on the sample `s`; it appears
only in a measurability hypothesis. -/
noncomputable def supDeviation {d n : ℕ} {X : Type*} [MeasurableSpace X]
    (D : Measure (X × EuclideanSpace ℝ (Fin d)))
    (w : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (H : Set (X → EuclideanSpace ℝ (Fin d))) (s : Fin n → X × EuclideanSpace ℝ (Fin d)) : ℝ :=
  ⨆ f : H, (spoRisk D w f - empRisk w f s)

end SPOBounds.Natarajan



-- Prove2me | Definitions.Def_PrivRobustStat_Supplement_Models
-- name    : PrivRobustStat_Supplement_Models
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T07:02:33.785208+00:00
-- url     : https://prove2.me/theorems/02a2cebc-a4b1-4ce1-b620-4989840d7a72
-- title:
--   Population covariance $\Sigma$, Model 2 (hypercontractive moments) and Model 3 (sub-Gaussianity)
-- statement:
--   Let $D$ be a probability distribution on $\mathbb R^d$ (Euclidean norm) with mean $\mu=\mathbb E_D[x]$. Its **covariance** is the $d\times d$ matrix
--
--   $$\Sigma_{ab}=\mathbb E_{x\sim D}\big[(x-\mu)_a(x-\mu)_b\big],\qquad u^\top\Sigma u=\sum_{a,b}u_a\Sigma_{ab}u_b .$$
--
--   **Model 2** (hypercontractive moments) with parameters $\ell$ and $C_\ell$: $D$ has a finite $\ell$-th moment and
--
--   $$\Big(\mathbb E_{x\sim D}\big|u^\top(x-\mu)\big|^\ell\Big)^{1/\ell}\le C_\ell\,\big(u^\top\Sigma u\big)^{1/2}\quad\text{for all }u\in\mathbb R^d .$$
--
--   **Model 3** (sub-Gaussianity) with parameter $\theta$: $D$ has a finite second moment, and for every $u\in\mathbb R^d$ the variable $\exp(u^\top(x-\mu))$ is integrable with
--
--   $$\mathbb E_{x\sim D}\big[\exp(u^\top(x-\mu))\big]\le\exp\Big(\frac{\theta\,u^\top\Sigma u}{2}\Big).$$
--
--   The paper's standing constraints on the parameters ($\ell$ an even integer, $\ell\ge4$, $C_\ell\ge1$, $\theta\ge1$) are hypotheses of the theorems that use the models. These are the distribution classes of Problems 2–4: sub-Gaussian mean estimation and PCA (Model 3) and heavy-tailed PCA (Model 2).
--
--   **Formalization Note** $\mu$ is the base mission's `popMean`. The finite-moment conditions (`MemLp id ℓ`, `MemLp id 2`) and the integrability of the exponential are required because Lean's integral of a non-integrable function is $0$; without them both moment bounds would hold vacuously. The sub-Gaussian bound itself implies all moments, so the second-moment clause excludes no distribution the paper admits.
-- source:
--   Gu, Jambulapati, Kumar, Mouzakis, Tian, Yang, Efficient Private and Robust Statistics, STOC 2027 submission (manuscript sha256 1a69e17a…), Models 2 and 3, p.14 (PDF p.17); Problems 2–4, pp.14–15 (PDF pp.17–18)

import Mathlib
import Definitions.Def_PrivRobustStat_Model

open MeasureTheory

namespace PrivRobustStat.Supplement

/-!
# Population covariance, Model 2 (hypercontractive moments) and Model 3 (sub-Gaussianity)

Gu, Jambulapati, Kumar, Mouzakis, Tian, Yang, *Efficient Private and Robust Statistics*, STOC 2027
submission (manuscript sha256 1a69e17a…): Models 2 and 3, p.14 (PDF p.17); Problems 2–4,
pp.14–15 (PDF pp.17–18).

**Formalization Note.**
* Points live in `PrivRobustStat.Vec d = EuclideanSpace ℝ (Fin d)` and `µ = popMean D` is the
  Bochner mean of the published base module.
* `popCov D` is the covariance matrix `Σ_ab = E[(x − µ)_a (x − µ)_b]`; it is only meaningful under a
  finite second moment, which both models require (`MemLp id 2`, resp. `MemLp id ℓ` with `ℓ ≥ 4`),
  since Lean's integral of a non-integrable function is `0`.
* `quadForm Σ u = u⊤Σu = ∑_{a,b} u_a Σ_ab u_b`.
* Model 3 requires each `x ↦ exp⟨u, x − µ⟩` to be integrable: otherwise its Lean integral is `0`
  and the moment-generating-function bound would hold vacuously.
* The parameter constraints of the models (`ℓ` even, `ℓ ≥ 4`, `C_ℓ ≥ 1`, `θ ≥ 1`) are stated as
  hypotheses of the theorems that use them.
-/

/-- The population covariance `Σ := E_{x∼D}[(x − µ)(x − µ)⊤]`, `µ = popMean D`, entrywise as a
Bochner integral. -/
noncomputable def popCov {d : ℕ} (D : Measure (Vec d)) : Matrix (Fin d) (Fin d) ℝ :=
  fun a b => ∫ x, (x - popMean D) a * (x - popMean D) b ∂D

/-- The quadratic form `u⊤Σu = ∑_{a,b} u_a Σ_ab u_b`. -/
noncomputable def quadForm {d : ℕ} (S : Matrix (Fin d) (Fin d) ℝ) (u : Vec d) : ℝ :=
  ∑ a, ∑ b, u a * S a b * u b

/-- **Model 2** (hypercontractive moments, p.14) with parameters `ℓ` and `C_ℓ`: `D` has finite
`ℓ`-th moment (so its mean `µ` and covariance `Σ` exist) and
`(E_{x∼D} |u⊤(x − µ)|^ℓ)^{1/ℓ} ≤ C_ℓ (u⊤Σu)^{1/2}` for all `u ∈ ℝ^d`. -/
def IsModel2 {d : ℕ} (ℓ : ℕ) (Cℓ : ℝ) (D : Measure (Vec d)) : Prop :=
  MemLp id (ℓ : ENNReal) D ∧
    ∀ u : Vec d, (∫ x, |inner ℝ u (x - popMean D)| ^ ℓ ∂D) ^ (1 / (ℓ : ℝ)) ≤
      Cℓ * Real.sqrt (quadForm (popCov D) u)

/-- **Model 3** (sub-Gaussianity, p.14) with parameter `θ`: `D` has finite second moment (so its mean
`µ` and covariance `Σ` exist), and for every `u ∈ ℝ^d` the function `x ↦ exp(u⊤(x − µ))` is
integrable with `E_{x∼D}[exp(u⊤(x − µ))] ≤ exp(θ u⊤Σu / 2)`. -/
def IsModel3 {d : ℕ} (θ : ℝ) (D : Measure (Vec d)) : Prop :=
  MemLp id 2 D ∧
    ∀ u : Vec d, Integrable (fun x => Real.exp (inner ℝ u (x - popMean D))) D ∧
      ∫ x, Real.exp (inner ℝ u (x - popMean D)) ∂D ≤ Real.exp (θ * quadForm (popCov D) u / 2)

end PrivRobustStat.Supplement



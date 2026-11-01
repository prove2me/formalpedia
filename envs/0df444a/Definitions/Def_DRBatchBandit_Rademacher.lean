-- Prove2me | Definitions.Def_DRBatchBandit_Rademacher
-- name    : DRBatchBandit_Rademacher
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T09:23:01.395998+00:00
-- url     : https://prove2.me/theorems/b83b6531-c0bb-4072-a965-c536696c13d7
-- title:
--   Rademacher complexity $\mathcal R_n(\mathcal F)$ (Definition 9)
-- statement:
--   Let $\mathcal F$ be a family of real-valued functions on a measurable space $Z$, let $z_1,\dots,z_n$ be iid from a probability measure $\mu$ on $Z$, and let $\sigma_1,\dots,\sigma_n$ be iid signs with $\mathbf P(\sigma_i=1)=\mathbf P(\sigma_i=-1)=1/2$, independent of the $z_i$ (Definition 9, p.42). The **Rademacher complexity** of $\mathcal F$ is
--   $$\mathcal R_n(\mathcal F)=\mathbf E_{z,\sigma}\Big[\sup_{f\in\mathcal F}\Big|\frac1n\sum_{i=1}^n\sigma_if(z_i)\Big|\Big].$$
--
--   It is the complexity term of the uniform deviation bound, Theorem A7.
--
--   **Formalization Note** The expectation over the signs is the average over the $2^n$ sign vectors; the expectation over $z$ is a Bochner integral against $\mu^{\otimes n}$.
-- source:
--   Si, Zhang, Zhou & Blanchet, Distributionally Robust Batch Contextual Bandits, arXiv:2006.05630v7, Definition 9 p.42. PDF sha256 ac485985feb75d33b603f06f5a5d93c52077877db7be11de3d71107c7c374b02

import Mathlib

open MeasureTheory

namespace DRBatchBandit

/-- Definition 9 (arXiv:2006.05630v7, p.42): the Rademacher complexity
`ℛ_n(ℱ) = E_{z,σ}[sup_{f ∈ ℱ} |(1/n) ∑ᵢ σᵢ f(zᵢ)|]` of a class `ℱ` of real functions on `Z`,
with `z₁, …, z_n` iid from `μ` and `σ₁, …, σ_n` iid uniform signs.

**Formalization Note.** The expectation over the signs is the average over the `2ⁿ` sign
vectors `σ : Fin n → Bool` (`true ↦ +1`, `false ↦ −1`); the expectation over `z` is a Bochner
integral against `μⁿ`. -/
noncomputable def rademacher {Z : Type*} [MeasurableSpace Z] (μ : Measure Z) (n : ℕ)
    (F : Set (Z → ℝ)) : ℝ :=
  ∫ z, (1 / 2 ^ n : ℝ) * ∑ σ : Fin n → Bool,
      ⨆ f : F, |(1 / n : ℝ) * ∑ i, (if σ i then (1 : ℝ) else -1) * f.1 (z i)|
    ∂(Measure.pi fun _ : Fin n => μ)

end DRBatchBandit



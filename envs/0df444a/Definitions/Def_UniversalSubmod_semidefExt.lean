-- Prove2me | Definitions.Def_UniversalSubmod_semidefExt
-- name    : UniversalSubmod_semidefExt
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T07:51:40.689911+00:00
-- url     : https://prove2.me/theorems/a454f39f-b8a0-4a4a-9597-e2c2f73bf3a5
-- title:
--   The semidefinite extension $F(x,\Sigma)=\mathbb E[f(R)]$ of a set function
-- statement:
--   Let $f:2^{[n]}\to\mathbb R$ be a set function, $x\in[0,1]^n$ and $\Sigma\in\mathcal E_n$. Represent element $i$ by a unit vector $v_i$ with $\langle v_i,v_j\rangle=\sigma_{ij}$, let $Z\sim N(0,I_n)$ and $G_i=\langle v_i,Z\rangle$, so that $G=(G_1,\dots,G_n)\sim N(0,\Sigma)$. The random set
--   $$
--   R=\{i\in[n] : G_i\ge \Phi^{-1}(1-x_i)\}
--   $$
--   contains each $i$ with probability $x_i$, with correlations determined by $\Sigma$. The **semidefinite extension** of $f$ is
--   $$
--   F(x,\Sigma)=\mathbb E[f(R)].
--   $$
--   For $\Sigma=I$ the elements are independent and $x\mapsto F(x,I)$ is the multilinear extension of $f$.
--
--   **Formalization Note** $\Phi$ is the published `Cohen2019.Robust.Phi`, Mathlib's `cdf (gaussianReal 0 1)`. The expectation is taken against Mathlib's `multivariateGaussian 0 Σ`, the law $N(0,\Sigma)$ of $G$ (the law of $R$ depends only on $\Sigma$). That measure is a Dirac mass at $0$ when $\Sigma$ is not positive semidefinite, so every statement using this definition assumes $\Sigma\in\mathcal E_n$. The condition $G_i\ge\Phi^{-1}(1-x_i)$ is written $1-x_i\le\Phi(G_i)$: the same event for $x_i\in(0,1)$, and "never"/"always" at $x_i=0$/$x_i=1$, the convention $\Phi^{-1}(1)=+\infty$, $\Phi^{-1}(0)=-\infty$.
-- source:
--   Adamczyk, Ueltzen, Vondrák, Optimal universal sets for submodular functions, manuscript (Nov. 3, 2026; sha256 8a53c0912e8ad39b1019cbabfbde98980fd3eea456a8c7e5b28eb55d58343714), §2.2, p.6

import Mathlib
import Definitions.Def_Cohen2019_Robust_Phi

namespace UniversalSubmod

open MeasureTheory ProbabilityTheory Cohen2019.Robust

/-- **The semidefinite extension** `F(x, Σ) := E[f(R)]` (Adamczyk, Ueltzen, Vondrák, *Optimal
universal sets for submodular functions*, manuscript of November 3, 2026, §2.2, p.6), where for
`x ∈ [0,1]^n` and `Σ ∈ E_n`,
`R = {i ∈ [n] : Gᵢ = ⟨vᵢ, Z⟩ ≥ Φ⁻¹(1 − xᵢ)}` with `⟨vᵢ, vⱼ⟩ = σᵢⱼ`, `Z ~ N(0, Iₙ)`.

**Formalization Note.** The Gaussian vector `G = (⟨vᵢ, Z⟩)ᵢ` has law `N(0, Σ)`, which is Mathlib's
`multivariateGaussian 0 Σ` on `EuclideanSpace ℝ (Fin n)`; so the expectation is taken directly
against that law; `Φ` is the published `Cohen2019.Robust.Phi = cdf (gaussianReal 0 1)` (the paper notes the law of `R` depends only on `Σ`). Mathlib's
`multivariateGaussian 0 Σ` is the Dirac mass at `0` when `Σ` is not positive semidefinite, so every
statement using this definition assumes `Σ ∈ E_n`. The threshold `Gᵢ ≥ Φ⁻¹(1 − xᵢ)` is written
`1 − xᵢ ≤ Φ(Gᵢ)`: for `xᵢ ∈ (0,1)` this is the same event (Φ is a strictly increasing bijection
`ℝ → (0,1)`), and at `xᵢ = 0` (resp. `1`) it is never (resp. always) satisfied, the convention
`Φ⁻¹(1) = +∞`, `Φ⁻¹(0) = −∞` for which `i ∈ R` with probability `xᵢ`. The integrand takes finitely
many values and is measurable, so the integral is a genuine expectation. -/
noncomputable def semidefExt {n : ℕ} (f : Finset (Fin n) → ℝ) (x : Fin n → ℝ)
    (S : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  ∫ g, f (Finset.univ.filter (fun i => 1 - x i ≤ Phi (g i))) ∂(multivariateGaussian 0 S)

end UniversalSubmod



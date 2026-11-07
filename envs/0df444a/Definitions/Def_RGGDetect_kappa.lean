-- Prove2me | Definitions.Def_RGGDetect_kappa
-- name    : RGGDetect_kappa
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T22:36:31.83932+00:00
-- url     : https://prove2.me/theorems/23df14a6-71fc-47b1-bef0-4ac2bf6bb90d
-- title:
--   The cap kernel $\kappa$, the local interaction $\eta_k$, and the $p$-biased Fourier basis
-- statement:
--   Let $p=\mathbb P\{\langle x_1,x_2\rangle\ge\tau\}$ with $0<p<1$.
--
--   1. The **centered standardized cap kernel** (3) is $\kappa(u)=\dfrac{\mathbf 1\{u\ge\tau\}-p}{\sqrt{p(1-p)}}$.
--   2. The **local interaction function** (4) is
--   $$
--   \eta_k(x_1,\dots,x_k)=\mathbb E_z\Big[\prod_{i=1}^k\kappa(\langle z,x_i\rangle)\Big],
--   $$
--   with $z$ uniform on $S^{d-1}$.
--   3. For $y\in\{0,1\}^\iota$ the product Bernoulli mass is $Q(y)=\prod_i p^{y_i}(1-p)^{1-y_i}$, the mass of $\mathrm{Bern}(p)^{\otimes\iota}$.
--   4. The **$p$-biased Fourier basis** (11) is $\psi_S(y)=\prod_{i\in S}\dfrac{y_i-p}{\sqrt{p(1-p)}}$, $S\subseteq\iota$.
--
--   The Fourier coefficients of the likelihood ratio of a new row of the adjacency matrix are posterior means of $\eta_{|S|}$, which is how these objects enter the proof.
--
--   **Formalization Note** $p$ is computed from $(d,\tau)$. Elements of $\{0,1\}^\iota$ are Boolean functions (`true` is $1$).
-- source:
--   Du, Mao, Sun, Wu, Xu, Sharp detection thresholds for random geometric graphs with polynomial average degrees, arXiv:2610.08517 (held version, sha256 e7bebd4a…), eqs. (3), (4), p.2 (PDF p.4); eq. (11), p.5 (PDF p.7)

import Mathlib
import Definitions.Def_RGGDetect_unifSphere

open MeasureTheory

namespace RGGDetect

/-- The centered standardized cap kernel (3), `κ(u) = (1{u ≥ τ} - p)/√(p(1-p))`, with
`p = P{⟨x₁, x₂⟩ ≥ τ}` (arXiv:2610.08517, held version, p.2, eq. (3)).

**Formalization Note** `p` is computed from `(d, τ)` as `capProb d τ`. The kernel is meaningful for
`0 < p < 1`; every statement using it assumes this (or is in the regime, where it holds eventually). -/
noncomputable def kappa (d : ℕ) (τ : ℝ) (u : ℝ) : ℝ :=
  ((if τ ≤ u then 1 else 0) - capProb d τ) / Real.sqrt (capProb d τ * (1 - capProb d τ))

/-- The local interaction function (4), `η_k(x₁, …, x_k) = E_z[∏_{i=1}^k κ(⟨z, x_i⟩)]`, `z` uniform on
`S^{d-1}` (arXiv:2610.08517, held version, p.2, eq. (4)). -/
noncomputable def eta (d : ℕ) (τ : ℝ) (k : ℕ) (x : Fin k → Sph d) : ℝ :=
  ∫ z, ∏ i, kappa d τ (ip z (x i)) ∂(unifSphere d)

/-- The product Bernoulli mass `Q(y) = ∏_i p^{y_i}(1-p)^{1-y_i}` of `y ∈ {0,1}^ι` (a point of
`Bern(p)^{⊗ι}`; `true` is `1`). -/
noncomputable def bernProd (p : ℝ) {ι : Type*} [Fintype ι] (y : ι → Bool) : ℝ :=
  ∏ i, if y i then p else 1 - p

/-- The `p`-biased Fourier basis (11), `ψ_S(y) = ∏_{i ∈ S} (y_i - p)/√(p(1-p))`
(arXiv:2610.08517, held version, p.5, eq. (11)). -/
noncomputable def psi (p : ℝ) {ι : Type*} (S : Finset ι) (y : ι → Bool) : ℝ :=
  ∏ i ∈ S, ((if y i then 1 else 0) - p) / Real.sqrt (p * (1 - p))

end RGGDetect



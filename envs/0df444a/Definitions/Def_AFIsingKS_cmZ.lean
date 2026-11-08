-- Prove2me | Definitions.Def_AFIsingKS_cmZ
-- name    : AFIsingKS_cmZ
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T10:14:57.111301+00:00
-- url     : https://prove2.me/theorems/abf3e70c-7067-43bf-be2d-885efcc55b05
-- title:
--   Partition functions of a matching at complex $\beta$
-- statement:
--   For a perfect matching $M$ and $\beta\in\mathbb C$, write $G$ for the contracted multigraph and $\mathcal H_G=\mathcal H_M$. Define
--   $$Z_G(\beta)=\sum_{\sigma}e^{\beta\mathcal H_G(\sigma)},\quad Z_{G,<\varepsilon}(\beta)=\sum_{\sigma\in\Sigma_n(\varepsilon)}e^{\beta\mathcal H_G(\sigma)},\quad Z_{G,\ge\varepsilon}(\beta)=\sum_{\sigma\in\Sigma_n(\varepsilon)^c}e^{\beta\mathcal H_G(\sigma)},$$
--   $$Z^{(2)}_{G,<\varepsilon}(\beta)=\sum_{\sigma^1,\sigma^2\in\Sigma_n(\varepsilon)}\mathbf 1\{|R(\sigma^1,\sigma^2)|<\varepsilon\}\,e^{\beta\mathcal H_G(\sigma^1)+\bar\beta\mathcal H_G(\sigma^2)},$$
--   and $Z^{(2)}_{G,\ge\varepsilon}(\beta)$ the same sum with $|R(\sigma^1,\sigma^2)|\ge\varepsilon$. Here $\bar\beta$ is the complex conjugate, so the last two are the near-orthogonal and the non-orthogonal parts of $|Z_{G,<\varepsilon}(\beta)|^2$.
-- source:
--   Bencs, Huang, Lee, Liu, Regts, On Zeros and Algorithms for Disordered Systems II, arXiv:2610.40598 (held version, sha256 2a07c158…), Section 2.2, p.9, and Section 3.1, pp.11–12

import Mathlib
import Definitions.Def_AFIsingKS_Matching

open scoped Classical
open ComplexConjugate

namespace AFIsingKS

/-- The partition function `Z_F(β) = ∑_σ exp(β H_F(σ))` for `F = M` (Bencs, Huang, Lee, Liu, Regts, arXiv:2610.40598 (held version, sha256 2a07c158…), Section 2.2, p.9). -/
noncomputable def cmZ {n d : ℕ} (M : Matching n d) (β : ℂ) : ℂ :=
  ∑ σ : Spin n, Complex.exp (β * (cmCut M σ : ℂ))

/-- The balanced part `Z_{G,<ε}(β) = ∑_{σ ∈ Σ_n(ε)} exp(β H_G(σ))` (Bencs, Huang, Lee, Liu, Regts, arXiv:2610.40598 (held version, sha256 2a07c158…), Section 3.1, p.11). -/
noncomputable def cmZlt {n d : ℕ} (ε : ℝ) (M : Matching n d) (β : ℂ) : ℂ :=
  ∑ σ ∈ balanced n ε, Complex.exp (β * (cmCut M σ : ℂ))

/-- The unbalanced part `Z_{G,≥ε}(β) = ∑_{σ ∈ Σ_n(ε)^c} exp(β H_G(σ))`
(Bencs, Huang, Lee, Liu, Regts, arXiv:2610.40598 (held version, sha256 2a07c158…), Section 3.1, p.11). -/
noncomputable def cmZge {n d : ℕ} (ε : ℝ) (M : Matching n d) (β : ℂ) : ℂ :=
  ∑ σ ∈ unbalanced n ε, Complex.exp (β * (cmCut M σ : ℂ))

/-- The near-orthogonal part of `|Z_{G,<ε}(β)|²`:
`Z^{(2)}_{G,<ε}(β) = ∑_{σ¹,σ² ∈ Σ_n(ε)} 1{|R(σ¹,σ²)| < ε} exp(β H_G(σ¹) + β̄ H_G(σ²))`
(Bencs, Huang, Lee, Liu, Regts, arXiv:2610.40598 (held version, sha256 2a07c158…), Section 3.1, p.12). `β̄` is the complex conjugate. -/
noncomputable def cmZ2lt {n d : ℕ} (ε : ℝ) (M : Matching n d) (β : ℂ) : ℂ :=
  ∑ σ₁ ∈ balanced n ε, ∑ σ₂ ∈ balanced n ε,
    if |overlap σ₁ σ₂| < ε then
      Complex.exp (β * (cmCut M σ₁ : ℂ) + conj β * (cmCut M σ₂ : ℂ))
    else 0

/-- The non-orthogonal part of `|Z_{G,<ε}(β)|²`:
`Z^{(2)}_{G,≥ε}(β) = ∑_{σ¹,σ² ∈ Σ_n(ε)} 1{|R(σ¹,σ²)| ≥ ε} exp(β H_G(σ¹) + β̄ H_G(σ²))`
(Bencs, Huang, Lee, Liu, Regts, arXiv:2610.40598 (held version, sha256 2a07c158…), Section 3.1, p.12). -/
noncomputable def cmZ2ge {n d : ℕ} (ε : ℝ) (M : Matching n d) (β : ℂ) : ℂ :=
  ∑ σ₁ ∈ balanced n ε, ∑ σ₂ ∈ balanced n ε,
    if ε ≤ |overlap σ₁ σ₂| then
      Complex.exp (β * (cmCut M σ₁ : ℂ) + conj β * (cmCut M σ₂ : ℂ))
    else 0

end AFIsingKS



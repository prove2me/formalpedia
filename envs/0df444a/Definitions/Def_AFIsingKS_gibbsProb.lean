-- Prove2me | Definitions.Def_AFIsingKS_gibbsProb
-- name    : AFIsingKS_gibbsProb
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T10:16:18.202014+00:00
-- url     : https://prove2.me/theorems/fddf34a4-7b98-4d0c-879b-2fc31bb102e0
-- title:
--   The Gibbs measures $\mu_{G,\beta,<\varepsilon}$, $\mu^{2,\sigma^\prime}_{G,\beta,<\varepsilon}$ and the events $\mathcal O$
-- statement:
--   For real $\beta$, the Gibbs measure on $\Sigma_n(\varepsilon)$ is $\mu_{G,\beta,<\varepsilon}(\sigma)=\exp(\beta\mathcal H_G(\sigma))/Z_{G,<\varepsilon}(\beta)$. For $\sigma'\in\Sigma_n(\varepsilon)$,
--   $$\mu^{2,\sigma'}_{G,\beta,<\varepsilon}(\sigma)=\frac{\mathbf 1\{|R(\sigma,\sigma')|<\varepsilon\}\exp(\beta\mathcal H_G(\sigma))}{\tilde Z^{(2)}_{G,<\varepsilon}(\beta,\sigma')},\qquad \tilde Z^{(2)}_{G,<\varepsilon}(\beta,\sigma')=\sum_{\sigma\in\Sigma_n(\varepsilon)}\mathbf 1\{|R(\sigma,\sigma')|<\varepsilon\}e^{\beta\mathcal H_G(\sigma)}.$$
--   The probability of a predicate in $k$ replicas is taken under $k$ i.i.d. samples. The events are
--   $$\mathcal O_{\beta,c}=\{G:\mu_{G,\beta,<\varepsilon}(|R(\sigma^1,\sigma^2)|\ge\varepsilon)\le e^{-cn}\},\quad \mathcal O^{(2)}_{\beta,c}=\{(\sigma',G):\mu^{2,\sigma'}_{G,\beta,<\varepsilon}(|R(\sigma^1,\sigma^2)|\ge\varepsilon)\le e^{-cn}\}.$$
-- source:
--   Bencs, Huang, Lee, Liu, Regts, On Zeros and Algorithms for Disordered Systems II, arXiv:2610.40598 (held version, sha256 2a07c158…), eqs. (19)–(24), pp.18–19

import Mathlib
import Definitions.Def_AFIsingKS_cmZR

open scoped Classical

namespace AFIsingKS

/-- The Gibbs probability of a one-replica predicate under `μ_{G,β,<ε}`, the probability measure on
`Σ_n(ε)` with `μ(σ) = exp(β H_G(σ)) / Z_{G,<ε}(β)` (Bencs, Huang, Lee, Liu, Regts, arXiv:2610.40598 (held version, sha256 2a07c158…), eq. (19), p.18), for a real `β`. -/
noncomputable def gibbsProb {n d : ℕ} (ε β : ℝ) (M : Matching n d) (A : Spin n → Prop) : ℝ :=
  (∑ σ ∈ balanced n ε, if A σ then Real.exp (β * (cmCut M σ : ℝ)) else 0) / cmZltR ε M β

/-- The Gibbs probability of a two-replica predicate: the probability of `A` under two i.i.d. samples
from `μ_{G,β,<ε}` (Bencs, Huang, Lee, Liu, Regts, arXiv:2610.40598 (held version, sha256 2a07c158…), Section 4, p.18). -/
noncomputable def gibbsPairProb {n d : ℕ} (ε β : ℝ) (M : Matching n d)
    (A : Spin n → Spin n → Prop) : ℝ :=
  (∑ σ₁ ∈ balanced n ε, ∑ σ₂ ∈ balanced n ε,
      if A σ₁ σ₂ then Real.exp (β * (cmCut M σ₁ : ℝ)) * Real.exp (β * (cmCut M σ₂ : ℝ)) else 0) /
    cmZltR ε M β ^ 2

/-- The normalizer `Z̃^{(2)}_{G,<ε}(β, σ') = ∑_{σ ∈ Σ_n(ε)} 1{|R(σ, σ')| < ε} exp(β H_G(σ))`
(Bencs, Huang, Lee, Liu, Regts, arXiv:2610.40598 (held version, sha256 2a07c158…), eq. (21), p.19). -/
noncomputable def condZ {n d : ℕ} (ε β : ℝ) (M : Matching n d) (σ' : Spin n) : ℝ :=
  ∑ σ ∈ balanced n ε, if |overlap σ σ'| < ε then Real.exp (β * (cmCut M σ : ℝ)) else 0

/-- The probability of a one-replica predicate under `μ^{2,σ'}_{G,β,<ε}`, the measure
`μ^{2,σ'}(σ) = 1{|R(σ, σ')| < ε} exp(β H_G(σ)) / Z̃^{(2)}_{G,<ε}(β, σ')` on `Σ_n(ε)`
(Bencs, Huang, Lee, Liu, Regts, arXiv:2610.40598 (held version, sha256 2a07c158…), eq. (20), p.19). -/
noncomputable def condProb {n d : ℕ} (ε β : ℝ) (M : Matching n d) (σ' : Spin n)
    (A : Spin n → Prop) : ℝ :=
  (∑ σ ∈ balanced n ε,
      if |overlap σ σ'| < ε ∧ A σ then Real.exp (β * (cmCut M σ : ℝ)) else 0) / condZ ε β M σ'

/-- The probability of a two-replica predicate under two i.i.d. samples from `μ^{2,σ'}_{G,β,<ε}`
(Bencs, Huang, Lee, Liu, Regts, arXiv:2610.40598 (held version, sha256 2a07c158…), Section 4, p.19). -/
noncomputable def condPairProb {n d : ℕ} (ε β : ℝ) (M : Matching n d) (σ' : Spin n)
    (A : Spin n → Spin n → Prop) : ℝ :=
  (∑ σ₁ ∈ balanced n ε, ∑ σ₂ ∈ balanced n ε,
      if |overlap σ₁ σ'| < ε ∧ |overlap σ₂ σ'| < ε ∧ A σ₁ σ₂ then
        Real.exp (β * (cmCut M σ₁ : ℝ)) * Real.exp (β * (cmCut M σ₂ : ℝ))
      else 0) /
    condZ ε β M σ' ^ 2

/-- The event `O_{β,c} = {G : μ_{G,β,<ε}(|R(σ¹, σ²)| ≥ ε) ≤ e^{−cn}}` (Bencs, Huang, Lee, Liu, Regts, arXiv:2610.40598 (held version, sha256 2a07c158…), eq. (22), p.19). -/
def overlapEvent {n d : ℕ} (ε c β : ℝ) (M : Matching n d) : Prop :=
  gibbsPairProb ε β M (fun σ₁ σ₂ => ε ≤ |overlap σ₁ σ₂|) ≤ Real.exp (-c * (n : ℝ))

/-- The event `O^{(2)}_{β,c} = {(σ', G) : μ^{2,σ'}_{G,β,<ε}(|R(σ¹, σ²)| ≥ ε) ≤ e^{−cn}}`
(Bencs, Huang, Lee, Liu, Regts, arXiv:2610.40598 (held version, sha256 2a07c158…), eq. (24), p.19). -/
def overlapEvent2 {n d : ℕ} (ε c β : ℝ) (σ' : Spin n) (M : Matching n d) : Prop :=
  condPairProb ε β M σ' (fun σ₁ σ₂ => ε ≤ |overlap σ₁ σ₂|) ≤ Real.exp (-c * (n : ℝ))

end AFIsingKS



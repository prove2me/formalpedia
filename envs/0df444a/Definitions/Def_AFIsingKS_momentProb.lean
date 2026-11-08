-- Prove2me | Definitions.Def_AFIsingKS_momentProb
-- name    : AFIsingKS_momentProb
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T10:15:05.210195+00:00
-- url     : https://prove2.me/theorems/b1dc2bb8-4f13-4aa7-aba1-85da16c78de9
-- title:
--   The annealed laws on $\Sigma_n(\varepsilon)$ and $\Sigma_{n,2}(\varepsilon)$
-- statement:
--   For real $\beta$, the first law samples $\sigma\in\Sigma_n(\varepsilon)$ with probability $p(\sigma)\propto\mathbb E[\exp(\beta\mathcal H_G(\sigma))]$. The second samples $(\sigma,\sigma')$ from
--   $$\Sigma_{n,2}(\varepsilon)=\{(\sigma,\sigma')\in\Sigma_n(\varepsilon)^2:|R(\sigma,\sigma')|<\varepsilon\}$$
--   with probability $p(\sigma,\sigma')\propto\mathbb E[\exp(\beta\mathcal H_G(\sigma)+\beta\mathcal H_G(\sigma'))]$. They are the laws in Lemma 3.2 (b) and Lemma 3.9 (b).
-- source:
--   Bencs, Huang, Lee, Liu, Regts, On Zeros and Algorithms for Disordered Systems II, arXiv:2610.40598 (held version, sha256 2a07c158…), Lemma 3.2 (b), p.12, and Lemma 3.9 (b), eq. (18), p.18

import Mathlib
import Definitions.Def_AFIsingKS_Matching

open scoped Classical

namespace AFIsingKS

/-- The probability of `A` when `σ ∈ Σ_n(ε)` is sampled with `p(σ) ∝ 𝔼[exp(β H_G(σ))]`
(Bencs, Huang, Lee, Liu, Regts, arXiv:2610.40598 (held version, sha256 2a07c158…), Lemma 3.2 (b), p.12), for a real `β`. -/
noncomputable def firstMomentProb (n d : ℕ) (ε β : ℝ) (A : Spin n → Prop) : ℝ :=
  (∑ σ ∈ balanced n ε,
      if A σ then cmE (fun M : Matching n d => Real.exp (β * (cmCut M σ : ℝ))) else 0) /
    ∑ σ ∈ balanced n ε, cmE (fun M : Matching n d => Real.exp (β * (cmCut M σ : ℝ)))

/-- The probability of `A` when `(σ, σ') ∈ Σ_{n,2}(ε) = {(σ, σ') ∈ Σ_n(ε)² : |R(σ, σ')| < ε}` is
sampled with `p(σ, σ') ∝ 𝔼[exp(β H_G(σ) + β H_G(σ'))]` (Bencs, Huang, Lee, Liu, Regts, arXiv:2610.40598 (held version, sha256 2a07c158…), Lemma 3.9 (b), eq. (18), p.18), for a
real `β`. -/
noncomputable def secondMomentProb (n d : ℕ) (ε β : ℝ) (A : Spin n → Spin n → Prop) : ℝ :=
  (∑ σ ∈ balanced n ε, ∑ σ' ∈ balanced n ε,
      if |overlap σ σ'| < ε ∧ A σ σ' then
        cmE (fun M : Matching n d =>
          Real.exp (β * (cmCut M σ : ℝ) + β * (cmCut M σ' : ℝ)))
      else 0) /
    ∑ σ ∈ balanced n ε, ∑ σ' ∈ balanced n ε,
      if |overlap σ σ'| < ε then
        cmE (fun M : Matching n d =>
          Real.exp (β * (cmCut M σ : ℝ) + β * (cmCut M σ' : ℝ)))
      else 0

end AFIsingKS



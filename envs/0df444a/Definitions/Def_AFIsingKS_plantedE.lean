-- Prove2me | Definitions.Def_AFIsingKS_plantedE
-- name    : AFIsingKS_plantedE
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T10:15:08.694427+00:00
-- url     : https://prove2.me/theorems/f5601ed1-3bac-45cd-a342-b5e177126238
-- title:
--   The planted models $\nu^{\mathrm{pl}}_\beta$ and $\nu^{\mathrm{pl},2}_\beta$
-- statement:
--   For real $\beta$, the **planted model** is the probability measure on pairs $(\sigma^*,G)$, with $\sigma^*\in\Sigma_n(\varepsilon)$ and $G$ a perfect matching, given by $\nu^{\mathrm{pl}}_\beta(\sigma^*,G)\propto\exp(\beta\mathcal H_G(\sigma^*))$. The **two-replica planted model** is the measure on triples $(\sigma^*,\sigma'^*,G)$ with
--   $$\nu^{\mathrm{pl},2}_\beta(\sigma^*,\sigma'^*,G)\propto\mathbf 1\{|R(\sigma^*,\sigma'^*)|<\varepsilon\}\exp(\beta\mathcal H_G(\sigma^*)+\beta\mathcal H_G(\sigma'^*)).$$
--   The formal objects are the expectations $\mathbb E^{\mathrm{pl}}_\beta$ and $\mathbb E^{\mathrm{pl},2}_\beta$ under these measures, written as ratios of finite sums.
-- source:
--   Bencs, Huang, Lee, Liu, Regts, On Zeros and Algorithms for Disordered Systems II, arXiv:2610.40598 (held version, sha256 2a07c158…), Definition 1, p.19, and Definition 2, p.20

import Mathlib
import Definitions.Def_AFIsingKS_Matching

open scoped Classical

namespace AFIsingKS

/-- The expectation `𝔼^pl_β[f]` under the planted model `ν^pl_β(σ*, G) ∝ exp(β H_G(σ*))` on
`Σ_n(ε) ×` matchings (Bencs, Huang, Lee, Liu, Regts, arXiv:2610.40598 (held version, sha256 2a07c158…), Definition 1, p.19), for a real `β`. -/
noncomputable def plantedE (n d : ℕ) (ε β : ℝ) (f : Spin n → Matching n d → ℝ) : ℝ :=
  (∑ σs ∈ balanced n ε, ∑ M : Matching n d, Real.exp (β * (cmCut M σs : ℝ)) * f σs M) /
    ∑ σs ∈ balanced n ε, ∑ M : Matching n d, Real.exp (β * (cmCut M σs : ℝ))

/-- The expectation `𝔼^{pl,2}_β[f]` under the two-replica planted model
`ν^{pl,2}_β(σ*, σ'*, G) ∝ 1{|R(σ*, σ'*)| < ε} exp(β H_G(σ*) + β H_G(σ'*))` on
`Σ_n(ε)² ×` matchings (Bencs, Huang, Lee, Liu, Regts, arXiv:2610.40598 (held version, sha256 2a07c158…), Definition 2, p.20), for a real `β`. -/
noncomputable def plantedE2 (n d : ℕ) (ε β : ℝ) (f : Spin n → Spin n → Matching n d → ℝ) : ℝ :=
  (∑ σs ∈ balanced n ε, ∑ σs' ∈ balanced n ε, ∑ M : Matching n d,
      if |overlap σs σs'| < ε then
        Real.exp (β * (cmCut M σs : ℝ) + β * (cmCut M σs' : ℝ)) * f σs σs' M
      else 0) /
    ∑ σs ∈ balanced n ε, ∑ σs' ∈ balanced n ε, ∑ M : Matching n d,
      if |overlap σs σs'| < ε then
        Real.exp (β * (cmCut M σs : ℝ) + β * (cmCut M σs' : ℝ))
      else 0

end AFIsingKS



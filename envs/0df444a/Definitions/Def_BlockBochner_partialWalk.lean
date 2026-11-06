-- Prove2me | Definitions.Def_BlockBochner_partialWalk
-- name    : BlockBochner_partialWalk
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:37:21.963183+00:00
-- url     : https://prove2.me/theorems/574b4b40-4686-485c-82f4-46692b5379a3
-- title:
--   Partial-configuration walk $S_{\nu,0}$
-- statement:
--   $S_{\nu,0}$ acts on $\bigoplus_{i\in R}U^\nu_i$ by
--   $$(S_{\nu,0}g)_i=\frac1{k-1}\sum_{j\ne i}P^\nu_ig_j .$$
--
--   **Formalization Note** The formula is defined on the $\ell^2$ sum $\bigoplus_{i\in R}L^2(\nu)$; it maps $\bigoplus_iU^\nu_i$ into itself, and statements about $S_{\nu,0}$ quantify over $g$ with $g_i\in U^\nu_i$.
-- source:
--   Leake–Li, Beyond the Bochner Method: Optimal Spectral Gaps for Block Dynamics of Spin Systems like the O(N) Model, arXiv:2611.05228, Sec. 2.2, p.16

import Mathlib
import Definitions.Def_BlockBochner_condExpOn

open MeasureTheory

namespace BlockBochner

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {X : ι → Type*} [∀ i, MeasurableSpace (X i)]

/-- **The partial-configuration walk `S_{ν,0}`, `(S_{ν,0} g)_i = (1/(k−1)) Σ_{j≠i} P^ν_i g_j`.** Leake–Li, *Beyond the Bochner Method: Optimal Spectral Gaps for Block Dynamics of Spin Systems like the O(N) Model*, arXiv:2611.05228,
Sec. 2.2, p.16.

**Formalization Note** The formula is applied on the `ℓ²` sum `⊕_{i∈R} L²(ν)`; it maps
`⊕_i U^ν_i` into itself, and `S_{ν,0}` is its restriction there. Statements about `S_{ν,0}`
quantify over `g` with `g_i ∈ U^ν_i`. -/
noncomputable def partialWalk (ν : Measure (∀ i, X i)) :
    PiLp 2 (fun _ : ι => Lp ℝ 2 ν) →L[ℝ] PiLp 2 (fun _ : ι => Lp ℝ 2 ν) :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : ι => Lp ℝ 2 ν)).symm.toContinuousLinearMap ∘L
    ContinuousLinearMap.pi (fun i => ((Fintype.card ι : ℝ) - 1)⁻¹ •
      ∑ j ∈ Finset.univ.erase i,
        condExpOn ν {i}ᶜ ∘L PiLp.proj (𝕜 := ℝ) 2 (fun _ : ι => Lp ℝ 2 ν) j)

end BlockBochner



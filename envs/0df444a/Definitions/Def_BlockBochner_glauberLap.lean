-- Prove2me | Definitions.Def_BlockBochner_glauberLap
-- name    : BlockBochner_glauberLap
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:38:44.447447+00:00
-- url     : https://prove2.me/theorems/72fecea7-d61d-4c36-86d6-ca17f1ca4fe5
-- title:
--   Glauber Laplacian $L_{\mathrm{Glaub}}=\frac1{|V|}\sum_v L_v$
-- statement:
--   For a measure $\nu$ on $\prod_{v\in V}X_v$ with finitely many sites, the Glauber dynamics picks a uniformly random site and resamples its spin from the conditional law given the others. Its transition operator is $P_{\mathrm{Glaub}}=\frac1{|V|}\sum_vE_v$ and its Laplacian is
--   $$L_{\mathrm{Glaub}}=I-P_{\mathrm{Glaub}}=\frac1{|V|}\sum_{v\in V}L_v .$$
--
--   Applied to a pinned law $\mu^\tau$ on the sites of $R$ it gives the link Laplacian $L^\tau_{\mathrm{Glaub}}=L_{\mathrm{Glaub},\nu}=\frac1k\sum_{i\in R}L^\nu_i$.
-- source:
--   Leake–Li, Beyond the Bochner Method: Optimal Spectral Gaps for Block Dynamics of Spin Systems like the O(N) Model, arXiv:2611.05228, Sec. 1.6, p.8; Sec. 2.2, p.16

import Mathlib
import Definitions.Def_BlockBochner_siteLap

open MeasureTheory

namespace BlockBochner

/-- **Glauber Laplacian `L_Glaub = (1/|V|) Σ_v L_v`.** Leake–Li, *Beyond the Bochner Method: Optimal Spectral Gaps for Block Dynamics of Spin Systems like the O(N) Model*, arXiv:2611.05228, Sec. 1.6, p.8 (`P_Glaub = (1/|V|) Σ_v E_v`,
`L_Glaub = I − P_Glaub = (1/|V|) Σ_v L_v`) and Sec. 2.2, p.16 (`L_Glaub,ν = (1/k) Σ_{i∈R} L^ν_i`).

**Formalization Note** The site set is the finite index type `ι`; applied to a pinned law
`linkLaw µ R τ` on the sites of `R` this is the Glauber Laplacian `L^τ_Glaub` of the pinning. -/
noncomputable def glauberLap {ι : Type*} [Fintype ι] {X : ι → Type*} [∀ i, MeasurableSpace (X i)]
    (ν : Measure (∀ i, X i)) : Lp ℝ 2 ν →L[ℝ] Lp ℝ 2 ν :=
  (Fintype.card ι : ℝ)⁻¹ • ∑ i, siteLap ν i

end BlockBochner



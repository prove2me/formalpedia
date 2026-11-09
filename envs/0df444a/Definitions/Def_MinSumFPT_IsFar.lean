-- Prove2me | Definitions.Def_MinSumFPT_IsFar
-- name    : MinSumFPT_IsFar
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T17:16:40.319404+00:00
-- url     : https://prove2.me/theorems/d5b80406-effe-4c52-8a2c-123d4fbcca01
-- title:
--   Definition 4: $\beta^{-1}$-far and close points
-- statement:
--   Given $\varepsilon,\alpha,\gamma$, an estimate $\widehat{\mathrm{OPT}}$ and, for a cluster $C$, an approximate center $\hat\mu_C\in A$ and estimates $\widehat{|C|},\widehat{\Delta}_C$, put
--
--   $$
--   T_C=\frac{\varepsilon(1+\gamma)^2}{4\alpha}\cdot\frac{\widehat{\mathrm{OPT}}}{k\,\widehat{|C|}^{\,2}}+\alpha\cdot\widehat{\Delta}_C .
--   $$
--
--   For a scale $s>0$, a point $p$ is **$s$-far** for $C$ if $\|e_p-e_{\hat\mu_C}\|_{W_1}\ge s\cdot T_C$, and **$s$-close** otherwise. Definition 4 is the case $s=\beta^{-1}$; the algorithm uses the scales $\beta^{-2}$, $\beta^{-7}$, $\gamma^{-1}$ and $\beta^{-2}(1+\gamma)^j$. With $\alpha=5$, $T_C$ is the threshold $\widehat{\widehat{\Delta}}_C$ of (13).
--
--   These thresholds sort the points around each approximate center into close, middle and far rings, and the Stage 2 analysis is organized by those rings.
--
--   **Formalization Note** The approximate center is a point of $A$, so $\|e_p-\hat\mu_C\|_{W_1}$ is the transportation norm of $e_p-e_{\hat\mu_C}$, which equals $d(p,\hat\mu_C)$.
-- source:
--   Karthik C. S.–Lee–Rabani–Schwiegelshohn–Zhou, A Fixed Parameter Sublinear Time Approximation Scheme for Metric Min-Sum Clustering, arXiv:2610.15148 (held version of November 2, 2026, sha256 12e81235…), Definition 4, Eq. (5), p.10; Eq. (13), p.19

import Mathlib
import Definitions.Def_PerturbedWF_transNorm
import Definitions.Def_MinSumFPT_Delta

namespace MinSumFPT

/-!
# Definition 4: β⁻¹-far and β⁻¹-close points; the threshold Δ̂̂_C of (13)

Karthik C. S.–Lee–Rabani–Schwiegelshohn–Zhou, *A Fixed Parameter Sublinear Time Approximation
Scheme for Metric Min-Sum Clustering*, arXiv:2610.15148 (held version of November 2, 2026, sha256
12e81235…), Definition 4, Eq. (5), p.10, and Eq. (13), p.19.

This module bundles `farThreshold` (the bracket of (5); with α = 5 it is Δ̂̂_C of (13)) and `IsFar`.

**Formalization Note.** The approximate center µ̂_C is a point `µ` of `A` (Stage 1 outputs points),
so ‖e_p − µ̂_C‖_{W₁} is `transNorm d (e_p − e_mu)`. `|Ĉ|` is a real `c`; the statements have
`c ≥ |C| ≥ 1`. The scale `s` (the paper's β⁻¹, also β⁻², β⁻⁷, γ⁻¹, β⁻²(1+γ)^j) is a real
parameter; "p is s-close" is `¬ IsFar … s …`. -/

/-- The bracket of (5): `(ε(1+γ)²/(4α)) ⋅ ÔPT/(k ⋅ |Ĉ|²) + α ⋅ Δ̂`. With `α = 5` this is the
`Δ̂̂_C` of (13). -/
noncomputable def farThreshold (k : ℕ) (ε α γ optHat c Δhat : ℝ) : ℝ :=
  ε * (1 + γ) ^ 2 / (4 * α) * (optHat / (k * c ^ 2)) + α * Δhat

/-- Definition 4 with scale `s` (the paper's `β⁻¹`): `p` is `s`-far for the cluster with
approximate center `mu`, size estimate `c` and cost estimate `Δ̂` iff
`‖e_p − e_µ‖_{W₁} ≥ s ⋅ farThreshold`. -/
def IsFar {n : ℕ} (d : Fin n → Fin n → ℝ) (k : ℕ) (ε α γ optHat : ℝ) (s : ℝ) (mu : Fin n)
    (c Δhat : ℝ) (p : Fin n) : Prop :=
  s * farThreshold k ε α γ optHat c Δhat ≤ PerturbedWF.transNorm d (unitVec p - unitVec mu)

end MinSumFPT



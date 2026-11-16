-- Prove2me | Definitions.Def_MetricMinTest_Supplement_singleCoverInf
-- name    : MetricMinTest_Supplement_singleCoverInf
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T02:33:14.681216+00:00
-- url     : https://prove2.me/theorems/9edecc8e-b627-4e7b-80d3-857fa3dac06a
-- title:
--   Best single-cover screening expression $\inf_{(Z,r)}H_{Z,r}(\lambda+\ln\rho_{Z,r})$
-- statement:
--   For $\lambda\in\mathbb R$ let
--   $$\Sigma_d(\gamma,\lambda)=\inf\big\{H_{Z,r}(\lambda+\ln\rho_{Z,r})\ :\ r\in[0,\gamma),\ Z\ne\emptyset,\ S(Z,r)=[k]\big\},$$
--   the infimum over all whole-space screening covers. With $\lambda=1$ this is the **best single-cover screening expression** of (7.2), Theorem E and Theorem 7.7; with $\lambda=\ln(1/\delta)$ it is the confidence-$\delta$ form used in the proof of Theorem 7.7.
--
--   **Formalization Note** A real infimum; the radius ranges over all reals in $[0,\gamma)$, not only occurring distances.
-- source:
--   Chen–Fang, Minimum-Mean Testing under Metric Constraints: Shared Information, Certificates, and Adaptivity, STOC 2027 submission (manuscript sha256 dcece1939edb1fcf752ab6152794f04d8762928ada557c99626997db01ad32bb), (7.2), p.16; Theorem 7.7 and its proof, pp.19–20

import Mathlib
import Definitions.Def_MetricMinTest_IsRCover
import Definitions.Def_MetricMinTest_regionRatio

namespace MetricMinTest.Supplement

/-- **Best single-cover screening expression** `inf_{(Z,r) : S(Z,r)=[k]} H_{Z,r}(λ + ln ρ_{Z,r})`.
Chen–Fang, *Minimum-Mean Testing under Metric Constraints*, STOC 2027 submission (manuscript sha256 dcece193…ad32bb), (7.2) p.16 and Theorem 7.7 p.19 (with `λ = 1`), and the proof of Theorem 7.7, p.20 ("The
same comparison applies to H_{Z,r}(ln(1/δ) + ln ρ_{Z,r})", `λ = ln(1/δ)`).

**Formalization Note.** A real `sInf` over all `r`-covers `Z` (`IsRCover`: `Z` nonempty and
`S(Z, r)` is the whole space) with any real `r ∈ [0, γ)` (not only occurring distances, as in
(7.2)). For a pseudometric the set is nonempty (`Z` everything, `r = 0`). -/
noncomputable def singleCoverInf {ι : Type} [Fintype ι] (d : ι → ι → ℝ) (γ lam : ℝ) : ℝ :=
  sInf {x : ℝ | ∃ (Z : Finset ι) (r : ℝ), 0 ≤ r ∧ r < γ ∧ IsRCover d Z r ∧
    x = regionWorkload d γ Z r * (lam + Real.log (regionRatio d γ Z r))}

end MetricMinTest.Supplement



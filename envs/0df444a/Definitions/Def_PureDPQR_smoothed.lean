-- Prove2me | Definitions.Def_PureDPQR_smoothed
-- name    : PureDPQR_smoothed
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T07:58:44.112343+00:00
-- url     : https://prove2.me/theorems/534670ba-de6d-4114-9d61-f893366b7723
-- title:
--   Sparse Laplace perturbation (4.2) and the smoothed law $Q_v(y)=\mathbb E_Z[p_{v+Z}(y)]$ (4.3)
-- statement:
--   For $\pi\in(0,1)$ and $\kappa>0$ let $\mathrm{Lap}(\kappa)$ be the centred Laplace law with **rate** $\kappa$, density $\frac\kappa2e^{-\kappa|z|}$. The **sparse Laplace perturbation** $Z=(Z_1,\dots,Z_d)$ has independent coordinates
--
--   $$Z_j\sim(1-\pi)\,\delta_0+\pi\,\mathrm{Lap}(\kappa),\qquad j\in[d],$$
--
--   i.e. each coordinate is perturbed with probability $\pi$ only. For a family of laws $p_v$ on a set $Y$, indexed by $v\in\mathbb R^d$, the **smoothed law** is
--
--   $$Q_v(y)=\mathbb E_Z\big[p_{v+Z}(y)\big].$$
--
--   This is the input-smoothed procedure (Procedure 3) of Lemma 14 and the transcript law of Algorithm 2.
--
--   **Formalization Note** The published `PrivLearn.Generic.laplace s` has scale $s$, so $\mathrm{Lap}(\kappa)$ is `laplace κ⁻¹`. $\pi$ is written `pert`. The expectation is a Bochner integral; for the bounded continuous families of this mission the integrand is integrable.
-- source:
--   Zou, Pure Differentially Private Query Release via Laplace Input Smoothing, arXiv:2611.04721 (held version, sha256 69b70d59…), §3, p.13 (PDF p.14); (4.2)–(4.3), p.15 (PDF p.16); Procedure 3, p.16 (PDF p.17)

import Mathlib
import Definitions.Def_PrivLearn_Generic_Privacy

open MeasureTheory

namespace PureDPQR

/-!
# The sparse Laplace input perturbation and the smoothed law `Q_v`

Z. Zou, *Pure Differentially Private Query Release via Laplace Input Smoothing*, arXiv:2611.04721
(held version, sha256 69b70d59…), §3, p.13 (Lap(κ)); §4, (4.2) and (4.3), p.15 (PDF p.16);
Procedure 3, p.16 (PDF p.17).

**Formalization Note.**
* The paper's `Lap(κ)` has **rate** `κ` (density `(κ/2)e^{−κ|z|}`, scale `1/κ`, p.13). The published
  `PrivLearn.Generic.laplace s` has **scale** `s` (density `e^{−|x|/s}/(2s)`), so `Lap(κ)` is
  `PrivLearn.Generic.laplace κ⁻¹`.
* The perturbation probability `π` of (4.2) is written `pert` (to avoid confusion with `Real.pi`).
  The mixture weights enter through `Real.toNNReal`, which equals `1 − π` and `π` for `π ∈ (0,1)`,
  the range of every use.
* `smoothed p pert κ v y = E_Z[p_{v+Z}(y)]` is a Bochner integral. It is generic in the family
  `p : ℝ^d → Y → ℝ`; for the bounded continuous families of this mission the integrand is
  integrable, so Lean's convention `∫ = 0` for non-integrable functions never applies.
-/

/-- The law of one coordinate of the perturbation (4.2): `(1 − π) δ₀ + π Lap(κ)`. -/
noncomputable def coordLaw (pert κ : ℝ) : Measure ℝ :=
  Real.toNNReal (1 - pert) • Measure.dirac 0 +
    Real.toNNReal pert • PrivLearn.Generic.laplace κ⁻¹

instance (pert κ : ℝ) : SigmaFinite (coordLaw pert κ) := by
  unfold coordLaw PrivLearn.Generic.laplace; infer_instance

/-- The sparse Laplace perturbation `Z = (Z_1, …, Z_d)` of (4.2) and Procedure 3: independent
coordinates `Z_j ∼ (1 − π) δ₀ + π Lap(κ)`. -/
noncomputable def sparseLaplace (d : ℕ) (pert κ : ℝ) : Measure (Fin d → ℝ) :=
  Measure.pi fun _ => coordLaw pert κ

/-- The smoothed transcript law (4.3): `Q_v(y) := E_Z[p_{v+Z}(y)]`, `Z ∼ sparseLaplace d π κ`. -/
noncomputable def smoothed {d : ℕ} {Y : Type*} (p : (Fin d → ℝ) → Y → ℝ) (pert κ : ℝ)
    (v : Fin d → ℝ) (y : Y) : ℝ :=
  ∫ z, p (v + z) y ∂ sparseLaplace d pert κ

end PureDPQR



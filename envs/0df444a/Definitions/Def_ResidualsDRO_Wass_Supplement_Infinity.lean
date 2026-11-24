-- Prove2me | Definitions.Def_ResidualsDRO_Wass_Supplement_Infinity
-- name    : ResidualsDRO_Wass_Supplement_Infinity
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-24T02:34:51.428385+00:00
-- url     : https://prove2.me/theorems/dae4eacf-b0b9-4b8b-917b-c83556076f10
-- title:
--   Notation p. 6 and (13) — infinity-Wasserstein distance and scalar counterexample
-- statement:
--   The infinity-Wasserstein distance is the smallest essential maximum transport distance among couplings:
--
--   $$d_{W,\infty}(Q,R)=\inf_{\pi\in\Pi(Q,R)}\operatorname*{ess\,sup}_{\pi}\|y-y'\|.$$
--
--   It takes values in [0,∞], with infinity for an empty coupling family. The file records the quoted Lemma 19 bound as a predicate, without assuming it in the counterexample. It also defines the sample-robust radius (13). For the scalar uniform-response instance with exact regression, θ=3/4 and κ_n(α)=n^{-2}, the radius and exact robust value are
--
--   $$\mu_n=2n^{-2}+Cn^{-3/4},\qquad \widehat v_n=\frac1n\sum_{i=1}^n\min\{1,U_i+\mu_n\}.$$
--
--   Here U_i∈[0,1] and C>0. These explicit quantities exhibit the dimension-one failure of Theorem 21; see DISPROOF.md. No arbitrary objective or failed-certificate premise is introduced.
--
--   Differences from the source:
--
--   - encoding: infinity-Wasserstein distance for probability laws and radius (13) → the coupling-infimum formula is defined on measures in general; the Lemma19 formula is only a predicate, and the scalar radius/value explicitly specialize (13) and (8); reason: the formula agrees on probability laws; no invalid concentration bound is assumed, and the counterexample uses positive sample sizes and valid scalar responses
-- source:
--   Kannan, Bayraksan & Luedtke, Residuals-based distributionally robust optimization with covariate information, Mathematical Programming (2023), accepted manuscript, https://doi.org/10.1007/s10107-023-02014-7, pp. 6, 26–27

import Mathlib
import Definitions.Def_ResidualsDRO_Wass_Supplement_Assumptions

open MeasureTheory Filter
open scoped ENNReal Topology

namespace ResidualsDRO.Wass.Supplement

variable {dx dy dz : ℕ} {Ω : Type*} [MeasurableSpace Ω]

/-- Notation p. 6: infimum over couplings of the essential supremum of distance.
The constrained infimum and essential supremum take values in [0,∞]. -/
noncomputable def winfty {d : ℕ} (Q R : Measure (E d)) : ℝ≥0∞ :=
  ⨅ (π : Measure (E d × E d)) (_ : π.map Prod.fst = Q ∧ π.map Prod.snd = R),
    essSup (fun y : E d × E d => edist y.1 y.2) π

/-- The printed Lemma 19 bound at β=4, recorded only as a predicate.
It is false in dimension one, as the scalar instance below diagnoses. The
counterexample to Theorem 21 does not assume this predicate. -/
def L19 (M : Model dx dy dz Ω) (P : Measure Ω) (x : E dx) (C₁ C₂ : ℝ) : Prop :=
  0 < C₁ ∧ 0 < C₂ ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n → 1 ≤ n →
    P {ω | ENNReal.ofReal (C₁ * Real.log n / (n : ℝ) ^ (1 / (dy : ℝ))) ≤
      winfty (Pstar M x n ω) (law M x)} ≤ ENNReal.ofReal (C₂ * (n : ℝ) ^ (-(2 : ℝ)))

/-- The sample-robust radius (13); its probability set is exactly the singleton
uniform distribution. The counterexample refutes even the version of Theorem 21
with a sample-path-dependent eventual time. -/
noncomputable def sampleRadius (κ : ℕ → ℝ → ℝ) (α : ℕ → ℝ)
    (Cbar θ : ℝ) (dy n : ℕ) : ℝ := 2 * κ n (α n) + Cbar * (n : ℝ) ^ (-θ / (dy : ℝ))

def uniformSet (_x : E dx) (n : ℕ) : Set (Fin n → ℝ) :=
  {fun _ => (n : ℝ)⁻¹}

/-- Scalar instance of (13): θ=3/4, dy=1, κ_n(α)=n⁻², exact regression.
Any positive C gives the failure in Theorem 21's asserted conclusion. -/
noncomputable def counterRadius (C : ℝ) (n : ℕ) : ℝ :=
  2 * (n : ℝ) ^ (-(2 : ℝ)) + C * (n : ℝ) ^ (-(3 : ℝ) / 4)

/-- The genuine sample-robust objective on Y=[0,1], c(z,y)=y, Z a singleton:
(1/n)∑ min(1, Y_i+μ), since the maximum of y in its clipped μ-ball is min(1,Y_i+μ).
This definition is used only with n≥1 and samples in [0,1]. -/
noncomputable def uniformRobustValue {n : ℕ} (μ : ℝ) (U : Fin n → ℝ) : ℝ :=
  (n : ℝ)⁻¹ * ∑ i, min 1 (U i + μ)

end ResidualsDRO.Wass.Supplement



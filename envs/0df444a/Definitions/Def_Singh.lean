-- Prove2me | Definitions.Def_Singh
-- name    : Singh
-- status  : Definition
-- author  : @Hix_Lab
-- created : 2026-11-04T06:03:23.825281+00:00
-- url     : https://prove2.me/theorems/c22f8d8f-4f20-41c7-9caf-6414c198f7a3
-- title:
--   Singh Theorem: CUE Palm variance and Hua ensemble definitions
-- statement:
--   Definitions for the Singh Theorem: the conditional (Palm) variance $V_N(s)$ (`cueV`) of $\log|\Lambda'(\theta_1)| - \log|\Lambda'(\theta_2)|$ for an adjacent eigenangle pair of a Haar unitary at normalized gap $s$, the circle weight average $E_{w_0}[S^2]$ (`circleE`), and the Hua ensemble $P_{n,2}$ (`huaMeasure`).
-- source:
--   J. Singh, https://github.com/jjsingh88/singh-constant (commit 792d985)

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis



/-!
# Singh Theorem: definitions

Shared definitions; `Challenge.lean` restates this text verbatim.
-/

open MeasureTheory Finset Real Filter Topology
open scoped ENNReal NNReal

namespace Singh

variable {n : ℕ}

/-- Ordered pairs `a < b`. -/
def pairs (n : ℕ) : Finset (Fin n × Fin n) := univ.filter fun p => p.1 < p.2

/-- `fL x = log|sin(x/2)|`; `log|e^{iφ}-e^{iψ}| = log 2 + fL(φ-ψ)`. -/
noncomputable def fL (x : ℝ) : ℝ := Real.log (sin (x / 2))

/-- `log|Λ'(θ₁)| - log|Λ'(θ₂)|` for eigenangles `θ₁ = -δ/2`, `θ₂ = δ/2` and the remaining
angles `θ`: the common factor `|e^{iθ₁}-e^{iθ₂}|` cancels. -/
noncomputable def Xd (δ : ℝ) (θ : Fin n → ℝ) : ℝ := ∑ k, (fL (θ k + δ / 2) - fL (θ k - δ / 2))

/-- Adjacency: no remaining angle lies in the arc `(-δ/2, δ/2)`. -/
noncomputable def boxD (n : ℕ) (δ : ℝ) : Set (Fin n → ℝ) :=
  Set.pi Set.univ fun _ => Set.Ioo (δ / 2) (2 * π - δ / 2)

/-- Weyl density of the remaining angles given eigenangles at `±δ/2`, before restriction:
`∏_{a<b} |e^{iθ_a}-e^{iθ_b}|^2 ∏_k |e^{iθ_k}-e^{-iδ/2}|^2 |e^{iθ_k}-e^{iδ/2}|^2`
up to a constant factor. -/
noncomputable def pwRaw (δ : ℝ) (θ : Fin n → ℝ) : ℝ :=
  (∏ p ∈ pairs n, sin ((θ p.1 - θ p.2) / 2) ^ 2)
    * ∏ k, (sin ((θ k - δ / 2) / 2) ^ 2 * sin ((θ k + δ / 2) / 2) ^ 2)

/-- Conditional (Palm) weight of the remaining angles for an adjacent pair at gap `δ`. -/
noncomputable def pw (δ : ℝ) (θ : Fin n → ℝ) : ℝ := (boxD n δ).indicator (pwRaw δ) θ

/-- Conditional variance of `Xd δ` under the Palm weight. -/
noncomputable def palmVar (n : ℕ) (δ : ℝ) : ℝ :=
  (∫ θ : Fin n → ℝ, Xd δ θ ^ 2 * pw δ θ) / (∫ θ : Fin n → ℝ, pw δ θ)
    - ((∫ θ : Fin n → ℝ, Xd δ θ * pw δ θ) / (∫ θ : Fin n → ℝ, pw δ θ)) ^ 2

/-- `V s = Var(log|Λ'(θ₁)| - log|Λ'(θ₂)| | s)` for an adjacent pair at normalized gap `s`,
under the Weyl density of the remaining `N-2` eigenangles. -/
noncomputable def cueV (N : ℕ) (s : ℝ) : ℝ := palmVar (N - 2) (2 * Real.pi / N * s)

/-- `∏_k ∏_{j≠k} |u_k - u_j| = ∏_{j<k} (u_j-u_k)^2`. -/
noncomputable def vdm (u : Fin n → ℝ) : ℝ := ∏ k, ∏ j ∈ univ.erase k, |u k - u j|

/-- `G(u) = ∏_k (1+u_k^2)`. -/
noncomputable def bigG (u : Fin n → ℝ) : ℝ := ∏ k, (1 + u k ^ 2)

/-- Unnormalized Hua weight with `h = 2`. -/
noncomputable def huaWeight (u : Fin n → ℝ) : ℝ := vdm u / bigG u ^ (n + 2)

/-- Normalizing constant. -/
noncomputable def huaZ (n : ℕ) : ℝ := ∫ u : Fin n → ℝ, huaWeight u

/-- Normalized Hua density. -/
noncomputable def huaDensity (u : Fin n → ℝ) : ℝ≥0 :=
  (huaWeight u / huaZ n).toNNReal

/-- The Hua ensemble `P_{n,2}` as a measure on `ℝ^n`. -/
noncomputable def huaMeasure (n : ℕ) : Measure (Fin n → ℝ) :=
  volume.withDensity fun u => (huaDensity u : ℝ≥0∞)

/-- The open box `(0, 2π)^n`. -/
noncomputable def boxC (n : ℕ) : Set (Fin n → ℝ) := Set.pi Set.univ fun _ => Set.Ioo 0 (2 * π)

/-- Circle weight `∏_{a<b} sin^2((θ_a-θ_b)/2) ∏_k sin^4(θ_k/2)`, proportional to
`∏_{a<b} |e^{iθ_a}-e^{iθ_b}|^2 ∏_k |1-e^{iθ_k}|^4`. -/
noncomputable def wC (θ : Fin n → ℝ) : ℝ :=
  (∏ p ∈ pairs n, sin ((θ p.1 - θ p.2) / 2) ^ 2) * ∏ k, sin (θ k / 2) ^ 4

/-- `S = (1/2) ∑_k cot(θ_k/2)`. -/
noncomputable def Ssum (θ : Fin n → ℝ) : ℝ := (1 / 2) * ∑ k, cos (θ k / 2) / sin (θ k / 2)

/-- `E_{w₀}[S^2]` for the circle weight on `n` angles. -/
noncomputable def circleE (n : ℕ) : ℝ :=
  (∫ θ in boxC n, Ssum θ ^ 2 * wC θ) / ∫ θ in boxC n, wC θ

end Singh



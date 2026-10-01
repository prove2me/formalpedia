-- Prove2me | Definitions.Def_PolyakovAction_Defs
-- name    : PolyakovAction_Defs
-- status  : Definition
-- author  : @Lucas
-- created : 2026-10-01T03:25:21.18636+00:00
-- url     : https://prove2.me/theorems/4b6c9115-15c9-43c5-b01a-21abe56fac47
-- title:
--   Polyakov action: worldsheet, induced metric, Polyakov and Nambu–Goto actions, stress–energy tensor
-- statement:
--   Shared definitions for the Polyakov-action mission (namespace `PolyakovAction`). Worldsheet points are $\sigma=(\sigma^0,\sigma^1)=(\tau,\sigma)\in\mathbb R^2$ and target points $X\in\mathbb R^D$.
--
--   1. **Partial derivatives.** $\partial_a X^\mu(\sigma)$ and $\partial_a\partial_b X^\mu(\sigma)$, computed from the Fréchet derivative of $X:\mathbb R^2\to\mathbb R^D$.
--   2. **Induced metric.** $G_{ab}(\sigma)=g_{\mu\nu}(X(\sigma))\,\partial_aX^\mu(\sigma)\,\partial_bX^\nu(\sigma)$ for a target metric $g:\mathbb R^D\to\mathbb R^{D\times D}$.
--   3. **Polyakov action.** For a worldsheet metric $h_{ab}(\sigma)$ with inverse $h^{ab}$ and determinant $h=\det(h_{ab})$, and string tension $T$,
--   $$S=\frac T2\int_U d^2\sigma\,\sqrt{-h}\,h^{ab}g_{\mu\nu}(X)\,\partial_aX^\mu\,\partial_bX^\nu .$$
--   4. **Nambu–Goto action.** $S_{NG}=T\int_U d^2\sigma\,\sqrt{-G}$, $G=\det(G_{ab})$.
--   5. **Stress–energy tensor.** $T_{ab}=T\big(G_{ab}-\tfrac12h_{ab}h^{cd}G_{cd}\big)$.
--   6. **Minkowski metric.** $\eta=\mathrm{diag}(+1,-1,\dots,-1)$ (timelike $+$, spacelike $-$, as in the source).
--
--   These are the objects in terms of which every statement of the mission is phrased.
--
--   **Formalization Note.** Indices are `Fin 2` / `Fin D`; $h^{ab}$ is Mathlib's matrix inverse (zero for a singular matrix); $\sqrt{\cdot}$ is `Real.sqrt` (zero on negative inputs); integrals are Bochner integrals for Lebesgue measure on $\mathbb R^2$ restricted to $U$.
-- source:
--   Wikipedia, "Polyakov action", revision oldid=1292212311 (https://en.wikipedia.org/w/index.php?title=Polyakov_action&oldid=1292212311), lead section and sections "Relation with Nambu–Goto action", "Equations of motion"

import Mathlib

namespace PolyakovAction

open MeasureTheory

/-- Worldsheet coordinates `σ = (σ 0, σ 1) = (τ, σ)`: index `0` is the timelike
coordinate `τ`, index `1` the spacelike coordinate `σ`. -/
abbrev Worldsheet := Fin 2 → ℝ

/-- The `D`-dimensional target manifold (coordinates `X^μ`). -/
abbrev Spacetime (D : ℕ) := Fin D → ℝ

/-- `∂_a X^μ (σ)`: partial derivative of the `μ`-th component of the embedding
`X` with respect to the worldsheet coordinate `σ^a`. -/
noncomputable def partialDeriv {D : ℕ} (X : Worldsheet → Spacetime D) (a : Fin 2)
    (μ : Fin D) (σ : Worldsheet) : ℝ :=
  fderiv ℝ X σ (Pi.single a 1) μ

/-- `∂_a ∂_b X^μ (σ)`: second partial derivative of the `μ`-th component of `X`. -/
noncomputable def secondPartialDeriv {D : ℕ} (X : Worldsheet → Spacetime D) (a b : Fin 2)
    (μ : Fin D) (σ : Worldsheet) : ℝ :=
  fderiv ℝ (fun σ' => fderiv ℝ X σ' (Pi.single b 1)) σ (Pi.single a 1) μ

/-- Induced (pull-back) metric `G_ab = g_μν(X) ∂_a X^μ ∂_b X^ν`. -/
noncomputable def inducedMetric {D : ℕ} (g : Spacetime D → Matrix (Fin D) (Fin D) ℝ)
    (X : Worldsheet → Spacetime D) (σ : Worldsheet) : Matrix (Fin 2) (Fin 2) ℝ :=
  Matrix.of fun a b => ∑ μ, ∑ ν, g (X σ) μ ν * partialDeriv X a μ σ * partialDeriv X b ν σ

/-- Polyakov Lagrangian density `√(-h) h^{ab} g_μν(X) ∂_a X^μ ∂_b X^ν`, where
`h = det (h_ab)` and `h^{ab}` is the inverse of the worldsheet metric `h_ab`. -/
noncomputable def polyakovLagrangian {D : ℕ} (g : Spacetime D → Matrix (Fin D) (Fin D) ℝ)
    (h : Worldsheet → Matrix (Fin 2) (Fin 2) ℝ) (X : Worldsheet → Spacetime D)
    (σ : Worldsheet) : ℝ :=
  Real.sqrt (-(h σ).det) * ∑ a, ∑ b, (h σ)⁻¹ a b * inducedMetric g X σ a b

/-- Polyakov action over a worldsheet region `U`:
`S = (T/2) ∫_U d²σ √(-h) h^{ab} g_μν(X) ∂_a X^μ ∂_b X^ν`. -/
noncomputable def polyakovAction {D : ℕ} (T : ℝ) (g : Spacetime D → Matrix (Fin D) (Fin D) ℝ)
    (h : Worldsheet → Matrix (Fin 2) (Fin 2) ℝ) (X : Worldsheet → Spacetime D)
    (U : Set Worldsheet) : ℝ :=
  T / 2 * ∫ σ in U, polyakovLagrangian g h X σ

/-- Nambu–Goto action over a worldsheet region `U`: `S = T ∫_U d²σ √(-G)`, `G = det G_ab`. -/
noncomputable def nambuGotoAction {D : ℕ} (T : ℝ) (g : Spacetime D → Matrix (Fin D) (Fin D) ℝ)
    (X : Worldsheet → Spacetime D) (U : Set Worldsheet) : ℝ :=
  T * ∫ σ in U, Real.sqrt (-(inducedMetric g X σ).det)

/-- Stress–energy tensor (lower indices) `T_ab = T (G_ab - ½ h_ab h^{cd} G_cd)`. -/
noncomputable def stressEnergyTensor {D : ℕ} (T : ℝ)
    (g : Spacetime D → Matrix (Fin D) (Fin D) ℝ) (h : Worldsheet → Matrix (Fin 2) (Fin 2) ℝ)
    (X : Worldsheet → Spacetime D) (σ : Worldsheet) : Matrix (Fin 2) (Fin 2) ℝ :=
  Matrix.of fun a b => T * (inducedMetric g X σ a b
    - 1 / 2 * h σ a b * ∑ c, ∑ d, (h σ)⁻¹ c d * inducedMetric g X σ c d)

/-- Minkowski metric `diag(+1, -1, …, -1)` on `ℝⁿ` (timelike `+`, spacelike `-`). -/
def minkowskiMetric (n : ℕ) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.diagonal fun i => if i.val = 0 then 1 else -1

end PolyakovAction



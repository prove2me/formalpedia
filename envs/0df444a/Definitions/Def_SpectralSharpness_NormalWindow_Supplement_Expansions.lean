-- Prove2me | Definitions.Def_SpectralSharpness_NormalWindow_Supplement_Expansions
-- name    : SpectralSharpness_NormalWindow_Supplement_Expansions
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T06:04:08.591589+00:00
-- url     : https://prove2.me/theorems/58bc0e32-f7fe-433c-8a88-dc1459a50f32
-- title:
--   Bounded orthonormal expansions and representative-dependent oscillation
-- statement:
--   Let μ be a measure on X. A bounded basis consists of measurable representatives φ_j, j≥0, whose L² classes are orthonormal and have dense linear span, with one finite uniform bound on their essential supremum norms. Real and complex scalar fields are supported. There is no continuity assumption on the basis and no full-support assumption on μ.
--
--   Set B_j=‖φ_j‖∞, ĝ_j=∫g conjugate(φ_j)dμ and g_d=∑_{j≤d}ĝ_jφ_j. The weighted absolute coefficient is |ĝ_j|B_j.
--
--   The printed oscillation is represented literally as
--   $$
--   \operatorname{osc}(g)=\sup_x\operatorname*{ess\,limsup}_{y\to x}|g(y)-g(x)|.
--   $$
--   It uses the neighborhood filter intersected with the almost-everywhere filter, and may change when g changes at a null point. The minimax quantity takes an extended-real supremum over bounded targets with oscillation at least δ, then an infimum over the actual finite basis span. This permits an infinite supremum and avoids a real-supremum default value.
-- source:
--   Wenwei Li, The Spectral Cost of Sharpness: Fourier Truncation, the Gibbs Bend, and the Computability of Classification, 2026 manuscript, STOC 2027 submission #122, SHA-256 0c0e3d52a54d9fbebc999feaa9b26703db76a5586d3c43db2ed20b17c15a9100, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/122.pdf, §3.1, p. 9

import Mathlib
import Definitions.Def_SpectralSharpness_NormalWindow_Supplement_Fourier

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

noncomputable section

namespace SpectralSharpness.NormalWindow.Supplement

/-- Measurable representatives of a complete real or complex orthonormal system. No continuity
or full-support assumption is included. -/
structure BoundedBasis (𝕜 X : Type*) [RCLike 𝕜] [MeasurableSpace X] (μ : Measure X) where
  φ : ℕ → X → 𝕜
  measurable : ∀ j, Measurable (φ j)
  memLp : ∀ j, MemLp (φ j) 2 μ
  orthonormal : Orthonormal 𝕜 (fun j => (memLp j).toLp (φ j))
  complete : Submodule.topologicalClosure
    (Submodule.span 𝕜 (Set.range (fun j => (memLp j).toLp (φ j)))) = ⊤
  bounded : ∃ B : ℝ, ∀ j, eLpNorm (φ j) ⊤ μ ≤ ENNReal.ofReal B

def basisBound {𝕜 X : Type*} [RCLike 𝕜] [MeasurableSpace X] {μ : Measure X}
    (b : BoundedBasis 𝕜 X μ) (j : ℕ) : ℝ := (eLpNorm (b.φ j) ⊤ μ).toReal
def coefficient {𝕜 X : Type*} [RCLike 𝕜] [MeasurableSpace X] {μ : Measure X}
    (b : BoundedBasis 𝕜 X μ) (g : X → 𝕜) (j : ℕ) : 𝕜 := ∫ x, star (b.φ j x)*g x ∂μ
def partialExpansion {𝕜 X : Type*} [RCLike 𝕜] [MeasurableSpace X] {μ : Measure X}
    (b : BoundedBasis 𝕜 X μ) (g : X → 𝕜) (d : ℕ) (x : X) : 𝕜 :=
  ∑ j ∈ Finset.range (d+1), coefficient b g j*b.φ j x

def weightedAbsolute {𝕜 X : Type*} [RCLike 𝕜] [MeasurableSpace X] {μ : Measure X}
    (b : BoundedBasis 𝕜 X μ) (g : X → 𝕜) (j : ℕ) : ℝ := ‖coefficient b g j‖ * basisBound b j
/-- Printed oscillation on actual representatives; a change on a null set may change it. -/
def essentialOscillation {𝕜 X : Type*} [RCLike 𝕜] [TopologicalSpace X] [MeasurableSpace X]
    (μ : Measure X) (g : X → 𝕜) : ℝ≥0∞ :=
  ⨆ x, Filter.limsup (fun y => ENNReal.ofReal ‖g y-g x‖) (nhds x ⊓ ae μ)

def inPartialSpan {𝕜 X : Type*} [RCLike 𝕜] [MeasurableSpace X] {μ : Measure X}
    (b : BoundedBasis 𝕜 X μ) (d : ℕ) (f : X → 𝕜) : Prop :=
  ∃ c : ℕ → 𝕜, ∀ x, f x = ∑ j ∈ Finset.range (d+1), c j*b.φ j x

def reconstructionMinimax {𝕜 X : Type*} [RCLike 𝕜] [TopologicalSpace X] [MeasurableSpace X]
    {μ : Measure X} (b : BoundedBasis 𝕜 X μ) (d : ℕ) (δ : ℝ) : ℝ≥0∞ :=
  ⨅ (f : X → 𝕜) (_ : inPartialSpan b d f),
    ⨆ (g : X → 𝕜) (_ : MemLp g ⊤ μ ∧ ENNReal.ofReal δ ≤ essentialOscillation μ g),
      eLpNorm (fun x => g x-f x) ⊤ μ

end SpectralSharpness.NormalWindow.Supplement



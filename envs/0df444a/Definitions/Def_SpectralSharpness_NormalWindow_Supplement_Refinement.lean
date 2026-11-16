-- Prove2me | Definitions.Def_SpectralSharpness_NormalWindow_Supplement_Refinement
-- name    : SpectralSharpness_NormalWindow_Supplement_Refinement
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T06:05:26.310056+00:00
-- url     : https://prove2.me/theorems/c0f701eb-fdde-4977-a8cc-2eceeea67cea
-- title:
--   Clamped refinement and general affine ReLU networks
-- statement:
--   Define clamp(y)=min(1,max(0,y)), Ψ(y)=clamp(2y−1/2), s₀(x)=clamp(x+1/2), s_{L+1}=Ψ∘s_L and s̃_L=2s_L−1. The interval window is the ordinary length of the uncertainty component containing zero inside [−1,1].
--
--   An affine layer stores its real matrix and bias. A scalar-input network stores a finite depth, each layer’s width, consecutive affine maps followed by coordinate ReLUs, and a final affine scalar output. Its evaluation is the actual composition; no representation of s̃_L is assumed. Depth counts hidden affine/ReLU layers. The parameter count includes every scalar weight and bias position, including the output bias:
--   $$
--   P=\sum_{i<D}(n_i+1)n_{i+1}+n_D+1.
--   $$
--   The logarithmic depth expression is the natural ceiling of log₂(γ/w). Its asymptotic use is restricted to positive w tending to zero. The exact printed 9L+6 count and the different L versus L+1 depth wordings are retained in the theorem, and their issues are documented separately.
-- source:
--   Wenwei Li, The Spectral Cost of Sharpness: Fourier Truncation, the Gibbs Bend, and the Computability of Classification, 2026 manuscript, STOC 2027 submission #122, SHA-256 0c0e3d52a54d9fbebc999feaa9b26703db76a5586d3c43db2ed20b17c15a9100, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/122.pdf, Definition 7.4; Lemma 7.5; Theorem 7.6, p. 20

import Mathlib
import Definitions.Def_SpectralSharpness_NormalWindow_Supplement_Fourier

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

noncomputable section

namespace SpectralSharpness.NormalWindow.Supplement

def clamp (y : ℝ) : ℝ := min 1 (max 0 y)
def refinement (y : ℝ) : ℝ := clamp (2*y-1/2)
def softState : ℕ → ℝ → ℝ
  | 0 => fun x => clamp (x+1/2)
  | L+1 => fun x => refinement (softState L x)
def softStep (L : ℕ) (x : ℝ) : ℝ := 2*softState L x-1

def intervalWindow (γ : ℝ) (f : ℝ → ℝ) : ℝ :=
  (volume (connectedComponentIn {x ∈ Set.Icc (-1:ℝ) 1 | |f x| < γ} 0)).toReal

/-- A general dense affine layer, independent of any target function. -/
structure AffineLayer (a b : ℕ) where
  weight : Fin b → Fin a → ℝ
  bias : Fin b → ℝ

def AffineLayer.eval {a b : ℕ} (l : AffineLayer a b) (x : Fin a → ℝ) : Fin b → ℝ :=
  fun i => l.bias i + ∑ j, l.weight i j*x j
/-- Hidden affine/ReLU layers followed by an affine scalar output. Depth counts hidden layers. -/
structure ReluNetwork where
  depth : ℕ
  widths : ℕ → ℕ
  inputWidth : widths 0 = 1
  layers : (i : Fin depth) → AffineLayer (widths i.val) (widths (i.val+1))
  outputWeight : Fin (widths depth) → ℝ
  outputBias : ℝ

def ReluNetwork.state (net : ReluNetwork) (x : ℝ) : (i : ℕ) → Fin (net.widths i) → ℝ
  | 0 => fun _ => x
  | i+1 => if h : i < net.depth then
      fun j => max 0 ((net.layers ⟨i,h⟩).eval (net.state x i) j)
    else fun _ => 0

def ReluNetwork.eval (net : ReluNetwork) (x : ℝ) : ℝ :=
  net.outputBias + ∑ j, net.outputWeight j*net.state x net.depth j

def ReluNetwork.widthAtMost (net : ReluNetwork) (m : ℕ) : Prop :=
  ∀ i, 0 < i → i ≤ net.depth → net.widths i ≤ m

def ReluNetwork.parameterCount (net : ReluNetwork) : ℕ :=
  (∑ i ∈ Finset.range net.depth, (net.widths i+1)*net.widths (i+1)) +
    net.widths net.depth+1

def logDepth (γ w : ℝ) : ℕ := ⌈Real.log (γ/w) / Real.log 2⌉₊

end SpectralSharpness.NormalWindow.Supplement



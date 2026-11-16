-- Prove2me | Definitions.Def_SpectralSharpness_NormalWindow_Supplement_Classification
-- name    : SpectralSharpness_NormalWindow_Supplement_Classification
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T06:06:42.888531+00:00
-- url     : https://prove2.me/theorems/06cafcc5-4a43-4f0f-b455-68ceefd4e76e
-- title:
--   Confident classifiers, threshold decisions and upper density bounds
-- statement:
--   The decision labels are −1, +1 and abstain, encoded by three distinct discrete values. A confident pair (f,c) has an exceptional set E of ordinary Lebesgue outer length at most ε. On E it abstains; outside E it decides with |f|≥γ, agrees with the sign of f and equals H. The specified threshold decision abstains exactly at |f|<γ, so equality |f|=γ is a decision.
--
--   The prescribed degree is the exact ceiling d=⌈8/(πε(1−γ)²)⌉. It is not rounded to an odd number. An upper density bound means a Borel probability supported on the torus interval with a measurable density at most ρ relative to ordinary length. No positive lower density is assumed.
--
--   A uniformly computable family uses one finite oracle program with the family index and requested precision as discrete input, working on every Cauchy name of every real input. These definitions retain the total discrete computation demanded by Theorem 8.2, although that demand conflicts with connectedness and is recorded as a source defect.
-- source:
--   Wenwei Li, The Spectral Cost of Sharpness: Fourier Truncation, the Gibbs Bend, and the Computability of Classification, 2026 manuscript, STOC 2027 submission #122, SHA-256 0c0e3d52a54d9fbebc999feaa9b26703db76a5586d3c43db2ed20b17c15a9100, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/122.pdf, Definition 8.1; Theorem 8.2, p. 24

import Mathlib
import Definitions.Def_SpectralSharpness_NormalWindow_Supplement_Computability

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

noncomputable section

namespace SpectralSharpness.NormalWindow.Supplement

/-- Labels 0=-1, 1=+1, 2=abstain; discrete output representation. -/
def labelValue (l : Fin 3) : ℝ := if l.val=0 then -1 else if l.val=1 then 1 else 0

def thresholdDecision (γ : ℝ) (f : ℝ → ℝ) (x : ℝ) : Fin 3 :=
  if |f x| < γ then 2 else if 0 < f x then 1 else 0

def Confident (ε γ : ℝ) (f : ℝ → ℝ) (c : ℝ → Fin 3) : Prop :=
  ∃ E : Set ℝ, E ⊆ torusInterval ∧ volume E ≤ ENNReal.ofReal ε ∧
    (∀ x ∈ E, c x=2) ∧
    (∀ x ∈ torusInterval, x ∉ E → c x ≠ 2 ∧ |f x| ≥ γ ∧
      labelValue (c x) = (if 0 < f x then 1 else if f x < 0 then -1 else 0) ∧
      labelValue (c x) = squareWave x)

def confidenceDegree (ε γ : ℝ) : ℕ := ⌈8/(Real.pi*ε*(1-γ)^2)⌉₊
/-- Upper density bound with respect to ordinary length, not a lower bound. -/
def UpperDensityBound (D : Measure ℝ) (ρ : ℝ) : Prop :=
  IsProbabilityMeasure D ∧ D torusIntervalᶜ=0 ∧
    ∃ p : ℝ → ℝ≥0∞, Measurable p ∧ D=torusMeasure.withDensity p ∧
      (∀ᵐ x ∂torusMeasure, p x ≤ ENNReal.ofReal ρ)

def uniformComputableFamily (S : Set ℝ) (F : ℕ → ℝ → ℝ) : Prop :=
  ∃ c : OracleProgram, ∀ m x, x ∈ S → ∀ q : ℕ → ℚ, cauchyName q x →
    ∀ n, ∃ fuel v, oracleEval fuel c (fun i => Encodable.encode (q i)) (Nat.pair m n)=some v ∧
      |(decodeRational v:ℝ)-F m x| ≤ (2:ℝ)^(-(n:ℤ))

end SpectralSharpness.NormalWindow.Supplement



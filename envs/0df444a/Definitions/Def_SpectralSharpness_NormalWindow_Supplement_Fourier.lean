-- Prove2me | Definitions.Def_SpectralSharpness_NormalWindow_Supplement_Fourier
-- name    : SpectralSharpness_NormalWindow_Supplement_Fourier
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T06:03:32.067718+00:00
-- url     : https://prove2.me/theorems/2dcb0238-d79b-46ef-bcf9-103dacae3a42
-- title:
--   Square wave, Fourier sums, torus windows and primitives
-- statement:
--   The square wave is H(x)=sgn(sin x), including zero at its jumps. For a nonnegative integer d the finite sine sum S_d and its Fejér weighted sum σ_d retain exactly positive odd frequencies k≤d, with amplitude 4/(πk) and Fejér weight 1−k/(d+1). The source uses positive odd degrees d=2m+1.
--
--   The uncertainty set is {|f|<γ} on the circle and w_γ(f) is the ordinary length of its connected component containing zero; a full-circle component has length 2π. Sharpness is 2γ/w_γ. The Gibbs profile is Φ(t)=(2/π)∫₀ᵗ sin(u)/u du, with its removable value at zero filled by 1. Its inverse is selected on [0,π]. The accumulator is the periodic extension of ∫₀ˣ f(s)ds and is used for mean-zero inputs.
--
--   The L² norm uses ordinary Lebesgue measure, as the numerical identities and proofs do; it is √(2π) times the normalized L² norm. Essential L∞ norms use extended nonnegative reals. Complex Fourier coefficients use the conventional 1/(2π) normalization, distinct from sine amplitudes. The one-dimensional spectrum predicate directly uses the published Euclidean-ball definition. These shared definitions keep windows, coefficients and integrals consistent across the companion results.
-- source:
--   Wenwei Li, The Spectral Cost of Sharpness: Fourier Truncation, the Gibbs Bend, and the Computability of Classification, 2026 manuscript, STOC 2027 submission #122, SHA-256 0c0e3d52a54d9fbebc999feaa9b26703db76a5586d3c43db2ed20b17c15a9100, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/122.pdf, Definition 2.2; Definition 4.1; Lemma 6.3; Definition 6.6, p. 7

import Mathlib
import Definitions.Def_SpectralSharpness_NormalWindow_BandLimited

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

noncomputable section

namespace SpectralSharpness.NormalWindow.Supplement

/-- Fundamental interval, ordinary Lebesgue measure, and odd positive degrees. -/
def torusInterval : Set ℝ := Set.Ico (-Real.pi) Real.pi
def torusMeasure : Measure ℝ := volume.restrict torusInterval
def oddDegree (m : ℕ) : ℕ := 2*m+1
abbrev oddLimit : Filter ℕ := Filter.atTop

def squareWave (x : ℝ) : ℝ := if Real.sin x = 0 then 0 else if 0 < Real.sin x then 1 else -1

def truncation (d : ℕ) (x : ℝ) : ℝ :=
  4 / Real.pi * ∑ k ∈ (Finset.range (d+1)).filter (fun k => 0 < k ∧ Odd k),
    Real.sin ((k:ℝ)*x) / (k:ℝ)
def fejer (d : ℕ) (x : ℝ) : ℝ :=
  4 / Real.pi * ∑ k ∈ (Finset.range (d+1)).filter (fun k => 0 < k ∧ Odd k),
    (1 - (k:ℝ)/((d:ℝ)+1)) * Real.sin ((k:ℝ)*x) / (k:ℝ)
def realCutoff (d : ℝ) : ℕ := ⌊d⌋₊
def truncationReal (d : ℝ) : ℝ → ℝ := truncation (realCutoff d)
def tailSquares (d : ℕ) : ℝ :=
  ∑' k : ℕ, if d < k ∧ Odd k then 1 / (k:ℝ)^2 else 0

def ltwo (f : ℝ → ℝ) : ℝ := Real.sqrt (∫ x, (f x)^2 ∂torusMeasure)
def linfty (f : ℝ → ℝ) : ℝ≥0∞ := eLpNorm f ⊤ torusMeasure
def supNorm (f : ℝ → ℝ) : ℝ := sSup (Set.range fun x => |f x|)
def uncertainty (γ : ℝ) (f : ℝ → ℝ) : Set ℝ := {x ∈ torusInterval | |f x| < γ}
/-- Component in the torus, represented by its preimage on one fundamental interval.
Periodicity is imposed on the arguments in the statements that use this definition. -/
def windowComponent (γ : ℝ) (f : ℝ → ℝ) : Set ℝ :=
  {x ∈ torusInterval | (x : Real.Angle) ∈
    connectedComponentIn {z : Real.Angle | |f z.toReal| < γ} 0}
def window (γ : ℝ) (f : ℝ → ℝ) : ℝ := (volume (windowComponent γ f)).toReal
def uncertaintyLength (γ : ℝ) (f : ℝ → ℝ) : ℝ := (volume (uncertainty γ f)).toReal
def sharpness (γ : ℝ) (f : ℝ → ℝ) : ℝ := 2*γ / window γ f

def scalarBandLimited (d : ℝ) (f : ℝ → ℝ) : Prop :=
  SpectralSharpness.NormalWindow.IsBandLimitedBall d (fun x : EuclideanSpace ℝ (Fin 1) => f (x 0))
def isOdd (f : ℝ → ℝ) : Prop := ∀ x, f (-x) = -f x

def sincRemovable (u : ℝ) : ℝ := if u=0 then 1 else Real.sin u/u
def gibbsProfile (t : ℝ) : ℝ := 2/Real.pi * ∫ u in (0:ℝ)..t, sincRemovable u
def gibbsConstant : ℝ := gibbsProfile Real.pi
def gibbsExcess : ℝ := gibbsConstant-1
/-- Only used under 0<γ<1, with unique existence supplied by Lemma 6.3. -/
def gibbsInverse (γ : ℝ) : ℝ := sInf {t ∈ Set.Icc 0 Real.pi | γ ≤ gibbsProfile t}
def accumulator (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  ∫ s in (0:ℝ)..((x : Real.Angle).toReal), f s

def fourier (f : ℝ → ℝ) (k : ℤ) : ℂ :=
  (1/(2*(Real.pi:ℂ))) * ∫ x, (f x:ℂ) * Complex.exp (-Complex.I*(k:ℂ)*(x:ℂ)) ∂torusMeasure

end SpectralSharpness.NormalWindow.Supplement



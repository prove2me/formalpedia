-- Prove2me | Definitions.Def_PalomarSolution
-- name    : PalomarSolution
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T15:07:55.928749+00:00
-- url     : https://prove2.me/theorems/f4229f42-197f-58e9-b593-d8c03ca16ac6
-- title:
--   Palomar Solution
-- statement:
--   Definitions and structural lemmas for Palomar Solution, from Matthew J. Colbrook (MColbrook/Eden_conjecture; see pinned Apache-2.0 LICENSE, NOTICE.md, and formalization.yaml)'s pinned Counterexample to the unrestricted form of Eden's conjecture development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/PalomarSolution.lean

import Definitions.Def_Eden_Solution
import Theorems.Thm_Eden_amplitudeSq_at_zero
import Theorems.Thm_Eden_amplitudeSq_zero_time
import Theorems.Thm_Eden_blockRotation_apply
import Theorems.Thm_Eden_diagonalLinear_apply
import Theorems.Thm_Eden_evolution_origin
import Theorems.Thm_Eden_evolution_zero_time
import Theorems.Thm_Eden_frequencyEvolution_zero_time
import Theorems.Thm_Eden_planarAmplitude_zero_time
import Theorems.Thm_Eden_planarDiagonal_apply
import Theorems.Thm_Eden_planarMovingPerturbation_zero_time
import Theorems.Thm_Eden_planarX_origin
import Theorems.Thm_Eden_planarX_zero_time
import Theorems.Thm_Eden_planarY_origin
import Theorems.Thm_Eden_planarY_zero_time
import Theorems.Thm_Eden_radialAmplitude_zero_time
import Theorems.Thm_Eden_radialDefect_at_one
import Theorems.Thm_Eden_radialDiscriminant_at_two
import Theorems.Thm_Eden_radialDiscriminant_at_zero
import Theorems.Thm_Eden_radialDiscriminant_zero_time
import Theorems.Thm_Eden_radiusEvolution_at_one
import Theorems.Thm_Eden_radiusEvolution_at_sqrt_two
import Theorems.Thm_Eden_radiusEvolution_at_zero
import Theorems.Thm_Eden_radiusEvolution_zero_time
import Theorems.Thm_Eden_singularValueFunction_zero
import Theorems.Thm_Eden_spectralProduct_zero
import Theorems.Thm_Eden_spectrumInterpolation_zero
import Theorems.Thm_Eden_squaredRadiusEvolution_at_one
import Theorems.Thm_Eden_squaredRadiusEvolution_at_two
import Theorems.Thm_Eden_squaredRadiusEvolution_at_zero
import Theorems.Thm_Eden_squaredRadiusEvolution_zero_time
attribute [local simp] Eden.amplitudeSq_at_zero
attribute [local simp] Eden.amplitudeSq_zero_time
attribute [local simp] Eden.blockRotation_apply
attribute [local simp] Eden.diagonalLinear_apply
attribute [local simp] Eden.evolution_origin
attribute [local simp] Eden.evolution_zero_time
attribute [local simp] Eden.frequencyEvolution_zero_time
attribute [local simp] Eden.planarAmplitude_zero_time
attribute [local simp] Eden.planarDiagonal_apply
attribute [local simp] Eden.planarMovingPerturbation_zero_time
attribute [local simp] Eden.planarX_origin
attribute [local simp] Eden.planarX_zero_time
attribute [local simp] Eden.planarY_origin
attribute [local simp] Eden.planarY_zero_time
attribute [local simp] Eden.radialAmplitude_zero_time
attribute [local simp] Eden.radialDefect_at_one
attribute [local simp] Eden.radialDiscriminant_at_two
attribute [local simp] Eden.radialDiscriminant_at_zero
attribute [local simp] Eden.radialDiscriminant_zero_time
attribute [local simp] Eden.radiusEvolution_at_one
attribute [local simp] Eden.radiusEvolution_at_sqrt_two
attribute [local simp] Eden.radiusEvolution_at_zero
attribute [local simp] Eden.radiusEvolution_zero_time
attribute [local simp] Eden.singularValueFunction_zero
attribute [local simp] Eden.spectralProduct_zero
attribute [local simp] Eden.spectrumInterpolation_zero
attribute [local simp] Eden.squaredRadiusEvolution_at_one
attribute [local simp] Eden.squaredRadiusEvolution_at_two
attribute [local simp] Eden.squaredRadiusEvolution_at_zero
attribute [local simp] Eden.squaredRadiusEvolution_zero_time


set_option autoImplicit true
noncomputable section
open Set Filter
open scoped Topology
namespace EdenPalomar
abbrev PhaseSpace := EuclideanSpace ℝ (Fin 5)
def radiusSq₁ (p : PhaseSpace) : ℝ := p 0 ^ 2 + p 1 ^ 2
def radiusSq₂ (p : PhaseSpace) : ℝ := p 2 ^ 2 + p 3 ^ 2
def q (s : ℝ) : ℝ := -(s - 1) * (s - 2)
def vectorField (c : ℝ) (p : PhaseSpace) : PhaseSpace :=
  !₂[q (radiusSq₁ p) * p 0 - p 1, q (radiusSq₁ p) * p 1 + p 0,
     q (radiusSq₂ p) * p 2 - Real.sqrt 2 * p 3,
     q (radiusSq₂ p) * p 3 + Real.sqrt 2 * p 2, -c * p 4]
def attractor : Set PhaseSpace :=
  {p | radiusSq₁ p ≤ 2 ∧ radiusSq₂ p ≤ 2 ∧ p 4 = 0}
def torus : Set PhaseSpace :=
  {p | radiusSq₁ p = 1 ∧ radiusSq₂ p = 1 ∧ p 4 = 0}
def torusPoint (θ₁ θ₂ : ℝ) : PhaseSpace :=
  !₂[Real.cos θ₁, Real.sin θ₁, Real.cos θ₂, Real.sin θ₂, 0]
def divergence (c : ℝ) (p : PhaseSpace) : ℝ :=
  LinearMap.trace ℝ PhaseSpace (fderiv ℝ (vectorField c) p).toLinearMap
def singularValueFunction (M : PhaseSpace →ₗ[ℝ] PhaseSpace) (d : ℝ) : ℝ :=
  ∏ i ∈ Finset.range 5, M.singularValues i ^ (min 1 (max 0 (d - i)))
def admissibleDimensions (φ : ℝ → PhaseSpace → PhaseSpace) (t : ℝ)
    (p : PhaseSpace) : Set ℝ :=
  {d | d ∈ Icc 0 5 ∧ 1 ≤ singularValueFunction (fderiv ℝ (φ t) p).toLinearMap d}
def finiteTimeDimension (φ : ℝ → PhaseSpace → PhaseSpace) (t : ℝ)
    (p : PhaseSpace) : ℝ := sSup (admissibleDimensions φ t p)
def globalLyapunovDimension (φ : ℝ → PhaseSpace → PhaseSpace) (K : Set PhaseSpace) : ℝ :=
  sInf {v : ℝ | ∃ t : ℝ, 0 < t ∧ v = sSup (finiteTimeDimension φ t '' K)}
def lyapunovExponent (φ : ℝ → PhaseSpace → PhaseSpace) (p : PhaseSpace)
    (i : Fin 5) : ℝ :=
  limUnder atTop (fun t : ℝ => Real.log ((fderiv ℝ (φ t) p).toLinearMap.singularValues i) / t)
def spectrumEntry (a : Fin 5 → ℝ) (i : ℕ) : ℝ :=
  if h : i < 5 then a ⟨i, h⟩ else 0
def spectrumPartialSum (a : Fin 5 → ℝ) (k : ℕ) : ℝ :=
  ∑ i ∈ Finset.range k, spectrumEntry a i
def nonnegativeSumIndices (a : Fin 5 → ℝ) : Finset ℕ :=
  (Finset.range 6).filter (fun k => 0 ≤ spectrumPartialSum a k)
theorem indices_nonempty (a : Fin 5 → ℝ) : (nonnegativeSumIndices a).Nonempty := by
  refine ⟨0, ?_⟩
  simp only [nonnegativeSumIndices, Finset.mem_filter, Finset.mem_range]
  exact ⟨by decide, by simp [spectrumPartialSum]⟩
def kaplanYorkeIndex (a : Fin 5 → ℝ) : ℕ :=
  (nonnegativeSumIndices a).max' (indices_nonempty a)
def kaplanYorkeDimension (a : Fin 5 → ℝ) : ℝ :=
  if kaplanYorkeIndex a = 0 then 0
  else if kaplanYorkeIndex a = 5 then 5
  else (kaplanYorkeIndex a : ℝ) +
    spectrumPartialSum a (kaplanYorkeIndex a) / |spectrumEntry a (kaplanYorkeIndex a)|
def asymptoticDimension (φ : ℝ → PhaseSpace → PhaseSpace) (p : PhaseSpace) : ℝ :=
  kaplanYorkeDimension (lyapunovExponent φ p)
def periodicEquilibriumSet (c : ℝ) (φ : ℝ → PhaseSpace → PhaseSpace) : Set PhaseSpace :=
  attractor ∩ ({p | vectorField c p = 0} ∪ {p | ∃ t : ℝ, 0 < t ∧ φ t p = p})
def IsGlobalAttractor (φ : ℝ → PhaseSpace → PhaseSpace) (K : Set PhaseSpace) : Prop :=
  K.Nonempty ∧ IsCompact K ∧ (∀ t : ℝ, 0 ≤ t → φ t '' K = K) ∧
    ∀ B : Set PhaseSpace, Bornology.IsBounded B → ∀ ε : ℝ, 0 < ε →
      ∃ T : ℝ, 0 ≤ T ∧ ∀ t : ℝ, T ≤ t → ∀ p ∈ B,
        ∃ q ∈ K, dist (φ t p) q < ε
end EdenPalomar



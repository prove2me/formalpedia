-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ResidueLatticeCount_UnitPreserving
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ResidueLatticeCount_UnitPreserving
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T20:33:29.762796+00:00
-- url     : https://prove2.me/theorems/03b22a6d-0f94-45b1-9cfc-f5b19f98b2ef
-- title:
--   Unit Preserving
-- statement:
--   Definitions and structural lemmas for Unit Preserving, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ResidueLatticeCount/UnitPreserving.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ResidueLatticeCount_HeckeLower
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField NumberField.mixedEmbedding NumberField.mixedEmbedding.fundamentalCone
  NumberField.InfinitePlace NumberField.Units MeasureTheory
open scoped nonZeroDivisors ENNReal Classical Pointwise
noncomputable section
namespace PI.Residue
section defs
variable (K : Type) [Field K] [NumberField K]
def box (r : InfinitePlace K → ℝ) : Set (mixedSpace K) := {y | ∀ w, normAtPlace w y < r w}
def shell : Set (mixedSpace K) :=
  {y | y ∈ fundamentalCone K ∧ 1 / 2 < mixedEmbedding.norm y ∧ mixedEmbedding.norm y ≤ 1}
def vfac : ℝ≥0∞ := 2 ^ nrRealPlaces K * (NNReal.pi : ℝ≥0∞) ^ nrComplexPlaces K
def hit (ρ : ℝ) (x : mixedSpace K) : Set (mixedSpace K) :=
  {y | ∀ w, normAtPlace w y * normAtPlace w x < ρ}
abbrev lat (J : (Ideal (𝓞 K))⁰) : Submodule ℤ (mixedSpace K) :=
  idealLattice K (FractionalIdeal.mk0 K J)
def classZeta (C : ClassGroup (𝓞 K)) (s : ℝ) : ℝ≥0∞ :=
  ∑' I : {I : (Ideal (𝓞 K))⁰ // ClassGroup.mk0 I = C},
    ENNReal.ofReal ((Ideal.absNorm (I.1 : Ideal (𝓞 K)) : ℝ) ^ (-s))
end defs
def LatticeCount : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (L : Submodule ℤ (mixedSpace K)) [DiscreteTopology L]
    [IsZLattice ℝ L] (B : Set (mixedSpace K)), MeasurableSet B →
    volume B ≤ (∑' x : L, (B - B).indicator (fun _ => (1 : ℝ≥0∞)) (x : mixedSpace K)) *
      ENNReal.ofReal (ZLattice.covolume L)
def BoxVolume : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (r : InfinitePlace K → ℝ), (∀ w, 0 < r w) →
    volume (box K r) = vfac K * ENNReal.ofReal (∏ w, r w ^ mult w)
def ShellVolume : Prop :=
  ∀ (K : Type) [Field K] [NumberField K],
    volume (shell K) = vfac K * ENNReal.ofReal (regulator K) / 2
def UnitPreserving : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (u : (𝓞 K)ˣ),
    MeasurePreserving (fun y : mixedSpace K => u • y) volume volume
def CountIntegral : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (J : (Ideal (𝓞 K))⁰) (ρ : ℝ), 0 < ρ →
    vfac K * ENNReal.ofReal ((ρ / 2) ^ Module.finrank ℚ K) * volume (shell K) ≤
      (∑' x : lat K J, volume (shell K ∩ hit K ρ (x : mixedSpace K))) *
        ENNReal.ofReal (ZLattice.covolume (lat K J))
def Unfold : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (J : (Ideal (𝓞 K))⁰) (ρ : ℝ), 0 < ρ →
    ∑' x : lat K J, volume (shell K ∩ hit K ρ (x : mixedSpace K)) ≤
      volume (shell K) +
        ∑' x : idealSet K J, volume ({y | 1 / 2 < mixedEmbedding.norm y} ∩ hit K ρ (x : mixedSpace K))
def HitBound : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (ρ s : ℝ) (x : mixedSpace K), 0 < ρ → 1 < s →
    0 < mixedEmbedding.norm x →
    volume ({y | 1 / 2 < mixedEmbedding.norm y} ∩ hit K ρ x) ≤
      vfac K * ENNReal.ofReal (ρ ^ Module.finrank ℚ K * (2 * ρ ^ Module.finrank ℚ K) ^ (s - 1) *
        mixedEmbedding.norm x ^ (-s))
def IdealSetSum : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (s : ℝ) (C : ClassGroup (𝓞 K)) (J : (Ideal (𝓞 K))⁰),
    ClassGroup.mk0 J = C⁻¹ →
    ∑' x : idealSet K J, ENNReal.ofReal (mixedEmbedding.norm (x : mixedSpace K) ^ (-s)) ≤
      (torsionOrder K : ℝ≥0∞) * ENNReal.ofReal ((Ideal.absNorm (J : Ideal (𝓞 K)) : ℝ) ^ (-s)) *
        classZeta K C s
def ClassSum : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (s : ℝ),
    Summable (fun I : {I : Ideal (𝓞 K) // I ≠ ⊥} => (Ideal.absNorm I.1 : ℝ) ^ (-s)) →
    ∑ C : ClassGroup (𝓞 K), classZeta K C s ≤ ENNReal.ofReal (idealZeta K s)
def ClassLower : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (s : ℝ) (C : ClassGroup (𝓞 K)), 1 < s →
    ENNReal.ofReal (regulator K) ≤
      ENNReal.ofReal ((4 : ℝ) ^ s * ((|discr K| : ℤ) : ℝ) ^ (s / 2) * torsionOrder K) * classZeta K C s
end PI.Residue



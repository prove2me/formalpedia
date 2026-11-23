-- Prove2me | Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__ExistsHorizontalGeneratorOfCharts_f0ad16e2bc421ec8
-- name    : P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__ExistsHorizontalGeneratorOfCharts_f0ad16e2bc421ec8
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T14:14:54.620794+00:00
-- url     : https://prove2.me/theorems/70deccd9-2d94-42fb-8bf2-748fbf086981
-- title:
--   Exists Horizontal Generator Of Charts
-- statement:
--   Definitions and structural lemmas for Exists Horizontal Generator Of Charts, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/Divisors₂/ExistsHorizontalGeneratorOfCharts.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DifferentiableOnOfTendstoLocallyUniformlyOn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_FderivIntegralApplyOfHolomorphicOfDominated
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open Set Filter Metric
open scoped Topology
namespace GlobalTheory.Published.LogLine
variable {n : ℕ}
def offDivisor (U : Set (Fin n → ℂ)) (S : Finset (Fin n)) : Set (Fin n → ℂ) :=
  {z | z ∈ U ∧ ∀ i ∈ S, z i ≠ 0}
def logPartial (S : Finset (Fin n)) (i : Fin n) (f : (Fin n → ℂ) → ℂ) (z : Fin n → ℂ) : ℂ :=
  (if i ∈ S then z i else 1) * fderiv ℂ f z (Pi.single i 1)
def IsHorizontalOn (S : Finset (Fin n)) (a : Fin n → (Fin n → ℂ) → ℂ) (f : (Fin n → ℂ) → ℂ)
    (V : Set (Fin n → ℂ)) : Prop :=
  DifferentiableOn ℂ f V ∧ ∀ z ∈ V, ∀ i, logPartial S i f z + a i z * f z = 0
end GlobalTheory.Published.LogLine
namespace GlobalTheory.Published
open LogLine
def CanonicalExtensionRankOne : Prop :=
  ∀ (n : ℕ) (U : Set (Fin n → ℂ)) (S : Finset (Fin n)) (a : Fin n → (Fin n → ℂ) → ℂ)
    (f : (Fin n → ℂ) → ℂ), IsOpen U →
    (∀ i, DifferentiableOn ℂ (a i) U) →
    (∀ i ∈ S, ∀ z ∈ U, z i = 0 → a i z = 0) →
    IsHorizontalOn S a f (offDivisor U S) →
    (∀ z ∈ offDivisor U S, f z ≠ 0) →
    ∃ F : (Fin n → ℂ) → ℂ, EqOn F f (offDivisor U S) ∧ IsHorizontalOn S a F U ∧
      (∀ z ∈ U, F z ≠ 0) ∧
      ∀ G : (Fin n → ℂ) → ℂ, ContinuousOn G U → EqOn G f (offDivisor U S) → EqOn G F U
end GlobalTheory.Published
namespace GlobalTheory.Published.LogLine
variable {n : ℕ}
def oneForm (b : Fin n → (Fin n → ℂ) → ℂ) (z : Fin n → ℂ) : (Fin n → ℂ) →L[ℂ] ℂ :=
  ∑ i, b i z • ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin n => ℂ) i
end GlobalTheory.Published.LogLine
namespace GlobalTheory.Published
open LogLine
end GlobalTheory.Published
namespace GlobalTheory.Published
open LogLine
end GlobalTheory.Published
namespace GlobalTheory.Published.LogLine
end GlobalTheory.Published.LogLine



-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_QuotIntegrableIffCutoff
-- name    : Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_QuotIntegrableIffCutoff
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T06:11:13.383033+00:00
-- url     : https://prove2.me/theorems/ce8bb648-91d0-4656-858c-c537d3c2c82d
-- title:
--   Quot Integrable Iff Cutoff
-- statement:
--   Definitions and structural lemmas for Quot Integrable Iff Cutoff, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/QuotIntegrableIffCutoff.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_BruhatFunctionExistsClosedSubgroup
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Topology
open scoped ENNReal
noncomputable section
namespace GlobalTheory.Tw
section Defs
variable {G : Type} [Group G] [MeasurableSpace G]
abbrev RCoset (T : Subgroup G) : Type := Quotient (QuotientGroup.rightRel T)
def IsQuotMeasure (T : Subgroup G) (μ : Measure G) (μT : Measure T) (ν : Measure (RCoset T)) : Prop :=
  ∀ f : G → ℝ≥0∞, Measurable f → ∫⁻ g, f g ∂μ = ∫⁻ c, ∫⁻ t : T, f (t * Quotient.out c) ∂μT ∂ν
def IsCosetCutoff (T : Subgroup G) (μT : Measure T) (β : G → NNReal) : Prop :=
  Measurable β ∧ ∀ x, ∫⁻ t : T, β (t * x) ∂μT = 1
def quotMeas (T : Subgroup G) (μ : Measure G) (μT : Measure T) : Measure (RCoset T) :=
  Classical.epsilon (IsQuotMeasure T μ μT)
def quotInt {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] (T : Subgroup G) (μ : Measure G) (μT : Measure T)
    (F : G → E) : E :=
  ∫ c, F (Quotient.out c) ∂quotMeas T μ μT
def QuotIntegrable {E : Type} [NormedAddCommGroup E] (T : Subgroup G) (μ : Measure G) (μT : Measure T)
    (F : G → E) : Prop :=
  Integrable (fun c : RCoset T => F (Quotient.out c)) (quotMeas T μ μT)
end Defs
section Exist
variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G]
  [MeasurableSpace G] [BorelSpace G] {T : Subgroup G} {μ : Measure G} {μT : Measure T}
variable [LocallyCompactSpace G] [T2Space G] [SFinite μ] [μ.IsMulLeftInvariant] [μT.IsHaarMeasure] [μT.IsInvInvariant]
end Exist
example {G : Type} [Group G] [MeasurableSpace G] : IsCosetCutoff (⊥ : Subgroup G) (Measure.dirac 1) fun _ => 1 :=
  ⟨measurable_const, fun _ => by simp⟩
end GlobalTheory.Tw



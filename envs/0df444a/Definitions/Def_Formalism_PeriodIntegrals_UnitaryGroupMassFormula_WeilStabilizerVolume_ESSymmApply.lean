-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_ESSymmApply
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_ESSymmApply
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T01:15:56.235035+00:00
-- url     : https://prove2.me/theorems/49d8eaa4-7b3f-4873-bceb-ebcd2e41bcc2
-- title:
--   ESSymm Apply
-- statement:
--   Definitions and structural lemmas for ESSymm Apply, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeilStabilizerVolume/ESSymmApply.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_RestrProdSt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace PI.VolStabW.RPA
open MeasureTheory Filter Finset
open scoped NNReal ENNReal
variable {ι : Type} {W : ι → Type} [∀ i, MeasurableSpace (W i)]
variable (m : ∀ i, Measure (W i)) (L : ∀ i, Set (W i))
def am (i : ι) : ℝ≥0 := (m i (L i)).toNNReal
def tl (S : Finset ι) : ℝ≥0 := ∏' i : {i // i ∉ S}, am m L i.1
def TailH : Prop :=
  ∀ S : Finset ι, ∃ c : ℝ≥0∞, c ≠ ⊤ ∧ HasProd (fun i : {i // i ∉ S} => m i.1 (L i.1)) c
variable {m L}
variable (m L)
def Pn (i : ι) : Measure (W i) := (m i (L i))⁻¹ • (m i).restrict (L i)
lemma Pn_prob {i : ι} (h : m i (L i) ≠ 0 ∧ m i (L i) ≠ ⊤) : IsProbabilityMeasure (Pn m L i) := by
  constructor
  rw [Pn, Measure.smul_apply, Measure.restrict_apply_univ, smul_eq_mul]
  exact ENNReal.inv_mul_cancel h.1 h.2
open Classical in

def Qm (S : Finset ι) : Measure (∀ i : {i // i ∉ S}, W i) :=
  if h : ∀ i, i ∉ S → m i (L i) ≠ 0 ∧ m i (L i) ≠ ⊤ then
    haveI : ∀ i : {i // i ∉ S}, IsProbabilityMeasure (Pn m L i.1) := fun i => Pn_prob m L (h i.1 i.2)
    tl m L S • Measure.infinitePi (fun i : {i // i ∉ S} => Pn m L i.1)
  else 0
instance Qm_fin (S : Finset ι) : IsFiniteMeasure (Qm m L S) := by
  unfold Qm; split_ifs with h
  · haveI : ∀ i : {i // i ∉ S}, IsProbabilityMeasure (Pn m L i.1) :=
      fun i => Pn_prob m L (h i.1 i.2)
    infer_instance
  · infer_instance
def Rm (S : Finset ι) : Measure (∀ i : {i // i ∈ S}, W i) :=
  Measure.pi (fun i : {i // i ∈ S} => (m i.1).restrict (L i.1)ᶜ)
open Classical in

def eS (S : Finset ι) : (∀ i, W i) ≃ᵐ (∀ i : {i // i ∈ S}, W i) × (∀ i : {i // i ∉ S}, W i) :=
  MeasurableEquiv.piEquivPiSubtypeProd W (fun i => i ∈ S)
def kap [∀ i, SigmaFinite (m i)] (S : Finset ι) : Measure (∀ i, W i) :=
  ((Rm m L S).prod (Qm m L S)).map (eS S).symm
open Classical in

def mu (S : Finset ι) (i : ι) : Measure (W i) :=
  if i ∈ S then (m i).restrict (L i)ᶜ else (m i).restrict (L i)
variable [∀ i, SigmaFinite (m i)]
instance kap_sfin (S : Finset ι) : SFinite (kap m L S) := by unfold kap Rm; infer_instance
variable {m L}
end PI.VolStabW.RPA



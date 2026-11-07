-- Prove2me | Definitions.Def_QEC_Coding_ProbabilisticConstruction_SphericalCap_Measure
-- name    : QEC_Coding_ProbabilisticConstruction_SphericalCap_Measure
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T09:50:31.164209+00:00
-- url     : https://prove2.me/theorems/5d7fdce2-1fb3-4947-9483-ab9e095d0a79
-- title:
--   Measure
-- statement:
--   Definitions and structural lemmas for Measure, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ProbabilisticConstruction/SphericalCap/Measure.lean

import Definitions.Def_QEC_Coding_ProbabilisticConstruction_SphericalCap_ConeSlices
import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Tactic
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_SphericalCap_axialEquiv_fst
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_SphericalCap_axialEquiv_snd_apply
attribute [local simp] QEC.Coding.ProbabilisticConstruction.SphericalCap.axialEquiv_fst
attribute [local simp] QEC.Coding.ProbabilisticConstruction.SphericalCap.axialEquiv_snd_apply


set_option autoImplicit false
namespace QEC.Coding.ProbabilisticConstruction.SphericalCap
open MeasureTheory Metric Set
open scoped ENNReal Pointwise
abbrev Space := EuclideanSpace ℝ (Fin 3)
abbrev Sphere := Metric.sphere (0 : Space) 1
noncomputable def area : Measure Sphere :=
  (volume : Measure Space).toSphere
instance : IsFiniteMeasure area := by unfold area; infer_instance
instance : area.IsOpenPosMeasure := by unfold area; infer_instance
@[simp] theorem norm_coe (s : Sphere) : ‖(s : Space)‖ = 1 := by
  simpa only [Metric.mem_sphere, dist_zero_right] using s.property
theorem span_singleton_ne_top (s : Sphere) :
    (ℝ ∙ (s : Space)) ≠ ⊤ := by
  have hs : (s : Space) ≠ 0 := by
    intro h
    have := norm_coe s
    simp [h] at this
  intro h
  have hd := finrank_span_singleton (K := ℝ) hs
  rw [h] at hd
  norm_num [Space] at hd
instance : MeasureTheory.NullSingletonClass area where
  measure_singleton s := by
    rw [area, Measure.toSphere_apply' _ (measurableSet_singleton s)]
    have hsub : Ioo (0 : ℝ) 1 • ((↑) '' ({s} : Set Sphere)) ⊆
        (ℝ ∙ (s : Space) : Set Space) := by
      rintro x ⟨r, hr, y, ⟨t, ht, rfl⟩, rfl⟩
      have ht : t = s := ht
      subst t
      exact Submodule.smul_mem _ r (Submodule.mem_span_singleton_self _)
    have hz : (volume : Measure Space)
        (Ioo (0 : ℝ) 1 • ((↑) '' ({s} : Set Sphere))) = 0 := by
      apply le_antisymm _ bot_le
      exact (measure_mono hsub).trans_eq
        (Measure.addHaar_submodule volume _ (span_singleton_ne_top s))
    rw [hz, mul_zero]
def cap (u : Sphere) (c : ℝ) : Set Sphere :=
  {s | c ≤ inner ℝ (u : Space) (s : Space)}
noncomputable def capLaw (u : Sphere) (c : ℝ) : Measure Sphere :=
  (area (cap u c))⁻¹ • area.restrict (cap u c)
noncomputable def capDisplacementLaw (R : ℝ) (u : Sphere) (c : ℝ) : Measure Space :=
  (capLaw u c).map (fun s : Sphere => R • (s : Space))
instance (u : Sphere) (c : ℝ) : MeasureTheory.NullSingletonClass (capLaw u c) where
  measure_singleton s := by
    simp only [capLaw, Measure.smul_apply, measure_singleton, smul_zero]
def displacementCap (R : ℝ) (u : Sphere) (c : ℝ) : Set Space :=
  {p | ‖p‖ = R ∧ R*c ≤ inner ℝ (u : Space) p}
end QEC.Coding.ProbabilisticConstruction.SphericalCap



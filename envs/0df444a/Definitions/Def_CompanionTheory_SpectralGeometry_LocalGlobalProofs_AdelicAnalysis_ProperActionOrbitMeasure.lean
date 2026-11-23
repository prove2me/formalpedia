-- Prove2me | Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_ProperActionOrbitMeasure
-- name    : CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_ProperActionOrbitMeasure
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T05:58:43.007803+00:00
-- url     : https://prove2.me/theorems/10f6d22d-cb43-4ac9-8316-94fd25f583ee
-- title:
--   Proper Action Orbit Measure
-- statement:
--   Definitions and structural lemmas for Proper Action Orbit Measure, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/ProperActionOrbitMeasure.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_QuotMeasUniq
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ArchimedeanOrbitMeasures_LintegralMulRightOfMem
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Topology
open scoped ENNReal NNReal Matrix
namespace GlobalTheory.CompanionTheory.SW.AbsUniq
def stabilizerOf {G V : Type} [Group G] (act : G → V → V) (h1 : ∀ x, act 1 x = x)
    (hm : ∀ g h x, act (g * h) x = act g (act h x)) (x₀ : V) : Subgroup G where
  carrier := {g | act g x₀ = x₀}
  mul_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq] at *
    rw [hm, hb, ha]
  one_mem' := h1 x₀
  inv_mem' := by
    intro a ha
    simp only [Set.mem_setOf_eq] at *
    have h : act a⁻¹ (act a x₀) = x₀ := by rw [← hm, inv_mul_cancel, h1]
    rwa [ha] at h
def orbitQuot {G V : Type} [Group G] (act : G → V → V) (h1 : ∀ x, act 1 x = x)
    (hm : ∀ g h x, act (g * h) x = act g (act h x)) (x₀ : V) :
    G ⧸ stabilizerOf act h1 hm x₀ → V :=
  Quotient.lift (fun g => act g x₀) (by
    intro a b hab
    have h : a⁻¹ * b ∈ stabilizerOf act h1 hm x₀ := QuotientGroup.leftRel_apply.1 hab
    have h' : act (a⁻¹ * b) x₀ = x₀ := h
    show act a x₀ = act b x₀
    conv_lhs => rw [← h']
    rw [← hm, mul_inv_cancel_left])
end GlobalTheory.CompanionTheory.SW.AbsUniq



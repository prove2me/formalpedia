-- Prove2me | Definitions.Def_CompanionTheory_RealGroups_DiscreteSeries_DiscreteSeriesClassification_DiscreteSeriesExhaustion_HeckeAlgebraActions_HeckeUnitTensors_CommuteLeftRightCasimir
-- name    : CompanionTheory_RealGroups_DiscreteSeries_DiscreteSeriesClassification_DiscreteSeriesExhaustion_HeckeAlgebraActions_HeckeUnitTensors_CommuteLeftRightCasimir
-- status  : Definition
-- author  : @community-bot-2
-- created : 2026-11-25T14:39:52.136603+00:00
-- url     : https://prove2.me/theorems/7bfa9f2c-1d5b-4fee-adcf-317bd920fbe9
-- title:
--   Commute Left Right Casimir
-- statement:
--   Definitions and structural lemmas for Commute Left Right Casimir, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/RealGroups/DiscreteSeries/DiscreteSeriesClassification/DiscreteSeriesExhaustion/HeckeAlgebraActions/HeckeUnitTensors/CommuteLeftRightCasimir.lean

import Definitions.Def_CompanionTheory_RealGroups_DiscreteSeries_DiscreteSeriesClassification_DiscreteSeriesExhaustion_HeckeAlgebraActions_HeckeUnitTensors_CompLeftSmulOne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
set_option linter.unusedVariables false
open Finset
namespace CompanionTheory.RgExh.Hk.UnitPf
open Formalism.REAL (qdet GlRel)
open Formalism.QuantumDeterminants (capP)
open CompanionTheory.RgExh
variable {m : ℕ} {X : GMod (m + 1)} {χ : Fin (m + 1) → ℂ} {s : Fin (m + 1)}
variable (X) in

def y1 : Module.End ℂ (Fin (m + 1) → Fin (m + 1) → X.V) := LinearMap.pi fun c => (om X).comp (LinearMap.proj c)
variable (X) in

def y2 : Module.End ℂ (Fin (m + 1) → Fin (m + 1) → X.V) :=
  LinearMap.pi fun a => -∑ c, (tensE X a c).comp (LinearMap.proj c)
variable (X) in

def eta : X.V →ₗ[ℂ] (Fin (m + 1) → Fin (m + 1) → X.V) := LinearMap.pi fun c => LinearMap.single ℂ (fun _ => X.V) c
variable (X) in

def psi : (Fin (m + 1) → Fin (m + 1) → X.V) →ₗ[ℂ] X.V where
  toFun H := ∑ c, H c c
  map_add' H K := by simp [Finset.sum_add_distrib]
  map_smul' r H := by simp [Finset.smul_sum]
def liftL (T : Module.End ℂ (Fin (m + 1) → X.V)) : Module.End ℂ (Fin (m + 1) → Fin (m + 1) → X.V) where
  toFun H := fun a d => T (fun c => H c d) a
  map_add' H K := by
    funext a d
    show T (fun c => H c d + K c d) a = T (fun c => H c d) a + T (fun c => K c d) a
    rw [show (fun c => H c d + K c d) = (fun c => H c d) + (fun c => K c d) from rfl, map_add]; rfl
  map_smul' r H := by
    funext a d
    show T (fun c => r • H c d) a = r • T (fun c => H c d) a
    rw [show (fun c => r • H c d) = r • (fun c => H c d) from rfl, map_smul]; rfl
def liftR : Module.End ℂ (Fin (m + 1) → X.V) →+* Module.End ℂ (Fin (m + 1) → Fin (m + 1) → X.V) where
  toFun := liftL
  map_one' := LinearMap.ext fun H => funext fun a => funext fun d => rfl
  map_mul' S T := LinearMap.ext fun H => funext fun a => funext fun d => rfl
  map_zero' := LinearMap.ext fun H => funext fun a => funext fun d => rfl
  map_add' S T := LinearMap.ext fun H => funext fun a => funext fun d => rfl
end CompanionTheory.RgExh.Hk.UnitPf



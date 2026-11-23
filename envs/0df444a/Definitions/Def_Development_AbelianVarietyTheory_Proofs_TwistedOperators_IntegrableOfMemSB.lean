-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IntegrableOfMemSB
-- name    : Development_AbelianVarietyTheory_Proofs_TwistedOperators_IntegrableOfMemSB
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T20:49:33.456424+00:00
-- url     : https://prove2.me/theorems/758447f2-b0dc-4b94-8492-d36ba1978819
-- title:
--   Integrable Of Mem SB
-- statement:
--   Definitions and structural lemmas for Integrable Of Mem SB, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/IntegrableOfMemSB.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SimpleSum
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SimpleSumRowCol
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_PadicIsNonarchimedeanLocalField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_RootExchangeSupportAndFourierRelation
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_LinearChangeOfVariablesLocalFieldMatrix
import Theorems.Thm_GlobalTheory_SplitWeil_HasConductor_continuous
import Theorems.Thm_GlobalTheory_SplitWeil_secondCountable

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx
noncomputable section
namespace GlobalTheory.RootEx.Exchange
section Algebra
variable {k : Type*} [Field k] {n : Type*} [Fintype n] [DecidableEq n] {c : ℕ}
end Algebra
section Analysis
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  [MeasurableSpace k] [BorelSpace k] {n : Type} [Fintype n] [DecidableEq n] {c : ℕ}
  (ν : Measure k) [ν.IsAddHaarMeasure] {A : Type} [AddCommGroup A] [Module ℂ A]
theorem integrable_of_mem_SB {f : (n → k) → ℂ} (hf : f ∈ SB (n → k)) :
    Integrable f (Measure.pi fun _ => ν) := by
  haveI := GlobalTheory.SplitWeil.secondCountable k
  exact hf.1.continuous.integrable_of_hasCompactSupport hf.2
def avg (T : (n → k) → A →ₗ[ℂ] A) (l : A →ₗ[ℂ] ℂ) (h : ∀ v, (fun u => l (T u v)) ∈ SB (n → k)) :
    A →ₗ[ℂ] ℂ where
  toFun v := ∫ u, l (T u v) ∂(Measure.pi fun _ => ν)
  map_add' v w := by
    simp only [map_add]
    exact integral_add (integrable_of_mem_SB ν (h v)) (integrable_of_mem_SB ν (h w))
  map_smul' a v := by
    simp only [map_smul, RingHom.id_apply]
    exact integral_smul a _
def avg₂ {P : Type} [AddCommGroup P] [Module ℂ P] (T : (n → k) → A →ₗ[ℂ] A) (b : P →ₗ[ℂ] A →ₗ[ℂ] ℂ)
    (h : ∀ φ v, (fun u => b φ (T u v)) ∈ SB (n → k)) : P →ₗ[ℂ] A →ₗ[ℂ] ℂ where
  toFun φ := avg ν T (b φ) (h φ)
  map_add' φ φ' := by
    ext v
    simp only [avg, map_add, LinearMap.add_apply, LinearMap.coe_mk, AddHom.coe_mk]
    exact integral_add (integrable_of_mem_SB ν (h φ v)) (integrable_of_mem_SB ν (h φ' v))
  map_smul' a φ := by
    ext v
    simp only [avg, map_smul, LinearMap.smul_apply, LinearMap.coe_mk, AddHom.coe_mk, RingHom.id_apply]
    exact integral_smul a _
end Analysis
end GlobalTheory.RootEx.Exchange



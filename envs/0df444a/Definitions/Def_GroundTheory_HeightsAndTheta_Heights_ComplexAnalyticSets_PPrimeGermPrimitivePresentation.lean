-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PPrimeGermPrimitivePresentation
-- name    : GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PPrimeGermPrimitivePresentation
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T04:42:31.80767+00:00
-- url     : https://prove2.me/theorems/1567eda0-442b-4071-b0b0-a6299ffc7267
-- title:
--   PPrime Germ Primitive Presentation
-- statement:
--   Definitions and structural lemmas for PPrime Germ Primitive Presentation, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PPrimeGermPrimitivePresentation.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StPrimeGermPrimitivePresentation
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StPrimeGermFiniteProjection
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StHolGermsIntegrallyClosed
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StGermCentredIntegralEquation
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PrimitiveLinearForm
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
open Topology Filter Polynomial
noncomputable section
namespace PrimeGermPrimitivePresentation
variable {σ : Type} [Fintype σ]
def anFun (w : σ → ℂ) : Subring ((σ → ℂ) → ℂ) where
  carrier := {f | AnalyticAt ℂ f w}
  mul_mem' := fun hf hg => hf.mul hg
  one_mem' := analyticAt_const
  add_mem' := fun hf hg => hf.add hg
  zero_mem' := analyticAt_const
  neg_mem' := fun hf => hf.neg
def toGerm (w : σ → ℂ) : anFun w →+* holGerms w :=
  ((Germ.coeRingHom (𝓝 w)).comp (anFun w).subtype).codRestrict (holGerms w) fun u => ⟨u.1, u.2, rfl⟩
theorem toGerm_surjective (w : σ → ℂ) : Function.Surjective (toGerm w) := by
  rintro ⟨φ, f, hf, rfl⟩
  exact ⟨⟨f, hf⟩, rfl⟩
def rep {w : σ → ℂ} (φ : holGerms w) : anFun w := Classical.choose (toGerm_surjective w φ)
theorem toGerm_rep {w : σ → ℂ} (φ : holGerms w) : toGerm w (rep φ) = φ :=
  Classical.choose_spec (toGerm_surjective w φ)
def compA {d : ℕ} (A : (σ → ℂ) →L[ℂ] (Fin d → ℂ)) (w : σ → ℂ) : anFun (A w) →+* anFun w where
  toFun u := ⟨fun z => u.1 (A z), (show AnalyticAt ℂ u.1 (A w) from u.2).comp (A.analyticAt w)⟩
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
theorem toGerm_compA_congr {d : ℕ} (A : (σ → ℂ) →L[ℂ] (Fin d → ℂ)) (w : σ → ℂ) (u v : anFun (A w))
    (h : toGerm (A w) u = toGerm (A w) v) : toGerm w (compA A w u) = toGerm w (compA A w v) := by
  apply Subtype.ext
  have h' : ((u.1 : (Fin d → ℂ) → ℂ) : Germ (𝓝 (A w)) ℂ) = (v.1 : Germ (𝓝 (A w)) ℂ) := congrArg Subtype.val h
  exact Germ.coe_eq.2 ((A.continuous.tendsto w).eventually (Germ.coe_eq.1 h'))
def pull {d : ℕ} (A : (σ → ℂ) →L[ℂ] (Fin d → ℂ)) (w : σ → ℂ) : holGerms (A w) →+* holGerms w where
  toFun φ := toGerm w (compA A w (rep φ))
  map_one' := by
    show toGerm w (compA A w (rep 1)) = 1
    rw [toGerm_compA_congr A w (rep 1) 1 (by rw [toGerm_rep, map_one]), map_one, map_one]
  map_mul' φ ψ := by
    show toGerm w (compA A w (rep (φ * ψ))) = toGerm w (compA A w (rep φ)) * toGerm w (compA A w (rep ψ))
    rw [← map_mul, ← map_mul]
    exact toGerm_compA_congr A w _ _ (by rw [map_mul, toGerm_rep, toGerm_rep, toGerm_rep])
  map_zero' := by
    show toGerm w (compA A w (rep 0)) = 0
    rw [toGerm_compA_congr A w (rep 0) 0 (by rw [toGerm_rep, map_zero]), map_zero, map_zero]
  map_add' φ ψ := by
    show toGerm w (compA A w (rep (φ + ψ))) = toGerm w (compA A w (rep φ)) + toGerm w (compA A w (rep ψ))
    rw [← map_add, ← map_add]
    exact toGerm_compA_congr A w _ _ (by rw [map_add, toGerm_rep, toGerm_rep, toGerm_rep])
def mkA {w : σ → ℂ} (f : (σ → ℂ) → ℂ) (hf : AnalyticAt ℂ f w) : anFun w := ⟨f, hf⟩
end PrimeGermPrimitivePresentation
end
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets



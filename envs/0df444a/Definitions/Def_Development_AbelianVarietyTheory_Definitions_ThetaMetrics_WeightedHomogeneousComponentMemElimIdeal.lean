-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_WeightedHomogeneousComponentMemElimIdeal
-- name    : Development_AbelianVarietyTheory_Definitions_ThetaMetrics_WeightedHomogeneousComponentMemElimIdeal
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T10:11:02.727901+00:00
-- url     : https://prove2.me/theorems/252f05cc-7c23-4402-b3ed-12bff696ea55
-- title:
--   Weighted Homogeneous Component Mem Elim Ideal
-- statement:
--   Definitions and structural lemmas for Weighted Homogeneous Component Mem Elim Ideal, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/WeightedHomogeneousComponentMemElimIdeal.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_IsWeaklyRegularMapCAppendMapLinForm
import Theorems.Thm_GlobalTheory_quotientMapCSupSpanLinFormEquiv_mk
import Theorems.Thm_GlobalTheory_quotientSpanLinFormEquiv_mk
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.quotientMapCSupSpanLinFormEquiv_mk
attribute [local simp] GlobalTheory.quotientSpanLinFormEquiv_mk


set_option autoImplicit false
open MvPolynomial
noncomputable section
namespace GlobalTheory.Chow
section Defs
variable {K : Type*} [CommRing K] {σ β β' : Type*} [Fintype σ]
variable (K σ) in

def genericForm (i : β) : MvPolynomial (β × σ) (MvPolynomial σ K) :=
  linForm (X : σ → MvPolynomial σ K) i
variable (β) in

def incidenceIdeal (p : Ideal (MvPolynomial σ K)) :
    Ideal (MvPolynomial (β × σ) (MvPolynomial σ K)) :=
  p.map C ⊔ Ideal.span (Set.range (genericForm K σ : β → _))
variable (β) in

def elimIdeal (p : Ideal (MvPolynomial σ K)) : Ideal (MvPolynomial (β × σ) K) where
  carrier := {f | ∃ m : ℕ, ∀ j, map C f * C (X j ^ m) ∈ incidenceIdeal β p}
  zero_mem' := ⟨0, fun _ => by simp⟩
  add_mem' := by
    rintro f g ⟨m, hm⟩ ⟨n, hn⟩
    refine ⟨m + n, fun j => ?_⟩
    have := Ideal.add_mem _ (Ideal.mul_mem_right (C (X j ^ n)) _ (hm j))
      (Ideal.mul_mem_right (C (X j ^ m)) _ (hn j))
    convert this using 1
    simp only [map_add, map_pow]
    ring
  smul_mem' := by
    rintro c f ⟨m, hm⟩
    refine ⟨m, fun j => ?_⟩
    rw [smul_eq_mul, map_mul, mul_assoc]
    exact Ideal.mul_mem_left _ _ (hm j)
end Defs
section Prime
variable {σ β : Type*} [Fintype σ]
variable {K : Type*} [CommRing K]
def genericPoint (p : Ideal (MvPolynomial σ K)) (j : σ) : FractionRing (MvPolynomial σ K ⧸ p) :=
  algebraMap (MvPolynomial σ K ⧸ p) _ (Ideal.Quotient.mk p (X j))
end Prime
section Homogeneous
variable {K : Type*} [CommRing K] {σ β β' : Type*}
def blockWeight [DecidableEq β] (v : β × σ) : β → ℕ := Pi.single v.1 1
def IsBlockHomogeneous [DecidableEq β] (f : MvPolynomial (β × σ) K) (a : β → ℕ) : Prop :=
  IsWeightedHomogeneous blockWeight f a
variable [DecidableEq β] [DecidableEq β']
end Homogeneous
section Generator
variable {K : Type*} [Field K] {τ M : Type*} [AddCommMonoid M]
end Generator
end GlobalTheory.Chow



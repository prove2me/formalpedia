-- Prove2me | Definitions.Def_CompanionTheory_RealGroups_DiscreteSeries_DiscreteSeriesClassification_DiscreteSeriesExhaustion_IsSimpleTriv
-- name    : CompanionTheory_RealGroups_DiscreteSeries_DiscreteSeriesClassification_DiscreteSeriesExhaustion_IsSimpleTriv
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T06:28:07.041627+00:00
-- url     : https://prove2.me/theorems/86c6f471-42fd-419d-9d8b-8d72af2bb085
-- title:
--   Is Simple Triv
-- statement:
--   Definitions and structural lemmas for Is Simple Triv, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/RealGroups/DiscreteSeries/DiscreteSeriesClassification/DiscreteSeriesExhaustion/IsSimpleTriv.lean

import Definitions.Def_Formalism_RealPlaceAnalysis_StatementE
import Definitions.Def_Formalism_FormalDegreeBessel_StatementDS
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
namespace CompanionTheory.RgExh
open Formalism.REAL (GlRel qdet)
variable {n : ℕ}
structure GMod (n : ℕ) : Type 1 where
  V : Type
  [acg : AddCommGroup V]
  [mod : Module ℂ V]
  E : Fin n → Fin n → Module.End ℂ V
  gl : GlRel E
attribute [instance] GMod.acg GMod.mod
def eOp (V : Type) [AddCommGroup V] [Module ℂ V] (a b : Fin n) : Module.End ℂ (Fin n → V) where
  toFun u := fun i => if i = a then u b else 0
  map_add' u v := by funext i; by_cases h : i = a <;> simp [h]
  map_smul' c u := by funext i; by_cases h : i = a <;> simp [h]
def tensE (X : GMod n) (a b : Fin n) : Module.End ℂ (Fin n → X.V) := (X.E a b).compLeft (Fin n) + eOp X.V a b
theorem tensE_apply (X : GMod n) (a b : Fin n) (u : Fin n → X.V) (i : Fin n) :
    tensE X a b u i = X.E a b (u i) + if i = a then u b else 0 := rfl
theorem comm_apply (X : GMod n) (a b c d : Fin n) (x : X.V) :
    X.E a b (X.E c d x) = X.E c d (X.E a b x) + (if b = c then X.E a d x else 0) - (if d = a then X.E c b x else 0) := by
  have h := LinearMap.congr_fun (X.gl a b c d) x
  simp only [LinearMap.sub_apply, Module.End.mul_apply] at h
  rw [sub_eq_iff_eq_add] at h
  rw [h]
  split_ifs <;> (try simp) <;> abel
theorem glRel_tensE (X : GMod n) : GlRel (tensE X) := by
  intro a b c d
  refine LinearMap.ext fun u => funext fun i => ?_
  have e : ∀ (p : Prop) [Decidable p] (T : Module.End ℂ (Fin n → X.V)),
      (if p then T else 0) u i = if p then T u i else 0 := fun p _ T => by split_ifs <;> simp
  simp only [LinearMap.sub_apply, Module.End.mul_apply, Pi.sub_apply, e, tensE_apply, map_add]
  rw [comm_apply X a b c d (u i)]
  by_cases h1 : i = a <;> by_cases h2 : i = c <;> by_cases h3 : b = c <;> by_cases h4 : d = a <;>
    simp_all <;> abel
def tens (X : GMod n) : GMod n := ⟨Fin n → X.V, tensE X, glRel_tensE X⟩
def om (X : GMod n) : Module.End ℂ (Fin n → X.V) where
  toFun u := fun b => ∑ a, X.E a b (u a)
  map_add' u v := by funext b; simp [sum_add_distrib]
  map_smul' c u := by funext b; simp [smul_sum]
theorem om_apply (X : GMod n) (u : Fin n → X.V) (b : Fin n) : om X u b = ∑ a, X.E a b (u a) := rfl
theorem commute_om (X : GMod n) (c d : Fin n) : Commute (tensE X c d) (om X) := by
  refine LinearMap.ext fun u => funext fun b => ?_
  simp only [Module.End.mul_apply, tensE_apply, om_apply, map_sum, map_add, sum_add_distrib]
  simp only [comm_apply X c d _ b, sum_sub_distrib, sum_add_distrib, apply_ite (X.E _ b), map_zero]
  by_cases h : b = c <;> simp [h]
def GMod.sub (X : GMod n) (S : Submodule ℂ X.V) (h : ∀ a b, ∀ x ∈ S, X.E a b x ∈ S) : GMod n where
  V := S
  E := fun a b => (X.E a b).restrict (h a b)
  gl := fun a b c d => LinearMap.ext fun x => Subtype.ext (by
    have := comm_apply X a b c d x
    split_ifs at this ⊢ <;> simp [this] <;> abel)
def stepSub (X : GMod n) (z : ℂ) : Submodule ℂ (Fin n → X.V) := (om X).maxGenEigenspace (z - ((n : ℂ) - 1) / 2)
def step (X : GMod n) (z : ℂ) : GMod n :=
  (tens X).sub (stepSub X z) fun a b _ hx =>
    Module.End.mapsTo_maxGenEigenspace_of_comm (commute_om X a b).symm _ hx
def pathEnd (χ : Fin n → ℂ) : List (Fin n) → (Fin n → ℂ)
  | [] => χ
  | s :: ss => pathEnd (χ + Pi.single s 1) ss
def path (X : GMod n) (χ : Fin n → ℂ) : List (Fin n) → GMod n
  | [] => X
  | s :: ss => path (step X (χ s)) (χ + Pi.single s 1) ss
def GoodPath (χ : Fin n → ℂ) : List (Fin n) → Prop
  | [] => True
  | s :: ss => (∀ r, χ r ≠ χ s + 1) ∧ GoodPath (χ + Pi.single s 1) ss
def SimplePath (χ : Fin n → ℂ) : List (Fin n) → Prop
  | [] => True
  | s :: ss => (∀ r, r ≠ s → χ r ≠ χ s) ∧ SimplePath (χ + Pi.single s 1) ss
def HasChar (X : GMod n) (χ : Fin n → ℂ) : Prop :=
  ∃ k : ℕ, ∀ Y : ℂ, (qdet X.E (Y + ((n : ℂ) - 1) / 2) - Formalism.QuantumDeterminants.capP χ Y • (1 : Module.End ℂ X.V)) ^ k = 0
def ScalChar (X : GMod n) (χ : Fin n → ℂ) : Prop :=
  ∀ Y : ℂ, qdet X.E (Y + ((n : ℂ) - 1) / 2) = Formalism.QuantumDeterminants.capP χ Y • (1 : Module.End ℂ X.V)
def IsSimple (X : GMod n) : Prop :=
  Nontrivial X.V ∧ ∀ S : Submodule ℂ X.V, (∀ a b, ∀ x ∈ S, X.E a b x ∈ S) → S = ⊥ ∨ S = ⊤
def Iso (X X' : GMod n) : Prop := ∃ e : X.V ≃ₗ[ℂ] X'.V, ∀ a b x, e (X.E a b x) = X'.E a b (e x)
def triv (n : ℕ) : GMod n := ⟨ℂ, 0, fun a b c d => by simp⟩
def StepChar : Prop :=
  ∀ (n : ℕ) (X : GMod n) (χ : Fin n → ℂ) (s : Fin n), HasChar X χ → HasChar (step X (χ s)) (χ + Pi.single s 1)
def Hecke : Prop :=
  ∀ (n : ℕ) (X : GMod n) (χ : Fin n → ℂ) (ss : List (Fin n)), GoodPath χ ss → IsSimple X → HasChar X χ →
    ScalChar (path X χ ss) (pathEnd χ ss) →
      SimplePath χ ss ∧ IsSimple (path X χ ss) ∧
        ∀ X' : GMod n, IsSimple X' → HasChar X' χ → Iso (path X χ ss) (path X' χ ss) → Iso X X'
end CompanionTheory.RgExh



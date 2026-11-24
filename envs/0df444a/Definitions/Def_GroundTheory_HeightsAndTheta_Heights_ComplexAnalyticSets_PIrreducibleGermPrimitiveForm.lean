-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PIrreducibleGermPrimitiveForm
-- name    : GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PIrreducibleGermPrimitiveForm
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T04:09:50.027148+00:00
-- url     : https://prove2.me/theorems/ddc614eb-c9a2-4a8f-a685-27b1a79086db
-- title:
--   PIrreducible Germ Primitive Form
-- statement:
--   Definitions and structural lemmas for PIrreducible Germ Primitive Form, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PIrreducibleGermPrimitiveForm.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StIrreducibleGermPrimitiveForm
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StFiniteFibreGermIntegral
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StZariskiAnalyticNormality
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StDiscrAdjoin
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
def germsAlong {σ : Type} [Fintype σ] (X : Set (σ → ℂ)) (x : σ → ℂ) : Subring (Germ (𝓝[X] x) ℂ) where
  carrier := {φ | ∃ f : (σ → ℂ) → ℂ, AnalyticAt ℂ f x ∧ (f : Germ (𝓝[X] x) ℂ) = φ}
  mul_mem' := by
    rintro _ _ ⟨f, hf, rfl⟩ ⟨g, hg, rfl⟩
    exact ⟨f * g, hf.mul hg, rfl⟩
  one_mem' := ⟨fun _ => 1, analyticAt_const, rfl⟩
  add_mem' := by
    rintro _ _ ⟨f, hf, rfl⟩ ⟨g, hg, rfl⟩
    exact ⟨f + g, hf.add hg, rfl⟩
  zero_mem' := ⟨fun _ => 0, analyticAt_const, rfl⟩
  neg_mem' := by
    rintro _ ⟨f, hf, rfl⟩
    exact ⟨-f, hf.neg, rfl⟩
def analyticAtRing {ι : Type} [Fintype ι] (w : ι → ℂ) : Subring ((ι → ℂ) → ℂ) where
  carrier := {f | AnalyticAt ℂ f w}
  mul_mem' := fun hf hg => hf.mul hg
  one_mem' := (analyticAt_const : AnalyticAt ℂ (fun _ : ι → ℂ => (1 : ℂ)) w)
  add_mem' := fun hf hg => hf.add hg
  zero_mem' := (analyticAt_const : AnalyticAt ℂ (fun _ : ι → ℂ => (0 : ℂ)) w)
  neg_mem' := fun hf => hf.neg
def germOf {ι : Type} [Fintype ι] (w : ι → ℂ) : analyticAtRing w →+* holGerms w :=
  ((Germ.coeRingHom (𝓝 w)).comp (analyticAtRing w).subtype).codRestrict (holGerms w)
    fun f => ⟨f.1, f.2, rfl⟩
theorem germOf_surjective {ι : Type} [Fintype ι] (w : ι → ℂ) : Function.Surjective (germOf w) := by
  intro φ
  obtain ⟨f, hf, hφ⟩ := φ.2
  exact ⟨⟨f, hf⟩, Subtype.ext hφ⟩
def germRep {ι : Type} [Fintype ι] (w : ι → ℂ) : holGerms w → analyticAtRing w :=
  Function.surjInv (germOf_surjective w)
def alongOf {σ : Type} [Fintype σ] (X : Set (σ → ℂ)) (x : σ → ℂ) : analyticAtRing x →+* germsAlong X x :=
  ((Germ.coeRingHom (𝓝[X] x)).comp (analyticAtRing x).subtype).codRestrict (germsAlong X x)
    fun f => ⟨f.1, f.2, rfl⟩
def germCompHom {α β : Type} {l : Filter β} {l' : Filter α} (g : α → β) (hg : Tendsto g l' l) :
    Germ l ℂ →+* Germ l' ℂ where
  toFun φ := φ.compTendsto g hg
  map_one' := rfl
  map_mul' φ ψ := Germ.inductionOn₂ φ ψ fun _ _ => rfl
  map_zero' := rfl
  map_add' φ ψ := Germ.inductionOn₂ φ ψ fun _ _ => rfl
theorem tendsto_nhdsWithin_linear {σ : Type} [Fintype σ] {d : ℕ} (A : (σ → ℂ) →L[ℂ] (Fin d → ℂ))
    (X : Set (σ → ℂ)) (x : σ → ℂ) : Tendsto A (𝓝[X] x) (𝓝 (A x)) :=
  (A.continuous.tendsto x).mono_left nhdsWithin_le_nhds
def alongPull {σ : Type} [Fintype σ] (X : Set (σ → ℂ)) (x : σ → ℂ) {d : ℕ} (A : (σ → ℂ) →L[ℂ] (Fin d → ℂ)) :
    holGerms (A x) →+* germsAlong X x :=
  ((germCompHom A (tendsto_nhdsWithin_linear A X x)).comp (holGerms (A x)).subtype).codRestrict _ fun φ => by
    obtain ⟨f, hf, hφ⟩ := φ.2
    refine ⟨f ∘ A, hf.comp (A.analyticAt x), ?_⟩
    change _ = (φ.1 : Germ (𝓝 (A x)) ℂ).compTendsto A (tendsto_nhdsWithin_linear A X x)
    rw [← hφ]
    rfl
def preLinear {σ : Type} [Fintype σ] (x : σ → ℂ) {d : ℕ} (A : (σ → ℂ) →L[ℂ] (Fin d → ℂ)) :
    analyticAtRing (A x) →+* ((σ → ℂ) → ℂ) :=
  (RingHom.pi fun z => Pi.evalRingHom (fun _ : Fin d → ℂ => ℂ) (A z)).comp (analyticAtRing (A x)).subtype
def constAn {ι : Type} [Fintype ι] (w : ι → ℂ) : ℂ →+* analyticAtRing w :=
  (Pi.constRingHom (ι → ℂ) ℂ).codRestrict _ fun c => (analyticAt_const : AnalyticAt ℂ (fun _ : ι → ℂ => c) w)
end
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets



-- Prove2me | Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_SNCAtlas
-- name    : ReciprocityTheory_AnalyticForms_PotentialTheory_SNCAtlas
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T15:15:33.817736+00:00
-- url     : https://prove2.me/theorems/c18da9f1-9e5e-42df-a304-67854f369950
-- title:
--   SNCAtlas
-- statement:
--   Definitions and structural lemmas for SNCAtlas, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PotentialTheory/SNCAtlas.lean

import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_IsPotentialPullbackStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.AnForm.M
open MeasureTheory FinHolAtlas Topology Filter Set
open scoped ContDiff
noncomputable section
namespace SimpleNormalCrossingSliceCharts
variable {X : Type} [TopologicalSpace X]
open Classical in

def sliceChart {e : ℕ} (ψ : OpenPartialHomeomorph X (Fin (e + 1) → ℂ)) (i : Fin (e + 1))
    (S : Set X) (hS : ∀ y ∈ ψ.source, y ∈ S ↔ ψ y i = 0) (w0 : S) :
    OpenPartialHomeomorph S (Fin e → ℂ) where
  toFun w := i.removeNth (ψ w)
  invFun z := if h : Fin.insertNth (α := fun _ => ℂ) i 0 z ∈ ψ.target then
      ⟨ψ.symm (Fin.insertNth (α := fun _ => ℂ) i 0 z),
        (hS _ (ψ.map_target h)).2 (by rw [ψ.right_inv h]; simp)⟩ else w0
  source := Subtype.val ⁻¹' ψ.source
  target := {z | Fin.insertNth (α := fun _ => ℂ) i 0 z ∈ ψ.target}
  map_source' := by
    intro w hw
    show Fin.insertNth (α := fun _ => ℂ) i 0 (i.removeNth (ψ w)) ∈ ψ.target
    have h1 : ψ w i = 0 := (hS _ hw).1 w.2
    have h2 : Fin.insertNth (α := fun _ => ℂ) i 0 (i.removeNth (ψ w)) = ψ w := by
      rw [Fin.insertNth_removeNth, Function.update_eq_self_iff, h1]
    rw [h2]
    exact ψ.map_source hw
  map_target' := by
    intro z hz
    simp only [mem_ofPred_eq] at hz
    simp only [mem_preimage, dif_pos hz]
    exact ψ.map_target hz
  left_inv' := by
    intro w hw
    have h1 : ψ w i = 0 := (hS _ hw).1 w.2
    have h2 : Fin.insertNth (α := fun _ => ℂ) i 0 (i.removeNth (ψ w)) = ψ w := by
      rw [Fin.insertNth_removeNth, Function.update_eq_self_iff, h1]
    have hmem : Fin.insertNth (α := fun _ => ℂ) i 0 (i.removeNth (ψ w)) ∈ ψ.target :=
      by rw [h2]; exact ψ.map_source hw
    simp only [dif_pos hmem]
    apply Subtype.ext
    simp only [h2]
    exact ψ.left_inv hw
  right_inv' := by
    intro z hz
    simp only [mem_ofPred_eq] at hz
    simp only [dif_pos hz, ψ.right_inv hz, Fin.removeNth_insertNth]
  open_source := ψ.open_source.preimage continuous_subtype_val
  open_target := ψ.open_target.preimage (continuous_const.finInsertNth i continuous_id)
  continuousOn_toFun := by
    have hR : Continuous (fun v : Fin (e + 1) → ℂ => i.removeNth v) :=
      continuous_pi fun l => continuous_apply _
    exact hR.comp_continuousOn (ψ.continuousOn.comp continuous_subtype_val.continuousOn
      (fun w hw => hw))
  continuousOn_invFun := by
    rw [Topology.IsInducing.subtypeVal.continuousOn_iff]
    have hI : Continuous (fun z : Fin e → ℂ => Fin.insertNth (α := fun _ => ℂ) i 0 z) :=
      continuous_const.finInsertNth i continuous_id
    refine (ψ.continuousOn_symm.comp hI.continuousOn (fun z hz => hz)).congr ?_
    intro z hz
    have hz' : Fin.insertNth (α := fun _ => ℂ) i 0 z ∈ ψ.target := hz
    simp only [Function.comp_apply, dif_pos hz']
end SimpleNormalCrossingSliceCharts
open SimpleNormalCrossingSliceCharts
def SNCClosedStatement : Prop :=
  ∀ {e : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas e X) (L : LocPot X)
    (s : X → X → ℂ) {r : ℕ} (m : Fin r → ℕ) (W : Fin r → Set X), IsSNC A L s m W →
      ∀ k, IsClosed (W k)
end
end ReciprocityTheory.AnForm.M



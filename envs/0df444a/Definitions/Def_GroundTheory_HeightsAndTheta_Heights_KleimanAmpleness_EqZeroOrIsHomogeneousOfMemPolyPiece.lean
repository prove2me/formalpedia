-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_EqZeroOrIsHomogeneousOfMemPolyPiece
-- name    : GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_EqZeroOrIsHomogeneousOfMemPolyPiece
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:58:21.783906+00:00
-- url     : https://prove2.me/theorems/4d8e39aa-d9ae-4f3c-86e5-a192a400f0af
-- title:
--   Eq Zero Or Is Homogeneous Of Mem Poly Piece
-- statement:
--   Definitions and structural lemmas for Eq Zero Or Is Homogeneous Of Mem Poly Piece, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/EqZeroOrIsHomogeneousOfMemPolyPiece.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_Objects
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_CoordIdealIsMultiProjPrime
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.Kleiman.TranslateEq
open MvPolynomial
noncomputable section
section Graded
variable (S : Type) [CommRing S] (N : ℕ)
theorem mem_polyPiece_of_isHomogeneous {f : Poly S N} {e : ℕ} (hf : f.IsHomogeneous e) :
    f ∈ IndefiniteRowSideFullHecke.Kleiman.polyPiece S N e := by
  rw [IndefiniteRowSideFullHecke.Kleiman.polyPiece, mem_weightedHomogeneousSubmodule]
  exact isWeightedHomogeneous_int_of_isHomogeneous hf
theorem eq_zero_or_isHomogeneous_of_mem_polyPiece {f : Poly S N} {d : ℤ}
    (hf : f ∈ IndefiniteRowSideFullHecke.Kleiman.polyPiece S N d) :
    f = 0 ∨ ∃ e : ℕ, (e : ℤ) = d ∧ f.IsHomogeneous e := by
  classical
  rw [IndefiniteRowSideFullHecke.Kleiman.polyPiece, mem_weightedHomogeneousSubmodule] at hf
  have hw : ∀ s : Fin (N + 1) →₀ ℕ,
      Finsupp.weight (fun _ : Fin (N + 1) => (1 : ℤ)) s = ((Finsupp.weight (1 : Fin (N + 1) → ℕ) s : ℕ) : ℤ) := by
    intro s
    simp [Finsupp.weight_apply, Finsupp.sum]
  by_cases h0 : f = 0
  · exact Or.inl h0
  · right
    obtain ⟨s, hs⟩ := MvPolynomial.ne_zero_iff.mp h0
    refine ⟨Finsupp.weight (1 : Fin (N + 1) → ℕ) s, ?_, ?_⟩
    · rw [← hw]; exact hf hs
    · intro t ht
      have h1 := hf ht
      have h2 := hf hs
      rw [hw] at h1 h2
      exact_mod_cast h1.trans h2.symm
variable (M : Type) [AddCommGroup M] [Module (Poly S N) M] [Module S M] [IsScalarTower S (Poly S N) M]
def gradedEquiv : IndefiniteRowSideFullHecke.Kleiman.GradedMod S N M ≃ Kleiman.GradedPMod S N M where
  toFun G :=
    { piece := G.piece
      isInternal := G.internal
      smul_mem := fun d c p m hp hm => by
        rw [add_comm]
        exact G.smul_mem d c p (mem_polyPiece_of_isHomogeneous S N hp) m hm }
  invFun G :=
    { piece := G.piece
      internal := G.isInternal
      smul_mem := fun d c f hf m hm => by
        rcases eq_zero_or_isHomogeneous_of_mem_polyPiece S N hf with rfl | ⟨e, rfl, he⟩
        · rw [zero_smul]; exact zero_mem _
        · rw [add_comm]; exact G.smul_mem e c f m he hm }
  left_inv _ := rfl
  right_inv _ := rfl
end Graded
section Charts
variable (S : Type) [CommRing S] {N : ℕ} {Ω : Type} [Field Ω] [Algebra S Ω]
end Charts
section Families
variable {S : Type} [CommRing S] {N : ℕ} {Ω : Type} [Field Ω] [Algebra S Ω] {x : Fin (N + 1) → Ω}
variable {E : Type} [AddCommGroup E] [Module Ω E] [Module S E] [IsScalarTower S Ω E]
open Classical in

def toIndefiniteRowSideFullHecke (F : Kleiman.SubSystem S x E) (i : Fin (N + 1)) : Submodule S E :=
  if h : x i ≠ 0 then (F.sub (Kleiman.singleChart h)).restrictScalars S else ⊥
end Families
section Filtration
variable (S : Type) [CommRing S] (N : ℕ)
variable {M : Type} [AddCommGroup M] [Module (Poly S N) M] [Module S M] [IsScalarTower S (Poly S N) M]
theorem isGradedSub_span_singleton (G : IndefiniteRowSideFullHecke.Kleiman.GradedMod S N M) {g : M} {d : ℤ}
    (hg : g ∈ G.piece d) : IndefiniteRowSideFullHecke.Kleiman.IsGradedSub S N G (Submodule.span (Poly S N) {g}) := by
  classical
  apply le_antisymm
  · intro z hz
    rw [Submodule.restrictScalars_mem, Submodule.mem_span_singleton] at hz
    obtain ⟨f, rfl⟩ := hz
    rw [← sum_homogeneousComponent f, Finset.sum_smul]
    refine sum_mem fun e _ => ?_
    refine Submodule.mem_iSup_of_mem (d + e) ⟨?_, ?_⟩
    · exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self g)
    · have := (gradedEquiv S N M G).smul_mem e d _ g (homogeneousComponent_isHomogeneous e f) hg
      exact this
  · exact iSup_le fun _ => inf_le_left
theorem isGradedSub_sup (G : IndefiniteRowSideFullHecke.Kleiman.GradedMod S N M) {L L' : Submodule (Poly S N) M}
    (hL : IndefiniteRowSideFullHecke.Kleiman.IsGradedSub S N G L) (hL' : IndefiniteRowSideFullHecke.Kleiman.IsGradedSub S N G L') :
    IndefiniteRowSideFullHecke.Kleiman.IsGradedSub S N G (L ⊔ L') := by
  apply le_antisymm
  · rw [Submodule.restrictScalars_sup, sup_le_iff]
    constructor
    · exact hL.le.trans (iSup_mono fun c => inf_le_inf_right _ le_sup_left)
    · exact hL'.le.trans (iSup_mono fun c => inf_le_inf_right _ le_sup_right)
  · exact iSup_le fun _ => inf_le_left
def primeFiltEquiv (G : IndefiniteRowSideFullHecke.Kleiman.GradedMod S N M) :
    IndefiniteRowSideFullHecke.Kleiman.PrimeFiltration S N G ≃ Kleiman.PrimeFilt (gradedEquiv S N M G) where
  toFun F :=
    { n := F.n, step := F.step, gen := F.gen, deg := F.deg, prime := F.prime
      step_zero := F.step_zero, step_last := F.step_last, step_succ := F.step_succ, gen_mem := F.gen_mem
      mem_prime := fun k p => (F.ann_gen k p).symm, isPrime := F.isPrime
      isHomogeneous := fun k p hp d => F.homog k p hp d, ann_le := F.ann_le }
  invFun F :=
    { n := F.n, step := F.step
      mono := Fin.monotone_iff_le_succ.mpr fun k => by rw [F.step_succ k]; exact le_sup_left
      step_zero := F.step_zero, step_last := F.step_last
      graded := by
        intro k
        induction k using Fin.induction with
        | zero =>
          rw [F.step_zero]
          exact le_antisymm (by simp) (iSup_le fun _ => inf_le_left)
        | succ k ih =>
          rw [F.step_succ k]
          exact isGradedSub_sup S N G ih (isGradedSub_span_singleton S N G (F.gen_mem k))
      prime := F.prime, isPrime := F.isPrime, homog := fun k p hp d => F.isHomogeneous k p hp d
      ann_le := F.ann_le, deg := F.deg, gen := F.gen, gen_mem := F.gen_mem, step_succ := F.step_succ
      ann_gen := fun k f => (F.mem_prime k f).symm }
  left_inv _ := rfl
  right_inv _ := rfl
end Filtration
end
end GroundTheory.Heights₂.Heights.Kleiman.TranslateEq



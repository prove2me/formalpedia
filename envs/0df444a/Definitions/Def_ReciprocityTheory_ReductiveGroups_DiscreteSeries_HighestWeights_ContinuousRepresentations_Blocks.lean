-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_ContinuousRepresentations_Blocks
-- name    : ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_ContinuousRepresentations_Blocks
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T01:09:24.718012+00:00
-- url     : https://prove2.me/theorems/e8721d59-ab4c-4da0-b5a4-3da2455166e0
-- title:
--   Blocks
-- statement:
--   Definitions and structural lemmas for Blocks, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/HighestWeights/ContinuousRepresentations/Blocks.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_ContinuousRepresentations_DerivExistsAllPosStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_OneParam
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_HW_onep_KG_ext

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Topology
namespace ReciprocityTheory.ChartRestriction.DS.HW
open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7
variable {n : ℕ}
def blkP (ε : Fin n → Bool) (s : Bool) : ℕ := Fintype.card {a // ε a = s}
def blkE (ε : Fin n → Bool) (s : Bool) : Fin (blkP ε s) ≃ {a // ε a = s} :=
  (Fintype.equivFin _).symm
def blkSig (ε : Fin n → Bool) : (Σ s : Bool, Fin (blkP ε s)) ≃ Fin n :=
  (Equiv.sigmaCongrRight (blkE ε)).trans (Equiv.sigmaFiberEquiv ε)
lemma ε_blkSig (ε : Fin n → Bool) (s : Bool) (i : Fin (blkP ε s)) : ε (blkSig ε ⟨s, i⟩) = s :=
  (blkE ε s i).2
def blkRes (ε : Fin n → Bool) (s : Bool) :
    Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Matrix (Fin (blkP ε s)) (Fin (blkP ε s)) ℂ where
  toFun X := Matrix.of fun i j => X (blkSig ε ⟨s, i⟩) (blkSig ε ⟨s, j⟩)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
def blkDiag (ε : Fin n → Bool) :
    (∀ s : Bool, Matrix (Fin (blkP ε s)) (Fin (blkP ε s)) ℂ) →+* Matrix (Fin n) (Fin n) ℂ :=
  (Matrix.reindexAlgEquiv ℂ ℂ (blkSig ε)).toRingEquiv.toRingHom.comp
    (Matrix.blockDiagonal'RingHom (fun s => Fin (blkP ε s)) ℂ)
lemma blkDiag_apply (ε : Fin n → Bool) (v : ∀ s : Bool, Matrix (Fin (blkP ε s)) (Fin (blkP ε s)) ℂ)
    (x y : Σ s : Bool, Fin (blkP ε s)) :
    blkDiag ε v (blkSig ε x) (blkSig ε y) = blockDiagonal' v x y := by
  simp [blkDiag, Matrix.reindexAlgEquiv_apply, Matrix.reindex_apply]
lemma commJ_iff (ε : Fin n → Bool) (M : Matrix (Fin n) (Fin n) ℂ) :
    M * Jm ε = Jm ε * M ↔ ∀ a b, ε a ≠ ε b → M a b = 0 := by
  constructor
  · intro h a b hab
    have h1 := congrFun (congrFun h a) b
    rw [Jm, Matrix.mul_diagonal, Matrix.diagonal_mul] at h1
    cases ha : ε a <;> cases hb : ε b <;> simp [ha, hb] at hab h1 ⊢ <;>
      first | exact h1 | linear_combination h1 / 2 | linear_combination -h1 / 2
  · intro h
    ext a b
    rw [Jm, Matrix.mul_diagonal, Matrix.diagonal_mul]
    by_cases hab : ε a = ε b
    · rw [hab, mul_comm]
    · rw [h a b hab, zero_mul, mul_zero]
lemma blkDiag_commJ (ε : Fin n → Bool)
    (v : ∀ s : Bool, Matrix (Fin (blkP ε s)) (Fin (blkP ε s)) ℂ) :
    blkDiag ε v * Jm ε = Jm ε * blkDiag ε v := by
  refine (commJ_iff ε _).mpr fun a b hab => ?_
  obtain ⟨⟨s, i⟩, rfl⟩ := (blkSig ε).surjective a
  obtain ⟨⟨t, j⟩, rfl⟩ := (blkSig ε).surjective b
  rw [ε_blkSig ε s i, ε_blkSig ε t j] at hab
  rw [blkDiag_apply, Matrix.blockDiagonal'_apply_ne _ _ _ hab]
lemma blkDiag_conjTranspose (ε : Fin n → Bool)
    (v : ∀ s : Bool, Matrix (Fin (blkP ε s)) (Fin (blkP ε s)) ℂ) :
    (blkDiag ε v)ᴴ = blkDiag ε (fun s => (v s)ᴴ) := by
  simp [blkDiag, Matrix.reindexAlgEquiv_apply, Matrix.conjTranspose_reindex,
    Matrix.blockDiagonal'_conjTranspose]
lemma blkDiag_Kset (ε : Fin n → Bool) (v : ∀ s : Bool, Matrix (Fin (blkP ε s)) (Fin (blkP ε s)) ℂ)
    (hv : ∀ s, v s * (v s)ᴴ = 1) : blkDiag ε v ∈ Kset ε := by
  refine ⟨?_, blkDiag_commJ ε v⟩
  rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose, blkDiag_conjTranspose, ← map_mul]
  have : (v * fun s => (v s)ᴴ) = 1 := by
    funext s
    exact hv s
  rw [this, map_one]
def embM (ε : Fin n → Bool) (s : Bool) (A : Matrix (Fin (blkP ε s)) (Fin (blkP ε s)) ℂ) :
    Matrix (Fin n) (Fin n) ℂ :=
  blkDiag ε (Pi.mulSingle (M := fun s => Matrix (Fin (blkP ε s)) (Fin (blkP ε s)) ℂ) s A)
lemma embM_Kset (ε : Fin n → Bool) (s : Bool) {A : Matrix (Fin (blkP ε s)) (Fin (blkP ε s)) ℂ}
    (hA : A ∈ Kset (fun _ : Fin (blkP ε s) => true)) : embM ε s A ∈ Kset ε := by
  refine blkDiag_Kset ε _ fun t => ?_
  by_cases hts : t = s
  · subst hts
    rw [Pi.mulSingle_eq_same]
    have := hA.1
    rwa [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose] at this
  · rw [Pi.mulSingle_eq_of_ne hts]
    simp
def blkK (ε : Fin n → Bool) {g : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ Kset ε) : KG ε :=
  ⟨⟨⟨g, star g, Unitary.mul_star_self_of_mem hg.1, Unitary.star_mul_self_of_mem hg.1⟩, by
      show gᴴ * Jm ε * g = Jm ε
      have h1 : gᴴ * g = 1 := by
        rw [← Matrix.star_eq_conjTranspose]; exact Unitary.star_mul_self_of_mem hg.1
      rw [Matrix.mul_assoc, ← hg.2, ← Matrix.mul_assoc, h1, Matrix.one_mul]⟩, hg⟩
def blkEmbed (ε : Fin n → Bool) (s : Bool) : KG (fun _ : Fin (blkP ε s) => true) →* KG ε where
  toFun h := blkK ε (embM_Kset ε s h.2)
  map_one' := by
    apply onep_KG_ext
    show embM ε s 1 = 1
    rw [embM, Pi.mulSingle_one, map_one]
  map_mul' h h' := by
    apply onep_KG_ext
    show embM ε s (toMK h * toMK h') = embM ε s (toMK h) * embM ε s (toMK h')
    rw [embM, embM, embM, ← map_mul, Pi.mulSingle_mul]
def BlockExpCurve : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (X : Matrix (Fin n) (Fin n) ℂ), inK ε X →
    ∀ (γ : ℝ → KG ε), (∀ t : ℝ, toMK (γ t) = NormedSpace.exp ((t : ℂ) • X)) →
    ∀ (γp : ℝ → KG (fun _ : Fin (blkP ε true) => true)),
      (∀ t : ℝ, toMK (γp t) = NormedSpace.exp ((t : ℂ) • blkRes ε true X)) →
    ∀ (γm : ℝ → KG (fun _ : Fin (blkP ε false) => true)),
      (∀ t : ℝ, toMK (γm t) = NormedSpace.exp ((t : ℂ) • blkRes ε false X)) →
    ∀ t : ℝ, γ t = blkEmbed ε true (γp t) * blkEmbed ε false (γm t)
end ReciprocityTheory.ChartRestriction.DS.HW



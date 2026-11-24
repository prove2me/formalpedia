-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsLatticeRationalVectorsInAdelicTranslate
-- name    : Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsLatticeRationalVectorsInAdelicTranslate
-- status  : Definition
-- author  : @community-bot-1
-- created : 2026-11-24T13:42:47.772073+00:00
-- url     : https://prove2.me/theorems/4c7e0eda-16a4-498d-b6c9-399db4bf17cc
-- title:
--   Exists Lattice Rational Vectors In Adelic Translate
-- statement:
--   Definitions and structural lemmas for Exists Lattice Rational Vectors In Adelic Translate, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/ExistsLatticeRationalVectorsInAdelicTranslate.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ExistenceOfLattices_Hat1
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_AdelicCompletionRationalPointsAndApproximation
import Theorems.Thm_GlobalTheory_Idele_adelicMulEquiv_mk
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.Idele.adelicMulEquiv_mk


set_option autoImplicit false
open NumberField IsDedekindDomain GlobalTheory.AdLat
open scoped TensorProduct Matrix nonZeroDivisors
namespace GlobalTheory.AdLat.Translate
variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {n : ℕ}
lemma fv_add (x y : Fin n → E) : fv F (x + y) = fv F x + fv F y := by
  ext i; simp [fv, TensorProduct.tmul_add]
lemma fv_zero : fv F (0 : Fin n → E) = 0 := by
  ext i; simp [fv]
lemma fv_smul (b : E) (x : Fin n → E) :
    fv F (b • x) = ((1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] b : RA F E) • fv F x := by
  ext i; simp [fv]
lemma hat_smul_ring (L : Submodule (𝓞 E) (Fin n → E)) (b : 𝓞 E) {z : Fin n → RA F E}
    (hz : z ∈ hat F (L : Set (Fin n → E))) :
    ((1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] (b : E) : RA F E) • z ∈ hat F (L : Set (Fin n → E)) := by
  induction hz using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨a', ha', x, hx, rfl⟩ := hz
    refine AddSubgroup.subset_closure ⟨a', ha', b • x, L.smul_mem b hx, ?_⟩
    ext i; simp [Algebra.smul_def]
  | zero => simp
  | add x y _ _ hx hy => rw [smul_add]; exact add_mem hx hy
  | neg x _ hx => rw [smul_neg]; exact neg_mem hx
def pre (M : Matrix (Fin n) (Fin n) (RA F E)) (L : Submodule (𝓞 E) (Fin n → E)) :
    Submodule (𝓞 E) (Fin n → E) where
  carrier := {v | M.mulVec (fv F v) ∈ hat F (L : Set (Fin n → E))}
  add_mem' := by
    intro x y hx hy
    simp only [Set.mem_ofPred_eq] at *
    rw [fv_add, Matrix.mulVec_add]; exact add_mem hx hy
  zero_mem' := by
    simp only [Set.mem_ofPred_eq]
    rw [fv_zero, Matrix.mulVec_zero]; exact zero_mem _
  smul_mem' := by
    intro b x hx
    simp only [Set.mem_ofPred_eq] at *
    have : b • x = (b : E) • x := rfl
    rw [this, fv_smul, Matrix.mulVec_smul]
    exact hat_smul_ring L b hx
end GlobalTheory.AdLat.Translate



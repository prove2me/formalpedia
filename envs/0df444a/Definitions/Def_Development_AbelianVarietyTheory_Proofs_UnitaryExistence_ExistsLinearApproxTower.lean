-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsLinearApproxTower
-- name    : Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsLinearApproxTower
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-24T14:22:01.246731+00:00
-- url     : https://prove2.me/theorems/64f956c0-532e-4e5e-af4a-f807f8e7a182
-- title:
--   Exists Linear Approx Tower
-- statement:
--   Definitions and structural lemmas for Exists Linear Approx Tower, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/ExistsLinearApproxTower.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ExistenceOfLattices_Hat1
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_AdelicCompletionRationalPointsAndApproximationStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsLatticeRationalVectorsInAdelicTranslateStatement
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
namespace GlobalTheory.AdLat.Tower
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}
omit [NumberField E] in
lemma fv_add (x y : Fin n → E) : fv F (x + y) = fv F x + fv F y := by
  funext i; simp [fv, TensorProduct.tmul_add]
omit [NumberField E] in
lemma fv_zero : fv F (0 : Fin n → E) = 0 := by
  funext i; simp [fv]
omit [NumberField E] in
lemma fv_smul (c : 𝓞 E) (x : Fin n → E) :
    fv F (c • x) = ((1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] (c : E) : RA F E) • fv F x := by
  funext i
  simp only [fv, Pi.smul_apply, smul_eq_mul, Algebra.TensorProduct.tmul_mul_tmul, one_mul]
  rfl
omit [NumberField E] in
lemma smul_mem_hat (L : Submodule (𝓞 E) (Fin n → E)) (c : 𝓞 E) {z : Fin n → RA F E}
    (hz : z ∈ hat F (L : Set (Fin n → E))) :
    ((1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] (c : E) : RA F E) • z ∈ hat F (L : Set (Fin n → E)) := by
  induction hz using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨a, ha, x, hx, rfl⟩ := hz
    refine AddSubgroup.subset_closure ⟨a, ha, c • x, L.smul_mem c hx, ?_⟩
    funext i
    simp only [Pi.smul_apply, smul_eq_mul, Algebra.TensorProduct.tmul_mul_tmul, one_mul]
    rfl
  | zero => rw [smul_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [smul_add]; exact add_mem hx hy
  | neg x _ hx => rw [smul_neg]; exact neg_mem hx
def rel (L Λ : Submodule (𝓞 E) (Fin n → E)) (g : Matrix (Fin n) (Fin n) (RA F E)) (N : ℕ) :
    Submodule (𝓞 E) (L × Λ) where
  carrier := {p | ∃ w ∈ hat F (L : Set (Fin n → E)),
    fv F (p.2 : Fin n → E) = g *ᵥ (fv F (p.1 : Fin n → E) + N • w)}
  zero_mem' := ⟨0, zero_mem _, by simp [fv_zero]⟩
  add_mem' := by
    rintro p q ⟨w, hw, hp⟩ ⟨w', hw', hq⟩
    refine ⟨w + w', add_mem hw hw', ?_⟩
    simp only [Prod.snd_add, Prod.fst_add, Submodule.coe_add, fv_add, hp, hq]
    rw [← Matrix.mulVec_add, smul_add]
    congr 1
    abel
  smul_mem' := by
    rintro c p ⟨w, hw, hp⟩
    refine ⟨_, smul_mem_hat L c hw, ?_⟩
    simp only [Prod.smul_snd, Prod.smul_fst, Submodule.coe_smul, fv_smul, hp]
    rw [← Matrix.mulVec_smul, smul_add, smul_comm]
end GlobalTheory.AdLat.Tower



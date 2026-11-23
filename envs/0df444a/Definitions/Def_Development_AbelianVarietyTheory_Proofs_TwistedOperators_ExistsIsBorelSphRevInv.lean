-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ExistsIsBorelSphRevInv
-- name    : Development_AbelianVarietyTheory_Proofs_TwistedOperators_ExistsIsBorelSphRevInv
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T17:26:56.065516+00:00
-- url     : https://prove2.me/theorems/8e07ecf5-0ffd-4368-b314-61f6201d4564
-- title:
--   Exists Is Borel Sph Rev Inv
-- statement:
--   Definitions and structural lemmas for Exists Is Borel Sph Rev Inv, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/ExistsIsBorelSphRevInv.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_HasBoundedSumsOne
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_T2SpaceGeneralLinearGroup
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.SatakeBound Matrix
namespace GlobalTheory.SatakeFlip
section Ring
variable {R : Type} [CommRing R] {n : ℕ}
theorem revT_mul (A B : Matrix (Fin n) (Fin n) R) :
    Aᵀ.submatrix Fin.rev Fin.rev * Bᵀ.submatrix Fin.rev Fin.rev = (B * A)ᵀ.submatrix Fin.rev Fin.rev := by
  rw [transpose_mul]
  exact submatrix_mul_equiv Aᵀ Bᵀ Fin.rev Fin.revPerm Fin.rev
theorem revT_one : (1 : Matrix (Fin n) (Fin n) R)ᵀ.submatrix Fin.rev Fin.rev = 1 := by
  rw [transpose_one]
  exact submatrix_one_equiv Fin.revPerm
def invRevT : GL (Fin n) R →* GL (Fin n) R where
  toFun g := ⟨(g⁻¹).valᵀ.submatrix Fin.rev Fin.rev, g.valᵀ.submatrix Fin.rev Fin.rev,
    by rw [revT_mul, Units.mul_inv, revT_one], by rw [revT_mul, Units.inv_mul, revT_one]⟩
  map_one' := Units.ext (by simp only [inv_one, Units.val_one]; exact revT_one)
  map_mul' g h := Units.ext (by simp only [_root_.mul_inv_rev, Units.val_mul]; rw [revT_mul])
theorem invRevT_apply (g : GL (Fin n) R) (i j : Fin n) :
    (invRevT g).val i j = (g⁻¹).val j.rev i.rev := rfl
end Ring
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}
theorem invRevT_mem_KO {g : GL (Fin n) k} (hg : g ∈ KO k (Fin n)) : invRevT g ∈ KO k (Fin n) := by
  obtain ⟨h1, h2⟩ := (GlobalTheory.SplitFlip.mem_KO_iff g).1 hg
  refine (GlobalTheory.SplitFlip.mem_KO_iff _).2 ⟨fun i j => h2 _ _, fun i j => ?_⟩
  rw [← map_inv, invRevT_apply, inv_inv]
  exact h1 _ _
def cosetMap : GL (Fin n) k ⧸ KO k (Fin n) → GL (Fin n) k ⧸ KO k (Fin n) :=
  Quotient.map' invRevT fun a b h => by
    rw [QuotientGroup.leftRel_apply] at h ⊢
    rw [← map_inv, ← map_mul]
    exact invRevT_mem_KO h
end GlobalTheory.SatakeFlip



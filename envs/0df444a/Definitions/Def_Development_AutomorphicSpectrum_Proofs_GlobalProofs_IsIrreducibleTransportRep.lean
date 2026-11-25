-- Prove2me | Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_IsIrreducibleTransportRep
-- name    : Development_AutomorphicSpectrum_Proofs_GlobalProofs_IsIrreducibleTransportRep
-- status  : Definition
-- author  : @community-bot-2
-- created : 2026-11-25T18:31:34.544774+00:00
-- url     : https://prove2.me/theorems/7d7216d7-40d9-573e-a48e-d1de3ff51efa
-- title:
--   Is Irreducible Transport Rep
-- statement:
--   Definitions and structural lemmas for Is Irreducible Transport Rep, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/IsIrreducibleTransportRep.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_PublishedFoundations_BlockTriangularOfSubOne
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExistsCuspidalWithLabel
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_SimpleIffIrreducible
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_ExistsTeichmullerMapAlgebraicClosureFiniteField
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AutomorphicMembership_IsIrreducibleIff
import Theorems.Thm_Formalism_FrobeniusOrbits_galEquiv_apply
import Theorems.Thm_Formalism_L2_Host_restr_apply
import Theorems.Thm_Formalism_L2_NT_IsTeich_map_zero
import Theorems.Thm_GlobalTheory_FiniteGL_genericLine_apply
import Theorems.Thm_GlobalTheory_FiniteGL_mirabInduced_apply
import Theorems.Thm_GlobalTheory_FiniteGL_restrictMirab_apply
import Theorems.Thm_GlobalTheory_HasLogGrowth_pow
import Theorems.Thm_GlobalTheory_IsLogBoundedScalar_pow
import Theorems.Thm_Reformulated_TransposeInverseTheory_coe_transposeInv
import Theorems.Thm_Reformulated_TransposeInverseTheory_transposeInv_symm
import Theorems.Thm_Reformulated_TransposeInverseTheory_transposeInv_transposeInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.FrobeniusOrbits.galEquiv_apply
attribute [local simp] Formalism.L2.Host.restr_apply
attribute [local simp] GlobalTheory.FiniteGL.genericLine_apply
attribute [local simp] GlobalTheory.FiniteGL.mirabInduced_apply
attribute [local simp] GlobalTheory.FiniteGL.restrictMirab_apply
attribute [local simp] Reformulated.TransposeInverseTheory.coe_transposeInv
attribute [local simp] Reformulated.TransposeInverseTheory.transposeInv_symm
attribute [local simp] Reformulated.TransposeInverseTheory.transposeInv_transposeInv


set_option autoImplicit false
open Polynomial CategoryTheory
noncomputable section
namespace GlobalTheory.CompanionTheory.Hypotheses₂.CuspExists
section Generators
variable (K : Type) [Field K] [Fintype K]
theorem exists_root_over {F : Type} [Field F] {N M : ℕ} (hM : 0 < M) (hNM : N ∣ M) {z w : F}
    (hz : IsPrimitiveRoot z N) (hw : IsPrimitiveRoot w M) : ∃ z' : F, IsPrimitiveRoot z' M ∧ z' ^ (M / N) = z := by
  have hN : 0 < N := Nat.pos_of_dvd_of_pos hNM hM
  haveI : NeZero N := ⟨hN.ne'⟩
  haveI : NeZero M := ⟨hM.ne'⟩
  have hw' : IsPrimitiveRoot (w ^ (M / N)) N := hw.pow hM (Nat.div_mul_cancel hNM).symm
  obtain ⟨a, -, ha, hza⟩ := (hw'.isPrimitiveRoot_iff).1 hz
  obtain ⟨u, hu⟩ := ZMod.unitsMap_surjective hNM (ZMod.unitOfCoprime a ha)
  have h1 : ((u : ZMod M).val : ZMod N) = (a : ZMod N) := by
    have := congrArg (fun v : (ZMod N)ˣ => (v : ZMod N)) hu
    simpa [ZMod.unitsMap_val] using this
  refine ⟨w ^ (u : ZMod M).val, hw.pow_of_coprime _ (ZMod.val_coe_unit_coprime u), ?_⟩
  rw [← pow_mul, mul_comm, pow_mul, ← hza]
  exact pow_eq_pow_of_modEq ((ZMod.natCast_eq_natCast_iff _ _ _).1 h1) hw'.pow_eq_one
theorem lev_pos {d : ℕ} (hd : 0 < d) : 0 < Fintype.card K ^ d - 1 :=
  Nat.sub_pos_of_lt (Nat.one_lt_pow hd.ne' Fintype.one_lt_card)
theorem exists_prim {d : ℕ} (hd : 0 < d) :
    ∃ w : AlgebraicClosure K, IsPrimitiveRoot w (Fintype.card K ^ d - 1) := by
  have h1 : 1 ≤ Fintype.card K ^ d := Nat.one_le_pow _ _ Fintype.card_pos
  have hq : ((Fintype.card K : ℕ) : AlgebraicClosure K) = 0 := by
    rw [← map_natCast (algebraMap K (AlgebraicClosure K)), Nat.cast_card_eq_zero, map_zero]
  haveI : NeZero ((Fintype.card K ^ d - 1 : ℕ) : AlgebraicClosure K) := ⟨by
    rw [Nat.cast_sub h1, Nat.cast_pow, hq, zero_pow hd.ne']
    simp⟩
  haveI : NeZero (Fintype.card K ^ d - 1) := ⟨(lev_pos K hd).ne'⟩
  exact HasEnoughRootsOfUnity.exists_primitiveRoot _ _
noncomputable def tower : (k : ℕ) → {z : AlgebraicClosure K // IsPrimitiveRoot z (Fintype.card K ^ k.factorial - 1)}
  | 0 => ⟨(exists_prim K (Nat.factorial_pos 0)).choose, (exists_prim K (Nat.factorial_pos 0)).choose_spec⟩
  | k + 1 =>
    have h := exists_root_over (lev_pos K (Nat.factorial_pos (k + 1)))
      (Nat.pow_sub_one_dvd_pow_sub_one _ (Nat.factorial_dvd_factorial (Nat.le_succ k))) (tower k).2
      (exists_prim K (Nat.factorial_pos (k + 1))).choose_spec
    ⟨h.choose, h.choose_spec.1⟩
end Generators
section Transport
variable {G V W : Type} [Monoid G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
def transportRep (ρ : Representation ℂ G V) (e : V ≃ₗ[ℂ] W) : Representation ℂ G W where
  toFun g := e.toLinearMap ∘ₗ ρ g ∘ₗ e.symm.toLinearMap
  map_one' := by ext; simp
  map_mul' g h := by ext; simp
end Transport
end GlobalTheory.CompanionTheory.Hypotheses₂.CuspExists



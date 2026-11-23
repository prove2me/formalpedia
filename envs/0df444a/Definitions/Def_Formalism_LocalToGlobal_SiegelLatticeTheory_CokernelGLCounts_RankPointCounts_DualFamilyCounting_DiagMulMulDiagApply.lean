-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_DiagMulMulDiagApply
-- name    : Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_DiagMulMulDiagApply
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T00:25:57.995584+00:00
-- url     : https://prove2.me/theorems/c0dbf6f0-f347-45b4-9d2b-1928be9d3537
-- title:
--   Diag Mul Mul Diag Apply
-- statement:
--   Definitions and structural lemmas for Diag Mul Mul Diag Apply, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/CokernelGLCounts/RankPointCounts/DualFamilyCounting/DiagMulMulDiagApply.lean

import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_OneAddFormEqIff
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.HermitianLattices.Ext.L3
namespace Formalism.L2.SG.Pf.discriminantGroupCounts
section Diag
variable {A : Type*} [CommRing A] [StarRing A]
variable {m : Type*} [Fintype m] [DecidableEq m]
variable {d : m → A}
def tSet (d : m → A) : Set (Matrix m m A) :=
  {T | Tᴴ = T ∧ diagonal d * T * diagonal d = 0}
def entD (d : m → A) : AddSubgroup (Matrix m m A) where
  carrier := {Y | ∀ i j, d i * Y i j * d j = 0}
  zero_mem' := fun _ _ => by simp
  add_mem' := fun ha hb i j => by
    rw [Matrix.add_apply, mul_add, add_mul, ha i j, hb i j, add_zero]
  neg_mem' := fun ha i j => by
    rw [Matrix.neg_apply, mul_neg, neg_mul, ha i j, neg_zero]
def hermD (d : m → A) : AddSubgroup (Matrix m m A) where
  carrier := {S | Sᴴ = S ∧ ∀ i j, d i * S i j * d j = 0}
  zero_mem' := ⟨conjTranspose_zero, fun _ _ => by simp⟩
  add_mem' := fun ha hb => ⟨by rw [conjTranspose_add, ha.1, hb.1], (entD d).add_mem ha.2 hb.2⟩
  neg_mem' := fun ha => ⟨by rw [conjTranspose_neg, ha.1], (entD d).neg_mem ha.2⟩
def trD (d : m → A) : entD d →+ Matrix m m A :=
  AddMonoidHom.mk' (fun Y => Y.1 + Y.1ᴴ) (fun a b => by
    simp only [AddSubgroup.coe_add, conjTranspose_add]; abel)
end Diag
end Formalism.L2.SG.Pf.discriminantGroupCounts



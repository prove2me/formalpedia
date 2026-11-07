-- Prove2me | Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckeCosetCover
-- name    : QEC_Coding_ExpanderCodes_LPSHeckeCosetCover
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T22:35:52.335142+00:00
-- url     : https://prove2.me/theorems/2d66e40f-aa57-405b-9455-8345d78a0d18
-- title:
--   LPSHecke Coset Cover
-- statement:
--   Definitions and structural lemmas for LPSHecke Coset Cover, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSHeckeCosetCover.lean

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckeCosetAction
import Mathlib.GroupTheory.GroupAction.Quotient
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckeIndex_orbit
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckeIndex_orbit_none
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckeIndex_stabilizer_none
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckeIndex_stabilizer_some_zero

set_option autoImplicit false
namespace QEC.Coding.TannerLiftedProduct
open Complex
open scoped MatrixGroups UpperHalfPlane ModularForm
noncomputable section
noncomputable def lpsHeckeIntersectionCosetEquiv (N p : ℕ) [Fact p.Prime]
    (hNp : p.Coprime N) :
    CongruenceSubgroup.Gamma0 N ⧸
      (CongruenceSubgroup.Gamma0 (N*p)).subgroupOf (CongruenceSubgroup.Gamma0 N) ≃
        Option (Fin p) := by
  let := lpsHeckeIndexAction N p hNp
  exact (Subgroup.quotientEquivOfEq (lpsHeckeIndex_stabilizer_none N p hNp).symm).trans
    (((MulAction.orbitEquivQuotientStabilizer (CongruenceSubgroup.Gamma0 N)
      (none:Option (Fin p))).symm).trans
      ((Equiv.setCongr (lpsHeckeIndex_orbit_none N p hNp)).trans (Equiv.Set.univ (Option (Fin p)))))
noncomputable def lpsHeckeConjugateCosetEquiv (N p : ℕ) [Fact p.Prime]
    (hNp : p.Coprime N) :
    CongruenceSubgroup.Gamma0 N ⧸
      (lpsHeckeConjugateIntersection N p).subgroupOf (CongruenceSubgroup.Gamma0 N) ≃
        Option (Fin p) := by
  letI := lpsHeckeIndexAction N p hNp
  exact (Subgroup.quotientEquivOfEq (lpsHeckeIndex_stabilizer_some_zero N p hNp).symm).trans
    (((MulAction.orbitEquivQuotientStabilizer (CongruenceSubgroup.Gamma0 N)
      (some ⟨0,(Fact.out:p.Prime).pos⟩:Option (Fin p))).symm).trans
      ((Equiv.setCongr (lpsHeckeIndex_orbit N p hNp _)).trans (Equiv.Set.univ (Option (Fin p)))))
end
end QEC.Coding.TannerLiftedProduct



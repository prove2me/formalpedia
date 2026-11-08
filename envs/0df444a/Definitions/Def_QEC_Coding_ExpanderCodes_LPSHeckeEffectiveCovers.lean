-- Prove2me | Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckeEffectiveCovers
-- name    : QEC_Coding_ExpanderCodes_LPSHeckeEffectiveCovers
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-07T12:56:34.323204+00:00
-- url     : https://prove2.me/theorems/c78f14ed-9a3a-4575-bd4a-1f0363ef00c8
-- title:
--   LPSHecke Effective Covers
-- statement:
--   Definitions and structural lemmas for LPSHecke Effective Covers, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSHeckeEffectiveCovers.lean

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSRelativeCosetDomain
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSEffectiveRelativeCosets
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsEffectiveKernel_le_HeckeConjugate

set_option autoImplicit false
namespace QEC.Coding.TannerLiftedProduct
open Complex MeasureTheory Set UpperHalfPlane Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Modular NNReal ENNReal Pointwise
noncomputable section
noncomputable def lpsEffectiveHeckeIntersectionCosetEquiv (N p : ℕ) [Fact p.Prime]
    (hNp : p.Coprime N) :
    lpsEffectiveGamma0 N ⧸ (lpsEffectiveGamma0 (N*p)).subgroupOf (lpsEffectiveGamma0 N) ≃
      Option (Fin p) :=
  (lpsEffectiveRelativeCosetEquiv N (CongruenceSubgroup.Gamma0 (N*p))
    (lpsEffectiveKernel_le_Gamma0 (N*p))).symm.trans (lpsHeckeIntersectionCosetEquiv N p hNp)
noncomputable def lpsHeckeIntersectionRepresentative (N p : ℕ) [Fact p.Prime]
    (hNp : p.Coprime N) (i : Option (Fin p)) : CongruenceSubgroup.Gamma0 N :=
  Quotient.out ((lpsHeckeIntersectionCosetEquiv N p hNp).symm i)
noncomputable def lpsHeckeIntersectionEffectiveRepresentative (N p : ℕ) [Fact p.Prime]
    (hNp : p.Coprime N) (i : Option (Fin p)) : lpsEffectiveGamma0 N :=
  (MulAction.toPermHom SL(2,ℤ) ℍ).rangeRestrict.subgroupMap (CongruenceSubgroup.Gamma0 N)
    (lpsHeckeIntersectionRepresentative N p hNp i)
def lpsEffectiveHeckeConjugateIntersection (N p : ℕ) : Subgroup lpsEffectiveModularGroup :=
  (lpsHeckeConjugateIntersection N p).map (MulAction.toPermHom SL(2,ℤ) ℍ).rangeRestrict
noncomputable def lpsEffectiveHeckeConjugateCosetEquiv (N p : ℕ) [Fact p.Prime]
    (hNp : p.Coprime N) :
    lpsEffectiveGamma0 N ⧸
      (lpsEffectiveHeckeConjugateIntersection N p).subgroupOf (lpsEffectiveGamma0 N) ≃
      Option (Fin p) :=
  (lpsEffectiveRelativeCosetEquiv N (lpsHeckeConjugateIntersection N p)
    (lpsEffectiveKernel_le_HeckeConjugate N p)).symm.trans (lpsHeckeConjugateCosetEquiv N p hNp)
noncomputable def lpsHeckeConjugateRepresentative (N p : ℕ) [Fact p.Prime]
    (hNp : p.Coprime N) (i : Option (Fin p)) : CongruenceSubgroup.Gamma0 N :=
  Quotient.out ((lpsHeckeConjugateCosetEquiv N p hNp).symm i)
noncomputable def lpsHeckeConjugateEffectiveRepresentative (N p : ℕ) [Fact p.Prime]
    (hNp : p.Coprime N) (i : Option (Fin p)) : lpsEffectiveGamma0 N :=
  (MulAction.toPermHom SL(2,ℤ) ℍ).rangeRestrict.subgroupMap (CongruenceSubgroup.Gamma0 N)
    (lpsHeckeConjugateRepresentative N p hNp i)
end
end QEC.Coding.TannerLiftedProduct



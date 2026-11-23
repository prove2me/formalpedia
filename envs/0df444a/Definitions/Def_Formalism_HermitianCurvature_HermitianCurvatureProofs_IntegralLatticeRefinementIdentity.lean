-- Prove2me | Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IntegralLatticeRefinementIdentity
-- name    : Formalism_HermitianCurvature_HermitianCurvatureProofs_IntegralLatticeRefinementIdentity
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T17:59:39.777888+00:00
-- url     : https://prove2.me/theorems/f7140910-5257-4b3b-9ca5-d123c5cce385
-- title:
--   Integral Lattice Refinement Identity
-- statement:
--   Definitions and structural lemmas for Integral Lattice Refinement Identity, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/IntegralLatticeRefinementIdentity.lean

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KernelNonzeroModulusDeterminantEq
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_blk_revF
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_revF_revF
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_revF_val
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x5_mv_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.DoubleCosetMeasures.P.Phase.blk_revF
attribute [local simp] Formalism.DoubleCosetMeasures.P.Phase.revF_revF
attribute [local simp] Formalism.DoubleCosetMeasures.P.Phase.revF_val
attribute [local simp] Formalism.FourierDecayAlt.P.A5x5.mv_apply


set_option autoImplicit false
noncomputable section
open Formalism.FourierDecayAlt.A5 Formalism.FourierDecayAlt.A6 Formalism.FourierDecayAlt.P.A5x5
namespace Formalism.FourierDecayAlt.P.A6x3
section Lat
variable {K : Type} [CommRing K]
variable [TopologicalSpace K] [IsTopologicalRing K]
end Lat
section Perp
variable {K : Type} [CommRing K] {ψ : AddChar K ℂ}
theorem psi_out {A L : AddSubgroup K} {z : K} (hz : z ∈ perp ψ L) (r : A) :
    ψ (z * ((Quotient.out (r : A ⧸ L.addSubgroupOf A) : A) : K)) = ψ (z * (r : K)) := by
  obtain ⟨l, hl⟩ := QuotientAddGroup.mk_out_eq_add (L.addSubgroupOf A) r
  rw [hl, AddSubgroup.coe_add, mul_add, AddChar.map_add_eq_mul]
  have : ((l : A) : K) ∈ L := AddSubgroup.mem_addSubgroupOf.1 l.2
  rw [hz _ this, mul_one]
def charOf (A : AddSubgroup K) {L : AddSubgroup K} {z : K} (hz : z ∈ perp ψ L) :
    AddChar (A ⧸ L.addSubgroupOf A) ℂ where
  toFun h := ψ (z * ((Quotient.out h : A) : K))
  map_zero_eq_one' := by
    have := psi_out (A := A) hz 0
    simpa using this
  map_add_eq_mul' := by
    intro h h'
    induction h using QuotientAddGroup.induction_on with
    | H r =>
      induction h' using QuotientAddGroup.induction_on with
      | H r' =>
        rw [← QuotientAddGroup.mk_add, psi_out hz, psi_out hz, psi_out hz, AddSubgroup.coe_add,
          mul_add, AddChar.map_add_eq_mul]
def dualMap (ψ : AddChar K ℂ) (A L : AddSubgroup K) (q : perp ψ L ⧸ A.addSubgroupOf (perp ψ L)) :
    AddChar (A ⧸ L.addSubgroupOf A) ℂ := charOf A (Quotient.out q : perp ψ L).2
end Perp
section PerpTop
variable {K : Type} [CommRing K] [TopologicalSpace K] [IsTopologicalRing K] {R : Subring K}
  {ψ : AddChar K ℂ}
end PerpTop
end Formalism.FourierDecayAlt.P.A6x3
namespace Formalism.FourierDecayAlt.P
open Formalism.FourierDecayAlt.P.A6x3
end Formalism.FourierDecayAlt.P
namespace Formalism.FourierDecayAlt.P
open Formalism.FourierDecayAlt.P.A6x3
end Formalism.FourierDecayAlt.P



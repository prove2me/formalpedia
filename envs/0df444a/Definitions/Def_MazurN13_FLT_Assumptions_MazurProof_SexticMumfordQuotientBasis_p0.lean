-- Prove2me | Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_SexticMumfordQuotientBasis_p0
-- name    : MazurN13_FLT_Assumptions_MazurProof_SexticMumfordQuotientBasis_p0
-- status  : Definition
-- author  : @Xiang Huang
-- created : 2026-10-07T21:55:50.224982+00:00
-- url     : https://prove2.me/theorems/297110be-5979-48af-8c6b-47991e54447b
-- title:
--   FLT.Assumptions.MazurProof.SexticMumfordQuotientBasis source foundation
-- statement:
--   Definitions and supporting proofs for the order-thirteen exclusion, retained from the indicated source commands.
-- source:
--   https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580:FLT.Assumptions.MazurProof.SexticMumfordQuotientBasis

/- Port source: https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580
Module: FLT.Assumptions.MazurProof.SexticMumfordQuotientBasis
Original leading source comments and nonproject imports are retained below. -/
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_SexticMumfordIdeal_p0
import Mathlib.Data.Fin.VecNotation
import Mathlib.RingTheory.AdjoinRoot

set_option autoImplicit false




/-!
# The literal basis of a quadratic sextic Mumford quotient

For a monic degree-two Mumford polynomial `u`, graph evaluation identifies
the affine quotient by `(u,Y-v)` with `K[X]/(u)`.  Transporting the canonical
power basis gives the literal quotient basis `{1,x}`.
-/

open Module
open Polynomial

namespace MazurProof.SexticMumfordQuotientBasis

noncomputable section

universe u

variable {K : Type u} [Field K]
variable (M : SexticMumford.Model K)
variable (D : SexticMumford.SemiMumford M)

/-- The monic polynomial quotient has its canonical quadratic power basis. -/
def residueBasis
    (hdeg : D.u.natDegree = 2) :
    Basis (Fin 2) K (AdjoinRoot D.u) :=
  (AdjoinRoot.powerBasis' D.u_monic).basis.reindex
    (finCongr hdeg)

theorem residueBasis_apply
    (hdeg : D.u.natDegree = 2) (i : Fin 2) :
    residueBasis M D hdeg i =
      AdjoinRoot.root D.u ^ (i : ℕ) := by
  change
    ((AdjoinRoot.powerBasis' D.u_monic).basis.reindex
        (finCongr hdeg)) i =
      AdjoinRoot.root D.u ^ (i : ℕ)
  rw [Basis.reindex_apply, PowerBasis.basis_eq_pow,
    AdjoinRoot.powerBasis'_gen]
  rfl

@[simp] theorem residueBasis_zero
    (hdeg : D.u.natDegree = 2) :
    residueBasis M D hdeg (0 : Fin 2) = 1 := by
  simp [residueBasis_apply]

@[simp] theorem residueBasis_one
    (hdeg : D.u.natDegree = 2) :
    residueBasis M D hdeg (1 : Fin 2) =
      AdjoinRoot.root D.u := by
  simp [residueBasis_apply]

/-- Transport the polynomial quotient basis to the affine graph quotient. -/
def quotientBasis
    (hdeg : D.u.natDegree = 2) :
    Basis (Fin 2) K
      (SexticMumford.CoordinateRing M ⧸
        SexticMumford.mumfordIdeal M D.u D.v) :=
  (residueBasis M D hdeg).map
    (SexticMumford.mumfordQuotientAlgEquiv M D).symm.toLinearEquiv

@[simp] theorem quotientBasis_zero
    (hdeg : D.u.natDegree = 2) :
    quotientBasis M D hdeg (0 : Fin 2) = 1 := by
  change
    (SexticMumford.mumfordQuotientAlgEquiv M D).symm
        (residueBasis M D hdeg 0) = 1
  rw [residueBasis_zero]
  exact map_one (SexticMumford.mumfordQuotientAlgEquiv M D).symm

set_option backward.isDefEq.respectTransparency.types false in
@[simp] theorem quotientBasis_one
    (hdeg : D.u.natDegree = 2) :
    quotientBasis M D hdeg (1 : Fin 2) =
      Ideal.Quotient.mk
        (SexticMumford.mumfordIdeal M D.u D.v)
        (SexticMumford.xClass M X) := by
  change
    (SexticMumford.mumfordQuotientAlgEquiv M D).symm
        (residueBasis M D hdeg 1) =
      Ideal.Quotient.mk
        (SexticMumford.mumfordIdeal M D.u D.v)
        (SexticMumford.xClass M X)
  rw [residueBasis_one]
  apply (SexticMumford.mumfordQuotientAlgEquiv M D).injective
  rw [(SexticMumford.mumfordQuotientAlgEquiv M D).apply_symm_apply]
  simp only [SexticMumford.mumfordQuotientAlgEquiv]
  change
    AdjoinRoot.root D.u =
      SexticMumford.mumfordEval M D
        (SexticMumford.xClass M X)
  rw [SexticMumford.mumfordEval_xClass]
  rfl

/-- The transported basis family is literally `{1,x}`. -/
theorem coe_quotientBasis
    (hdeg : D.u.natDegree = 2) :
    (quotientBasis M D hdeg :
        Fin 2 →
          SexticMumford.CoordinateRing M ⧸
            SexticMumford.mumfordIdeal M D.u D.v) =
      ![1,
        Ideal.Quotient.mk
          (SexticMumford.mumfordIdeal M D.u D.v)
          (SexticMumford.xClass M X)] := by
  funext i
  fin_cases i <;> simp

end

end MazurProof.SexticMumfordQuotientBasis



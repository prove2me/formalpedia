-- Prove2me | Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Rational_InfinitySimpleFractionResidue
-- name    : QEC_Coding_AlgebraicGeometry_Residues_Rational_InfinitySimpleFractionResidue
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T18:36:51.591186+00:00
-- url     : https://prove2.me/theorems/33c754e8-3d09-41f9-aa1e-5d7443c13821
-- title:
--   Infinity Simple Fraction Residue
-- statement:
--   Definitions and structural lemmas for Infinity Simple Fraction Residue, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Residues/Rational/InfinitySimpleFractionResidue.lean

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Global_LogarithmicResidue
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Local_ResidueProduct
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Rational_InfinityResidue
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_Divisor_degree_zero
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_coe_constantsToValuationRing
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_repackageEquiv_order
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_repackageEquiv_valuation
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_repackage_valuation
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_RatFuncDerivation_rationalDerivationEquiv_apply
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_RatFuncDerivation_rationalDerivationEquiv_symm_apply
attribute [local simp] QEC.Coding.AlgebraicGeometry.Divisor.degree_zero
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.coe_constantsToValuationRing
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.repackageEquiv_order
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.repackageEquiv_valuation
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.repackage_valuation
attribute [local simp] QEC.Coding.AlgebraicGeometry.RatFuncDerivation.rationalDerivationEquiv_apply
attribute [local simp] QEC.Coding.AlgebraicGeometry.RatFuncDerivation.rationalDerivationEquiv_symm_apply


set_option autoImplicit false
open scoped Polynomial RatFunc WithZero
namespace QEC.Coding.AlgebraicGeometry
namespace Differential
open FunctionFieldDifferential
variable {k : Type*} [Field k] [Finite k]
theorem rationalInfinitySimpleFractionCoefficient_mem
    (q b : k[X]) (hq : q.Monic) (hb : b.degree < q.degree) :
    -(RatFunc.X *
        (algebraMap k[X] (RatFunc k) b /
          algebraMap k[X] (RatFunc k) q)) ∈
      (GlobalPlace.rationalInfinity k).valuationRing := by
  classical
  by_cases hb0 : b = 0
  · simp [hb0]
  have hq0 : q ≠ 0 := hq.ne_zero
  have hb_map : algebraMap k[X] (RatFunc k) b ≠ 0 :=
    RatFunc.algebraMap_ne_zero hb0
  have hq_map : algebraMap k[X] (RatFunc k) q ≠ 0 :=
    RatFunc.algebraMap_ne_zero hq0
  have hquotient :
      algebraMap k[X] (RatFunc k) b /
          algebraMap k[X] (RatFunc k) q ≠ 0 :=
    div_ne_zero hb_map hq_map
  have hscalar :
      -(RatFunc.X *
          (algebraMap k[X] (RatFunc k) b /
            algebraMap k[X] (RatFunc k) q)) ≠ 0 :=
    neg_ne_zero.mpr (mul_ne_zero RatFunc.X_ne_zero hquotient)
  apply (GlobalPlace.mem_valuationRing_iff
    (GlobalPlace.rationalInfinity k) _).mpr
  change RatFunc.inftyValuation k
      (-(RatFunc.X *
        (algebraMap k[X] (RatFunc k) b /
          algebraMap k[X] (RatFunc k) q))) ≤ 1
  rw [RatFunc.inftyValuation_apply,
    RatFunc.inftyValuation_of_nonzero (F := k) hscalar,
    ← WithZero.exp_zero]
  apply WithZero.exp_le_exp.mpr
  rw [RatFunc.intDegree_neg,
    RatFunc.intDegree_mul RatFunc.X_ne_zero hquotient,
    RatFunc.intDegree_X,
    RatFunc.intDegree_div hb_map hq_map,
    RatFunc.intDegree_polynomial, RatFunc.intDegree_polynomial]
  have hdegree : b.natDegree < q.natDegree :=
    (Polynomial.natDegree_lt_iff_degree_lt hb0).mpr (by
      simpa only [Polynomial.degree_eq_natDegree hq0] using hb)
  omega
noncomputable def rationalInfinitySimpleFractionCoefficient
    (q b : k[X]) (hq : q.Monic) (hb : b.degree < q.degree) :
    (GlobalPlace.rationalInfinity k).valuationRing :=
  ⟨-(RatFunc.X *
      (algebraMap k[X] (RatFunc k) b /
        algebraMap k[X] (RatFunc k) q)),
    rationalInfinitySimpleFractionCoefficient_mem q b hq hb⟩
noncomputable def rationalInfinitySimpleFractionAtSimplePole
    (q b : k[X]) (hq : q.Monic) (hb : b.degree < q.degree) :
    simplePoleDifferentialLattice (GlobalPlace.rationalInfinity k) :=
  rationalInfinitySimpleFractionCoefficient q b hq hb •
    logarithmicDifferentialAtSimplePole (k := k) (F := RatFunc k)
      (GlobalPlace.rationalInfinity k) (RatFunc.X : RatFunc k)⁻¹
      (inv_ne_zero RatFunc.X_ne_zero)
end Differential
end QEC.Coding.AlgebraicGeometry



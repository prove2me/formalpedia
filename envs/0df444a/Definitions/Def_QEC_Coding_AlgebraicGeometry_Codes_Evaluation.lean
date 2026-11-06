-- Prove2me | Definitions.Def_QEC_Coding_AlgebraicGeometry_Codes_Evaluation
-- name    : QEC_Coding_AlgebraicGeometry_Codes_Evaluation
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T18:21:32.188142+00:00
-- url     : https://prove2.me/theorems/eb1e9896-0b1c-44f0-946e-1aa3997fd6b6
-- title:
--   Evaluation
-- statement:
--   Definitions and structural lemmas for Evaluation, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Codes/Evaluation.lean

import Definitions.Def_QEC_Coding_Core_Definitions
import Definitions.Def_QEC_Coding_AlgebraicGeometry_RiemannRoch_NegativeDegreeVanishing
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_RationalPlaceDegree
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_mem_riemannRochSubmodule_iff
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_RationalPlace_evaluate_constants

set_option autoImplicit false
namespace QEC.Coding.AlgebraicGeometry
open scoped BigOperators Polynomial RatFunc WithZero
variable {k F ι : Type*}
variable [Field k] [Finite k] [Field F] [Algebra k F]
variable [Fintype ι]
noncomputable def zeroCoordinateDivisor (Q : ι → RationalPlace k F)
    (S : Finset ι) : Divisor (GlobalPlace k F) := by
  classical
  exact ∑ i ∈ S, Finsupp.single (Q i).place (1 : ℤ)
noncomputable def evaluationDivisor (Q : ι → RationalPlace k F) :
    Divisor (GlobalPlace k F) :=
  zeroCoordinateDivisor Q Finset.univ
theorem evaluationRegularity (G : Divisor (GlobalPlace k F))
    (Q : ι → RationalPlace k F) (hG : ∀ i, G (Q i).place = 0)
    (f : GlobalPlace.riemannRochSubmodule G) (i : ι) :
    GlobalPlace.RegularAt (Q i).place (f : F) := by
  have hbound : (Q i).place.valuation (f : F) ≤ WithZero.exp (G (Q i).place) :=
    (GlobalPlace.mem_riemannRochSubmodule_iff G (f : F)).mp f.property (Q i).place
  rw [hG i] at hbound
  rw [WithZero.exp_zero] at hbound
  exact hbound
theorem rational_evaluateRegular_add (Q : RationalPlace k F)
    (f g : F) (hf : GlobalPlace.RegularAt Q.place f)
    (hg : GlobalPlace.RegularAt Q.place g)
    (hfg : GlobalPlace.RegularAt Q.place (f + g)) :
    Q.evaluateRegular (f + g) hfg =
      Q.evaluateRegular f hf + Q.evaluateRegular g hg := by
  let xf : GlobalPlace.valuationRing Q.place :=
    ⟨f, (GlobalPlace.mem_valuationRing_iff Q.place f).mpr hf⟩
  let xg : GlobalPlace.valuationRing Q.place :=
    ⟨g, (GlobalPlace.mem_valuationRing_iff Q.place g).mpr hg⟩
  let xfg : GlobalPlace.valuationRing Q.place :=
    ⟨f + g, (GlobalPlace.mem_valuationRing_iff Q.place (f + g)).mpr hfg⟩
  change Q.evaluate xfg = Q.evaluate xf + Q.evaluate xg
  have hsum : xfg = xf + xg := by
    rfl
  rw [hsum]
  exact Q.evaluate.map_add xf xg
theorem rational_evaluateRegular_smul (Q : RationalPlace k F)
    (a : k) (f : F) (hf : GlobalPlace.RegularAt Q.place f)
    (hsf : GlobalPlace.RegularAt Q.place (a • f)) :
    Q.evaluateRegular (a • f) hsf = a • Q.evaluateRegular f hf := by
  let xf : GlobalPlace.valuationRing Q.place :=
    ⟨f, (GlobalPlace.mem_valuationRing_iff Q.place f).mpr hf⟩
  let xaf : GlobalPlace.valuationRing Q.place :=
    ⟨a • f, (GlobalPlace.mem_valuationRing_iff Q.place (a • f)).mpr hsf⟩
  let xa : GlobalPlace.valuationRing Q.place :=
    GlobalPlace.constantsToValuationRing Q.place a
  change Q.evaluate xaf = a • Q.evaluate xf
  have haf : xaf = xa * xf := by
    apply Subtype.ext
    change a • f = algebraMap k F a * f
    exact Algebra.smul_def _ _
  calc
    Q.evaluate xaf = Q.evaluate (xa * xf) := congrArg Q.evaluate haf
    _ = Q.evaluate xa * Q.evaluate xf := Q.evaluate.map_mul xa xf
    _ = a * Q.evaluate xf := by
      change Q.evaluate (GlobalPlace.constantsToValuationRing Q.place a) * Q.evaluate xf =
        a * Q.evaluate xf
      rw [Q.evaluate_constants]
    _ = a • Q.evaluate xf := (smul_eq_mul _ _).symm
noncomputable def agEvaluationLinearMap (G : Divisor (GlobalPlace k F))
    (Q : ι → RationalPlace k F) (hG : ∀ i, G (Q i).place = 0) :
    GlobalPlace.riemannRochSubmodule G →ₗ[k] Word k ι where
  toFun f := fun i => (Q i).evaluateRegular (f : F) (evaluationRegularity G Q hG f i)
  map_add' f g := by
    funext i
    exact rational_evaluateRegular_add (Q i) (f : F) (g : F)
      (evaluationRegularity G Q hG f i)
      (evaluationRegularity G Q hG g i)
      (evaluationRegularity G Q hG (f + g) i)
  map_smul' a f := by
    funext i
    exact rational_evaluateRegular_smul (Q i) a (f : F)
      (evaluationRegularity G Q hG f i)
      (evaluationRegularity G Q hG (a • f) i)
noncomputable def agEvaluationCode [Fintype k]
    (G : Divisor (GlobalPlace k F)) (Q : ι → RationalPlace k F)
    (hG : ∀ i, G (Q i).place = 0) : LinearCode k ι where
  carrier := (agEvaluationLinearMap G Q hG).range
end QEC.Coding.AlgebraicGeometry



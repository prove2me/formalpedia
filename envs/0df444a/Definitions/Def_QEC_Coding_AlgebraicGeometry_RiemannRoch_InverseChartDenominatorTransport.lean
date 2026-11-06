-- Prove2me | Definitions.Def_QEC_Coding_AlgebraicGeometry_RiemannRoch_InverseChartDenominatorTransport
-- name    : QEC_Coding_AlgebraicGeometry_RiemannRoch_InverseChartDenominatorTransport
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T13:55:49.413349+00:00
-- url     : https://prove2.me/theorems/4eaedb13-3996-4587-abbe-f643d2500c76
-- title:
--   Inverse Chart Denominator Transport
-- statement:
--   Definitions and structural lemmas for Inverse Chart Denominator Transport, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/RiemannRoch/InverseChartDenominatorTransport.lean

import Mathlib.Algebra.Polynomial.Laurent
import Definitions.Def_QEC_Coding_AlgebraicGeometry_RiemannRoch_DirectChartCommonDenominator
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_InverseAffinePlace
set_option autoImplicit false
namespace QEC.Coding.AlgebraicGeometry.InverseChartDenominatorTransport
open scoped LaurentPolynomial Polynomial RatFunc
variable {k F ι : Type*}
noncomputable def ratFuncXUnit (k : Type*) [Field k] : (RatFunc k)ˣ :=
  Units.mk0 RatFunc.X RatFunc.X_ne_zero
noncomputable def directLaurentToRatFunc (k : Type*) [Field k] :
    LaurentPolynomial k →+* RatFunc k :=
  LaurentPolynomial.eval₂ (algebraMap k (RatFunc k)) (ratFuncXUnit k)
noncomputable def inverseLaurentCoordinate (k : Type*) [Field k] :
    k[X] →ₐ[k] LaurentPolynomial k :=
  (LaurentPolynomial.invert (R := k)).toAlgHom.comp Polynomial.toLaurentAlg
noncomputable def inverseLaurentToRatFunc (k : Type*) [Field k] :
    k[X] →+* RatFunc k :=
  (directLaurentToRatFunc k).comp (inverseLaurentCoordinate k).toRingHom
noncomputable def rationalInvolutionOnPolynomial (k : Type*) [Field k] :
    k[X] →+* RatFunc k :=
  (InverseAffinePlace.rationalInvolution k).toRingHom.comp
    (algebraMap k[X] (RatFunc k))
noncomputable def inverseBasis
    [Field k] [Field F]
    [ρ : Algebra (RatFunc k) F] [_π : Algebra (Polynomial k) F]
    [_τ : IsScalarTower (Polynomial k) (RatFunc k) F]
    [φ : _root_.FunctionField k F] [s : Algebra.IsSeparable (RatFunc k) F]
    (b : Module.Basis ι (RatFunc k) F) :
    let : Algebra (RatFunc k) F := InverseAffinePlace.transportedRationalAlgebra
      (k := k) (F := F) (oldRationalAlgebra := ρ)
    let : Algebra (Polynomial k) F := InverseAffinePlace.transportedPolynomialAlgebra
      (k := k) (F := F) (oldRationalAlgebra := ρ)
    let : IsScalarTower (Polynomial k) (RatFunc k) F :=
      InverseAffinePlace.transportedScalarTower (k := k) (F := F)
        (oldRationalAlgebra := ρ)
    let : _root_.FunctionField k F := InverseAffinePlace.transportedFunctionField
      (k := k) (F := F) (oldRationalAlgebra := ρ) (oldFunctionField := φ)
    let : Algebra.IsSeparable (RatFunc k) F :=
      InverseAffinePlace.transportedIsSeparable (k := k) (F := F)
        (oldRationalAlgebra := ρ) (oldSeparable := s)
    Module.Basis ι (RatFunc k) F := by
  let oldModule : Module (RatFunc k) F := @Algebra.toModule (RatFunc k) F _ _ ρ
  let oldBasis : @Module.Basis ι (RatFunc k) F _ _ oldModule := b
  let transportedAlg : Algebra (RatFunc k) F := InverseAffinePlace.transportedRationalAlgebra
    (k := k) (F := F) (oldRationalAlgebra := ρ)
  let : Algebra (RatFunc k) F := transportedAlg
  let newModule : Module (RatFunc k) F := @Algebra.toModule (RatFunc k) F _ _
    transportedAlg
  let : Algebra (Polynomial k) F := InverseAffinePlace.transportedPolynomialAlgebra
    (k := k) (F := F) (oldRationalAlgebra := ρ)
  let : IsScalarTower (Polynomial k) (RatFunc k) F :=
    InverseAffinePlace.transportedScalarTower (k := k) (F := F)
      (oldRationalAlgebra := ρ)
  let : _root_.FunctionField k F := InverseAffinePlace.transportedFunctionField
    (k := k) (F := F) (oldRationalAlgebra := ρ) (oldFunctionField := φ)
  let : Algebra.IsSeparable (RatFunc k) F := InverseAffinePlace.transportedIsSeparable
    (k := k) (F := F) (oldRationalAlgebra := ρ) (oldSeparable := s)
  exact @Module.Basis.mapCoeffs ι (RatFunc k) F _ _ oldModule oldBasis
    (RatFunc k) _ newModule (InverseAffinePlace.rationalInvolution k).toRingEquiv.symm (by
      intro c x
      let hNew := transportedAlg.smul_def' ((InverseAffinePlace.rationalInvolution k).symm c) x
      let hOld := ρ.smul_def' c x
      change @SMul.smul (RatFunc k) F newModule.toSMul
          ((InverseAffinePlace.rationalInvolution k).symm c) x =
        @SMul.smul (RatFunc k) F oldModule.toSMul c x
      calc
        @SMul.smul (RatFunc k) F newModule.toSMul
            ((InverseAffinePlace.rationalInvolution k).symm c) x =
            (@Algebra.algebraMap (RatFunc k) F _ _ transportedAlg)
              ((InverseAffinePlace.rationalInvolution k).symm c) * x :=
          hNew
        _ = (@Algebra.algebraMap (RatFunc k) F _ _ ρ) c * x := by
          apply congrArg (fun z : F => z * x)
          change InverseAffinePlace.transportedRationalMap
              (k := k) (F := F) (oldRationalAlgebra := ρ)
              ((InverseAffinePlace.rationalInvolution k).symm c) =
            (@Algebra.algebraMap (RatFunc k) F _ _ ρ) c
          simp [InverseAffinePlace.transportedRationalMap]
        _ = @SMul.smul (RatFunc k) F oldModule.toSMul c x :=
          hOld.symm)
end QEC.Coding.AlgebraicGeometry.InverseChartDenominatorTransport



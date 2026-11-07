-- Prove2me | Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalGaussSpecialFiber
-- name    : QEC_Coding_ExpanderCodes_LPSOriginalGaussSpecialFiber
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-07T04:19:43.910892+00:00
-- url     : https://prove2.me/theorems/c51b8862-b23b-4683-9d2a-9b227417dcc0
-- title:
--   LPSOriginal Gauss Special Fiber
-- statement:
--   Definitions and structural lemmas for LPSOriginal Gauss Special Fiber, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalGaussSpecialFiber.lean

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalGaussLocalOrder
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerProperModel
import Mathlib.RingTheory.RamificationInertia.Ramification
import Mathlib.RingTheory.Smooth.Fiber
import Mathlib.RingTheory.IntegralClosure.GoingDown
import Mathlib.RingTheory.Ideal.Height
set_option autoImplicit false
namespace QEC.Coding.TannerLiftedProduct
noncomputable section
attribute [local instance] lpsOriginalGaussPrime_isPrime lpsOriginalGaussPrime_principal
def lpsOriginalGaussBaseToGeneratedField
    (N : ℕ) [NeZero N] (hN : 0 < N) (p : ℕ) [Fact p.Prime] :
    let := lpsOriginalJFractionEmbeddingQ.toAlgebra
    LPSOriginalGaussBase p →+* lpsOriginalGeneratedFunctionFieldQ N hN :=
  (lpsOriginalGaussAffineToGenerated N hN p).comp
    (algebraMap (LPSOriginalGaussBase p) (LPSOriginalGaussAffineOrder N hN p))
lemma lpsOriginalGaussBaseToGeneratedField_base
    (N : ℕ) [NeZero N] (hN : 0 < N) (p : ℕ) [Fact p.Prime] (f : Polynomial ℤ) :
    let := lpsOriginalJFractionEmbeddingQ.toAlgebra
    lpsOriginalGaussBaseToGeneratedField N hN p
      (algebraMap (Polynomial ℤ) (LPSOriginalGaussBase p) f) =
      lpsOriginalIntegerBaseToGeneratedField N hN f := by
  let := lpsOriginalJFractionEmbeddingQ.toAlgebra
  change lpsOriginalGaussAffineToGenerated N hN p
    (AdjoinRoot.of (lpsOriginalGaussPolynomial N hN p)
      (algebraMap (Polynomial ℤ) (LPSOriginalGaussBase p) f)) = _
  rw [← AdjoinRoot.map_of (algebraMap (Polynomial ℤ) (LPSOriginalGaussBase p))
    (lpsOriginalIntegerPolynomial N hN) (lpsOriginalGaussPolynomial N hN p) dvd_rfl]
  change lpsOriginalGaussAffineToGenerated N hN p
    (lpsOriginalIntegerAffineToGauss N hN p
      (AdjoinRoot.of (lpsOriginalIntegerPolynomial N hN) f)) = _
  rw [lpsOriginalGaussAffineToGenerated_base]
  exact lpsOriginalIntegerAffineToGenerated_base N hN f
lemma lpsOriginalGaussBase_scalarTower
    (N : ℕ) [NeZero N] (hN : 0 < N) (p : ℕ) [Fact p.Prime] :
    let := lpsOriginalJFractionEmbeddingQ.toAlgebra
    let := (lpsOriginalIntegerBaseToGeneratedField N hN).toAlgebra
    let := (lpsOriginalGaussBaseToGeneratedField N hN p).toAlgebra
    IsScalarTower (Polynomial ℤ) (LPSOriginalGaussBase p)
      (lpsOriginalGeneratedFunctionFieldQ N hN) := by
  let := lpsOriginalJFractionEmbeddingQ.toAlgebra
  let := (lpsOriginalIntegerBaseToGeneratedField N hN).toAlgebra
  let := (lpsOriginalGaussBaseToGeneratedField N hN p).toAlgebra
  apply IsScalarTower.of_algebraMap_eq'
  apply RingHom.ext
  intro f
  exact (lpsOriginalGaussBaseToGeneratedField_base N hN p f).symm
def lpsOriginalIntegerNormalZeroToGaussNormalization
    (N : ℕ) [NeZero N] (hN : 0 < N) (p : ℕ) [Fact p.Prime] :
    let := lpsOriginalJFractionEmbeddingQ.toAlgebra
    let := (lpsOriginalIntegerBaseToGeneratedField N hN).toAlgebra
    let := (lpsOriginalGaussBaseToGeneratedField N hN p).toAlgebra
    integralClosure (Polynomial ℤ) (lpsOriginalGeneratedFunctionFieldQ N hN) →+*
      integralClosure (LPSOriginalGaussBase p) (lpsOriginalGeneratedFunctionFieldQ N hN) := by
  let := lpsOriginalJFractionEmbeddingQ.toAlgebra
  let := (lpsOriginalIntegerBaseToGeneratedField N hN).toAlgebra
  let := (lpsOriginalGaussBaseToGeneratedField N hN p).toAlgebra
  let := lpsOriginalGaussBase_scalarTower N hN p
  exact { toFun := fun x => ⟨x.val,x.property.tower_top⟩
          map_one' := rfl
          map_mul' _ _ := rfl
          map_zero' := rfl
          map_add' _ _ := rfl }
section NormalizationFiber
variable (N : ℕ) [NeZero N] (hN : 0 < N) (p : ℕ) [Fact p.Prime]
local instance gaussFiberBaseFieldAlgebra :
    Algebra (LPSOriginalGaussBase p) (lpsOriginalGeneratedFunctionFieldQ N hN) :=
  ((lpsOriginalGaussAffineToGenerated N hN p).comp
    (algebraMap (LPSOriginalGaussBase p) (LPSOriginalGaussAffineOrder N hN p))).toAlgebra
local notation "D" => integralClosure (LPSOriginalGaussBase p) (lpsOriginalGeneratedFunctionFieldQ N hN)
local instance gaussFiberNormalizationCommRing : CommRing D := inferInstance
local instance gaussFiberNormalizationRing : Ring D := CommRing.toRing
local instance gaussFiberNormalizationSemiring : Semiring D :=
  (gaussFiberNormalizationCommRing N hN p).toCommSemiring.toSemiring
include hN
end NormalizationFiber
end
end QEC.Coding.TannerLiftedProduct
namespace QEC.Coding.AlgebraicGeometry
end QEC.Coding.AlgebraicGeometry
namespace QEC.Coding.TannerLiftedProduct
noncomputable section
attribute [local instance] lpsOriginalGaussPrime_isPrime
local instance verticalPrimeJAlgebra :
    Algebra (FractionRing (Polynomial ℚ)) LPSOriginalHolomorphicFractionField :=
  lpsOriginalJFractionEmbeddingQ.toAlgebra
variable (N : ℕ) (hN : 0 < N)
local instance verticalPrimeBaseFieldAlgebra :
    Algebra (Polynomial ℤ) (lpsOriginalGeneratedFunctionFieldQ N hN) :=
  (lpsOriginalIntegerBaseToGeneratedField N hN).toAlgebra
local notation "K" => lpsOriginalGeneratedFunctionFieldQ N hN
local notation "C" => integralClosure (Polynomial ℤ) K
local instance verticalPrimeNormalCommRing : CommRing C := inferInstance
local instance verticalPrimeNormalRing : Ring C := CommRing.toRing
local instance verticalPrimeNormalSemiring : Semiring C :=
  (verticalPrimeNormalCommRing N hN).toCommSemiring.toSemiring
include hN
end
end QEC.Coding.TannerLiftedProduct



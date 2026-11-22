-- Prove2me | Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ReductionSecondStep
-- name    : Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ReductionSecondStep
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T21:26:17.176386+00:00
-- url     : https://prove2.me/theorems/ebde9996-e5cc-4940-9260-e35e76102a94
-- title:
--   Reduction Second Step
-- statement:
--   Definitions and structural lemmas for Reduction Second Step, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/QuotientMetricDivisors/HermitianTwistDivisors/ReductionSecondStep.lean

import Mathlib
import Definitions.Def_Formalism_QuotientMetricDivisors_ProdFormula
import Definitions.Def_Formalism_HarderNarasimhan_ShiftInvariance
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_IndexBasic
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ProdFormula
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_LcvBasis
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_IdxChange
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ValBasic
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ImageLcv
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_RatHerm
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_LocBasis
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField IsDedekindDomain
open scoped Matrix ComplexOrder
noncomputable section
namespace Formalism.DivisionValues
namespace StepBAux
section Gram
variable {K : Type} [Field K] [NumberField K] [StarRing K]
def cvec {d : ℕ} (σ : K →+* ℂ) (x : Fin d → K) : Fin d → ℂ := fun i => σ (x i)
def met {d : ℕ} (X : InfinitePlace K → Matrix (Fin d) (Fin d) ℂ) (v : InfinitePlace K) :
    Matrix (Fin d) (Fin d) ℂ :=
  ((X v)⁻¹).conjTranspose * (X v)⁻¹
def fmat {d m : ℕ} (σ : K →+* ℂ) (e : Fin m → Fin d → K) : Matrix (Fin d) (Fin m) ℂ :=
  Matrix.of fun i a => σ (e a i)
end Gram
section Lat
variable {K : Type} [Field K] [NumberField K] [StarRing K]
def matEquiv {d : ℕ} (φ : Matrix (Fin d) (Fin d) K) (hφ : IsUnit φ.det) :
    (Fin d → K) ≃ₗ[𝓞 K] (Fin d → K) :=
  LinearEquiv.ofBijective ((Matrix.mulVecLin φ).restrictScalars (𝓞 K))
    ⟨Matrix.mulVec_injective_iff_isUnit.mpr ((Matrix.isUnit_iff_isUnit_det φ).mpr hφ),
     Matrix.mulVec_surjective_iff_isUnit.mpr ((Matrix.isUnit_iff_isUnit_det φ).mpr hφ)⟩
end Lat
section Val
variable {K : Type} [Field K] [NumberField K] [StarRing K]
end Val
section Add
variable {R K V : Type*} [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K]
  [IsFractionRing R K] [AddCommGroup V] [Module K V] [Module R V] [IsScalarTower R K V]
end Add
section Local
variable {K : Type} [Field K] [NumberField K] [StarRing K]
end Local
section Supp
variable {K : Type} [Field K] [NumberField K] [StarRing K]
end Supp
end StepBAux
end Formalism.DivisionValues



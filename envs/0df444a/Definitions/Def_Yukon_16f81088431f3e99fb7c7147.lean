-- Prove2me | Definitions.Def_Yukon_16f81088431f3e99fb7c7147
-- name    : Yukon_16f81088431f3e99fb7c7147
-- status  : Definition
-- author  : @yukon
-- created : 2026-10-03T06:47:44.33699+00:00
-- url     : https://prove2.me/theorems/57069a3d-fa32-49cb-81b3-988a0d995dc6
-- title:
--   YukonModule.ProximityPrize.SubmissionLower.MovingSourceMovingDegrees6814.part0
-- statement:
--   Source module ProximityPrize.SubmissionLower.MovingSourceMovingDegrees6814.
-- source:
--   https://github.com/proximity-prize/proximity-prize/blob/9008f0e2b2edb0647da15baac454a68072f0ba29/ProximityPrize/SubmissionLower/MovingSourceMovingDegrees6814.lean
--
--   yukon-proof-operation:certificate-r13-b54-60e85a3cb621705a2a2cbc098025619fe816bdee00b85f47d6caeb502580514b
--   [yukon-proof-receipt:eyJlbnZpcm9ubWVudCI6eyJtYXRobGliUmV2IjoiMGRmNDQ0YTM2MGVhYTYwYWI4YzExZGNhNTFhODZhZjY5Mjk1NTQ3NCIsInRvb2xjaGFpbiI6ImxlYW5wcm92ZXIvbGVhbjQ6djQuMzMuMSJ9LCJoYXNoIjoiMDNhMDk5MTBlYWZjYmFlOWJiYWQ2MTFjY2E5ZTY2OGVlNzVjMjYzOTAxODMxODFjZjAzYTE3NTMyZjI0ZTUxYiIsImtpbmQiOiJkZWZpbml0aW9uIiwibWFya2VyIjoieXVrb24tcHJvb2Ytb3BlcmF0aW9uOmNlcnRpZmljYXRlLXIxMy1iNTQtNjBlODVhM2NiNjIxNzA1YTJhMmNiYzA5ODAyNTYxOWZlODE2YmRlZTAwYjg1ZjQ3ZDZjYWViNTAyNTgwNTE0YiIsInRhZyI6ImJldHRlci1jb2RlcyIsInRhcmdldCI6Ill1a29uXzE2ZjgxMDg4NDMxZjNlOTlmYjdjNzE0NyIsInYiOjJ9]

import Definitions.Def_Yukon_ad71038421ad49c036e88a5d














































































































































































































































































































































































set_option backward.isDefEq.respectTransparency.types false
/-! Apply the whole-carrier point budget to the ACTUAL generic embedding
points of the old moving projection. Regularity and isolation are supplied
by the existing certificate, not added as point-budget assumptions. -/
namespace ProximityPrize.SubmissionLower.MovingSourceMovingDegrees6814
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 30000
set_option maxHeartbeats 300000
open scoped BigOperators
open RCN002 RCN084 RCN095 RCN134 RCN135 RCN136 RCN199 RCN202 RCN207 RCN208 RCN264 RCN313 RCN344
open MovingFiberThreeSources6811 MovingSourceTargetField6814 MovingSourceWholeCarrier6814
open MovingSourceGeometricBudget6814 MovingSourceWholeCount6814

variable {K : Type} [Field K]
local notation "Omega" => GenericField K
local notation "OmegaT" => GenericField (GenericField K)
local notation "phi" => RingHom.comp (coefficientEmbedding (GenericField K)) (polynomialEmbedding K)
local notation "lift" => MvPolynomial.map (coefficientEmbedding (GenericField K))
local instance  _root_.ProximityPrize.SubmissionLower.MovingSourceMovingDegrees6814.instAlgebraRatFuncGenericField : Algebra (RatFunc Omega) OmegaT := targetAlgebra Omega
local instance  _root_.ProximityPrize.SubmissionLower.MovingSourceMovingDegrees6814.instIsScalarTowerGenericFieldRatFunc : IsScalarTower Omega (RatFunc Omega) OmegaT := target_tower Omega

def baseCarrier (F : MvPolynomial (Fin 4) K) := surfaceMap (polynomialEmbedding K) F
def baseH (F : MvPolynomial (Fin 4) K) := surfaceMap (polynomialEmbedding K) (polyH K F)
def baseG (F : MvPolynomial (Fin 4) K) := surfaceMap (polynomialEmbedding K) (polyG K F)

abbrev OriginalFamily (F : MvPolynomial (Fin 4) K) (n : ℕ)
    (coeff : Fin (n+1) → MvPolynomial (Fin 3) Omega) :=
  RegularComponent Omega (baseCarrier F) (filteredCut n coeff (baseH F) (baseG F)) (baseH F)

def targetCut (n : ℕ) (coeff : Fin (n+1) → MvPolynomial (Fin 3) Omega)
    (Q A : MvPolynomial (Fin 3) Omega) : MvPolynomial (Fin 3) OmegaT :=
  eliminatedCut n (fun j => lift (coeff j)) (lift Q) (lift A) (initialCoordinate Omega)

theorem scalar_eq_lift (P : MvPolynomial (Fin 3) Omega) : scalarPolynomialMap Omega OmegaT P=lift P := by
  rw [scalarPolynomialMap,←coefficientEmbedding_eq_algebraMap Omega]

theorem lift_surface (P : MvPolynomial (Fin 4) K) :
    lift (surfaceMap (polynomialEmbedding K) P)=surfaceMap phi P := by
  simp only [surfaceMap,RingHom.comp_apply,MvPolynomial.map_map]

theorem eval_lift_embedding (C : Ideal (MvPolynomial (Fin 3) Omega)) [C.IsPrime]
    (f : CoordinateField Omega C →ₐ[Omega] OmegaT) (P : MvPolynomial (Fin 3) Omega) :
    MvPolynomial.eval (embeddingPoint C f) (lift P)=f (coordinateEvaluation Omega C P) := by
  rw [MvPolynomial.eval_map,coefficientEmbedding_eq_algebraMap]
  exact AlgHom.congr_fun (embeddingPoint_aeval C f) P




/-- Reuse the existing small cut flag on the actual target polynomial. -/
theorem targetCut_small_flag
    (F : MvPolynomial (Fin 4) K) (a b s n : ℕ) (center : FlagDegree)
    (coeff : Fin (n+1) → MvPolynomial (Fin 3) Omega) (flags : Fin (n+1) → FlagDegree)
    (hH : PolynomialInFlag ⟨a,b+1,s+1⟩ (baseH F))
    (hG : PolynomialInFlag ⟨a,b,s+3⟩ (baseG F))
    (hcoeff : ∀ j, PolynomialInFlag (flags j) (coeff j))
    (heq : ∀ j, flags j+(n-j.val) • (⟨a,b+1,s+1⟩ : FlagDegree)+
      j.val • (⟨a,b,s+3⟩ : FlagDegree)=center+n • (⟨2*a,2*b+1,2*s+3⟩ : FlagDegree))
    (Q A : MvPolynomial (Fin 3) Omega)
    (hQ : PolynomialInFlag (2 • unitAllFlag) Q) (hA : PolynomialInFlag unitYZFlag A) :
    PolynomialInFlag (center+n • (⟨a,b+1,s+2⟩ : FlagDegree)) (targetCut n coeff Q A) := by
  have hh := (fiber_small_flags (E:=OmegaT) a b s n center (baseH F) (baseG F) Q A coeff flags
    hH hG hQ hA hcoeff heq).2
  simpa only [fiberCut,scalar_eq_lift,target_variable,targetCut] using hh





end
end ProximityPrize.SubmissionLower.MovingSourceMovingDegrees6814



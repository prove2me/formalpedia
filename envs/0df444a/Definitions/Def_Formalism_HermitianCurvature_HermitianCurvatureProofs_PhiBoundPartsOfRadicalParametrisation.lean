-- Prove2me | Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PhiBoundPartsOfRadicalParametrisation
-- name    : Formalism_HermitianCurvature_HermitianCurvatureProofs_PhiBoundPartsOfRadicalParametrisation
-- status  : Definition
-- author  : @community-bot-6
-- created : 2026-11-24T15:53:32.393047+00:00
-- url     : https://prove2.me/theorems/83f1abda-1f53-47ff-b5cd-b0f96e9f1015
-- title:
--   Phi Bound Parts Of Radical Parametrisation
-- statement:
--   Definitions and structural lemmas for Phi Bound Parts Of Radical Parametrisation, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/PhiBoundPartsOfRadicalParametrisation.lean

import Definitions.Def_Formalism_HermitianCurvature_StatementU
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DilationUnipotentWeylMeasure
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SymmetricScalarBlockMatrixTranspose
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SymmetricScalarBlockMatrixMul
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DirectionsInParabolic
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_Block3MulBlocks
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CoordinateSizesOfHypotheses
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_CayleyTransformPreservesForm
import Theorems.Thm_Formalism_FourierDecayAlt_P_B4_mulL_apply
import Theorems.Thm_Formalism_FourierDecayAlt_P_BetaSesquilinearity_Pr_ck

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix MeasureTheory
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U Formalism.REAL Formalism.QuantumDeterminants
namespace Formalism.FourierDecayAlt.P.Ux10
end Formalism.FourierDecayAlt.P.Ux10
open MeasureTheory Filter Topology
namespace Formalism.FourierDecayAlt.P.Ux10
section meas
variable {α : Type*} [MeasurableSpace α] {μ : Measure α} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
end meas
section pint
variable {α : Type*} [MeasurableSpace α] {μ : Measure α}
end pint
section struct
variable {𝔤 E : Type*} [NormedAddCommGroup 𝔤] [NormedSpace ℝ 𝔤] [NormedAddCommGroup E] [NormedSpace ℝ E]
  {ι : Type*} [Fintype ι]
end struct
end Formalism.FourierDecayAlt.P.Ux10
open Matrix Filter Topology
namespace Formalism.FourierDecayAlt.P.Ux10
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.B4
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ}
section smooth
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] {n : WithTop ℕ∞} {s : Set X}
end smooth
def prj (Z : Mat k r) : Mat k r := (1 / 2 : ℂ) • (Z - Hpk k r * Zᴴ * Hpk k r)
def kap (Y : Mat k r) : Mat k r := (1 + Y) * (1 - Y)⁻¹
def iot (Z : Mat k r) : Mat k r := (Z - 1) * (Z + 1)⁻¹
section smooth2
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] {n : WithTop ℕ∞} {s : Set X}
end smooth2
abbrev J (k r : ℕ) : Type := Fin (2 * r + k + 1) × Fin (2 * r + k + 1) × Bool
def Eb (i : J k r) : Mat k r :=
  Matrix.of fun p q => if p = i.1 ∧ q = i.2.1 then (if i.2.2 then Complex.I else 1) else 0
def Mv (Y : J k r → ℝ) : Mat k r :=
  Matrix.of fun p q => ((Y (p, q, false) : ℝ) : ℂ) + ((Y (p, q, true) : ℝ) : ℂ) * Complex.I
def co (Z : Mat k r) : J k r → ℝ := fun i => if i.2.2 then (Z i.1 i.2.1).im else (Z i.1 i.2.1).re
def Lt (i : J k r) : Mat k r := (nrm (true, prj (Eb i))).2
def kc (i : J k r) (Z : Mat k r) : ℝ := co Z i * ‖prj (Eb i)‖
def chart (g0 : Mat k r) (Y : J k r → ℝ) : Mat k r := kap (prj (Mv Y)) * g0
def Dom (k r : ℕ) : Set (J k r → ℝ) := {Y | IsUnit (1 - prj (Mv Y)).det}
def mulB (k r : ℕ) : Mat k r →L[ℝ] Mat k r →L[ℝ] Mat k r :=
  LinearMap.toContinuousLinearMap
    { toFun := fun A => mulL A
      map_add' := fun A B => by ext g : 1; simp [mulL_apply, Matrix.add_mul]
      map_smul' := fun c A => by ext g : 1; simp [mulL_apply] }
def cT (k r : ℕ) : Mat k r →L[ℝ] Mat k r :=
  LinearMap.toContinuousLinearMap
    { toFun := fun A => Aᴴ
      map_add' := fun A B => conjTranspose_add A B
      map_smul' := fun c A => by
        simp only [RingHom.id_apply]
        rw [RCLike.real_smul_eq_coe_smul (K := ℂ), RCLike.real_smul_eq_coe_smul (K := ℂ),
          conjTranspose_smul]
        simp only [RCLike.star_def, RCLike.conj_ofReal] }
def ebv (b : J k r) : J k r → ℝ := fun j => if b = j then 1 else 0
def sC (g0 : Mat k r) (i b : J k r) (Y : J k r → ℝ) : ℝ :=
  kc i (-(fderiv ℝ (chart g0) Y (ebv b)) * (chart g0 Y)⁻¹)
def aC (g0 : Mat k r) (i : J k r) (Y : J k r → ℝ) : (J k r → ℝ) →L[ℝ] ℝ :=
  ∑ b, sC g0 i b Y • ContinuousLinearMap.proj b
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
def rho (g0 : Mat k r) (x : Mat k r) : J k r → ℝ := co (iot (x * g0⁻¹))
def Sr (g0 : Mat k r) : Set (Mat k r) := {x | IsUnit (x * g0⁻¹ + 1).det}
end Formalism.FourierDecayAlt.P.Ux10
open Matrix MeasureTheory Filter Topology
namespace Formalism.FourierDecayAlt.P.Ux10
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.B4
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {α : Type*} [MeasurableSpace α] {μ : Measure α}
  {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
section exch
variable [CompleteSpace E]
end exch
section ck
variable [CompleteSpace E]
end ck
end Formalism.FourierDecayAlt.P.Ux10
open Matrix MeasureTheory Filter Topology
namespace Formalism.FourierDecayAlt.P.Ux10
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U Formalism.REAL Formalism.QuantumDeterminants
section cont
variable {X : Type*} [TopologicalSpace X]
end cont
section psi
variable {X : Type*} [TopologicalSpace X]
end psi
section cd
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
end cd
end Formalism.FourierDecayAlt.P.Ux10
open Matrix MeasureTheory Filter Topology
namespace Formalism.FourierDecayAlt.P.Ux10
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.P.B4
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
end Formalism.FourierDecayAlt.P.Ux10
open Matrix MeasureTheory Filter Topology
namespace Formalism.FourierDecayAlt.P.Ux10
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.P.B4
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
end Formalism.FourierDecayAlt.P.Ux10
namespace Formalism.FourierDecayAlt.P
open Formalism.FourierDecayAlt.U
end Formalism.FourierDecayAlt.P



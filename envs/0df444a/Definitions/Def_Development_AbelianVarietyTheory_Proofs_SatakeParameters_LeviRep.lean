-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_LeviRep
-- name    : Development_AbelianVarietyTheory_Proofs_SatakeParameters_LeviRep
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T17:42:19.629551+00:00
-- url     : https://prove2.me/theorems/325c6e1f-466b-461d-825c-fcc59bdb13e6
-- title:
--   Levi Rep
-- statement:
--   Definitions and structural lemmas for Levi Rep, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SatakeParameters/LeviRep.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_GaloisGeometry_IsParahoricVec
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_HasFiniteLengthOfIsIrreducible
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_EventuallyCompSideMulEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IsMulLeftInvariantVolGL
import Theorems.Thm_GlobalTheory_SmGL_IsSmoothChar_comp

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil
open scoped TensorProduct
namespace GlobalTheory.GodementJacquet
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {r t : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
def eMat (k : Type) [Field k] (r t : ℕ) : Matrix (Fin (r + t)) (Fin r) k :=
  Matrix.of fun i j => if (i : ℕ) = j then 1 else 0
def coef (σ : Representation ℂ (GL (Fin r) k) V) (Bf : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ) (v w : V)
    (g : GL (Fin r) k) : ℂ :=
  Bf (σ g⁻¹ v) w
def gjInt [MeasurableSpace (GL (Fin r) k)] (m : Measure (GL (Fin r) k)) (μ : kˣ →* ℂˣ) (σ : Representation ℂ (GL (Fin r) k) V)
    (Bf : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ) (Φ : Matrix (Fin (r + t)) (Fin r) k → ℂ)
    (h : GL (Fin (r + t)) k) (v w : V) : ℂ :=
  ∫ g, om μ g h Φ (eMat k r t) * coef σ Bf v w g ∂m
abbrev leviRep (t : ℕ) (μ : kˣ →* ℂˣ) (σ : Representation ℂ (GL (Fin r) k) V) :
    Representation ℂ (Levi k (Two (Fin r) (Fin t))) (V ⊗[ℂ] ℂ) :=
  (extTensor σ (detRep (Fin t) μ)).comp (leviTwo k (Fin r) (Fin t)).symm.toMonoidHom
end GlobalTheory.GodementJacquet



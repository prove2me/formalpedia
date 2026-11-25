-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_StatementsStabilizerCovolume
-- name    : GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_StatementsStabilizerCovolume
-- status  : Definition
-- author  : @community-bot-6
-- created : 2026-11-25T02:46:44.234859+00:00
-- url     : https://prove2.me/theorems/02fb6948-1de9-5a2e-9f6b-ac991f5ad237
-- title:
--   Statements Stabilizer Covolume
-- statement:
--   Definitions and structural lemmas for Statements Stabilizer Covolume, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/StatementsStabilizerCovolume.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_StatementsVecFixGroup
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace GroundTheory.Heights₂.Heights.FiniteCovolume
open NumberField GroundTheory.Automorphic Module Matrix MeasureTheory
open scoped ENNReal
noncomputable section
variable {F E : Type*} [Field F] [Field E] [NumberField F] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] [IsTotallyReal F] [IsTotallyComplex E]
variable {W : Type*} [AddCommGroup W] [Module E W] {ι : Type*} [Fintype ι] [DecidableEq ι]
def StabilizerCovolumeFinite.Statement (h : HermitianForm F E W) (v : Basis ι E W) : Prop :=
  ∀ (D : ℕ) (La : AddSubgroup W) (x₀ : W), IsDIntegral h D La → x₀ ∈ La → x₀ ≠ 0 →
    h.toSesq x₀ x₀ = 0 → ∀ (ν : Measure (vecFixGroup h v x₀)), ν.IsHaarMeasure →
    ∃ FD₀ : Set (vecFixGroup h v x₀),
      IsFundamentalDomain ((vecStabGroup h v La x₀).subgroupOf (vecFixGroup h v x₀)) FD₀ ν ∧
      0 < ν FD₀ ∧ ν FD₀ < ⊤
section Inhabitants
open GaussianPlane
end Inhabitants
end
end GroundTheory.Heights₂.Heights.FiniteCovolume



-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_StUnipRadicalOfRational
-- name    : GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_StUnipRadicalOfRational
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-25T03:41:15.791389+00:00
-- url     : https://prove2.me/theorems/2761e4b0-2698-43a9-aedb-2fe85efd3ef2
-- title:
--   St Unip Radical Of Rational
-- statement:
--   Definitions and structural lemmas for St Unip Radical Of Rational, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/StUnipRadicalOfRational.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_StatementsStabilizerLevi
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace GroundTheory.Heights₂.Heights.FiniteCovolume
open NumberField GroundTheory.Automorphic Module Matrix Topology
noncomputable section
variable {F E : Type*} [Field F] [Field E] [NumberField F] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] [IsTotallyReal F] [IsTotallyComplex E]
variable {W : Type*} [AddCommGroup W] [Module E W] {ι : Type*} [Fintype ι] [DecidableEq ι]
def UnipRadicalOfRational.Statement (h : HermitianForm F E W) (v : Basis ι E W) : Prop :=
  ∀ (x₀ : W) (γ : h.unitaryGroup), γ • x₀ = x₀ →
    (∀ z : W, h.toSesq x₀ z = 0 → ∃ a : E, γ • z = z + a • x₀) →
    archEmbed h v γ ∈ unipRadical h v x₀
section Inhabitants
open GaussianPlane
end Inhabitants
end
end GroundTheory.Heights₂.Heights.FiniteCovolume



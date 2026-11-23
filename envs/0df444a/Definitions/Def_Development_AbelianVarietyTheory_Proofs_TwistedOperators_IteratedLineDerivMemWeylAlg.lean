-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IteratedLineDerivMemWeylAlg
-- name    : Development_AbelianVarietyTheory_Proofs_TwistedOperators_IteratedLineDerivMemWeylAlg
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T15:52:03.832185+00:00
-- url     : https://prove2.me/theorems/01be8d39-5011-4684-be3b-3729379a2213
-- title:
--   Iterated Line Deriv Mem Weyl Alg
-- statement:
--   Definitions and structural lemmas for Iterated Line Deriv Mem Weyl Alg, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/IteratedLineDerivMemWeylAlg.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_RealMetaplecticRepresentation
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Complex SchwartzMap LineDeriv Matrix
open scoped Real RealInnerProductSpace ContDiff FourierTransform
namespace GlobalTheory.RealWeil
variable {l : Type} [Fintype l]
def weylAlg (l : Type) [Fintype l] : Subalgebra ℂ (Sch l →L[ℂ] Sch l) := Algebra.adjoin ℂ (Set.range dRho)
variable [DecidableEq l]
def weightOp (l : Type) [Fintype l] [DecidableEq l] : Sch l →L[ℂ] Sch l :=
  1 - ((4 * π ^ 2 : ℝ) : ℂ)⁻¹ • ∑ j : l, dRho (Pi.single (Sum.inr j) 1) * dRho (Pi.single (Sum.inr j) 1)
def besselOp (l : Type) [Fintype l] [DecidableEq l] : Sch l →L[ℂ] Sch l :=
  1 - ((4 * π ^ 2 : ℝ) : ℂ)⁻¹ • ∑ j : l, dRho (Pi.single (Sum.inl j) 1) * dRho (Pi.single (Sum.inl j) 1)
def schwartzToL2 (l : Type) [Fintype l] : Sch l →L[ℂ] L2 l := toLpCLM ℂ ℂ 2 volume
section Metaplectic
variable {G : Type} [Group G] {pr : G →* Matrix.symplecticGroup l ℝ} {om : G →* (L2 l ≃ₗᵢ[ℂ] L2 l)}
  {omS : G →* (Sch l →L[ℂ] Sch l)}
end Metaplectic
end GlobalTheory.RealWeil
end



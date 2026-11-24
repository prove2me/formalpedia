-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_ConclRankZeroRight
-- name    : Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_ConclRankZeroRight
-- status  : Definition
-- author  : @community-bot-3
-- created : 2026-11-24T21:00:17.304147+00:00
-- url     : https://prove2.me/theorems/8751c954-df1d-404c-ad2a-e592a47d3f2b
-- title:
--   Concl Rank Zero Right
-- statement:
--   Definitions and structural lemmas for Concl Rank Zero Right, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/TwistedTraceFormula/ConclRankZeroRight.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_KudlaSplittingSplitUnitary
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_SumSquaresNeThreeThreeAdic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_WeilObjectsInhabited
import Theorems.Thm_GlobalTheory_HermLocal_Model_conjSqrt_apply
import Theorems.Thm_GlobalTheory_LocalQuad_HermClass_Congr_det

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Matrix
namespace GlobalTheory.SplitUnitary.Model
open GlobalTheory.WeilM (UG hTens IsQuad IsHerm ResEtaPow)
open GlobalTheory.SplitWeil (SB IsSmoothRep nabs)
open GlobalTheory.HermLocal.Model (conjSqrt conjSqrt_apply)
section Form
variable {F : Type} [Field F] {E : Type} [Field E] [Algebra F E] (c : E →ₐ[F] E)
end Form
section Edge
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {E : Type} [Field E] [Algebra F E] [TopologicalSpace E] [IsModuleTopology F E] (c : E →ₐ[F] E)
  {α ν : Type} [Fintype α] [DecidableEq α] [Fintype ν] [DecidableEq ν]
def Concl (hc : ∀ z, c (c z) = z) (ν : Type) [Fintype ν] [DecidableEq ν] (Q : Matrix α α E) {ψ : AddChar F ℂ}
    (hψ : Continuous ψ) (χ : Eˣ →* Circle) : Prop :=
  ∃ ω : Representation ℂ (UG c (stdJ ν E)) (SB (Matrix α ν E)),
      IsSmoothRep ω ∧
      (∀ μ : @Measure (Matrix α ν E) (borel _), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
        ∀ (g : UG c (stdJ ν E)) (φ : SB (Matrix α ν E)),
          ∫⁻ x, ‖(ω g φ : Matrix α ν E → ℂ) x‖ₑ ^ 2 ∂μ = ∫⁻ x, ‖(φ : Matrix α ν E → ℂ) x‖ₑ ^ 2 ∂μ) ∧
      (∀ (g : UG c (stdJ ν E)) (w : Matrix α (ν ⊕ ν) E),
        Heisenberg₂ c hψ Q w * ω g =
          ω g * Heisenberg₂ c hψ Q (w * ((g : GL (ν ⊕ ν) E) : Matrix (ν ⊕ ν) (ν ⊕ ν) E))) ∧
      ∀ (a : GL ν E) (φ : SB (Matrix α ν E)) (x : Matrix α ν E),
        (ω (levi c hc a) φ : Matrix α ν E → ℂ) x =
          (χ (Matrix.GeneralLinearGroup.det a) : ℂ) *
            ((nabs F (Units.map (Algebra.norm F : E →* F) (Matrix.GeneralLinearGroup.det a)) ^
              ((Fintype.card α : ℝ) / 2) : ℝ) : ℂ) *
            (φ : Matrix α ν E → ℂ) (x * (a : Matrix ν ν E))
end Edge
end GlobalTheory.SplitUnitary.Model
end



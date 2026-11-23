-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_DefiniteCompactness_ExistsCompactOfDefinite
-- name    : Development_AbelianVarietyTheory_PublishedTheorems_DefiniteCompactness_ExistsCompactOfDefinite
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T12:52:41.640121+00:00
-- url     : https://prove2.me/theorems/8d7a585f-c2c0-44ce-aba1-395a13296fa6
-- title:
--   Exists Compact Of Definite
-- statement:
--   Definitions and structural lemmas for Exists Compact Of Definite, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/DefiniteCompactness/ExistsCompactOfDefinite.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_WeightFunctionOnFrames
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_DetNeZeroOfIsOrth
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_IntegralConjInnerMulInnerOfIsEmptyEquiv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix
namespace GlobalTheory.Published
def UnitaryFiniteCovolume (E : Type) [Field E] [NumberField E] [IsCMField E] : Prop :=
  ∀ (r : ℕ) (X : Data E r) (H : Subgroup (X.Ψ → GL (Fin r) ℂ)),
    (∀ g, g ∈ H ↔ X.IsUnitaryC fun τ => (g τ : Matrix (Fin r) (Fin r) ℂ)) →
    ∀ [MeasurableSpace H] [BorelSpace H] (ν : Measure H) [ν.IsHaarMeasure],
      ∃ Ω : Set H, MeasurableSet Ω ∧ ν Ω < ⊤ ∧
        ∀ g : H, ∃ γ : GL (Fin r) E, IsUStab X.Gm X.Λ γ ∧ ∃ w ∈ Ω, ∀ τ : X.Ψ,
          (((g : X.Ψ → GL (Fin r) ℂ) τ : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) =
            (γ : Matrix (Fin r) (Fin r) E).map τ.1 *
              (((w : X.Ψ → GL (Fin r) ℂ) τ : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ)
namespace UnitaryFiniteCovolume
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
end UnitaryFiniteCovolume
end GlobalTheory.Published



-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsDiagOrdOne
-- name    : GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsDiagOrdOne
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:11:25.544766+00:00
-- url     : https://prove2.me/theorems/07129d3f-8392-4851-a6ca-b69c4b8f2b03
-- title:
--   Statements Diag Ord One
-- statement:
--   Definitions and structural lemmas for Statements Diag Ord One, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/StatementsDiagOrdOne.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsDiagDiv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.Inter
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI
noncomputable section
def DiagOrdOne.Statement : Prop :=
  ∀ (Ω : Type) [Field Ω] (ι ν κ : Type) [Fintype ι] [Fintype ν] [Fintype κ] (E : Type) [AddCommGroup E]
    [Module Ω E] (Φ : Type) [Field Φ] [Algebra Ω Φ] (x : ι → Ω) (B : ChartBundle ℤ x 2 E)
    (e : Module.Basis (Fin 2) Ω E) (φ : κ → E →ₗ[Ω] Ω) (δ : ν → Ω),
    T.IsTwistedDualSec B φ → T.IsTwistedDualGen B φ → T.IsTwistedDetGen B e δ → (∃ i, x i ≠ 0) →
    ∀ a : Fin 2 → Φ, AlgebraicIndependent Ω a →
    ∀ (n : ℕ) (g h : MRing (T.wwIdx ι ν κ)), IsMultiHomog g (T.wwDeg n 1) →
      IsMultiHomog h (T.wwDeg (n + 3) 0) → h ∉ T.wwIdeal x δ e φ (a 0) (a 1) →
      aeval (T.wwCoord x δ e φ (a 0) (a 1)) g = T.diagSec a * aeval (T.wwCoord x δ e φ (a 0) (a 1)) h →
        multAt (T.wwIdeal x δ e φ (a 0) (a 1) ⊔ Ideal.span {g}) (T.wwIdeal x δ e φ (a 0) (a 0)) = 1
end
end GroundTheory.Heights₂.Heights.Inter



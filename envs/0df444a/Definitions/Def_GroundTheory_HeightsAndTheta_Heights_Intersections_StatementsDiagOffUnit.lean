-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsDiagOffUnit
-- name    : GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsDiagOffUnit
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:11:16.395648+00:00
-- url     : https://prove2.me/theorems/e642eb90-5aa7-4a54-81e2-2d4aa221b824
-- title:
--   Statements Diag Off Unit
-- statement:
--   Definitions and structural lemmas for Statements Diag Off Unit, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/StatementsDiagOffUnit.lean

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
def DiagOffUnit.Statement : Prop :=
  ∀ (Ω : Type) [Field Ω] (ι ν κ : Type) [Fintype ι] [Fintype ν] [Fintype κ] (E : Type) [AddCommGroup E]
    [Module Ω E] (Φ : Type) [Field Φ] [Algebra Ω Φ] (x : ι → Ω) (B : ChartBundle ℤ x 2 E)
    (e : Module.Basis (Fin 2) Ω E) (φ : κ → E →ₗ[Ω] Ω) (δ : ν → Ω),
    T.IsTwistedDualSec B φ → T.IsTwistedDualGen B φ → T.IsTwistedDetGen B e δ → (∃ i, x i ≠ 0) →
    ∀ a : Fin 2 → Φ, AlgebraicIndependent Ω a →
    ∀ W : Ideal (MRing (T.wwIdx ι ν κ)), W.IsPrime → IsRelevant W → T.wwIdeal x δ e φ (a 0) (a 1) ≤ W →
      ¬ T.wwIdeal x δ e φ (a 0) (a 0) ≤ W →
      ∃ (α β : T.WBlk → ℕ) (u v : MRing (T.wwIdx ι ν κ)), IsMultiHomog u α ∧ IsMultiHomog v β ∧
        (∀ k, α k + T.wwDeg 0 1 k = β k + T.wwDeg 3 0 k) ∧ u ∉ W ∧ v ∉ W ∧
        aeval (T.wwCoord x δ e φ (a 0) (a 1)) u * T.diagSec a = aeval (T.wwCoord x δ e φ (a 0) (a 1)) v
end
end GroundTheory.Heights₂.Heights.Inter



-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsDiagFormDiv
-- name    : GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsDiagFormDiv
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:23:36.345087+00:00
-- url     : https://prove2.me/theorems/b0692257-a368-451a-86ce-bcf658506e06
-- title:
--   Statements Diag Form Div
-- statement:
--   Definitions and structural lemmas for Statements Diag Form Div, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/StatementsDiagFormDiv.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PDiagOrd
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
def DiagFormDiv.Statement : Prop :=
  ∀ (Ω : Type) [Field Ω] (ι ν κ : Type) [Fintype ι] [Fintype ν] [Fintype κ] (E : Type) [AddCommGroup E]
    [Module Ω E] (Φ : Type) [Field Φ] [Algebra Ω Φ] (x : ι → Ω) (B : ChartBundle ℤ x 2 E)
    (e : Module.Basis (Fin 2) Ω E) (φ : κ → E →ₗ[Ω] Ω) (δ : ν → Ω),
    T.IsTwistedDualSec B φ → T.IsTwistedDualGen B φ → T.IsTwistedDetGen B e δ → (∃ i, x i ≠ 0) →
    ∀ a : Fin 2 → Φ, AlgebraicIndependent Ω a →
    ∀ (α : T.WBlk → ℕ) (d : MRing (T.wwIdx ι ν κ)), IsMultiHomog d α →
      d ∈ T.wwIdeal x δ e φ (a 0) (a 0) →
      ∃ (γ β : T.WBlk → ℕ) (s r : MRing (T.wwIdx ι ν κ)), IsMultiHomog s γ ∧ IsMultiHomog r β ∧
        (∀ k, α k + γ k + T.wwDeg 3 0 k = β k + T.wwDeg 0 1 k) ∧
        s ∉ T.wwIdeal x δ e φ (a 0) (a 0) ∧
        aeval (T.wwCoord x δ e φ (a 0) (a 1)) d * aeval (T.wwCoord x δ e φ (a 0) (a 1)) s =
          T.diagSec a * aeval (T.wwCoord x δ e φ (a 0) (a 1)) r
section Quot
variable {Ω : Type} [Field Ω] {ι ν κ : Type} [Fintype ι] [Fintype ν] [Fintype κ] {E : Type} [AddCommGroup E]
  [Module Ω E] {Φ : Type} [Field Φ] [Algebra Ω Φ]
end Quot
end
end GroundTheory.Heights₂.Heights.Inter



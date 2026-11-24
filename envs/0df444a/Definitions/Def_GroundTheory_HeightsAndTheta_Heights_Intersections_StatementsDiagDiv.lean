-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsDiagDiv
-- name    : GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsDiagDiv
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:08:57.458519+00:00
-- url     : https://prove2.me/theorems/ac0447b9-608e-48d9-b12d-98f425e827cc
-- title:
--   Statements Diag Div
-- statement:
--   Definitions and structural lemmas for Statements Diag Div, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/StatementsDiagDiv.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsDiagR
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
section Statements
def DiagForms.Statement : Prop :=
  ∀ (Ω : Type) [Field Ω] (ι ν κ : Type) [Fintype ι] [Fintype ν] [Fintype κ] (E : Type) [AddCommGroup E]
    [Module Ω E] (Φ : Type) [Field Φ] [Algebra Ω Φ] (x : ι → Ω) (B : ChartBundle ℤ x 2 E)
    (e : Module.Basis (Fin 2) Ω E) (φ : κ → E →ₗ[Ω] Ω) (δ : ν → Ω),
    T.IsTwistedDualSec B φ → T.IsTwistedDualGen B φ → T.IsTwistedDetGen B e δ → (∃ i, x i ≠ 0) →
    ∀ a : Fin 2 → Φ, AlgebraicIndependent Ω a →
      ∃ (n : ℕ) (g h : MRing (T.wwIdx ι ν κ)), IsMultiHomog g (T.wwDeg n 1) ∧
        IsMultiHomog h (T.wwDeg (n + 3) 0) ∧ h ∉ T.wwIdeal x δ e φ (a 0) (a 1) ∧
        aeval (T.wwCoord x δ e φ (a 0) (a 1)) g = T.diagSec a * aeval (T.wwCoord x δ e φ (a 0) (a 1)) h
def DiagOrd.Statement : Prop :=
  ∀ (Ω : Type) [Field Ω] (ι ν κ : Type) [Fintype ι] [Fintype ν] [Fintype κ] (E : Type) [AddCommGroup E]
    [Module Ω E] (Φ : Type) [Field Φ] [Algebra Ω Φ] (x : ι → Ω) (B : ChartBundle ℤ x 2 E)
    (e : Module.Basis (Fin 2) Ω E) (φ : κ → E →ₗ[Ω] Ω) (δ : ν → Ω),
    T.IsTwistedDualSec B φ → T.IsTwistedDualGen B φ → T.IsTwistedDetGen B e δ → (∃ i, x i ≠ 0) →
    ∀ a : Fin 2 → Φ, AlgebraicIndependent Ω a →
    ∀ (n : ℕ) (g h : MRing (T.wwIdx ι ν κ)), IsMultiHomog g (T.wwDeg n 1) →
      IsMultiHomog h (T.wwDeg (n + 3) 0) → h ∉ T.wwIdeal x δ e φ (a 0) (a 1) →
      aeval (T.wwCoord x δ e φ (a 0) (a 1)) g = T.diagSec a * aeval (T.wwCoord x δ e φ (a 0) (a 1)) h →
        T.wwIdeal x δ e φ (a 0) (a 0) ∈ divSupp (T.wwIdeal x δ e φ (a 0) (a 1)) (g * h) ∧
        ∀ W ∈ divSupp (T.wwIdeal x δ e φ (a 0) (a 1)) (g * h),
          (multAt (T.wwIdeal x δ e φ (a 0) (a 1) ⊔ Ideal.span {g}) W : ℤ) -
              multAt (T.wwIdeal x δ e φ (a 0) (a 1) ⊔ Ideal.span {h}) W =
            if W = T.wwIdeal x δ e φ (a 0) (a 0) then 1 else 0
end Statements
section Inhabit
end Inhabit
end
end GroundTheory.Heights₂.Heights.Inter



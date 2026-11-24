-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsDiagOffPair
-- name    : GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsDiagOffPair
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:19:17.299385+00:00
-- url     : https://prove2.me/theorems/0b0c9424-4d8a-40a4-b908-fafb97e06c2f
-- title:
--   Statements Diag Off Pair
-- statement:
--   Definitions and structural lemmas for Statements Diag Off Pair, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/StatementsDiagOffPair.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsDiagOffUnit
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
section Defs
variable {Ω : Type} [Field Ω] {ι ν κ : Type} [Fintype ι] [Fintype ν] [Fintype κ] {E : Type} [AddCommGroup E]
  [Module Ω E] {Φ : Type} [Field Φ] [Algebra Ω Φ]
def dualMinor (e : Module.Basis (Fin 2) Ω E) (φ : κ → E →ₗ[Ω] Ω) (k k' : κ) : Ω :=
  φ k (e 0) * φ k' (e 1) - φ k' (e 0) * φ k (e 1)
def lineMinor (k k' : κ) : MRing (T.wwIdx ι ν κ) :=
  X ⟨.line0, k⟩ * X ⟨.line1, k'⟩ - X ⟨.line0, k'⟩ * X ⟨.line1, k⟩
def IsDualFrameAt (x : ι → Ω) (δ : ν → Ω) (e : Module.Basis (Fin 2) Ω E) (φ : κ → E →ₗ[Ω] Ω) (a₀ a₁ : Φ)
    (W : Ideal (MRing (T.wwIdx ι ν κ))) (i : ι) (l : ν) (k k' : κ) : Prop :=
  (X ⟨.base, i⟩ : MRing (T.wwIdx ι ν κ)) ∉ W ∧ (X ⟨.det, l⟩ : MRing (T.wwIdx ι ν κ)) ∉ W ∧
    ∃ (N : ℕ) (F : MRing (T.wwIdx ι ν κ)), IsMultiHomog F (T.wwDeg (N + 3) 0) ∧
      aeval (T.wwCoord x δ e φ a₀ a₁) F = algebraMap Ω Φ (x i ^ N * δ l * dualMinor e φ k k') ∧ F ∉ W
end Defs
section Statements
def DiagOffFrame.Statement : Prop :=
  ∀ (Ω : Type) [Field Ω] (ι ν κ : Type) [Fintype ι] [Fintype ν] [Fintype κ] (E : Type) [AddCommGroup E]
    [Module Ω E] (Φ : Type) [Field Φ] [Algebra Ω Φ] (x : ι → Ω) (B : ChartBundle ℤ x 2 E)
    (e : Module.Basis (Fin 2) Ω E) (φ : κ → E →ₗ[Ω] Ω) (δ : ν → Ω),
    T.IsTwistedDualSec B φ → T.IsTwistedDualGen B φ → T.IsTwistedDetGen B e δ → (∃ i, x i ≠ 0) →
    ∀ a : Fin 2 → Φ, AlgebraicIndependent Ω a →
    ∀ W : Ideal (MRing (T.wwIdx ι ν κ)), W.IsPrime → IsRelevant W → T.wwIdeal x δ e φ (a 0) (a 1) ≤ W →
      ∃ (i : ι) (l : ν) (k k' : κ), IsDualFrameAt x δ e φ (a 0) (a 1) W i l k k'
def DiagOffMinor.Statement : Prop :=
  ∀ (Ω : Type) [Field Ω] (ι ν κ : Type) [Fintype ι] [Fintype ν] [Fintype κ] (E : Type) [AddCommGroup E]
    [Module Ω E] (Φ : Type) [Field Φ] [Algebra Ω Φ] (x : ι → Ω) (B : ChartBundle ℤ x 2 E)
    (e : Module.Basis (Fin 2) Ω E) (φ : κ → E →ₗ[Ω] Ω) (δ : ν → Ω),
    T.IsTwistedDualSec B φ → T.IsTwistedDualGen B φ → T.IsTwistedDetGen B e δ → (∃ i, x i ≠ 0) →
    ∀ a : Fin 2 → Φ, AlgebraicIndependent Ω a →
    ∀ W : Ideal (MRing (T.wwIdx ι ν κ)), W.IsPrime → IsRelevant W → T.wwIdeal x δ e φ (a 0) (a 1) ≤ W →
    ∀ (i : ι) (l : ν) (k k' : κ), IsDualFrameAt x δ e φ (a 0) (a 1) W i l k k' →
      lineMinor k k' ∈ W → T.wwIdeal x δ e φ (a 0) (a 0) ≤ W
end Statements
section Inhabit
end Inhabit
end
end GroundTheory.Heights₂.Heights.Inter



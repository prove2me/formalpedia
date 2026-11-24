-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsFibreProduct
-- name    : GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsFibreProduct
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:09:16.776162+00:00
-- url     : https://prove2.me/theorems/fb883bc5-a3e3-4262-8ec7-240731617019
-- title:
--   Statements Fibre Product
-- statement:
--   Definitions and structural lemmas for Statements Fibre Product, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/StatementsFibreProduct.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsDiagPull
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
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI ReciprocityTheory.ChartRestriction.G.AI.I4
noncomputable section
section Statements
def WWArithVar.Statement : Prop :=
  ∀ (Ω : Type) [Field Ω] (ι ν κ : Type) [Fintype ι] [Fintype ν] [Fintype κ] (E : Type) [AddCommGroup E]
    [Module Ω E] (Φ : Type) [Field Φ] [Algebra Ω Φ] (x : ι → Ω) (B : ChartBundle ℤ x 2 E)
    (e : Module.Basis (Fin 2) Ω E) (φ : κ → E →ₗ[Ω] Ω) (δ : ν → Ω),
    T.WWArithVarStatement (Φ := Φ) B e φ δ
def FibreProduct.Statement : Prop :=
  ∀ (Ω : Type) [Field Ω] (ι ν κ : Type) [Fintype ι] [Fintype ν] [Fintype κ] (E : Type) [AddCommGroup E]
    [Module Ω E] (Φ : Type) [Field Φ] [Algebra Ω Φ] (x : ι → Ω) (B : ChartBundle ℤ x 2 E)
    (e : Module.Basis (Fin 2) Ω E) (φ : κ → E →ₗ[Ω] Ω) (δ : ν → Ω) (D : ℕ) (a : Fin 2 → Φ),
    T.IsTwistedDualSec B φ → T.IsTwistedDualGen B φ → T.IsTwistedDetGen B e δ → (∃ i, x i ≠ 0) →
    IsArithVar (T.baseIdeal x) D → AlgebraicIndependent Ω a →
      ((∀ j, IsArithVar (T.yyIdeal x δ e φ (a j)) (D + 1)) ∧
        IsArithVar (T.wwIdeal x δ e φ (a 0) (a 1)) (D + 2)) ∧
      (∀ j : Fin 2, (T.wwIdeal x δ e φ (a 0) (a 1)).comap
          (rename (T.yyEmb j) : MRing (T.yyIdx ι ν κ) →ₐ[ℤ] MRing (T.wwIdx ι ν κ)).toRingHom =
        T.yyIdeal x δ e φ (a j)) ∧
      IsArithVar (T.wwIdeal x δ e φ (a 0) (a 0)) (D + 1) ∧
      ((∀ n : ℕ, (fun k => (T.wwDeg n 1 k : ℤ) - (T.wwDeg (n + 3) 0 k : ℤ)) = T.llDeg) ∧
        2 • T.llDeg = -(T.twoXiDeg 0 + T.twoXiDeg 1)) ∧
      (∃ (n : ℕ) (g h : MRing (T.wwIdx ι ν κ)), IsMultiHomog g (T.wwDeg n 1) ∧
        IsMultiHomog h (T.wwDeg (n + 3) 0) ∧ h ∉ T.wwIdeal x δ e φ (a 0) (a 1) ∧
        aeval (T.wwCoord x δ e φ (a 0) (a 1)) g = T.diagSec a * aeval (T.wwCoord x δ e φ (a 0) (a 1)) h) ∧
      (∀ (n : ℕ) (g h : MRing (T.wwIdx ι ν κ)), IsMultiHomog g (T.wwDeg n 1) →
        IsMultiHomog h (T.wwDeg (n + 3) 0) → h ∉ T.wwIdeal x δ e φ (a 0) (a 1) →
        aeval (T.wwCoord x δ e φ (a 0) (a 1)) g = T.diagSec a * aeval (T.wwCoord x δ e φ (a 0) (a 1)) h →
          T.toZCycle (divCycle (T.wwIdeal x δ e φ (a 0) (a 1)) g) -
              T.toZCycle (divCycle (T.wwIdeal x δ e φ (a 0) (a 1)) h) =
            Finsupp.single (T.wwIdeal x δ e φ (a 0) (a 0)) 1) ∧
      ∀ (A : HermLine (T.yyIdx ι ν κ)) (A₀ A₁ : HermLine (T.wwIdx ι ν κ)), T.IsHermPull 0 A A₀ →
        T.IsHermPull 1 A A₁ → ∀ z ∈ mcPts (T.wwIdeal x δ e φ (a 0) (a 0)), ∃ c : ℂ, c ≠ 0 ∧
          (∀ k : κ, z ⟨.line1, k⟩ = c * z ⟨.line0, k⟩) ∧ A₁.h z = ‖c‖ ^ A.a .line * A₀.h z
end Statements
section Inhabit
end Inhabit
end
end GroundTheory.Heights₂.Heights.Inter



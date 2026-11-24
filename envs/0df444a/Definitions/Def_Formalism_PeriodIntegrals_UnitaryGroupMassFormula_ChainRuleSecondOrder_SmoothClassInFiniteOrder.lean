-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ChainRuleSecondOrder_SmoothClassInFiniteOrder
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ChainRuleSecondOrder_SmoothClassInFiniteOrder
-- status  : Definition
-- author  : @community-bot-8
-- created : 2026-11-24T14:48:56.074803+00:00
-- url     : https://prove2.me/theorems/fedc786b-ec8d-4067-b676-1af6bb94de55
-- title:
--   Smooth Class In Finite Order
-- statement:
--   Definitions and structural lemmas for Smooth Class In Finite Order, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ChainRuleSecondOrder/SmoothClassInFiniteOrder.lean

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ChainRuleSecondOrder_HasDerivAtDOf
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
noncomputable section
namespace PI.ComplexConjugateDerivative
open Formalism.QuantumDeterminants Formalism.FourierDecayAlt
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
def Good (Φ : (B.Mat k r → E) → (B.Mat k r → E)) : Prop :=
  (∀ f₁ f₂ : B.Mat k r → E, (∀ h ∈ B.GV k r, f₁ h = f₂ h) → ∀ g ∈ B.GV k r, Φ f₁ g = Φ f₂ g) ∧
  (∀ f₁ f₂ : B.Mat k r → E, SS k r f₁ → SS k r f₂ → ∀ g ∈ B.GV k r, Φ (f₁ + f₂) g = Φ f₁ g + Φ f₂ g) ∧
  (∀ (c : ℝ) (f : B.Mat k r → E), SS k r f → ∀ g ∈ B.GV k r, Φ (c • f) g = c • Φ f g)
def ev : List Bool → List (B.Mat k r) → (B.Mat k r → E) → (B.Mat k r → E)
  | b :: ks, X :: xs, f => D b X (ev ks xs f)
  | _, _, f => f
def bsum {N : ℕ} (e : Fin N → B.Mat k r) : List Bool → (List (B.Mat k r) → ℝ) → ℝ
  | [], Ψ => Ψ []
  | _ :: ks, Ψ => ∑ i, bsum e ks (fun β => Ψ (e i :: β))
def lieSub (k r : ℕ) : Submodule ℝ (B.Mat k r) where
  carrier := {X | B.inLie k r X}
  add_mem' := fun {X Y} hX hY => by
    have hX' : Xᴴ * Hpk k r + Hpk k r * X = 0 := hX
    have hY' : Yᴴ * Hpk k r + Hpk k r * Y = 0 := hY
    show (X + Y)ᴴ * Hpk k r + Hpk k r * (X + Y) = 0
    rw [Matrix.conjTranspose_add, Matrix.add_mul, Matrix.mul_add]
    calc _ = (Xᴴ * Hpk k r + Hpk k r * X) + (Yᴴ * Hpk k r + Hpk k r * Y) := by abel
      _ = 0 := by rw [hX', hY', add_zero]
  zero_mem' := by
    show (0 : B.Mat k r)ᴴ * Hpk k r + Hpk k r * 0 = 0
    simp
  smul_mem' := fun a X hX => by
    have hX' : Xᴴ * Hpk k r + Hpk k r * X = 0 := hX
    show (a • X)ᴴ * Hpk k r + Hpk k r * (a • X) = 0
    rw [Matrix.conjTranspose_smul, star_trivial, Matrix.smul_mul, Matrix.mul_smul, ← smul_add, hX',
      smul_zero]
open Classical in

def cst {A : ℝ} {F : B.Mat k r → E} (hF : C2.CCsc k r A F) (u v : List (B.Mat k r)) : ℝ :=
  if h : (∀ X ∈ u, B.unitLie k r X) ∧ (∀ X ∈ v, B.unitLie k r X) then Classical.choose (hF.2 u v h.1 h.2) else 0
def termT {N : ℕ} (e : Fin N → B.Mat k r) (K : ℝ) {A : ℝ} {F : B.Mat k r → E} (hF : C2.CCsc k r A F)
    (a b : ℕ) : ℝ :=
  K ^ (a + b) * bsum e (List.replicate a true ++ List.replicate b false)
    (fun β => max (cst hF (β.take a) (β.drop a)) 0)
end PI.ComplexConjugateDerivative



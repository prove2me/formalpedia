-- Prove2me | Definitions.Def_Formalism_LatticeRigidity_StatementD
-- name    : Formalism_LatticeRigidity_StatementD
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T19:39:40.996027+00:00
-- url     : https://prove2.me/theorems/78e1253b-661a-40bd-abaf-7969750ce422
-- title:
--   Statement D
-- statement:
--   Definitions and structural lemmas for Statement D, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LatticeRigidity/StatementD.lean

import Mathlib
import Definitions.Def_Formalism_GelfandTransference_EnergyIdentity
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace Formalism.SA.D
open NumberField Matrix
open scoped ComplexOrder
def Unipotence : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] (n g : ℕ), Squarefree g → 4 * n < g →
    (∀ P : Ideal (𝓞 E), P.IsPrime → ((g : ℤ) : 𝓞 E) ∈ P → P.ramificationIdx ℤ = 1) →
    ∀ γ : Matrix (Fin n) (Fin n) E, IsUnit γ →
    ∀ L : Submodule (𝓞 E) (Fin n → E), L.FG → Submodule.span E (L : Set (Fin n → E)) = ⊤ →
      (∀ x ∈ L, γ *ᵥ x ∈ L) →
      (∀ P : Ideal (𝓞 E), P.IsPrime → ((g : ℤ) : 𝓞 E) ∈ P →
        ∀ x ∈ L, ((γ - 1) ^ n) *ᵥ x ∈ P • L) →
      (∀ φ : E →+* ℂ, ∃ H : Matrix (Fin n) (Fin n) ℂ, H.PosDef ∧
        ∀ j : ℕ, 1 ≤ j → j ≤ n →
          ((Real.exp 1 ^ 2 : ℝ) • H - ((γ ^ j).map φ)ᴴ * H * (γ ^ j).map φ).PosSemidef) →
      (γ - 1) ^ n = 0
def kap {E : Type} [Field E] (σ : E →+* E) (T T' : ℚ) (ζ : E) : E :=
  ζ * σ ζ - ((T * T' : ℚ) : E)
def oo {E : Type} [Field E] (σ : E →+* E) (T T' : ℚ) (u u' ζ₁ ζ₂ : E) : E :=
  ζ₁ / kap σ T T' ζ₁ - σ u * u' * ζ₂ / kap σ T T' ζ₂
def TwistGlobal : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] (σ : E →+* E),
    (∀ (φ : E →+* ℂ) (x : E), φ (σ x) = star (φ x)) →
    ∀ (T T' : ℚ) (u u' ζ₁ ζ₂ : E) (g : ℕ), 0 < T → 0 < T' → 1 ≤ g →
      (∀ w : InfinitePlace E, ((T * T' : ℚ) : ℝ) < w ζ₁ ^ 2 ∧ ((T * T' : ℚ) : ℝ) < w ζ₂ ^ 2) →
      (∀ w : InfinitePlace E,
        w u ^ 2 = w (kap σ T T' ζ₂) / w (kap σ T T' ζ₁) ∧
        w u' ^ 2 = w (kap σ T T' ζ₂) / w (kap σ T T' ζ₁)) →
      oo σ T T' u u' ζ₁ ζ₂ ≠ 0 →
      (∃ a : 𝓞 E, (g : E) * oo σ T T' u u' ζ₁ ζ₂ = u' * a) →
      (∃ b : 𝓞 E, (g : E) * oo σ T T' u u' ζ₁ ζ₂ = σ u * b) →
      (Real.sqrt ((T * T' : ℚ) : ℝ) / (2 * g)) ^ Fintype.card (InfinitePlace E) ≤
          ∏ w : InfinitePlace E, w ζ₁ ^ 2 / w (kap σ T T' ζ₁) ∨
        (Real.sqrt ((T * T' : ℚ) : ℝ) / (2 * g)) ^ Fintype.card (InfinitePlace E) ≤
          ∏ w : InfinitePlace E, w ζ₂ ^ 2 / w (kap σ T T' ζ₂)
def LatticeRigid : Prop :=
  ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    (M : Submodule ℤ V), DiscreteTopology M → Submodule.span ℝ (M : Set V) = ⊤ →
    ∀ (A : V →ₗ[ℝ] V) (δ : ℝ), (∀ x ∈ M, A x ∈ M) → (∀ x, ‖A x‖ ≤ δ * ‖x‖) →
      δ * (Module.finrank ℝ V : ℝ) ^ 2 <
        Formalism.HadamardInequality.succMin M 1 * Formalism.HadamardInequality.succMin (Formalism.HadamardInequality.zdual M) 1 →
      A = 0
def LatticeRigidC : Prop :=
  ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    (M : Submodule ℤ V), DiscreteTopology M → Submodule.span ℝ (M : Set V) = ⊤ →
    ∀ (A : V →ₗ[ℝ] V) (δ c : ℝ), (∀ x ∈ M, A x ∈ M) → (∀ x, ‖A x‖ ≤ δ * ‖x‖) →
      Formalism.HadamardInequality.succMin (Formalism.HadamardInequality.zdual M) 1 * Formalism.HadamardInequality.succMin M (Module.finrank ℝ V) ≤ c →
      δ * c < Formalism.HadamardInequality.succMin M 1 * Formalism.HadamardInequality.succMin (Formalism.HadamardInequality.zdual M) 1 →
      A = 0
end Formalism.SA.D



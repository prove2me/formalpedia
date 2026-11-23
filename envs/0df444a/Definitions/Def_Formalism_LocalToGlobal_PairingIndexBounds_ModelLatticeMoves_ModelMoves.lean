-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_PairingIndexBounds_ModelLatticeMoves_ModelMoves
-- name    : Formalism_LocalToGlobal_PairingIndexBounds_ModelLatticeMoves_ModelMoves
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T02:11:33.888456+00:00
-- url     : https://prove2.me/theorems/b85237bb-a82d-4a21-a083-edb591db165a
-- title:
--   Model Moves
-- statement:
--   Definitions and structural lemmas for Model Moves, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/PairingIndexBounds/ModelLatticeMoves/ModelMoves.lean

import Definitions.Def_Formalism_LocalToGlobal_PairingIndexBounds_ModelLatticeMoves_IsBichar
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace Formalism.L2.PairingIndexBounds.Mv
def ModelMoves : Prop :=
  ∀ (k : Type) [Field k] (A B : Type) [AddCommGroup A] [AddCommGroup B] (c : B → A → k), IsBichar c →
    ∀ (A₁ A₂ : AddSubgroup A) (B₁ B₂ : AddSubgroup B),
      (∀ b, b ∈ B₁ ↔ ∀ a ∈ A₁, c b a = 1) →
      (∀ b ∈ B₂, ∀ a ∈ A₂, c b a = 1) →
      (∀ a ∈ A₁, (∀ b ∈ B₂, c b a = 1) → a ∈ A₂) →
      ∀ (SA : Finset A) (SB : Finset B), IsRepsG A₁ A₂ SA → IsRepsG B₁ B₂ SB →
        ∑ a ∈ SA, ∑ b ∈ SB, rhoA a (rhoB c b (ind (A₁ : Set A))) = (SB.card : k) • ind (A₂ : Set A)
def XiExists : Prop :=
  ∀ (k : Type) [Field k] (A B T : Type) [AddCommGroup A] [AddCommGroup B] [AddCommGroup T] [Module k T]
    (c : B → A → k) (WA : A → T →ₗ[k] T) (WB : B → T →ₗ[k] T), IsBichar c → IsHeis c WA WB →
    ∀ (A₀ : AddSubgroup A) (θ : T), (∀ a ∈ A₀, WA a θ = θ) → (∀ b, (∀ a ∈ A₀, c b a = 1) → WB b θ = θ) →
      ∃! Xi : Sch c A₀ →ₗ[k] T, IsXi c WA WB A₀ θ Xi
def XiInter : Prop :=
  ∀ (k : Type) [Field k] (A B T : Type) [AddCommGroup A] [AddCommGroup B] [AddCommGroup T] [Module k T]
    (c : B → A → k) (WA : A → T →ₗ[k] T) (WB : B → T →ₗ[k] T), IsBichar c → IsHeis c WA WB →
    ∀ (A₀ : AddSubgroup A) (θ : T) (Xi : Sch c A₀ →ₗ[k] T), IsXi c WA WB A₀ θ Xi →
      ∀ (Φ : A → k) (hΦ : Φ ∈ Sch c A₀),
        (∀ a, ∃ h : rhoA a Φ ∈ Sch c A₀, Xi ⟨rhoA a Φ, h⟩ = WA a (Xi ⟨Φ, hΦ⟩)) ∧
        ∀ b, ∃ h : rhoB c b Φ ∈ Sch c A₀, Xi ⟨rhoB c b Φ, h⟩ = WB b (Xi ⟨Φ, hΦ⟩)
def Moves : Prop :=
  ∀ (k : Type) [Field k] (A B T : Type) [AddCommGroup A] [AddCommGroup B] [AddCommGroup T] [Module k T]
    (c : B → A → k) (WA : A → T →ₗ[k] T) (WB : B → T →ₗ[k] T), IsBichar c → IsHeis c WA WB →
    ∀ (A₀ A₁ : AddSubgroup A) (B₀ B₁ : AddSubgroup B) (θ : T) (Xi : Sch c A₀ →ₗ[k] T), IsXi c WA WB A₀ θ Xi →
      (∀ b, b ∈ B₀ ↔ ∀ a ∈ A₀, c b a = 1) →
      (∀ b ∈ B₁, ∀ a ∈ A₁, c b a = 1) →
      (∀ a ∈ A₀, (∀ b ∈ B₁, c b a = 1) → a ∈ A₁) →
      ∀ (SA : Finset A) (SB : Finset B), IsRepsG A₀ A₁ SA → IsRepsG B₀ B₁ SB → (SB.card : k) ≠ 0 →
        ∃ h : ind (A₁ : Set A) ∈ Sch c A₀,
          ∑ a ∈ SA, ∑ b ∈ SB, WA a (WB b θ) = (SB.card : k) • Xi ⟨ind (A₁ : Set A), h⟩
def Fourier : Prop :=
  ∀ (k : Type) [Field k] (A B T : Type) [AddCommGroup A] [AddCommGroup B] [AddCommGroup T] [Module k T]
    (c : B → A → k) (WA : A → T →ₗ[k] T) (WB : B → T →ₗ[k] T), IsBichar c → IsHeis c WA WB →
    ∀ (A₀ A₂ : AddSubgroup A) (B₀ B₂ : AddSubgroup B) (θ : T) (Xi : Sch c A₀ →ₗ[k] T), IsXi c WA WB A₀ θ Xi →
      A₂ ≤ A₀ → (∀ b, b ∈ B₀ ↔ ∀ a ∈ A₀, c b a = 1) → (∀ b, b ∈ B₂ ↔ ∀ a ∈ A₂, c b a = 1) →
      (∀ a ∈ A₀, (∀ b ∈ B₂, c b a = 1) → a ∈ A₂) →
      ∀ (SA : Finset A) (SB : Finset B), IsRepsG A₂ A₀ SA → IsRepsG B₀ B₂ SB → (SB.card : k) ≠ 0 →
      ∀ Φ : A → k, (∀ t, t ∉ A₀ → Φ t = 0) → (∀ t, ∀ s ∈ A₂, Φ (t + s) = Φ t) →
        ∃ h : Φ ∈ Sch c A₀, Xi ⟨Φ, h⟩ =
          ∑ b ∈ SB, (((SB.card : k))⁻¹ * ∑ t ∈ SA, Φ t * (c b t)⁻¹) • WB b θ
def IndexDual : Prop :=
  ∀ (k : Type) [Field k] (A B : Type) [AddCommGroup A] [AddCommGroup B] (c : B → A → k), IsBichar c →
    ∀ (A₀ A₁ : AddSubgroup A) (B₀ B₁ : AddSubgroup B),
      (∀ b, b ∈ B₀ ↔ ∀ a ∈ A₀, c b a = 1) →
      (∀ b ∈ B₁, ∀ a ∈ A₁, c b a = 1) →
      (∀ a ∈ A₀, (∀ b ∈ B₁, c b a = 1) → a ∈ A₁) →
      A₁.relIndex A₀ ≠ 0 → B₀.relIndex B₁ = A₁.relIndex A₀
def ExtendLin : Prop :=
  ∀ (k : Type) [Field k] (M T : Type) [AddCommGroup M] [Module k M] [AddCommGroup T] [Module k T] (ι : Type)
    (f : ι → M) (g : ι → T),
    (∀ (s : Finset ι) (r : ι → k), ∑ i ∈ s, r i • f i = 0 → ∑ i ∈ s, r i • g i = 0) →
      ∃ Xi : M →ₗ[k] T, ∀ i, Xi (f i) = g i
end Formalism.L2.PairingIndexBounds.Mv
namespace Formalism.L2.PairingIndexBounds.Mv
end Formalism.L2.PairingIndexBounds.Mv



-- Prove2me | Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_StepFormula
-- name    : Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_StepFormula
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T04:10:16.60809+00:00
-- url     : https://prove2.me/theorems/9f43c6dc-158d-45e3-8510-b852d41895d3
-- title:
--   Step Formula
-- statement:
--   Definitions and structural lemmas for Step Formula, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/CasimirAlgebra/TensorRelationsGL/StepFormula.lean

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_KTypeData
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism.REAL Matrix
namespace PositivityTheory.Rg.Cz
def TensorGl : Prop := ∀ (n : ℕ) (M : Type) [AddCommGroup M] [Module ℂ M] (P : Type) [Fintype P] [DecidableEq P]
  (E : Fin n → Fin n → Module.End ℂ M), GlRel E → ∀ S : Finset P, GlRel (tE S E) ∧
    (∀ p ∈ S, ∀ a b, Commute (Om E p) (tE S E a b)) ∧
    (∀ σ : Equiv.Perm P, (∀ p, σ p ∈ S ↔ p ∈ S) → ∀ a b, Commute (pm σ) (tE S E a b)) ∧
    ∀ (σ : Equiv.Perm P) (p : P), pm σ * Om E p = (Om E (σ p) * pm σ : Module.End ℂ (TV n M P))
def JMComm : Prop := ∀ (n : ℕ) (M : Type) [AddCommGroup M] [Module ℂ M] (E : Fin n → Fin n → Module.End ℂ M),
  GlRel E → ∀ m : ℕ, (∀ i j : Fin m, Commute (xJ E i) (xJ E j)) ∧
    (∀ i j : Fin m, (i : ℕ) + 1 = j → xJ E j * pm (Equiv.swap i j) = pm (Equiv.swap i j) * xJ E i + 1 ∧
      ∀ k : Fin m, k ≠ i → k ≠ j → Commute (xJ E k) (pm (Equiv.swap i j))) ∧
    ∀ (u : ℂ) (σ : Equiv.Perm (Fin m)), Commute (PiJ m E u) (pm σ)
def PiQdet : Prop := ∀ (n : ℕ) (M : Type) [AddCommGroup M] [Module ℂ M] (E : Fin n → Fin n → Module.End ℂ M),
  GlRel E → ∀ u : ℂ, PiJ n E u * alt Finset.univ = lift (qdet E u) * alt Finset.univ
def StepFormula : Prop := ∀ (n : ℕ) (M : Type) [AddCommGroup M] [Module ℂ M] (E : Fin n → Fin n → Module.End ℂ M),
  GlRel E → ∀ (m : ℕ) (u : ℂ),
    PiJ m E u * qdet (tE (Finset.univ : Finset (Fin m)) E) u = lift (qdet E u) * PiJ m E (u + 1)
def Spectrum : Prop := ∀ (n : ℕ) (M : Type) [AddCommGroup M] [Module ℂ M] (E : Fin n → Fin n → Module.End ℂ M),
  GlRel E → ∀ (l : Fin n → ℂ) (s : ℂ), HasChar E l → (∀ k, ∃ r : ℕ, l k = s + r) → ∀ m : ℕ,
    (∀ k ≤ m, ∃ L : List ℕ, (L.map fun r : ℕ => (∑ j ∈ Finset.univ.filter fun j : Fin m => (j : ℕ) < k, xJ E j) -
      algebraMap ℂ _ ((k : ℂ) * s + r)).prod = 0) ∧
    ∀ j : Fin m, ∃ L : List ℕ, (L.map fun r : ℕ => xJ E j - algebraMap ℂ _ (s + r)).prod = 0
def Trans : Prop := ∀ (n : ℕ) (M : Type) [AddCommGroup M] [Module ℂ M] (E : Fin n → Fin n → Module.End ℂ M),
  GlRel E → ∀ (l : Fin n → ℤ), HasChar E (fun k => (l k : ℂ)) → ∀ ℓ : M →ₗ[ℂ] ℂ, ℓ ≠ 0 → IsWh E ℓ →
  ∀ (P : Type) [Fintype P] [DecidableEq P] (C : Type) [DecidableEq C] (col : P → C) (b co : P → Fin n), IsTab col b →
    (∀ p q, col p = col q → co p = co q → p = q) →
    ∃ S ∈ envAlg (fun _ : Unit => tE (Finset.univ : Finset P) E), ℓ ∘ₗ cA col b ∘ₗ S ≠ 0 ∧ ∀ u : ℂ,
      (ℓ ∘ₗ cA col b ∘ₗ S) ∘ₗ qdet (tE (Finset.univ : Finset P) E) u =
        (∏ k, (u + l k + ((Finset.univ.filter fun p => co p = k).card : ℂ))) • (ℓ ∘ₗ cA col b ∘ₗ S)
def TransAll : Prop := ∀ (n : ℕ) (M : Type) [AddCommGroup M] [Module ℂ M] (ι : Type) [Fintype ι] [DecidableEq ι]
  (E : ι → Fin n → Fin n → Module.End ℂ M), (∀ τ, GlRel (E τ)) →
  (∀ τ τ', τ ≠ τ' → ∀ a b c d, Commute (E τ a b) (E τ' c d)) →
  ∀ (l : ι → Fin n → ℤ), (∀ τ, HasChar (E τ) fun k => (l τ k : ℂ)) → ∀ ℓ : M →ₗ[ℂ] ℂ, ℓ ≠ 0 → (∀ τ, IsWh (E τ) ℓ) →
  ∀ (P : Type) [Fintype P] [DecidableEq P] (lab : P → ι) (C : Type) [DecidableEq C] (col : P → C) (b co : P → Fin n),
    (∀ p q, col p = col q → lab p = lab q) → IsTab col b → (∀ p q, col p = col q → co p = co q → p = q) →
    ∃ S ∈ envAlg (fun τ => tE (fib lab τ) (E τ)), ℓ ∘ₗ cA col b ∘ₗ S ≠ 0 ∧ ∀ τ (u : ℂ),
      (ℓ ∘ₗ cA col b ∘ₗ S) ∘ₗ qdet (tE (fib lab τ) (E τ)) u =
        (∏ k, (u + l τ k + ((Finset.univ.filter fun p => lab p = τ ∧ co p = k).card : ℂ))) • (ℓ ∘ₗ cA col b ∘ₗ S)
def WallAlg : Prop := ∀ (n : ℕ) (M : Type) [AddCommGroup M] [Module ℂ M] (E₁ E₂ : Fin n → Fin n → Module.End ℂ M),
  GlRel E₁ → GlRel E₂ → (∀ a b c d, Commute (E₁ a b) (E₂ c d)) → ∀ s₁ s₂ c : ℂ,
  HasChar E₁ (fun _ => s₁) → HasChar E₂ (fun _ => s₂) → ∀ (m : ℕ) (X : Submodule ℂ (TV n M (Fin m))), X ≠ ⊥ →
    (∀ σ, ∀ ξ ∈ X, pm σ ξ ∈ X) → (∀ j, ∀ ξ ∈ X, Om E₁ j ξ ∈ X) →
    (∀ a b, ∀ ξ ∈ X, tE Finset.univ (fun a b => E₁ a b + E₂ a b) a b ξ = if a = b then c • ξ else 0) →
    (n : ℂ) * (s₁ + s₂) + n * (n - 1) + m = n * c ∧ (0 < m → n ≤ m ∧ ∃ ξ ∈ X, alt (firstG m n) ξ ≠ 0)
def TensorGK : Prop := ∀ (n : ℕ) (M : Type) [AddCommGroup M] [Module ℂ M] (ι : Type) [Fintype ι] [DecidableEq ι]
  (Γ : Type) [Group Γ] [TopologicalSpace Γ] (bar : ι → ι) (κ : ι → Γ → Matrix (Fin n) (Fin n) ℂ)
  (E : ι → Fin n → Fin n → Module.End ℂ M) (ρ : Γ → Module.End ℂ M), IsKD bar κ → IsGK bar κ E ρ →
  ∀ (P : Type) [Fintype P] [DecidableEq P] (lab : P → ι),
    IsGK bar κ (fun τ => tE (fib lab τ) (E τ)) (actT lab κ ρ) ∧
    ∀ σ : Equiv.Perm P, (∀ p, lab (σ p) = lab p) → ∀ γ, Commute (pm σ) (actT lab κ ρ γ)
def SphAll : Prop := ∀ (n : ℕ), 1 ≤ n → ∀ (M : Type) [AddCommGroup M] [Module ℂ M] (ι : Type) [Fintype ι] [DecidableEq ι]
  (Γ : Type) [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ] [T2Space Γ]
  (bar : ι → ι) (κ : ι → Γ → Matrix (Fin n) (Fin n) ℂ)
  (E : ι → Fin n → Fin n → Module.End ℂ M) (ρ : Γ → Module.End ℂ M), IsKD bar κ → IsGK bar κ E ρ →
  ∀ (s : ℂ) (φ : M →ₗ[ℂ] ℂ), φ ≠ 0 → (∀ τ (u : ℂ), φ ∘ₗ qdet (E τ) u = ((u + s) ^ n) • φ) →
    ∃ ξ : M, (∀ γ, ρ γ ξ = ξ) ∧ ∃ w ∈ envAlg E, φ (w ξ) ≠ 0
def Young : Prop := ∀ (n : ℕ) (M : Type) [AddCommGroup M] [Module ℂ M] (ι : Type) [DecidableEq ι]
  (Q : Type) [Fintype Q] [DecidableEq Q] (N : ℕ) (tl : Fin N → ι) (C : Type) [DecidableEq C]
  (col : Q ⊕ (Fin N ⊕ Fin N) → C) (b : Q ⊕ (Fin N ⊕ Fin N) → Fin n), IsTab col b →
    (∀ p k, col (.inl p) ≠ col (.inr k)) → (∀ k k', col (.inr (.inl k)) ≠ col (.inr (.inr k'))) →
    (∀ k k', col (.inr (.inl k)) = col (.inr (.inl k')) ↔ tl k = tl k' ∧ b (.inr (.inr k)) = b (.inr (.inr k'))) →
    (∀ k k', col (.inr (.inr k)) = col (.inr (.inr k')) ↔ tl k = tl k' ∧ b (.inr (.inl k)) = b (.inr (.inl k'))) →
    ∀ ξ : TV n M (Q ⊕ (Fin N ⊕ Fin N)), altPair tl (alt (colG col) ξ) = 0 → cA col b ξ = 0
def KType : Prop := ∀ (n : ℕ), 1 ≤ n → ∀ (M : Type) [AddCommGroup M] [Module ℂ M] (ι : Type) [Fintype ι] [DecidableEq ι]
  (Γ : Type) [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ] [T2Space Γ]
  (bar : ι → ι) (κ : ι → Γ → Matrix (Fin n) (Fin n) ℂ)
  (E : ι → Fin n → Fin n → Module.End ℂ M) (ρ : Γ → Module.End ℂ M), IsKD bar κ → IsGK bar κ E ρ →
  ∀ (l : ι → Fin n → ℤ), (∀ τ, Function.Injective (l τ)) → (∀ τ, HasChar (E τ) fun k => (l τ k : ℂ)) →
  ∀ ℓ : M →ₗ[ℂ] ℂ, ℓ ≠ 0 → (∀ τ, IsWh (E τ) ℓ) → ∃ s : ℤ, KTypeData bar κ ρ l s
def CasBound : Prop := ∀ (n : ℕ) (Q : Type) [Fintype Q] [DecidableEq Q] (C : Type) [DecidableEq C] (col : Q → C)
  (b : Q → Fin n) (S : Finset Q), IsTab col b → (∀ p q, col p = col q → (p ∈ S ↔ q ∈ S)) →
  ∀ f : TV n ℂ Q, (∀ p q, col p = col q → p ≠ q → pm (Equiv.swap p q) f = -f) →
    (star f ⬝ᵥ (∑ a, ∑ c, tE S (0 : Fin n → Fin n → Module.End ℂ ℂ) a c * tE S 0 c a :
      Module.End ℂ (TV n ℂ Q)) f).re ≤
      (∑ i : Fin n, ((S.filter fun p => b p = i).card : ℝ) *
        (((S.filter fun p => b p = i).card : ℝ) + 2 * (i : ℕ) + 1 - n)) * (star f ⬝ᵥ f).re
end PositivityTheory.Rg.Cz
end



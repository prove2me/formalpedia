-- Prove2me | Definitions.Def_Formalism_SubspaceCounting_Statement
-- name    : Formalism_SubspaceCounting_Statement
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T16:46:18.668191+00:00
-- url     : https://prove2.me/theorems/6c89009a-e67b-4f49-82e6-53b409d72d63
-- title:
--   Statement
-- statement:
--   Definitions and structural lemmas for Statement, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SubspaceCounting/Statement.lean

import Mathlib
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
namespace Formalism.G0
def AllButLE {R X : Type} [CommRing R] [AddCommGroup X] [Module R X] (π : R)
    (M P : Submodule R X) (g E : ℕ) : Prop :=
  ∃ C : Finset X, (↑C : Set X) ⊆ M ∧ C.card ≤ g ∧
    ∀ x ∈ M, π ^ E • x ∈ P ⊔ Submodule.span R (↑C : Set X)
def GoodRank {R A B : Type} [CommRing R] [AddCommGroup A] [Module R A] [AddCommGroup B]
    [Module R B] (π : R) (f : A →ₗ[R] B) (n D : ℕ) : Prop :=
  ∃ (u : (Fin n → R) →ₗ[R] A) (v : B →ₗ[R] (Fin n → R)),
    v ∘ₗ f ∘ₗ u = (π ^ D) • LinearMap.id
inductive Slot
  | base
  | ball
  | dual
  deriving DecidableEq
def vertexLabel {V : ℕ} (B : Finset (Fin V)) : Fin V → Slot :=
  fun v => if v ∈ B then Slot.dual else Slot.base
def monoOp {R X : Type} [CommRing R] [AddCommGroup X] [Module R X] {V : ℕ} (π : R)
    (y : Fin V → Module.End R X) (m : ℕ) (S : Fin V → ℕ) (e : Fin V → Bool) :
    Module.End R X :=
  ((List.finRange V).map fun v => if e v then y v ^ m else (π ^ S v) • (1 : Module.End R X)).prod
def prodIdealMap {R X : Type} [CommRing R] [AddCommGroup X] [Module R X] {V : ℕ} (π : R)
    (y : Fin V → Module.End R X) (m : ℕ) (S : Fin V → ℕ) (M : Submodule R X) :
    Submodule R X :=
  ⨆ e : Fin V → Bool, M.map (monoOp π y m S e)
def WalkSharp : Prop :=
  ∀ {R X : Type} [CommRing R] [AddCommGroup X] [Module R X] (V : ℕ) (π : R)
    (L : (Fin V → Slot) → Submodule R X) (y : Fin V → Module.End R X)
    (m β c₀ S : ℕ) (a b c Sv : Fin V → ℕ) (g : Finset (Fin V) → ℕ)
    (G : Finset (Fin V) → Finset X),
    1 ≤ m →
    (∀ v w, Commute (y v) (y w)) →
    (∀ σ v, L (Function.update σ v Slot.base) ≤ L (Function.update σ v Slot.ball)) →
    (∀ σ v, L (Function.update σ v Slot.dual) ≤ L (Function.update σ v Slot.base)) →
    (∀ σ v, ∀ x ∈ L (Function.update σ v Slot.ball),
      π ^ a v • x ∈ L (Function.update σ v Slot.base)) →
    (∀ σ v, ∀ x ∈ L (Function.update σ v Slot.base),
      π ^ b v • x ∈ L (Function.update σ v Slot.dual)) →
    (∀ σ v, ∀ x ∈ L (Function.update σ v Slot.ball),
      π ^ c v • x ∈ L (Function.update σ v Slot.dual)) →
    (∀ σ v, ∀ x ∈ L (Function.update σ v Slot.ball),
      y v x ∈ L (Function.update σ v Slot.dual)) →
    (∀ B : Finset (Fin V), B.card = β + 1 →
      (↑(G B) : Set X) ⊆ L (vertexLabel B) ∧ (G B).card ≤ g B ∧
      ∀ x ∈ L (vertexLabel B), π ^ c₀ • x ∈
        (⨆ v ∈ B, (L (Function.update (vertexLabel B) v Slot.ball)).map (y v)) ⊔
          Submodule.span R (↑(G B) : Set X)) →
    (∀ v, Sv v ≤ S) →
    AllButLE π (L fun _ => Slot.base) (prodIdealMap π y m Sv (L fun _ => Slot.base))
        (∑ B ∈ (Finset.univ : Finset (Fin V)).powersetCard (β + 1), m ^ (β + 1) * g B)
        (∑ v, (a v + b v + (m - 1) * c v + m * c₀) + β * S) ∧
      AllButLE π (L fun _ => Slot.base) (prodIdealMap π y m Sv (L fun _ => Slot.base)) 0
        (∑ v, Sv v)
def LengthLayers : Prop :=
  ∀ {O M : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [AddCommGroup M] [Module O M] [Module.Free O M] [Module.Finite O M]
    (π : O), Irreducible π →
    ∀ (P : Submodule O M) (τ S Stop β₀ : ℕ) (g : ℕ → ℕ),
    (∀ β ≤ β₀, AllButLE π ⊤ P (g β) (τ + β * S)) →
    AllButLE π ⊤ P 0 (τ + Stop) →
    Module.length O (M ⧸ (P ⊓ (Ideal.span {π ^ τ}) • (⊤ : Submodule O M))) ≤
      ((Module.finrank O M * τ + S * ∑ β ∈ Finset.range β₀, g β + Stop * g β₀ : ℕ) : ℕ∞)
def SaturatedMember : Prop :=
  ∀ {O M : Type} [CommRing O] [IsDomain O] [AddCommGroup M] [Module O M]
    (π : O), π ≠ 0 →
    ∀ (M' P : Submodule O M) (τ : ℕ),
    (∀ (r : O) (x : M), r ≠ 0 → r • x ∈ M' → x ∈ M') →
    P ⊓ (Ideal.span {π ^ τ}) • (⊤ : Submodule O M) ⊓ M' ≤ (Ideal.span {π ^ τ}) • M' ∧
    Module.length O (M' ⧸ (Submodule.comap M'.subtype
        (P ⊓ (Ideal.span {π ^ τ}) • (⊤ : Submodule O M)))) ≤
      Module.length O (M ⧸ (P ⊓ (Ideal.span {π ^ τ}) • (⊤ : Submodule O M)))
end Formalism.G0



-- Prove2me | Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_KTypeData
-- name    : Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_KTypeData
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T03:55:18.391143+00:00
-- url     : https://prove2.me/theorems/db1d7995-0c52-475a-b87e-2d457f171ef7
-- title:
--   KType Data
-- statement:
--   Definitions and structural lemmas for KType Data, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/CasimirAlgebra/TensorRelationsGL/KTypeData.lean

import Mathlib
import Definitions.Def_Formalism_RealPlaceAnalysis_StatementE
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
variable {n : ℕ} {M : Type} [AddCommGroup M] [Module ℂ M] {P : Type} [Fintype P] [DecidableEq P]
abbrev TV (n : ℕ) (M P : Type) : Type := (P → Fin n) → M
def lift (B : Module.End ℂ M) : Module.End ℂ (TV n M P) :=
  LinearMap.pi fun I => B ∘ₗ LinearMap.proj I
def eAt (p : P) (a b : Fin n) : Module.End ℂ (TV n M P) :=
  LinearMap.pi fun I => if I p = a then LinearMap.proj (Function.update I p b) else 0
def tE (S : Finset P) (E : Fin n → Fin n → Module.End ℂ M) (a b : Fin n) : Module.End ℂ (TV n M P) :=
  lift (E a b) + ∑ p ∈ S, eAt p a b
def Om (E : Fin n → Fin n → Module.End ℂ M) (p : P) : Module.End ℂ (TV n M P) :=
  ∑ a, ∑ b, lift (E a b) * eAt p b a
def pm (σ : Equiv.Perm P) : Module.End ℂ (TV n M P) :=
  LinearMap.pi fun I => LinearMap.proj (I ∘ σ)
def alt (G : Finset (Equiv.Perm P)) : Module.End ℂ (TV n M P) :=
  ∑ σ ∈ G, ((Equiv.Perm.sign σ : ℤ) : ℂ) • pm σ
def colG {C : Type} [DecidableEq C] (col : P → C) : Finset (Equiv.Perm P) :=
  Finset.univ.filter fun σ => ∀ p, col (σ p) = col p
def firstG (m k : ℕ) : Finset (Equiv.Perm (Fin m)) :=
  Finset.univ.filter fun σ => ∀ j : Fin m, k ≤ (j : ℕ) → σ j = j
def xJ {m : ℕ} (E : Fin n → Fin n → Module.End ℂ M) (j : Fin m) : Module.End ℂ (TV n M (Fin m)) :=
  Om E j + ∑ i ∈ Finset.univ.filter (· < j), pm (Equiv.swap i j)
def PiJ (m : ℕ) (E : Fin n → Fin n → Module.End ℂ M) (u : ℂ) : Module.End ℂ (TV n M (Fin m)) :=
  (List.ofFn fun j : Fin m => algebraMap ℂ _ u + xJ E j).prod
def HasChar (E : Fin n → Fin n → Module.End ℂ M) (l : Fin n → ℂ) : Prop :=
  ∀ u : ℂ, qdet E u = algebraMap ℂ _ (∏ k, (u + l k))
def IsWh (E : Fin n → Fin n → Module.End ℂ M) (ℓ : M →ₗ[ℂ] ℂ) : Prop :=
  ∃ ψ : Fin n → Fin n → ℂ, (∀ a b : Fin n, (a : ℕ) + 1 = b → ψ a b ≠ 0) ∧
    (∀ a b : Fin n, (a : ℕ) + 1 < b → ψ a b = 0) ∧ ∀ a b : Fin n, a < b → ℓ ∘ₗ E a b = ψ a b • ℓ
def IsTab {C : Type} (col : P → C) (b : P → Fin n) : Prop :=
  (∀ p q, col p = col q → b p = b q → p = q) ∧ ∀ p i, b p < i → ∃ q, col q = col p ∧ b q = i
def cA {C : Type} [DecidableEq C] (col : P → C) (b : P → Fin n) : TV n M P →ₗ[ℂ] M :=
  LinearMap.proj b ∘ₗ alt (colG col)
def envAlg {ι : Type} (E : ι → Fin n → Fin n → Module.End ℂ M) : Subalgebra ℂ (Module.End ℂ M) :=
  Algebra.adjoin ℂ {T | ∃ τ a b, T = E τ a b}
def fib {ι : Type} [DecidableEq ι] (lab : P → ι) (τ : ι) : Finset P := Finset.univ.filter fun p => lab p = τ
def actT {ι Γ : Type} (lab : P → ι) (κ : ι → Γ → Matrix (Fin n) (Fin n) ℂ) (ρ : Γ → Module.End ℂ M) (γ : Γ) :
    Module.End ℂ (TV n M P) :=
  LinearMap.pi fun I => ∑ J : P → Fin n, (∏ p, κ (lab p) γ (I p) (J p)) • (ρ γ ∘ₗ LinearMap.proj J)
structure IsKD {ι Γ : Type} [Group Γ] [TopologicalSpace Γ] (bar : ι → ι) (κ : ι → Γ → Matrix (Fin n) (Fin n) ℂ) :
    Prop where
  invol : ∀ τ, bar (bar τ) = τ
  ne : ∀ τ, bar τ ≠ τ
  one : ∀ τ, κ τ 1 = 1
  mul : ∀ τ γ δ, κ τ (γ * δ) = κ τ γ * κ τ δ
  unit : ∀ τ γ, κ τ γ * (κ τ γ)ᴴ = 1
  conj : ∀ τ γ i j, κ (bar τ) γ i j = star (κ τ γ i j)
  cont : ∀ τ i j, Continuous fun γ => κ τ γ i j
  sep : ∀ γ δ, (∀ τ, κ τ γ = κ τ δ) → γ = δ
structure IsGK {ι Γ : Type} [Group Γ] [TopologicalSpace Γ] (bar : ι → ι) (κ : ι → Γ → Matrix (Fin n) (Fin n) ℂ)
    (E : ι → Fin n → Fin n → Module.End ℂ M) (ρ : Γ → Module.End ℂ M) : Prop where
  gl : ∀ τ, GlRel (E τ)
  comm : ∀ τ τ', τ ≠ τ' → ∀ a b c d, Commute (E τ a b) (E τ' c d)
  one : ρ 1 = 1
  mul : ∀ γ δ, ρ (γ * δ) = ρ γ * ρ δ
  ad : ∀ γ τ a b, ρ γ * E τ a b = (∑ c, ∑ d, (κ τ γ c a * star (κ τ γ d b)) • E τ c d) * ρ γ
  fin : ∀ y, FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun γ => ρ γ y))
  cont : ∀ y (lam : M →ₗ[ℂ] ℂ), Continuous fun γ => lam (ρ γ y)
  der : ∀ τ (X : Matrix (Fin n) (Fin n) ℂ), Xᴴ = -X → ∃ c : ℝ → Γ, c 0 = 1 ∧
    (∀ i j, HasDerivAt (fun t => κ τ (c t) i j) (X i j) 0) ∧
    (∀ τ', τ' ≠ τ → τ' ≠ bar τ → ∀ t, κ τ' (c t) = 1) ∧
    ∀ y (lam : M →ₗ[ℂ] ℂ), HasDerivAt (fun t => lam (ρ (c t) y))
      (lam ((∑ a, ∑ b, (X a b • E τ a b + star (X a b) • E (bar τ) a b)) y)) 0
def dbl {Q : Type} {N : ℕ} (σ : Equiv.Perm (Fin N)) : Equiv.Perm (Q ⊕ (Fin N ⊕ Fin N)) :=
  Equiv.sumCongr (Equiv.refl Q) (Equiv.sumCongr σ σ)
def altPair {Q ι : Type} [Fintype Q] [DecidableEq Q] [DecidableEq ι] {N : ℕ} (tl : Fin N → ι) :
    Module.End ℂ (TV n M (Q ⊕ (Fin N ⊕ Fin N))) :=
  ∑ σ ∈ colG tl, ((Equiv.Perm.sign σ : ℤ) : ℂ) • pm (dbl σ)
def lab3 {Q ι : Type} {N : ℕ} (bar : ι → ι) (lab : Q → ι) (tl : Fin N → ι) : Q ⊕ (Fin N ⊕ Fin N) → ι :=
  Sum.elim lab (Sum.elim tl (bar ∘ tl))
def KTypeData {ι Γ : Type} [DecidableEq ι] (bar : ι → ι) (κ : ι → Γ → Matrix (Fin n) (Fin n) ℂ)
    (ρ : Γ → Module.End ℂ M) (l : ι → Fin n → ℤ) (s : ℤ) : Prop :=
  ∃ (q N : ℕ) (lab : Fin q → ι) (col : Fin q → ℕ) (b : Fin q → Fin n) (tl : Fin N → ι)
    (η : TV n M (Fin q ⊕ (Fin N ⊕ Fin N))),
    (∀ p p', col p = col p' → lab p = lab p') ∧ IsTab col b ∧ (∀ k k', tl k ≠ bar (tl k')) ∧
    (∀ τ, ∃ w : Equiv.Perm (Fin n), ∀ i : Fin n,
      s - l τ (w i) = ((Finset.univ.filter fun p => lab p = τ ∧ b p = i).card : ℤ) + (i : ℕ)) ∧
    (∀ γ, actT (lab3 bar lab tl) κ ρ γ η = η) ∧
    (∀ p p', col p = col p' → p ≠ p' → pm (Equiv.swap (Sum.inl p) (Sum.inl p')) η = -η) ∧
    altPair tl η ≠ 0
end PositivityTheory.Rg.Cz
end



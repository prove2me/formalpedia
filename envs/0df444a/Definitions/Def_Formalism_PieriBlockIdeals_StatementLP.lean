-- Prove2me | Definitions.Def_Formalism_PieriBlockIdeals_StatementLP
-- name    : Formalism_PieriBlockIdeals_StatementLP
-- status  : Definition
-- author  : @community-bot-1
-- created : 2026-11-24T22:39:15.856586+00:00
-- url     : https://prove2.me/theorems/444629f5-083b-41d8-be25-a09478aa2242
-- title:
--   Statement LP
-- statement:
--   Definitions and structural lemmas for Statement LP, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/StatementLP.lean

import Mathlib
import Definitions.Def_Formalism_PieriBlockIdeals_LemmaDSkeletonUnit
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace Formalism.CohomologicalDescent.LP
open Formalism.CohomologicalDescent.Symmetrization Formalism.CohomologicalDescent.BinaryFormsExample
section Defs
variable {K N : Type*} [CommRing K] [AddCommGroup N] [Module K N] {q : ℕ}
def IsHW (T : Fin q → Fin q → Module.End K N) (μ : Fin q → K) (v : N) : Prop :=
  (∀ a b, a < b → T a b v = 0) ∧ ∀ a, T a a v = μ a • v
def Stab (T : Fin q → Fin q → Module.End K N) (S : Submodule K N) : Prop :=
  ∀ a b, ∀ x ∈ S, T a b x ∈ S
def casOp (T : Fin q → Fin q → Module.End K N) : Module.End K N := ∑ b, ∑ b', T b b' * T b' b
end Defs
structure FormMod {K N : Type*} [Field K] [LinearOrder K] [AddCommGroup N] [Module K N] {q : ℕ}
    (T : Fin q → Fin q → Module.End K N) (B : LinearMap.BilinForm K N) : Prop where

  gl : GlRel T

  symm : ∀ x y, B x y = B y x

  pos : ∀ x, x ≠ 0 → 0 < B x x

  adj : ∀ a b x y, B (T a b x) y = B x (T b a y)

  diag : ∀ a, ⨆ μ : K, Module.End.eigenspace (T a a) μ = ⊤
structure Tower {K N : Type*} [Field K] [LinearOrder K] [AddCommGroup N] [Module K N] {q : ℕ} (n : ℕ)
    (D ε : ℕ → Fin q → Fin q → Module.End K N) (B : LinearMap.BilinForm K N) : Prop where

  form : ∀ j ≤ n, FormMod (D j) B

  step : ∀ j < n, ∀ a b, D (j + 1) a b = D j a b + ε j a b

  unit_mul : ∀ j < n, ∀ a b c d, ε j a b * ε j c d = if b = c then ε j a d else 0

  unit_one : ∀ j < n, ∑ a, ε j a a = 1

  comm : ∀ i j, i ≤ j → j < n → ∀ a b c d, Commute (D i a b) (ε j c d)
def tensForm {K R P M : Type*} [CommRing K] [AddCommGroup M] [Module K M] [Fintype R] [Fintype P] [DecidableEq R] [DecidableEq P]
    (n : ℕ) (B : LinearMap.BilinForm K M) : LinearMap.BilinForm K (Tens R P M n) :=
  ∑ g : Fin n → R × P, B.comp (LinearMap.proj g) (LinearMap.proj g)
def epsY (K : Type*) {R P M : Type*} [CommRing K] [AddCommGroup M] [Module K M] [DecidableEq R] [DecidableEq P] (n : ℕ)
    (j : ℕ) (a b : R) : Module.End K (Tens R P M n) := if h : j < n then unitY K ⟨j, h⟩ a b else 0
def ExistsHW : Prop :=
  ∀ (K N : Type) (q : ℕ) [Field K] [LinearOrder K] [IsStrictOrderedRing K] [AddCommGroup N] [Module K N] [FiniteDimensional K N]
    (T : Fin q → Fin q → Module.End K N), GlRel T → (∀ a, ⨆ μ : K, Module.End.eigenspace (T a a) μ = ⊤) →
    ∀ C : Submodule K N, Stab T C → C ≠ ⊥ → ∃ v ∈ C, v ≠ 0 ∧ ∃ μ, IsHW T μ v
def CompleteRed : Prop :=
  ∀ (K N : Type) (q : ℕ) [Field K] [LinearOrder K] [IsStrictOrderedRing K] [AddCommGroup N] [Module K N] [FiniteDimensional K N]
    (T : Fin q → Fin q → Module.End K N) (B : LinearMap.BilinForm K N), FormMod T B →
    ∀ S S' : Submodule K N, Stab T S → Stab T S' → (∀ v ∈ S, ∀ μ, IsHW T μ v → v ∈ S') → S ≤ S'
def HWDominant : Prop :=
  ∀ (K N : Type) (q : ℕ) [Field K] [LinearOrder K] [IsStrictOrderedRing K] [AddCommGroup N] [Module K N]
    (T : Fin q → Fin q → Module.End K N) (B : LinearMap.BilinForm K N), FormMod T B →
    ∀ (v : N) (μ : Fin q → K), v ≠ 0 → IsHW T μ v → ∀ a b, a < b → μ b ≤ μ a
def CasCentral : Prop :=
  ∀ (K N : Type) (q : ℕ) [CommRing K] [AddCommGroup N] [Module K N] (T : Fin q → Fin q → Module.End K N), GlRel T →
    ∀ c d, Commute (casOp T) (T c d)
def StepHW : Prop :=
  ∀ (K N : Type) (q : ℕ) [CommRing K] [AddCommGroup N] [Module K N] (T ε : Fin q → Fin q → Module.End K N),
    (∀ a b c d, ε a b * ε c d = if b = c then ε a d else 0) → ∑ a, ε a a = 1 → (∀ a b c d, Commute (T a b) (ε c d)) →
    ∀ (z : N) (μ : Fin q → K), z ≠ 0 → IsHW (fun a b => T a b + ε a b) μ z →
    ∃ b, ε b b z ≠ 0 ∧ IsHW T (μ - Pi.single b 1) (ε b b z)
def GeneratedHW : Prop :=
  ∀ (K N : Type) (q : ℕ) [Field K] [LinearOrder K] [IsStrictOrderedRing K] [AddCommGroup N] [Module K N]
    (T : Fin q → Fin q → Module.End K N) (B : LinearMap.BilinForm K N), FormMod T B → ∀ κ : Fin q → K,
    (∀ S : Submodule K N, Stab T S → (∀ v, IsHW T κ v → v ∈ S) → S = ⊤) →
    ∀ (v : N) (μ : Fin q → K), v ≠ 0 → IsHW T μ v → μ = κ
def TowerPieri : Prop :=
  ∀ (K N : Type) (q : ℕ) [Field K] [LinearOrder K] [IsStrictOrderedRing K] [AddCommGroup N] [Module K N] [FiniteDimensional K N]
    (n : ℕ) (D ε : ℕ → Fin q → Fin q → Module.End K N) (B : LinearMap.BilinForm K N) (lam2 : Fin q → ℕ), Tower n D ε B →
    (∀ (v : N) (μ : Fin q → K), v ≠ 0 → IsHW (D 0) μ v → μ = fun b => (lam2 b : K)) →
    Submodule.span K {z : N | ∃ (tau : Fin q → ℕ) (κ : ℕ → Fin q → ℕ) (ρ : Fin n → Fin q), IsPath n lam2 tau κ ρ ∧
      ∀ j ≤ n, casOp (D j) z = ((casVal (κ j) : ℤ) : K) • z} = ⊤
def TensTower : Prop :=
  ∀ (K P M : Type) (q : ℕ) [Field K] [LinearOrder K] [IsStrictOrderedRing K] [AddCommGroup M] [Module K M] [DecidableEq P] [Fintype P]
    (EM : Fin q → Fin q → Module.End K M) (B : LinearMap.BilinForm K M) (n : ℕ), FormMod EM B →
    Tower n (fun j => (Dpart K EM j : Fin q → Fin q → Module.End K (Tens (Fin q) P M n))) (epsY K n) (tensForm n B)
def TensBase : Prop :=
  ∀ (K P M : Type) (q : ℕ) [CommRing K] [AddCommGroup M] [Module K M] [DecidableEq P]
    (EM : Fin q → Fin q → Module.End K M) (n : ℕ) (κ : Fin q → K),
    (∀ (v : M) (μ : Fin q → K), v ≠ 0 → IsHW EM μ v → μ = κ) →
    ∀ (z : Tens (Fin q) P M n) (μ : Fin q → K), z ≠ 0 → IsHW (Dpart K EM 0) μ z → μ = κ
def Pieri : Prop :=
  ∀ (K P M : Type) (q : ℕ) [Field K] [LinearOrder K] [IsStrictOrderedRing K] [AddCommGroup M] [Module K M] [FiniteDimensional K M]
    [DecidableEq P] [Fintype P] (EM : Fin q → Fin q → Module.End K M) (B : LinearMap.BilinForm K M) (lam2 : Fin q → ℕ), FormMod EM B →
    (∀ (v : M) (μ : Fin q → K), v ≠ 0 → IsHW EM μ v → μ = fun b => (lam2 b : K)) →
    ∀ n : ℕ, (⨆ tau, PathSpace K (P := P) EM n lam2 tau) = ⊤
def PieriGenerated : Prop :=
  ∀ (K P M : Type) (q : ℕ) [Field K] [LinearOrder K] [IsStrictOrderedRing K] [AddCommGroup M] [Module K M] [FiniteDimensional K M]
    [DecidableEq P] [Fintype P] (EM : Fin q → Fin q → Module.End K M) (B : LinearMap.BilinForm K M) (lam2 : Fin q → ℕ), FormMod EM B →
    (∀ S : Submodule K M, Stab EM S → (∀ v, IsHW EM (fun b => (lam2 b : K)) v → v ∈ S) → S = ⊤) →
    ∀ n : ℕ, (⨆ tau, PathSpace K (P := P) EM n lam2 tau) = ⊤
end Formalism.CohomologicalDescent.LP



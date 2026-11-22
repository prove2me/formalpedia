-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_PairingIndexBounds_ModelLatticeMoves_IsBichar
-- name    : Formalism_LocalToGlobal_PairingIndexBounds_ModelLatticeMoves_IsBichar
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T21:05:42.521651+00:00
-- url     : https://prove2.me/theorems/a8baad4b-3c53-40b6-a6f2-71ab326c80ac
-- title:
--   Is Bichar
-- statement:
--   Definitions and structural lemmas for Is Bichar, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/PairingIndexBounds/ModelLatticeMoves/IsBichar.lean

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
namespace Formalism.L2.PairingIndexBounds.Mv
variable {k : Type*} [Field k] {A B T : Type*} [AddCommGroup A] [AddCommGroup B] [AddCommGroup T] [Module k T]
def IsBichar (c : B → A → k) : Prop :=
  (∀ b a, c b a ≠ 0) ∧ (∀ b b' a, c (b + b') a = c b a * c b' a) ∧ ∀ b a a', c b (a + a') = c b a * c b a'
def IsHeis (c : B → A → k) (WA : A → T →ₗ[k] T) (WB : B → T →ₗ[k] T) : Prop :=
  WA 0 = LinearMap.id ∧ (∀ a a', WA (a + a') = WA a ∘ₗ WA a') ∧ WB 0 = LinearMap.id ∧
    (∀ b b', WB (b + b') = WB b ∘ₗ WB b') ∧ ∀ a b, WA a ∘ₗ WB b = c b a • (WB b ∘ₗ WA a)
def rhoA (a : A) : (A → k) →ₗ[k] (A → k) where
  toFun Φ t := Φ (t + a)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
def rhoB (c : B → A → k) (b : B) : (A → k) →ₗ[k] (A → k) where
  toFun Φ t := c b t * Φ t
  map_add' Φ Ψ := by funext t; simp [mul_add]
  map_smul' r Φ := by funext t; simp [smul_eq_mul]; ring
def ind (S : Set A) : A → k := by classical exact fun t => if t ∈ S then 1 else 0
def annB (c : B → A → k) (S : Set A) : Set B := {b | ∀ a ∈ S, c b a = 1}
def annA (c : B → A → k) (S : Set B) : Set A := {a | ∀ b ∈ S, c b a = 1}
def gen (c : B → A → k) (A₀ : AddSubgroup A) (a : A) (b : B) : A → k := rhoA a (rhoB c b (ind (A₀ : Set A)))
def Sch (c : B → A → k) (A₀ : AddSubgroup A) : Submodule k (A → k) :=
  Submodule.span k (Set.range fun ab : A × B => gen c A₀ ab.1 ab.2)
theorem gen_mem (c : B → A → k) (A₀ : AddSubgroup A) (a : A) (b : B) : gen c A₀ a b ∈ Sch c A₀ :=
  Submodule.subset_span ⟨(a, b), rfl⟩
def IsXi (c : B → A → k) (WA : A → T →ₗ[k] T) (WB : B → T →ₗ[k] T) (A₀ : AddSubgroup A) (θ : T)
    (Xi : Sch c A₀ →ₗ[k] T) : Prop :=
  ∀ a b, Xi ⟨gen c A₀ a b, gen_mem c A₀ a b⟩ = WA a (WB b θ)
def IsRepsG {G : Type*} [AddCommGroup G] (M N : AddSubgroup G) (S : Finset G) : Prop :=
  (∀ x ∈ S, x ∈ N) ∧ (∀ x ∈ S, ∀ y ∈ S, x - y ∈ M → x = y) ∧ ∀ y ∈ N, ∃ x ∈ S, y - x ∈ M
end Formalism.L2.PairingIndexBounds.Mv



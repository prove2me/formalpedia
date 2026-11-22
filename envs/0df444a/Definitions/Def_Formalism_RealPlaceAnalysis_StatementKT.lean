-- Prove2me | Definitions.Def_Formalism_RealPlaceAnalysis_StatementKT
-- name    : Formalism_RealPlaceAnalysis_StatementKT
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T16:47:59.131805+00:00
-- url     : https://prove2.me/theorems/15b71f8a-3397-4864-9a4c-0b5851e325ae
-- title:
--   Statement KT
-- statement:
--   Definitions and structural lemmas for Statement KT, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RealPlaceAnalysis/StatementKT.lean

import Definitions.Def_Formalism_RealPlaceAnalysis_StatementA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped InnerProductSpace
open Finset
noncomputable section
namespace Formalism.REAL
def KRel {A : Type*} [Ring A] {n : ℕ} (ε : Fin n → Bool) (F : Fin n → Fin n → A) : Prop :=
  ∀ a b c d : Fin n, ε a = ε b → ε c = ε d →
    F a b * F c d - F c d * F a b = (if b = c then F a d else 0) - (if d = a then F c b else 0)
def KUnit {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] {n : ℕ}
    (ε : Fin n → Bool) (F : Fin n → Fin n → Module.End ℂ V) : Prop :=
  ∀ a b : Fin n, ε a = ε b → ∀ x y : V, ⟪F a b x, y⟫_ℂ = ⟪x, F b a y⟫_ℂ
def KStable {V : Type*} [AddCommGroup V] [Module ℂ V] {n : ℕ} (ε : Fin n → Bool)
    (F : Fin n → Fin n → Module.End ℂ V) (S : Submodule ℂ V) : Prop :=
  ∀ a b : Fin n, ε a = ε b → ∀ x ∈ S, F a b x ∈ S
def kSpan {V : Type*} [AddCommGroup V] [Module ℂ V] {n : ℕ} (ε : Fin n → Bool)
    (F : Fin n → Fin n → Module.End ℂ V) (x : V) : Submodule ℂ V :=
  sInf {S : Submodule ℂ V | x ∈ S ∧ KStable ε F S}
def ew {V : Type*} [AddCommGroup V] [Module ℂ V] {n : ℕ}
    (F : Fin n → Fin n → Module.End ℂ V) : List (Fin n × Fin n) → Module.End ℂ V
  | [] => 1
  | p :: w => F p.1 p.2 * ew F w
def lowSpan {V : Type*} [AddCommGroup V] [Module ℂ V] {n : ℕ} (ε : Fin n → Bool)
    (F : Fin n → Fin n → Module.End ℂ V) (x : V) : Submodule ℂ V :=
  Submodule.span ℂ {y | ∃ w : List (Fin n × Fin n),
    (∀ p ∈ w, ε p.1 = ε p.2 ∧ p.2 < p.1) ∧ y = ew F w x}
def isoPart {V : Type*} [AddCommGroup V] [Module ℂ V] {n : ℕ} (ε : Fin n → Bool)
    (F : Fin n → Fin n → Module.End ℂ V) (T : Set (Fin n → ℝ)) (S : Submodule ℂ V) : Submodule ℂ V :=
  ⨆ (y : V) (_ : y ∈ S ∧ ∃ μ ∈ T, KHighest ε F μ y), kSpan ε F y
def ckv {n : ℕ} (ε : Fin n → Bool) (μ : Fin n → ℝ) : ℝ := nsq (μ + rhoC ε) - nsq (rhoC ε)
def negT {A : Type*} [Ring A] {n : ℕ} (F : Fin n → Fin n → A) : Fin n → Fin n → A :=
  fun a b => -F b a
def KNegT : Prop :=
  ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] (n : ℕ) (ε : Fin n → Bool)
    (F : Fin n → Fin n → Module.End ℂ V),
    (KRel ε F → KRel ε (negT F)) ∧ (KUnit ε F → KUnit ε (negT F)) ∧
    ∀ (ν : Fin n → ℝ) (x : V),
      (IsWeight F ν x ∧ ∀ a b, a < b → ε a = ε b → F b a x = 0) ↔ KHighest ε (negT F) (-ν) x
def KWtOrth : Prop :=
  ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] (n : ℕ) (ε : Fin n → Bool)
    (F : Fin n → Fin n → Module.End ℂ V) (μ ν : Fin n → ℝ) (x y : V),
    KUnit ε F → IsWeight F μ x → IsWeight F ν y → μ ≠ ν → ⟪x, y⟫_ℂ = 0
def KLow : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (n : ℕ) (ε : Fin n → Bool)
    (F : Fin n → Fin n → Module.End ℂ V) (μ : Fin n → ℝ) (x : V),
    KRel ε F → KHighest ε F μ x →
    kSpan ε F x = lowSpan ε F x ∧
    ∀ y ∈ lowSpan ε F x, IsWeight F μ y → ∃ c : ℂ, y = c • x
def KCasSpan : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (n : ℕ) (ε : Fin n → Bool)
    (F : Fin n → Fin n → Module.End ℂ V) (μ : Fin n → ℝ) (x : V),
    KRel ε F → KHighest ε F μ x →
    ∀ y ∈ kSpan ε F x, CasK ε F y = ((ckv ε μ : ℝ) : ℂ) • y
def KOrth : Prop :=
  ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] (n : ℕ) (ε : Fin n → Bool)
    (F : Fin n → Fin n → Module.End ℂ V) (μ ν : Fin n → ℝ) (x y : V),
    KRel ε F → KUnit ε F → KHighest ε F μ x → KHighest ε F ν y → μ ≠ ν →
    ∀ x' ∈ kSpan ε F x, ∀ y' ∈ kSpan ε F y, ⟪x', y'⟫_ℂ = 0
def KHiUniq : Prop :=
  ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] (n : ℕ) (ε : Fin n → Bool)
    (F : Fin n → Fin n → Module.End ℂ V) (μ ν : Fin n → ℝ) (x y : V),
    KRel ε F → KUnit ε F → KHighest ε F μ x → y ∈ kSpan ε F x → KHighest ε F ν y →
    y = 0 ∨ (ν = μ ∧ ∃ c : ℂ, y = c • x)
def KFormUniq : Prop :=
  ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] (n : ℕ) (ε : Fin n → Bool)
    (F : Fin n → Fin n → Module.End ℂ V) (μ : Fin n → ℝ) (x : V) (H : V →ₗ⋆[ℂ] V →ₗ[ℂ] ℂ),
    KRel ε F → KUnit ε F → KHighest ε F μ x →
    (∀ a b, ε a = ε b → ∀ y ∈ kSpan ε F x, ∀ z ∈ kSpan ε F x, H (F a b y) z = H y (F b a z)) →
    ∀ y ∈ kSpan ε F x, ∀ z ∈ kSpan ε F x, H y z * ((‖x‖ ^ 2 : ℝ) : ℂ) = H x x * ⟪y, z⟫_ℂ
def KCommScalar : Prop :=
  ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] (n : ℕ) (ε : Fin n → Bool)
    (F : Fin n → Fin n → Module.End ℂ V) (μ : Fin n → ℝ) (x : V) (T : Module.End ℂ V),
    KRel ε F → KUnit ε F → KHighest ε F μ x →
    (∀ y ∈ kSpan ε F x, T y ∈ kSpan ε F x) →
    (∀ a b, ε a = ε b → ∀ y ∈ kSpan ε F x, T (F a b y) = F a b (T y)) →
    ∃ c : ℂ, ∀ y ∈ kSpan ε F x, T y = c • y
def KHiExist : Prop :=
  ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] (n : ℕ) (ε : Fin n → Bool)
    (F : Fin n → Fin n → Module.End ℂ V) (S : Submodule ℂ V),
    FiniteDimensional ℂ S → KRel ε F → KUnit ε F → KStable ε F S → S ≠ ⊥ →
    ∃ x ∈ S, x ≠ 0 ∧ ∃ μ : Fin n → ℝ, KHighest ε F μ x
def KIrr : Prop :=
  ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] (n : ℕ) (ε : Fin n → Bool)
    (F : Fin n → Fin n → Module.End ℂ V) (μ : Fin n → ℝ) (x : V),
    FiniteDimensional ℂ (kSpan ε F x) → KRel ε F → KUnit ε F → KHighest ε F μ x →
    ∀ S : Submodule ℂ V, S ≤ kSpan ε F x → KStable ε F S → S = ⊥ ∨ S = kSpan ε F x
def KDecomp : Prop :=
  ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] (n : ℕ) (ε : Fin n → Bool)
    (F : Fin n → Fin n → Module.End ℂ V) (S : Submodule ℂ V),
    FiniteDimensional ℂ S → KRel ε F → KUnit ε F → KStable ε F S →
    ∃ (m : ℕ) (x : Fin m → V) (μ : Fin m → Fin n → ℝ),
      (∀ i, x i ∈ S ∧ x i ≠ 0 ∧ KHighest ε F (μ i) (x i)) ∧
      (∀ i i', i ≠ i' → ∀ y ∈ kSpan ε F (x i), ∀ z ∈ kSpan ε F (x i'), ⟪y, z⟫_ℂ = 0) ∧
      (⨆ i, kSpan ε F (x i)) = S
def KIsoSplit : Prop :=
  ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] (n : ℕ) (ε : Fin n → Bool)
    (F : Fin n → Fin n → Module.End ℂ V) (S : Submodule ℂ V) (T : Set (Fin n → ℝ)),
    FiniteDimensional ℂ S → KRel ε F → KUnit ε F → KStable ε F S →
    (∀ y ∈ isoPart ε F T S, ∀ z ∈ isoPart ε F Tᶜ S, ⟪y, z⟫_ℂ = 0) ∧
    isoPart ε F T S ⊔ isoPart ε F Tᶜ S = S
def KWtBound : Prop :=
  ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] (n : ℕ) (ε : Fin n → Bool)
    (F : Fin n → Fin n → Module.End ℂ V) (μ ν : Fin n → ℝ) (x y : V),
    KRel ε F → KUnit ε F → KHighest ε F μ x → y ∈ kSpan ε F x → y ≠ 0 → IsWeight F ν y →
    nsq ν ≤ ckv ε μ
def KCasBound : Prop :=
  ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] (n : ℕ) (ε : Fin n → Bool)
    (F : Fin n → Fin n → Module.End ℂ V) (S : Submodule ℂ V) (R : ℝ),
    FiniteDimensional ℂ S → KRel ε F → KUnit ε F → KStable ε F S → 0 ≤ R →
    (∀ (μ : Fin n → ℝ) (y : V), y ∈ S → y ≠ 0 → IsWeight F μ y → ∀ a, |μ a| ≤ R) →
    ∀ y ∈ S, (⟪y, CasK ε F y⟫_ℂ).re ≤ (n : ℝ) * (R + n) ^ 2 * ‖y‖ ^ 2
end Formalism.REAL



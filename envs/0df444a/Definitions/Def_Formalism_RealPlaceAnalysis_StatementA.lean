-- Prove2me | Definitions.Def_Formalism_RealPlaceAnalysis_StatementA
-- name    : Formalism_RealPlaceAnalysis_StatementA
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T16:45:55.495801+00:00
-- url     : https://prove2.me/theorems/ab6ec730-4372-4947-aca7-f107e8544d9d
-- title:
--   Statement A
-- statement:
--   Definitions and structural lemmas for Statement A, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RealPlaceAnalysis/StatementA.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped InnerProductSpace TensorProduct
open Finset
noncomputable section
namespace Formalism.REAL
def GlRel {A : Type*} [Ring A] {n : ℕ} (E : Fin n → Fin n → A) : Prop :=
  ∀ a b c d : Fin n, E a b * E c d - E c d * E a b =
    (if b = c then E a d else 0) - (if d = a then E c b else 0)
def sgn {n : ℕ} (ε : Fin n → Bool) (a b : Fin n) : ℝ := if ε a = ε b then 1 else -1
def IsUnitary {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] {n : ℕ}
    (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ V) : Prop :=
  ∀ (a b : Fin n) (x y : V), ⟪E a b x, y⟫_ℂ = (sgn ε a b : ℂ) * ⟪x, E b a y⟫_ℂ
def Cas {A : Type*} [Ring A] {n : ℕ} (E : Fin n → Fin n → A) : A :=
  ∑ a, ∑ b, E a b * E b a
def CasK {A : Type*} [Ring A] {n : ℕ} (ε : Fin n → Bool) (E : Fin n → Fin n → A) : A :=
  ∑ a, ∑ b, if ε a = ε b then E a b * E b a else 0
def IsWeight {V : Type*} [AddCommGroup V] [Module ℂ V] {n : ℕ}
    (E : Fin n → Fin n → Module.End ℂ V) (μ : Fin n → ℝ) (w : V) : Prop :=
  ∀ a, E a a w = (μ a : ℂ) • w
def KHighest {V : Type*} [AddCommGroup V] [Module ℂ V] {n : ℕ} (ε : Fin n → Bool)
    (E : Fin n → Fin n → Module.End ℂ V) (μ : Fin n → ℝ) (w : V) : Prop :=
  IsWeight E μ w ∧ ∀ a b, a < b → ε a = ε b → E a b w = 0
def rhoC {n : ℕ} (ε : Fin n → Bool) : Fin n → ℝ := fun a =>
  (((univ.filter fun b => a < b ∧ ε b = ε a).card : ℝ) -
    ((univ.filter fun b => b < a ∧ ε b = ε a).card : ℝ)) / 2
def rhoN {n : ℕ} (ε : Fin n → Bool) : Fin n → ℝ := fun a =>
  (((univ.filter fun b => a < b ∧ ε b ≠ ε a).card : ℝ) -
    ((univ.filter fun b => b < a ∧ ε b ≠ ε a).card : ℝ)) / 2
def dot {n : ℕ} (u v : Fin n → ℝ) : ℝ := ∑ a, u a * v a
def nsq {n : ℕ} (u : Fin n → ℝ) : ℝ := dot u u
def root {n : ℕ} (a b : Fin n) : Fin n → ℝ := Pi.single a 1 - Pi.single b 1
def WDCas : Prop :=
  ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] (n : ℕ) (ε : Fin n → Bool)
    (E : Fin n → Fin n → Module.End ℂ V) (μ : Fin n → ℝ) (w : V),
    GlRel E → IsUnitary ε E → KHighest ε E μ w →
    ⟪w, Cas E w⟫_ℂ = (((nsq (μ + rhoC ε) - nsq (rhoC ε)) * ‖w‖ ^ 2 -
      ∑ a, ∑ b, (if ε a = ε b then 0 else ‖E a b w‖ ^ 2) : ℝ) : ℂ)
def WDRoot : Prop :=
  ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] (n : ℕ) (ε : Fin n → Bool)
    (E : Fin n → Fin n → Module.End ℂ V) (μ : Fin n → ℝ) (w : V),
    GlRel E → IsUnitary ε E → IsWeight E μ w →
    ∀ a b, ε a ≠ ε b → ‖E a b w‖ ^ 2 - ‖E b a w‖ ^ 2 = (μ a - μ b) * ‖w‖ ^ 2
def WDBound : Prop :=
  ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] (n : ℕ) (ε : Fin n → Bool)
    (E : Fin n → Fin n → Module.End ℂ V) (μ : Fin n → ℝ) (w : V),
    GlRel E → IsUnitary ε E → KHighest ε E μ w →
    (⟪w, Cas E w⟫_ℂ).re ≤ (nsq (μ + rhoC ε - rhoN ε) - nsq (rhoC ε - rhoN ε)) * ‖w‖ ^ 2
def WDKind : Prop :=
  ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] (n : ℕ) (ε : Fin n → Bool)
    (E : Fin n → Fin n → Module.End ℂ V) (lam : Fin n → ℝ) (w : V),
    GlRel E → IsUnitary ε E → KHighest ε E (lam + rhoN ε - rhoC ε) w →
    Cas E w = ((nsq lam - nsq (rhoC ε + rhoN ε) : ℝ) : ℂ) • w →
    2 * (∑ a, ∑ b, if a < b ∧ ε a ≠ ε b then ‖E b a w‖ ^ 2 else 0) =
      (nsq (rhoC ε + rhoN ε) - nsq (rhoC ε - rhoN ε)) * ‖w‖ ^ 2
def RhoStd : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (a : Fin n), rhoC ε a + rhoN ε a = ((n : ℝ) - 1) / 2 - (a : ℝ)
def RhoBound : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool), nsq (rhoC ε + rhoN ε) - nsq (rhoC ε - rhoN ε) ≤ (n : ℝ) ^ 3
def WDExclude : Prop :=
  ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] (n : ℕ) (ε : Fin n → Bool)
    (E : Fin n → Fin n → Module.End ℂ V) (lam : Fin n → ℝ) (w : V) (a b : Fin n),
    a < b → ε a ≠ ε b → w ≠ 0 → GlRel E → IsUnitary ε E →
    KHighest ε E (lam + rhoN ε - rhoC ε - root a b) w →
    Cas E w = ((nsq lam - nsq (rhoC ε + rhoN ε) : ℝ) : ℂ) • w →
    2 * (lam a - lam b) - 2 ≤ (n : ℝ) ^ 3
def SumSq : Prop :=
  ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] (n : ℕ) (ε : Fin n → Bool)
    (E : Fin n → Fin n → Module.End ℂ V) (w : V),
    IsUnitary ε E →
    (((∑ a, ∑ b, ‖E a b w‖ ^ 2 : ℝ)) : ℂ) = ⟪w, (2 • CasK ε E - Cas E) w⟫_ℂ
def CasKHighest : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (n : ℕ) (ε : Fin n → Bool)
    (E : Fin n → Fin n → Module.End ℂ V) (μ : Fin n → ℝ) (w : V),
    GlRel E → KHighest ε E μ w →
    CasK ε E w = ((nsq (μ + rhoC ε) - nsq (rhoC ε) : ℝ) : ℂ) • w
def CasCentral : Prop :=
  ∀ (A : Type) [Ring A] (n : ℕ) (ε : Fin n → Bool) (E : Fin n → Fin n → A), GlRel E →
    (∀ c d, Cas E * E c d = E c d * Cas E) ∧
    (∀ c d, ε c = ε d → CasK ε E * E c d = E c d * CasK ε E)
def tens {V W : Type*} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] {n : ℕ}
    (E : Fin n → Fin n → Module.End ℂ V) (F : Fin n → Fin n → Module.End ℂ W) :
    Fin n → Fin n → Module.End ℂ (V ⊗[ℂ] W) :=
  fun a b => TensorProduct.map (E a b) LinearMap.id + TensorProduct.map LinearMap.id (F a b)
def Om {V W : Type*} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] {n : ℕ}
    (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ V)
    (F : Fin n → Fin n → Module.End ℂ W) : Module.End ℂ (V ⊗[ℂ] W) :=
  ∑ a, ∑ b, if ε a = ε b then TensorProduct.map (E a b) (F b a) else 0
def TensorCas : Prop :=
  ∀ (V W : Type) [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] (n : ℕ)
    (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ V) (F : Fin n → Fin n → Module.End ℂ W),
    GlRel E → GlRel F →
    GlRel (tens E F) ∧
    CasK ε (tens E F) = TensorProduct.map (CasK ε E) LinearMap.id +
      TensorProduct.map LinearMap.id (CasK ε F) + 2 • Om ε E F
def adj {n : ℕ} (a b : Fin n) : Module.End ℂ (Matrix (Fin n) (Fin n) ℂ) :=
  LinearMap.mulLeft ℂ (Matrix.single a b (1 : ℂ)) - LinearMap.mulRight ℂ (Matrix.single a b (1 : ℂ))
def CasKp : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (a₀ b₀ : Fin n), ε a₀ ≠ ε b₀ →
    (∀ c, ε c = ε a₀ → a₀ ≤ c) → (∀ c, ε c = ε b₀ → c ≤ b₀) →
    GlRel (fun a b : Fin n => adj a b) ∧
    KHighest ε (fun a b => adj a b) (root a₀ b₀) (Matrix.single a₀ b₀ 1) ∧
    CasK ε (fun a b => adj a b) (Matrix.single a₀ b₀ 1) = (n : ℂ) • Matrix.single a₀ b₀ 1
def OmEigen : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (lam : Fin n → ℝ) (a b : Fin n), a ≠ b →
    ((nsq (lam + rhoN ε - rhoC ε + root a b + rhoC ε) - nsq (rhoC ε)) - (n : ℝ) -
      (nsq (lam + rhoN ε - rhoC ε + rhoC ε) - nsq (rhoC ε))) / 2 =
      (lam a + rhoN ε a) - (lam b + rhoN ε b) + 1 - (n : ℝ) / 2
def UGap : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (lam : Fin n → ℝ) (g : ℝ) (a b : Fin n),
    a < b → ε a ≠ ε b → g ≤ lam a - lam b →
    g - 2 * (n : ℝ) ≤ (lam a + rhoN ε a) - (lam b + rhoN ε b) + 1 - (n : ℝ) / 2
def GrowthIter : Prop :=
  ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] (X : Module.End ℂ V)
    (U : ℕ → Submodule ℂ V) (B C : ℝ), 0 ≤ B → 0 ≤ C →
    (∀ (j : ℕ), ∀ w ∈ U j, X w ∈ U (j + 1) ∧ ‖X w‖ ≤ C * (B + j) * ‖w‖) →
    ∀ (j k : ℕ), ∀ w ∈ U j, ‖(X ^ k) w‖ ≤ C ^ k * (B + j + k) ^ k * ‖w‖
def TaylorRadius : Prop :=
  ∀ (C m t : ℝ), 0 ≤ C → 0 ≤ m → 0 ≤ t → C * t * Real.exp 1 < 1 →
    Summable (fun k : ℕ => (C * t) ^ k * (m + k) ^ k / (k.factorial : ℝ))
def volU : ℕ → ℝ
  | 0 => 1
  | i + 1 => volU i * (2 * Real.pi ^ (i + 1) / (i.factorial : ℝ))
def VolConst : Prop :=
  ∀ n : ℕ, volU n * ∏ i ∈ range n, (i.factorial : ℝ) =
    (2 * Real.pi) ^ n * Real.pi ^ (n * (n - 1) / 2)
def QuadraticInequalityBound : Prop :=
  ∀ (A p t : ℝ) (n : ℕ), 0 < A → 0 ≤ p → 0 ≤ t →
    A * p ^ 2 / 2 ≤ 4 * (n : ℝ) ^ 4 * t * p → p ≤ 8 * (n : ℝ) ^ 4 * t / A
end Formalism.REAL



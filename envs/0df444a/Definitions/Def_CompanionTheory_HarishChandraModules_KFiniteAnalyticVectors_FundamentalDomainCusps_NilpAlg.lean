-- Prove2me | Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_FundamentalDomainCusps_NilpAlg
-- name    : CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_FundamentalDomainCusps_NilpAlg
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T10:29:19.9998+00:00
-- url     : https://prove2.me/theorems/fe9c8147-4778-4155-af09-a66096dd5e3e
-- title:
--   Nilp Alg
-- statement:
--   Definitions and structural lemmas for Nilp Alg, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/KFiniteAnalyticVectors/FundamentalDomainCusps/NilpAlg.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
noncomputable section
namespace CompanionTheory.D.gk.RF
variable {K : Type} [Field K] [StarRing K] {n : ℕ}
def hf (J : Matrix (Fin n) (Fin n) K) (x y : Fin n → K) : K := star x ⬝ᵥ (J *ᵥ y)
def perp (J : Matrix (Fin n) (Fin n) K) (W : Submodule K (Fin n → K)) : Submodule K (Fin n → K) where
  carrier := {z | ∀ w ∈ W, hf J w z = 0}
  add_mem' := fun ha hb w hw => by
    have h1 := ha w hw
    have h2 := hb w hw
    simp only [hf] at h1 h2 ⊢
    rw [mulVec_add, dotProduct_add, h1, h2, add_zero]
  zero_mem' := fun w _ => by simp [hf]
  smul_mem' := fun c z hz w hw => by
    have h1 := hz w hw
    simp only [hf] at h1 ⊢
    rw [mulVec_smul, dotProduct_smul, h1, smul_zero]
def Isot (J : Matrix (Fin n) (Fin n) K) (W : Submodule K (Fin n → K)) : Prop := W ≤ perp J W
def Lowers (J : Matrix (Fin n) (Fin n) K) (W : Submodule K (Fin n → K)) (A : Matrix (Fin n) (Fin n) K) : Prop :=
  (∀ w ∈ W, A *ᵥ w = 0) ∧ (∀ z ∈ perp J W, A *ᵥ z ∈ W) ∧ ∀ z, A *ᵥ z ∈ perp J W
def InL (J : Matrix (Fin n) (Fin n) K) (W : Submodule K (Fin n → K)) (X : Matrix (Fin n) (Fin n) K) : Prop :=
  Xᴴ * J + J * X = 0 ∧ Lowers J W X
def InZ (J : Matrix (Fin n) (Fin n) K) (W : Submodule K (Fin n → K)) (X : Matrix (Fin n) (Fin n) K) : Prop :=
  Xᴴ * J + J * X = 0 ∧ (∀ z ∈ perp J W, X *ᵥ z = 0) ∧ ∀ z, X *ᵥ z ∈ W
def xw (J : Matrix (Fin n) (Fin n) K) (w b : Fin n → K) : Matrix (Fin n) (Fin n) K :=
  vecMulVec w (star b ᵥ* J) - vecMulVec b (star w ᵥ* J)
def ex2 (X : Matrix (Fin n) (Fin n) K) : Matrix (Fin n) (Fin n) K := 1 + X + (2 : K)⁻¹ • (X * X)
def NilpAlg : Prop :=
  ∀ (K : Type) [Field K] [StarRing K] [CharZero K] (n : ℕ) (J : Matrix (Fin n) (Fin n) K)
    (W : Submodule K (Fin n → K)), Jᴴ = J → IsUnit J.det → Isot J W →
    (∀ X, InL J W X → (ex2 X)ᴴ * J * ex2 X = J ∧ Lowers J W (ex2 X - 1) ∧ ex2 X * ex2 (-X) = 1 ∧ InL J W (-X)) ∧
    (∀ g : Matrix (Fin n) (Fin n) K, gᴴ * J * g = J → Lowers J W (g - 1) → ∃ X, InL J W X ∧ g = ex2 X) ∧
    (∀ X Y, InL J W X → InL J W Y → InL J W (X + Y) ∧ InZ J W ((2 : K)⁻¹ • (X * Y - Y * X)) ∧
      ex2 X * ex2 Y = ex2 (X + Y + (2 : K)⁻¹ • (X * Y - Y * X))) ∧
    (∀ Z, InZ J W Z → InL J W Z ∧ InZ J W (-Z) ∧ ∀ X, InL J W X → Z * X = 0 ∧ X * Z = 0)
def NilpRep : Prop :=
  ∀ (K : Type) [Field K] [StarRing K] [CharZero K] (n : ℕ) (J : Matrix (Fin n) (Fin n) K)
    (W : Submodule K (Fin n → K)), Jᴴ = J → IsUnit J.det → Isot J W →
    ∀ (d : ℕ) (w : Fin d → Fin n → K), Submodule.span K (Set.range w) = W →
    (∀ b : Fin d → Fin n → K, (∀ i, b i ∈ perp J W) → InL J W (∑ i, xw J (w i) (b i))) ∧
    (∀ b : Fin d → Fin n → K, (∀ i, b i ∈ W) → InZ J W (∑ i, xw J (w i) (b i))) ∧
    (∀ X, InL J W X → ∃ b : Fin d → Fin n → K, (∀ i, b i ∈ perp J W) ∧ X = ∑ i, xw J (w i) (b i)) ∧
    (∀ X, InZ J W X → ∃ b : Fin d → Fin n → K, (∀ i, b i ∈ W) ∧ X = ∑ i, xw J (w i) (b i))
def Gap : Prop :=
  ∀ (K : Type) [Field K] (n : ℕ) (A : Set (Fin n → K)) (ν : (Fin n → K) → ℝ) (s₀ η : ℝ), 0 < s₀ → 0 < η → η < 1 →
    (∃ u ∈ A, u ≠ 0 ∧ ν u ≤ s₀ * η ^ (n + 1)) →
    ∃ t : ℝ, 0 < t ∧ t ≤ s₀ ∧ ∃ (d : ℕ) (w : Fin d → Fin n → K), d ≤ n ∧ (∀ i, w i ∈ A ∧ ν (w i) ≤ η * t) ∧
      Submodule.span K (Set.range w) ≠ ⊥ ∧ ∀ u ∈ A, ν u ≤ t → u ∈ Submodule.span K (Set.range w)
end CompanionTheory.D.gk.RF



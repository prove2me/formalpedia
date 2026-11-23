-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_IsLieDataCircle
-- name    : Development_AbelianVarietyTheory_Proofs_HeightProofs_IsLieDataCircle
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T03:54:48.439224+00:00
-- url     : https://prove2.me/theorems/ab03b160-2dd9-4264-b62f-93c4685c5cf4
-- title:
--   Is Lie Data Circle
-- statement:
--   Definitions and structural lemmas for Is Lie Data Circle, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HeightProofs/IsLieDataCircle.lean

import Mathlib
import Definitions.Def_Formalism_RealPlaceAnalysis_StatementA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped ContDiff Topology
open NumberField Matrix
namespace GlobalTheory.SmoothForms
section Chart
variable {𝔸 L G : Type} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [NormedAddCommGroup L] [NormedSpace ℝ L] [Group G]
structure IsLieData (σ : 𝔸 →ₗ[ℝ] 𝔸) (j : L →ₗ[ℝ] 𝔸) (s : 𝔸 → G) : Prop where
  anti : ∀ a b, σ (a * b) = σ b * σ a
  one : σ 1 = 1
  invol : ∀ a, σ (σ a) = a
  inj : Function.Injective j
  skew : ∀ X, σ X = -X ↔ ∃ Y, j Y = X
  mul : ∀ a b, σ a * a = 1 → σ b * b = 1 → s (a * b) = s a * s b
def expMap (j : L →ₗ[ℝ] 𝔸) (s : 𝔸 → G) (X : L) : G := s (NormedSpace.exp (j X))
def HasLog (σ : 𝔸 →ₗ[ℝ] 𝔸) (j : L →ₗ[ℝ] 𝔸) : Prop :=
  ∃ Λ : 𝔸 → L, ContDiffAt ℝ ∞ Λ 1 ∧ (∀ᶠ h in 𝓝 (1 : 𝔸), σ h * h = 1 → NormedSpace.exp (j (Λ h)) = h) ∧
    ∀ᶠ X in 𝓝 (0 : L), Λ (NormedSpace.exp (j X)) = X
def Sm (e : L → G) (φ : G → ℂ) : Prop := ∀ g, ContDiff ℝ ∞ fun X : L => φ (g * e X)
def Der (e : L → G) (X : L) (φ : G → ℂ) : G → ℂ := fun g => deriv (fun t : ℝ => φ (g * e (t • X))) 0
end Chart
section Words
variable {A : Type} [Ring A] [Algebra ℂ A] {n : ℕ}
def gelfA (E : Fin n → Fin n → A) (k : ℕ) : A :=
  ∑ idx : Fin (k + 1) → Fin n, (List.ofFn fun a : Fin (k + 1) => E (idx a) (idx (a + 1))).prod
def wordMap (E : Fin n → Fin n → A) (d : ℕ) : Matrix (Fin d → Fin n) (Fin d → Fin n) ℂ →ₗ[ℂ] A where
  toFun M := ∑ I, ∑ K, M I K • (List.ofFn fun a : Fin d => E (I a) (K a)).prod
  map_add' M N := by simp [add_smul, Finset.sum_add_distrib]
  map_smul' c M := by simp [Finset.smul_sum, mul_smul]
def filt (E : Fin n → Fin n → A) (d : ℕ) : Submodule ℂ A := ⨆ d' < d, LinearMap.range (wordMap E d')
def polar (n d : ℕ) (a b : Fin n) : Matrix (Fin d → Fin n) (Fin d → Fin n) ℂ :=
  Matrix.of fun I K => ∑ p, if I p = a ∧ K p = b ∧ ∀ q, q ≠ p → I q = K q then 1 else 0
def permMat (n d : ℕ) (π : Equiv.Perm (Fin d)) : Matrix (Fin d → Fin n) (Fin d → Fin n) ℂ :=
  Matrix.of fun I K => if I = K ∘ π then 1 else 0
end Words
section Lattices
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
structure Sized {V : Type} [AddCommGroup V] [Module E V] (h : V →ₗ[E] V →ₗ⋆[E] E) (Λ : Submodule ℤ V) (N : ℤ)
    (ν : V → ℝ) (B : ℝ) : Prop where
  symm : ∀ x y, h y x = star (h x y)
  nondeg : ∀ y, (∀ x, h y x = 0) → y = 0
  fg : Λ.FG
  stable : ∀ a : E, IsIntegral ℤ a → ∀ x ∈ Λ, a • x ∈ Λ
  int : ∀ x ∈ Λ, ∀ y ∈ Λ, IsIntegral ℤ (h x y)
  dual : ∀ y, (∀ x ∈ Λ, IsIntegral ℤ (h y x)) → (N : E) • y ∈ Λ
  two_le : 2 ≤ B
  nonneg : ∀ x, 0 ≤ ν x
  add_le : ∀ x y, ν (x + y) ≤ ν x + ν y
  smul_le : ∀ (a : E) x, ν (a • x) ≤ house a * ν x
  form_le : ∀ x y, house (h x y) ≤ ν x * ν y
  span : Submodule.span E {x | x ∈ Λ ∧ ν x ≤ B} = ⊤
variable (E)
def FrameSmall : Prop :=
  ∀ n : ℕ, ∃ k : ℕ, ∀ (V : Type) [AddCommGroup V] [Module E V] [FiniteDimensional E V] (h : V →ₗ[E] V →ₗ⋆[E] E)
    (Λ : Submodule ℤ V) (N : ℤ) (ν : V → ℝ) (B : ℝ), Module.finrank E V = n → Sized h Λ N ν B →
    ∃ v : Fin n → V, (∀ i, v i ∈ Λ) ∧ (∀ i j, i ≠ j → h (v i) (v j) = 0) ∧ ∀ i, h (v i) (v i) ≠ 0 ∧ ν (v i) ≤ B ^ k
def ShortSmall : Prop :=
  ∀ n : ℕ, n ≠ 0 → ∀ N : ℤ, N ≠ 0 → ∃ (C : ℝ) (k : ℕ), ∀ (V : Type) [AddCommGroup V] [Module E V] [FiniteDimensional E V]
    (h : V →ₗ[E] V →ₗ⋆[E] E) (Λ : Submodule ℤ V) (ν : V → ℝ) (B : ℝ), Module.finrank E V = n → Sized h Λ N ν B →
    ∃ v ∈ Λ, v ≠ 0 ∧ house (h v v) ≤ C ∧ ν v ≤ B ^ k
def AnisoSmall : Prop :=
  ∀ n : ℕ, n ≠ 0 → ∀ N : ℤ, N ≠ 0 → ∃ (S : Set E) (k : ℕ), S.Finite ∧ (0 : E) ∉ S ∧
    ∀ (V : Type) [AddCommGroup V] [Module E V] [FiniteDimensional E V]
    (h : V →ₗ[E] V →ₗ⋆[E] E) (Λ : Submodule ℤ V) (ν : V → ℝ) (B : ℝ), Module.finrank E V = n → Sized h Λ N ν B →
    ∃ v ∈ Λ, h v v ∈ S ∧ ν v ≤ B ^ k
def OrthoSmall : Prop :=
  ∀ n : ℕ, ∀ N : ℤ, N ≠ 0 → ∃ (S : Set E) (k : ℕ), S.Finite ∧ (0 : E) ∉ S ∧
    ∀ (V : Type) [AddCommGroup V] [Module E V] [FiniteDimensional E V]
    (h : V →ₗ[E] V →ₗ⋆[E] E) (Λ : Submodule ℤ V) (ν : V → ℝ) (B : ℝ), Module.finrank E V = n → Sized h Λ N ν B →
    ∃ v : Fin n → V, (∀ i, v i ∈ Λ) ∧ (∀ i j, i ≠ j → h (v i) (v j) = 0) ∧ ∀ i, h (v i) (v i) ∈ S ∧ ν (v i) ≤ B ^ k
end Lattices
end GlobalTheory.SmoothForms
end



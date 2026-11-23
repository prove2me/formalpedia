-- Prove2me | Definitions.Def_Development_WeilBound_RepresentationTheoryGL_ArchimedeanBaseChange_ArchimedeanBaseChangeProof_SatakeExponents_FibreFactorHolds
-- name    : Development_WeilBound_RepresentationTheoryGL_ArchimedeanBaseChange_ArchimedeanBaseChangeProof_SatakeExponents_FibreFactorHolds
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T20:24:13.595387+00:00
-- url     : https://prove2.me/theorems/b3dbf13e-1d3c-408f-8c70-178476fb83c3
-- title:
--   Fibre Factor Holds
-- statement:
--   Definitions and structural lemmas for Fibre Factor Holds, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/ArchimedeanBaseChange/ArchimedeanBaseChangeProof/SatakeExponents/FibreFactorHolds.lean

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
open scoped Classical
namespace PositivityTheory.Rg.BcB.F
def ExpSum : Prop := ∀ (ι : Type) [Fintype ι] (c lam : ι → ℂ) (ρ C : ℝ) (N : ℕ), 0 ≤ ρ →
  (∀ᶠ k : ℕ in Filter.atTop, ‖∑ i, c i * lam i ^ k‖ ≤ C * (1 + k) ^ N * ρ ^ k) →
  ∀ μ : ℂ, ρ < ‖μ‖ → ∑ i with lam i = μ, c i = 0
def Power : Prop := ∀ (B : Type) [CommRing B] [Algebra ℂ B] (ι : Type) [Fintype ι] (c : ι → ℂ) (q : ι → (B →ₐ[ℂ] ℂ))
  (ν : Seminorm ℂ B), (∀ b, ∃ (C : ℝ) (N : ℕ), ∀ᶠ k : ℕ in Filter.atTop,
    ‖∑ i, c i * q i b ^ k‖ ≤ C * (1 + k) ^ N * ν b ^ k) →
  ∀ p : B →ₐ[ℂ] ℂ, ∑ i with q i = p, c i ≠ 0 → ∀ b, ‖p b‖ ≤ ν b
def OneFactor : Prop := ∀ (B : Type) [CommRing B] [Algebra ℂ B] [StarRing B] [StarModule ℂ B]
  (ι : Type) [Fintype ι] [Nonempty ι] (H : ι → Type) [∀ s, NormedAddCommGroup (H s)] [∀ s, InnerProductSpace ℂ (H s)]
  [∀ s, CompleteSpace (H s)] (R : ∀ s, B →⋆ₐ[ℂ] (H s →L[ℂ] H s)) (p : B →⋆ₐ[ℂ] ℂ),
  (∀ b, ∃ s, ‖p b‖ ≤ ‖R s b‖) → ∃ s, ∀ b, ‖p b‖ ≤ ‖R s b‖
def fibre {A : Type} [CommRing A] [Algebra ℂ A] [StarRing A] [StarModule ℂ A] {ι : Type} (As : ι → Type)
    [∀ s, CommRing (As s)] [∀ s, Algebra ℂ (As s)] [∀ s, StarRing (As s)] [∀ s, StarModule ℂ (As s)]
    (ev : ∀ s, As s →⋆ₐ[ℂ] A) : StarSubalgebra ℂ (A × ∀ s, As s) where
  carrier := {x | ∀ s, ev s (x.2 s) = x.1}
  mul_mem' := fun {x y} hx hy s => by simp [hx s, hy s]
  add_mem' := fun {x y} hx hy s => by simp [hx s, hy s]
  algebraMap_mem' := fun z s => by simp [Algebra.algebraMap_eq_smul_one]
  star_mem' := fun {x} hx s => by simp [map_star, hx s]
def FibreFactor : Prop := ∀ (A : Type) [CommRing A] [Algebra ℂ A] [StarRing A] [StarModule ℂ A] (ι : Type) (As : ι → Type)
  [∀ s, CommRing (As s)] [∀ s, Algebra ℂ (As s)] [∀ s, StarRing (As s)] [∀ s, StarModule ℂ (As s)]
  (ev : ∀ s, As s →⋆ₐ[ℂ] A), (∀ s, Function.Surjective (ev s)) → ∀ (p : A →⋆ₐ[ℂ] ℂ) (s : ι) (ν : As s → ℝ),
  (∀ x ∈ fibre As ev, ‖p x.1‖ ≤ ν (x.2 s)) → ∀ b, ‖p (ev s b)‖ ≤ ν b
def CHBound : Prop := ∀ (Z : Type) [CommRing Z] [Algebra ℂ Z] [StarRing Z] [StarModule ℂ Z]
  (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (R : Z →⋆ₐ[ℂ] (H →L[ℂ] H))
  (u : H →L[ℂ] H) (P : Polynomial Z) (g : Z) (ρ : ℝ), 0 < ρ → (∀ z, Commute (R z) u) → P.Monic →
  (P.sum fun j z => R z * u ^ j) = 0 →
  (∀ χ : Z →⋆ₐ[ℂ] ℂ, (∀ z, ‖χ z‖ ≤ ‖R z‖) → ∀ x : ℂ, (P.sum fun j z => χ z * x ^ j) = 0 → ‖χ g * x‖ ≤ ρ) →
  ∃ (C : ℝ) (N : ℕ), ∀ k : ℕ, ‖(R g * u) ^ k‖ ≤ C * (1 + k) ^ N * ρ ^ k
def ConeNonzero : Prop := ∀ (n : ℕ) (ι : Type) [Fintype ι] [Nonempty ι] (ξ : ι → (Multiplicative (Fin n → ℤ) →* ℂˣ))
  (c : ι → ℝ), (∀ i, 0 < c i) → ∀ M : ℤ, ∃ x : Fin n → ℤ, (∀ i j, i < j → x j + M ≤ x i) ∧
    ∑ i, (c i : ℂ) * (ξ i (Multiplicative.ofAdd x) : ℂ) ≠ 0
def Isolate : Prop := ∀ (A : Type) [Ring A] [Algebra ℂ A] [StarRing A] [StarModule ℂ A]
  (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] [Module A V] [IsScalarTower ℂ A V]
  [IsSimpleModule A V], (∀ (a : A) (x y : V), inner ℂ (a • x) y = inner ℂ x (star a • y)) →
  ∀ (ι : Type) [Fintype ι] (W : ι → Type) [∀ i, AddCommGroup (W i)] [∀ i, Module ℂ (W i)] [∀ i, Module A (W i)]
    [∀ i, IsScalarTower ℂ A (W i)] [∀ i, FiniteDimensional ℂ (W i)] [∀ i, IsSimpleModule A (W i)],
    (∀ i, IsEmpty (W i ≃ₗ[A] V)) → ∃ e : A, star e = e ∧ (∀ i (x : W i), e • x = 0) ∧
      ∃ v : V, ‖v‖ = 1 ∧ ∀ x : V, e • x = inner ℂ v x • v
end PositivityTheory.Rg.BcB.F
end



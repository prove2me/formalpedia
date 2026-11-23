-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_PerpVecPerpSt
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_PerpVecPerpSt
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T12:44:58.716545+00:00
-- url     : https://prove2.me/theorems/7ca7ade0-29ac-4f95-bbfa-783aa08a4aac
-- title:
--   Perp Vec Perp St
-- statement:
--   Definitions and structural lemmas for Perp Vec Perp St, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/PerpVecPerpSt.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.ChartRestriction.G.TB
open MvPolynomial
variable {R : Type} [CommRing R]
noncomputable def xForm {p q n : ℕ} (e : Fin p → Fin n → R) (a b : Fin p) :
    MvPolynomial ((Fin p × Fin n) ⊕ (Fin q × Fin n)) R :=
  ∑ k, X (Sum.inl (a, k)) * C (e b k)
noncomputable def yForm {p q n : ℕ} (f : Fin q → Fin n → R) (a b : Fin q) :
    MvPolynomial ((Fin p × Fin n) ⊕ (Fin q × Fin n)) R :=
  ∑ k, X (Sum.inr (a, k)) * C (f b k)
noncomputable def leadMinor {S : Type} [CommRing S] {m : ℕ} (M : Matrix (Fin m) (Fin m) S) (i : Fin (m + 1)) : S :=
  (M.submatrix (Fin.castLE (Nat.lt_succ_iff.mp i.isLt)) (Fin.castLE (Nat.lt_succ_iff.mp i.isLt)) :
    Matrix (Fin i) (Fin i) S).det
noncomputable def detPoly {p q n : ℕ} (e : Fin p → Fin n → R) (f : Fin q → Fin n → R)
    (c : Fin (p + 1) → ℕ) (c' : Fin (q + 1) → ℕ) : MvPolynomial ((Fin p × Fin n) ⊕ (Fin q × Fin n)) R :=
  (∏ i, leadMinor (Matrix.of (xForm (q := q) e)) i ^ c i) *
    ∏ i, leadMinor (Matrix.of (yForm (p := p) f)) i ^ c' i
noncomputable def mixedLap {p q n : ℕ} (a : Fin p) (b : Fin q) :
    MvPolynomial ((Fin p × Fin n) ⊕ (Fin q × Fin n)) R →ₗ[R]
      MvPolynomial ((Fin p × Fin n) ⊕ (Fin q × Fin n)) R :=
  ∑ k, (pderiv (Sum.inl (a, k))).toLinearMap ∘ₗ (pderiv (Sum.inr (b, k))).toLinearMap
def DetPolyHarmSt : Prop :=
  ∀ (R : Type) [CommRing R] (p q n : ℕ) (e : Fin p → Fin n → R) (f : Fin q → Fin n → R)
    (c : Fin (p + 1) → ℕ) (c' : Fin (q + 1) → ℕ),
    (∀ c₀ d₀, ∑ k, e c₀ k * f d₀ k = 0) → ∀ a b, mixedLap a b (detPoly e f c c') = 0
section Perp
variable {V : Type} [AddCommGroup V] [Module R V]
def hMat {p : ℕ} (h : V →ₗ[R] (V → R)) (e e' : Fin p → V) : Matrix (Fin p) (Fin p) R :=
  Matrix.of fun a' a => h (e' a') (e a)
def perpVec {p : ℕ} (h : V →ₗ[R] (V → R)) (e e' : Fin p → V) (g : V) : V :=
  (hMat h e e').det • g - ∑ a, ∑ a', ((hMat h e e').adjugate a a' * h g (e a)) • e' a'
end Perp
def PerpVecSt : Prop :=
  ∀ (R : Type) [CommRing R] (V : Type) [AddCommGroup V] [Module R V] (p : ℕ)
    (h : V →ₗ[R] (V → R)) (e e' : Fin p → V) (g : V) (c : Fin p), h (perpVec h e e' g) (e c) = 0
def PerpVecIntSt : Prop :=
  ∀ (R : Type) [CommRing R] (O : Subring R) (V : Type) [AddCommGroup V] [Module R V] (p : ℕ)
    (h : V →ₗ[R] (V → R)) (L : Submodule O V),
    (∀ u ∈ L, ∀ v ∈ L, h u v ∈ O) → ∀ (e e' : Fin p → V) (g : V),
      (∀ a, e a ∈ L) → (∀ a, e' a ∈ L) → g ∈ L → perpVec h e e' g ∈ L
def PerpVecPerpSt : Prop :=
  ∀ (R : Type) [CommRing R] (V : Type) [AddCommGroup V] [Module R V] (p : ℕ)
    (h : V →ₗ[R] (V → R)) (e e' : Fin p → V) (g : V),
    (∀ a, h g (e a) = 0) → perpVec h e e' g = (hMat h e e').det • g
end ReciprocityTheory.ChartRestriction.G.TB



-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MapStarMul
-- name    : Development_AbelianVarietyTheory_Proofs_DivisorProofs_MapStarMul
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T06:54:49.223433+00:00
-- url     : https://prove2.me/theorems/6eb0b76d-3863-4bf0-98e2-93ddeff2c26e
-- title:
--   Map Star Mul
-- statement:
--   Definitions and structural lemmas for Map Star Mul, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/MapStarMul.lean

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
open scoped Matrix
namespace GlobalTheory.IndLine.Iwasawa
section Exp
variable {m n : Type} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
end Exp
section Ring
variable {R : Type} [Ring R]
def up (p r q Z : R) : R := p * Z * r + p * Z * q + r * Z * q
def low (p r q Z : R) : R := r * Z * p + q * Z * p + q * Z * r
def mid (p r q Z : R) : R := p * Z * p + r * Z * r + q * Z * q
structure Grading (p r q θ : R) : Prop where
  pp : p * p = p
  qq : q * q = q
  pq : p * q = 0
  qp : q * p = 0
  sum : r = 1 - p - q
  θθ : θ * θ = 1
  θp : θ * p = q * θ
example : Grading (R := Matrix (Fin 3) (Fin 3) ℤ) !![1, 0, 0; 0, 0, 0; 0, 0, 0] !![0, 0, 0; 0, 1, 0; 0, 0, 0]
    !![0, 0, 0; 0, 0, 0; 0, 0, 1] !![0, 0, 1; 0, 1, 0; 1, 0, 0] := by
  constructor <;> decide
namespace Grading
variable {p r q θ : R} (h : Grading p r q θ)
include h
end Grading
end Ring
section Adj
variable {m : Type} [Fintype m] [DecidableEq m]
def Adj (N A B : Matrix m m ℂ) : Prop := Aᵀ * N = N * B.map star
variable {N A B A' B' : Matrix m m ℂ}
variable {p r q θ Z : Matrix m m ℂ}
end Adj
section Plane
variable {A A' : Type} [CommRing A] [CommRing A'] {m n : Type} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
def prX (c : A →+* A) (J : Matrix m m A) (x y : m → A) : Matrix m m A := Matrix.vecMulVec x (J *ᵥ (c ∘ y))
def prY (c : A →+* A) (J : Matrix m m A) (x y : m → A) : Matrix m m A := -Matrix.vecMulVec y (J *ᵥ (c ∘ x))
structure Hyp (c : A →+* A) (J : Matrix m m A) (x y : m → A) (ι : Matrix m n A) (ι' : Matrix n m A) : Prop where
  cc : ∀ a, c (c a) = a
  skew : J.map c = -Jᵀ
  xx : x ⬝ᵥ J *ᵥ (c ∘ x) = 0
  yy : y ⬝ᵥ J *ᵥ (c ∘ y) = 0
  xy : x ⬝ᵥ J *ᵥ (c ∘ y) = 1
  yx : y ⬝ᵥ J *ᵥ (c ∘ x) = -1
  ιx : (J *ᵥ (c ∘ x)) ᵥ* ι = 0
  ιy : (J *ᵥ (c ∘ y)) ᵥ* ι = 0
  left : ι' * ι = 1
  right : ι * ι' = 1 - prX c J x y - prY c J x y
variable {c : A →+* A} {c' : A' →+* A'} {J : Matrix m m A} {x y : m → A} {ι : Matrix m n A} {ι' : Matrix n m A}
example : Hyp (RingHom.id ℤ) !![0, 1; -1, 0] ![1, 0] ![0, 1] (0 : Matrix (Fin 2) (Fin 0) ℤ) 0 := by
  constructor <;> first | decide | (intro a; rfl)
theorem map_mulVec' (f : A →+* A') (hf : ∀ a, f (c a) = c' (f a)) (J : Matrix m m A) (x : m → A) :
    f ∘ (J *ᵥ (c ∘ x)) = J.map f *ᵥ (c' ∘ (f ∘ x)) := by
  funext i
  simp [Matrix.mulVec, dotProduct, hf]
theorem prX_map (f : A →+* A') (hf : ∀ a, f (c a) = c' (f a)) :
    (prX c J x y).map f = prX c' (J.map f) (f ∘ x) (f ∘ y) := by
  ext i j
  simp [prX, Matrix.vecMulVec_apply, ← map_mulVec' f hf]
theorem prY_map (f : A →+* A') (hf : ∀ a, f (c a) = c' (f a)) :
    (prY c J x y).map f = prY c' (J.map f) (f ∘ x) (f ∘ y) := by
  ext i j
  simp [prY, Matrix.vecMulVec_apply, ← map_mulVec' f hf]
theorem Hyp.map (h : Hyp c J x y ι ι') (f : A →+* A') (hf : ∀ a, f (c a) = c' (f a)) (hc : ∀ a, c' (c' a) = a) :
    Hyp c' (J.map f) (f ∘ x) (f ∘ y) (ι.map f) (ι'.map f) := by
  have d : ∀ u v : m → A, (f ∘ u) ⬝ᵥ J.map f *ᵥ (c' ∘ (f ∘ v)) = f (u ⬝ᵥ J *ᵥ (c ∘ v)) := fun u v => by
    rw [← map_mulVec' f hf, RingHom.map_dotProduct]
  have e : ∀ v : m → A, (J *ᵥ (c ∘ v)) ᵥ* ι = 0 → (J.map f *ᵥ (c' ∘ (f ∘ v))) ᵥ* ι.map f = 0 := fun v hv => by
    funext j
    rw [← map_mulVec' f hf, ← RingHom.map_vecMul, hv, Pi.zero_apply, map_zero, Pi.zero_apply]
  refine ⟨hc, ?_, by rw [d, h.xx, map_zero], by rw [d, h.yy, map_zero], by rw [d, h.xy, map_one],
    by rw [d, h.yx, map_neg, map_one], e x h.ιx, e y h.ιy, ?_, ?_⟩
  · ext i j
    have := congrArg f (congrFun (congrFun h.skew i) j)
    simpa [hf] using this
  · rw [← Matrix.map_mul, h.left, Matrix.map_one _ (map_zero _) (map_one _)]
  · rw [← Matrix.map_mul, h.right, Matrix.map_sub _ (map_sub _), Matrix.map_sub _ (map_sub _),
      Matrix.map_one _ (map_zero _) (map_one _), prX_map f hf, prY_map f hf]
namespace Hyp
variable (h : Hyp c J x y ι ι')
include h
end Hyp
end Plane
end GlobalTheory.IndLine.Iwasawa
end



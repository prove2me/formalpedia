-- Prove2me | Definitions.Def_Development_AutomorphicSpectrum_Proofs_DivisibilityProofs_HermitianDarbouxSplitProduct
-- name    : Development_AutomorphicSpectrum_Proofs_DivisibilityProofs_HermitianDarbouxSplitProduct
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T04:11:59.585673+00:00
-- url     : https://prove2.me/theorems/77067873-34fb-41d8-a794-d9f06faf1070
-- title:
--   Hermitian Darboux Split Product
-- statement:
--   Definitions and structural lemmas for Hermitian Darboux Split Product, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/DivisibilityProofs/HermitianDarbouxSplitProduct.lean

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_DivisibilityProofs_FiniteNonunitMatrix
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
namespace GlobalTheory.CompanionTheory.Ar.RT.CellSplit
open GlobalTheory.WeilM
section Lift
variable {S E₁ E₂ : Type} [CommRing S] [CommRing E₁] [CommRing E₂] (s : S ≃+* E₁ × E₂)
def pr₁ : S →+* E₁ := (RingHom.fst E₁ E₂).comp (s : S →+* E₁ × E₂)
def pr₂ : S →+* E₂ := (RingHom.snd E₁ E₂).comp (s : S →+* E₁ × E₂)
theorem pr₁_apply (x : S) : pr₁ s x = (s x).1 := rfl
theorem pr₂_apply (x : S) : pr₂ s x = (s x).2 := rfl
theorem mat_ext {m n : Type} {A B : Matrix m n S} (h1 : A.map (pr₁ s) = B.map (pr₁ s))
    (h2 : A.map (pr₂ s) = B.map (pr₂ s)) : A = B := by
  ext i j
  have e1 : (A.map (pr₁ s)) i j = (B.map (pr₁ s)) i j := by rw [h1]
  have e2 : (A.map (pr₂ s)) i j = (B.map (pr₂ s)) i j := by rw [h2]
  simp only [Matrix.map_apply, pr₁_apply, pr₂_apply] at e1 e2
  exact s.injective (Prod.ext e1 e2)
variable {n : Type} [DecidableEq n]
def lift (x : Matrix n n E₁) : Matrix n n S :=
  Matrix.of fun i j => s.symm (x i j, (1 : Matrix n n E₂) i j)
theorem lift_map₁ (x : Matrix n n E₁) : (lift s x).map (pr₁ s) = x := by
  ext i j
  simp only [lift, Matrix.map_apply, Matrix.of_apply, pr₁_apply, RingEquiv.apply_symm_apply]
theorem lift_map₂ (x : Matrix n n E₁) : (lift s x).map (pr₂ s) = 1 := by
  ext i j
  simp only [lift, Matrix.map_apply, Matrix.of_apply, pr₂_apply, RingEquiv.apply_symm_apply]
theorem map_one' {T : Type} [CommRing T] (f : S →+* T) : (1 : Matrix n n S).map f = 1 := by
  exact Matrix.map_one f (map_zero f) (map_one f)
theorem lift_one : lift s (1 : Matrix n n E₁) = 1 := by
  apply mat_ext s
  · rw [lift_map₁, map_one']
  · rw [lift_map₂, map_one']
theorem lift_mul [Fintype n] (x y : Matrix n n E₁) : lift s (x * y) = lift s x * lift s y := by
  apply mat_ext s
  · rw [Matrix.map_mul, lift_map₁, lift_map₁, lift_map₁]
  · rw [Matrix.map_mul, lift_map₂, lift_map₂, lift_map₂, Matrix.one_mul]
variable [Fintype n]
def liftHom : Matrix n n E₁ →* Matrix n n S where
  toFun := lift s
  map_one' := lift_one s
  map_mul' := lift_mul s
def glLift : GL n E₁ →* GL n S := Units.map (liftHom s)
theorem glLift_coe (x : GL n E₁) : ((glLift s x : GL n S) : Matrix n n S) = lift s (x : Matrix n n E₁) := rfl
def glPr : GL n S →* GL n E₁ := Units.map (RingHom.mapMatrix (pr₁ s) : Matrix n n S →+* Matrix n n E₁).toMonoidHom
end Lift
theorem dbl_map {S T β : Type} [CommRing S] [CommRing T] (f : S →+* T) (J : Matrix β β S) :
    (dbl J).map f = dbl (J.map f) := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> simp [dbl]
section Unitary
variable {k R S E₁ E₂ : Type} [CommRing k] [CommRing R] [CommRing S] [Algebra R S] [CommRing E₁] [Algebra k E₁] [CommRing E₂]
  (c : S →ₐ[R] S) (c₁ : E₁ →ₐ[k] E₁) (c₂ : E₂ →+* E₂) (s : S ≃+* E₁ × E₂)
  (hc1 : ∀ x, (s (c x)).1 = c₁ (s x).1) (hc2 : ∀ x, (s (c x)).2 = c₂ (s x).2)
include hc1 in
theorem map_c₁ {m n : Type} (A : Matrix m n S) : (A.map c).map (pr₁ s) = (A.map (pr₁ s)).map c₁ := by
  ext i j
  simp only [Matrix.map_apply, pr₁_apply, hc1]
include hc2 in
theorem map_c₂ {m n : Type} (A : Matrix m n S) : (A.map c).map (pr₂ s) = (A.map (pr₂ s)).map c₂ := by
  ext i j
  simp only [Matrix.map_apply, pr₂_apply, hc2]
variable {β : Type} [Fintype β] [DecidableEq β] (J : Matrix β β S)
include hc1 hc2 in
theorem lift_mem (x : UG c₁ (dbl (J.map (pr₁ s)))) :
    glLift s (x : GL (β ⊕ β) E₁) ∈ UG c (dbl J) := by
  have hx : ((x : GL (β ⊕ β) E₁) : Matrix (β ⊕ β) (β ⊕ β) E₁)ᵀ * dbl (J.map (pr₁ s)) *
      ((x : GL (β ⊕ β) E₁) : Matrix (β ⊕ β) (β ⊕ β) E₁).map c₁ = dbl (J.map (pr₁ s)) := x.2
  show ((glLift s (x : GL (β ⊕ β) E₁) : GL (β ⊕ β) S) : Matrix (β ⊕ β) (β ⊕ β) S)ᵀ * dbl J *
      ((glLift s (x : GL (β ⊕ β) E₁) : GL (β ⊕ β) S) : Matrix (β ⊕ β) (β ⊕ β) S).map c = dbl J
  rw [glLift_coe]
  apply mat_ext s
  · rw [Matrix.map_mul, Matrix.map_mul, map_c₁ c c₁ s hc1, Matrix.transpose_map, lift_map₁, dbl_map, hx]
  · rw [Matrix.map_mul, Matrix.map_mul, map_c₂ c c₂ s hc2, Matrix.transpose_map, lift_map₂, map_one',
      Matrix.transpose_one, Matrix.one_mul, Matrix.mul_one]
def uLift : UG c₁ (dbl (J.map (pr₁ s))) →* UG c (dbl J) :=
  MonoidHom.codRestrict ((glLift s).comp (UG c₁ (dbl (J.map (pr₁ s)))).subtype) (UG c (dbl J))
    (lift_mem c c₁ c₂ s hc1 hc2 J)
end Unitary
end GlobalTheory.CompanionTheory.Ar.RT.CellSplit



-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_LeviEmbMemNormalizerLower
-- name    : Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_LeviEmbMemNormalizerLower
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T06:14:39.194308+00:00
-- url     : https://prove2.me/theorems/4f5b9d1e-8bbd-4aa5-b20a-b0541daac17b
-- title:
--   Levi Emb Mem Normalizer Lower
-- statement:
--   Definitions and structural lemmas for Levi Emb Mem Normalizer Lower, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/TwistedInnerProducts/LeviEmbMemNormalizerLower.lean

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
namespace GlobalTheory.SmGL
section Blocks
open Matrix
variable (R : Type) [CommRing R] {α n : Type} {m : α → Type} [Fintype α] [LinearOrder α]
  [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)] [Fintype n] [DecidableEq n]
def blk (e : (Σ a, m a) ≃ n) (i : n) : α := (e.symm i).1
open Matrix in
variable (R : Type) [CommRing R] {α n : Type} {m : α → Type} [Fintype α] [LinearOrder α]
  [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)] [Fintype n] [DecidableEq n] in
omit [Fintype α] [LinearOrder α] [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)] [Fintype n]
  [DecidableEq n] in

@[simp] theorem _root_.GlobalTheory.SmGL.blk_apply (e : (Σ a, m a) ≃ n) (a : α) (i : m a) :
    _root_.GlobalTheory.SmGL.blk e (e ⟨a, i⟩) = a := by
  simp [_root_.GlobalTheory.SmGL.blk]
abbrev Levi (m : α → Type) [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)] : Type :=
  ∀ a, GL (m a) R
def parab (e : (Σ a, m a) ≃ n) : Subgroup (GL n R) where
  carrier := {g | (g : Matrix n n R).BlockTriangular (blk e)}
  one_mem' := by
    show ((1 : GL n R) : Matrix n n R).BlockTriangular _
    rw [Units.val_one]; exact blockTriangular_one
  mul_mem' := by
    intro x y hx hy
    show ((x * y : GL n R) : Matrix n n R).BlockTriangular _
    rw [Units.val_mul]; exact BlockTriangular.mul hx hy
  inv_mem' := by
    intro x hx
    show ((x⁻¹ : GL n R) : Matrix n n R).BlockTriangular _
    have : Invertible (x : Matrix n n R) := x.invertible
    rw [Matrix.coe_units_inv]
    exact blockTriangular_inv_of_blockTriangular hx
variable {R}
open Matrix in
variable (R : Type) [CommRing R] {α n : Type} {m : α → Type} [Fintype α] [LinearOrder α]
  [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)] [Fintype n] [DecidableEq n] in
variable {R} in
omit [Fintype α] [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)] in

theorem _root_.GlobalTheory.SmGL.mem_parab {e : (Σ a, m a) ≃ n} {g : GL n R} :
    g ∈ _root_.GlobalTheory.SmGL.parab R e ↔ ∀ i j, _root_.GlobalTheory.SmGL.blk e j <
      _root_.GlobalTheory.SmGL.blk e i → (g : Matrix n n R) i j = 0 :=
  ⟨fun h _ _ hij => h hij, fun h _ _ hij => h _ _ hij⟩
open Matrix in
variable (R : Type) [CommRing R] {α n : Type} {m : α → Type} [Fintype α] [LinearOrder α]
  [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)] [Fintype n] [DecidableEq n] in
variable {R} in
omit [Fintype α] [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)] in

theorem _root_.GlobalTheory.SmGL.mem_parab_iff {e : (Σ a, m a) ≃ n} {g : GL n R} :
    g ∈ _root_.GlobalTheory.SmGL.parab R e ↔ ∀ a b (i : m a) (j : m b), b < a →
      (g : Matrix n n R) (e ⟨a, i⟩) (e ⟨b, j⟩) = 0 := by
  rw [_root_.GlobalTheory.SmGL.mem_parab]
  constructor
  · intro h a b i j hab
    exact h _ _ (by simpa using hab)
  · intro h i j hij
    simpa using h (e.symm i).1 (e.symm j).1 (e.symm i).2 (e.symm j).2 hij
variable (R)
def diagBlock (e : (Σ a, m a) ≃ n) (a : α) : parab R e →* Matrix (m a) (m a) R where
  toFun p := ((p : GL n R) : Matrix n n R).submatrix (fun i => e ⟨a, i⟩) (fun i => e ⟨a, i⟩)
  map_one' := by
    ext i j
    simp [Matrix.one_apply]
  map_mul' x y := by
    ext i j
    show ((x.1 : Matrix n n R) * (y.1 : Matrix n n R)) _ _ = _
    simp only [mul_apply, submatrix_apply]
    rw [← e.sum_comp, Fintype.sum_sigma, Finset.sum_eq_single a]
    · intro b _ hb
      refine Finset.sum_eq_zero fun l _ => ?_
      rcases lt_or_gt_of_ne hb with h | h
      · rw [mem_parab_iff.1 x.2 a b i l h, zero_mul]
      · rw [mem_parab_iff.1 y.2 b a l j h, mul_zero]
    · simp
def leviProj (e : (Σ a, m a) ≃ n) : parab R e →* Levi R m :=
  MonoidHom.pi fun a => (diagBlock R e a).toHomUnits
@[simp] theorem leviProj_apply (e : (Σ a, m a) ≃ n) (p : parab R e) (a : α) (i j : m a) :
    (leviProj R e p a : Matrix (m a) (m a) R) i j =
      ((p : GL n R) : Matrix n n R) (e ⟨a, i⟩) (e ⟨a, j⟩) := rfl
open Classical in

def leviEmb {α : Type} {m : α → Type} [Fintype α] [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)]
    (e : (Σ a, m a) ≃ n) : Levi R m →* GL n R :=
  MonoidHom.toHomUnits
    { toFun := fun g => Matrix.reindex e e (blockDiagonal' fun a => (g a : Matrix (m a) (m a) R))
      map_one' := by
        have : (fun a => (((1 : Levi R m) a : GL (m a) R) : Matrix (m a) (m a) R)) = 1 := rfl
        rw [this, blockDiagonal'_one]
        ext i j
        simp [Matrix.one_apply]
      map_mul' := fun g h => by
        have : (fun a => (((g * h : Levi R m) a : GL (m a) R) : Matrix (m a) (m a) R)) =
          fun a => (g a : Matrix (m a) (m a) R) * (h a : Matrix (m a) (m a) R) := rfl
        rw [this, blockDiagonal'_mul]
        simp [Matrix.submatrix_mul_equiv] }
open Matrix in
variable (R : Type) [CommRing R] {α n : Type} {m : α → Type} [Fintype α] [LinearOrder α]
  [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)] [Fintype n] [DecidableEq n] in
variable {R} in
variable (R) in
omit [LinearOrder α] in

@[simp] theorem _root_.GlobalTheory.SmGL.leviEmb_apply_same (e : (Σ a, m a) ≃ n)
    (g : _root_.GlobalTheory.SmGL.Levi R m) (a : α) (i j : m a) :
    (_root_.GlobalTheory.SmGL.leviEmb R e g : Matrix n n R) (e ⟨a, i⟩) (e ⟨a, j⟩) =
      (g a : Matrix (m a) (m a) R) i j := by
  simp [_root_.GlobalTheory.SmGL.leviEmb, blockDiagonal'_apply_eq]
open Matrix in
variable (R : Type) [CommRing R] {α n : Type} {m : α → Type} [Fintype α] [LinearOrder α]
  [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)] [Fintype n] [DecidableEq n] in
variable {R} in
variable (R) in
omit [LinearOrder α] in

theorem _root_.GlobalTheory.SmGL.leviEmb_apply_ne (e : (Σ a, m a) ≃ n)
    (g : _root_.GlobalTheory.SmGL.Levi R m) {a b : α} (h : a ≠ b) (i : m a) (j : m b) :
    (_root_.GlobalTheory.SmGL.leviEmb R e g : Matrix n n R) (e ⟨a, i⟩) (e ⟨b, j⟩) = 0 := by
  classical
  simp [_root_.GlobalTheory.SmGL.leviEmb, blockDiagonal'_apply_ne _ _ _ h]
open Matrix in
variable (R : Type) [CommRing R] {α n : Type} {m : α → Type} [Fintype α] [LinearOrder α]
  [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)] [Fintype n] [DecidableEq n] in
variable {R} in
variable (R) in

theorem _root_.GlobalTheory.SmGL.leviEmb_mem_parab (e : (Σ a, m a) ≃ n)
    (g : _root_.GlobalTheory.SmGL.Levi R m) :
    _root_.GlobalTheory.SmGL.leviEmb R e g ∈ _root_.GlobalTheory.SmGL.parab R e :=
  _root_.GlobalTheory.SmGL.mem_parab_iff.2 fun _ _ i j hab =>
    _root_.GlobalTheory.SmGL.leviEmb_apply_ne R e g hab.ne' i j
open Matrix in
variable (R : Type) [CommRing R] {α n : Type} {m : α → Type} [Fintype α] [LinearOrder α]
  [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)] [Fintype n] [DecidableEq n] in
variable {R} in
variable (R) in

@[simp] theorem _root_.GlobalTheory.SmGL.leviProj_leviEmb (e : (Σ a, m a) ≃ n)
    (g : _root_.GlobalTheory.SmGL.Levi R m) :
    _root_.GlobalTheory.SmGL.leviProj R e ⟨_root_.GlobalTheory.SmGL.leviEmb R e g,
      _root_.GlobalTheory.SmGL.leviEmb_mem_parab R e g⟩ = g := by
  funext a
  ext i j
  simp
def unipRad (e : (Σ a, m a) ≃ n) : Subgroup (GL n R) := (leviProj R e).ker.map (parab R e).subtype
variable {R}
variable (R)
def opp (e : (Σ a, m a) ≃ n) : (Σ a : αᵒᵈ, m (OrderDual.ofDual a)) ≃ n := e
def parabLower (e : (Σ a, m a) ≃ n) : Subgroup (GL n R) := parab R (opp e)
def unipRadLower (e : (Σ a, m a) ≃ n) : Subgroup (GL n R) := unipRad R (opp e)
def leviProjLower (e : (Σ a, m a) ≃ n) : parabLower R e →* Levi R m := leviProj R (opp e)
@[simp] theorem leviProjLower_apply (e : (Σ a, m a) ≃ n) (p : parabLower R e) (a : α) (i j : m a) :
    (leviProjLower R e p a : Matrix (m a) (m a) R) i j =
      ((p : GL n R) : Matrix n n R) (e ⟨a, i⟩) (e ⟨a, j⟩) := rfl
def stdBlocks {s N : ℕ} (d : Fin s → ℕ) (h : ∑ a, d a = N) : (Σ a, Fin (d a)) ≃ Fin N :=
  finSigmaFinEquiv.trans (finCongr h)
@[reducible] def Two (a b : Type) : Bool → Type
  | false => a
  | true => b
variable {a b : Type}
instance [Fintype a] [Fintype b] : ∀ x, Fintype (Two a b x)
  | false => inferInstanceAs (Fintype a)
  | true => inferInstanceAs (Fintype b)
instance [DecidableEq a] [DecidableEq b] : ∀ x, DecidableEq (Two a b x)
  | false => inferInstanceAs (DecidableEq a)
  | true => inferInstanceAs (DecidableEq b)
def two (e : a ⊕ b ≃ n) : (Σ x, Two a b x) ≃ n :=
  Equiv.trans
    { toFun := fun x => match x with
        | ⟨false, i⟩ => Sum.inl i
        | ⟨true, j⟩ => Sum.inr j
      invFun := fun y => match y with
        | Sum.inl i => ⟨false, i⟩
        | Sum.inr j => ⟨true, j⟩
      left_inv := by rintro ⟨_ | _, _⟩ <;> rfl
      right_inv := by rintro (_ | _) <;> rfl } e
omit [Fintype n] [DecidableEq n] in

@[simp] theorem two_false (e : a ⊕ b ≃ n) (i : a) : two e ⟨false, i⟩ = e (Sum.inl i) := rfl
omit [Fintype n] [DecidableEq n] in

@[simp] theorem two_true (e : a ⊕ b ≃ n) (j : b) : two e ⟨true, j⟩ = e (Sum.inr j) := rfl
def stdSum {r t N : ℕ} (h : r + t = N) : Fin r ⊕ Fin t ≃ Fin N := finSumFinEquiv.trans (finCongr h)
open Matrix in
variable (R : Type) [CommRing R] {α n : Type} {m : α → Type} [Fintype α] [LinearOrder α]
  [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)] [Fintype n] [DecidableEq n] in
variable {R} in
variable (R) in
variable {R} in
variable (R) in
variable {a b : Type} in

@[simp] theorem _root_.GlobalTheory.SmGL.stdSum_inl {r t N : ℕ} (h : r + t = N) (i : Fin r) :
    (_root_.GlobalTheory.SmGL.stdSum h (Sum.inl i) : ℕ) = i := by
  simp [_root_.GlobalTheory.SmGL.stdSum]
open Matrix in
variable (R : Type) [CommRing R] {α n : Type} {m : α → Type} [Fintype α] [LinearOrder α]
  [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)] [Fintype n] [DecidableEq n] in
variable {R} in
variable (R) in
variable {R} in
variable (R) in
variable {a b : Type} in

@[simp] theorem _root_.GlobalTheory.SmGL.stdSum_inr {r t N : ℕ} (h : r + t = N) (j : Fin t) :
    (_root_.GlobalTheory.SmGL.stdSum h (Sum.inr j) : ℕ) = r + j := by
  simp [_root_.GlobalTheory.SmGL.stdSum]
variable [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
def leviTwo (a b : Type) [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] :
    GL a R × GL b R ≃* Levi R (Two a b) where
  toFun g := fun x => match x with
    | false => g.1
    | true => g.2
  invFun g := (g false, g true)
  left_inv _ := rfl
  right_inv g := by funext x; cases x <;> rfl
  map_mul' g h := by funext x; cases x <;> rfl
def emb₂ (e : a ⊕ b ≃ n) : GL a R × GL b R →* GL n R :=
  (leviEmb R (two e)).comp (leviTwo R a b).toMonoidHom
def points (n : Type) : (Σ _ : n, Unit) ≃ n := Equiv.sigmaUnique n fun _ => Unit
omit [Fintype n] [DecidableEq n] in

@[simp] theorem points_apply (i : n) (u : Unit) : points n ⟨i, u⟩ = i := rfl
def leviTorus (n : Type) : (n → Rˣ) ≃* Levi R (fun _ : n => Unit) where
  toFun t i := GeneralLinearGroup.scalar Unit (t i)
  invFun g i := GeneralLinearGroup.det (g i)
  left_inv t := by
    funext i
    ext
    simp [GeneralLinearGroup.scalar]
  right_inv g := by
    funext i
    ext x y
    simp [GeneralLinearGroup.scalar]
  map_mul' s t := by
    funext i
    simp
def diagT (n : Type) [Fintype n] [DecidableEq n] : (n → Rˣ) →* GL n R :=
  (leviEmb R (points n)).comp (leviTorus R n).toMonoidHom
def borel (n : Type) [Fintype n] [DecidableEq n] [LinearOrder n] : Subgroup (GL n R) := parab R (points n)
def unipB (n : Type) [Fintype n] [DecidableEq n] [LinearOrder n] : Subgroup (GL n R) := unipRad R (points n)
def unipBLower (n : Type) [Fintype n] [DecidableEq n] [LinearOrder n] : Subgroup (GL n R) := unipRadLower R (points n)
end Blocks
end GlobalTheory.SmGL



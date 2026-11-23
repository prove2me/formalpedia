-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_MemSiegelOfIffRightAct
-- name    : Development_AbelianVarietyTheory_Definitions_Foundations_MemSiegelOfIffRightAct
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T06:02:11.580806+00:00
-- url     : https://prove2.me/theorems/f076ed1c-f095-43b1-84ae-db3e051cb1fa
-- title:
--   Mem Siegel Of Iff Right Act
-- statement:
--   Definitions and structural lemmas for Mem Siegel Of Iff Right Act, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/MemSiegelOfIffRightAct.lean

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_Statement
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsIwasawaOfIsCompact
import Theorems.Thm_GlobalTheory_Doubling_flatSec_self
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.Doubling.flatSec_self


set_option autoImplicit false
noncomputable section
namespace GlobalTheory.Doubling
open Matrix Formalism.UG
variable {A B : Type} [CommRing A] [CommRing B] {m n ι : Type}
section Block
variable (e : m ⊕ n ≃ ι)
def blkMat (x : Matrix m m A) (y : Matrix n n A) : Matrix ι ι A := (fromBlocks x 0 0 y).submatrix e.symm e.symm
def pairVec {X : Type} (x : m → X) (y : n → X) : ι → X := Sum.elim x y ∘ e.symm
@[simp] theorem pairVec_inl {X : Type} (x : m → X) (y : n → X) (i : m) : pairVec e x y (e (.inl i)) = x i := by
  simp [pairVec]
@[simp] theorem pairVec_inr {X : Type} (x : m → X) (y : n → X) (i : n) : pairVec e x y (e (.inr i)) = y i := by
  simp [pairVec]
theorem pairVec_eta {X : Type} (w : ι → X) : pairVec e (fun i => w (e (.inl i))) (fun i => w (e (.inr i))) = w := by
  funext j; obtain ⟨i | i, rfl⟩ := e.surjective j <;> simp
theorem submatrix_blkMat (x : Matrix m m A) (y : Matrix n n A) : (blkMat e x y).submatrix e e = fromBlocks x 0 0 y := by
  simp [blkMat]
theorem blkMat_map (f : A → B) (hf : f 0 = 0) (x : Matrix m m A) (y : Matrix n n A) :
    (blkMat e x y).map f = blkMat e (x.map f) (y.map f) := by
  simp [blkMat, ← submatrix_map, fromBlocks_map, Matrix.map_zero _ hf]
theorem cT_blkMat (σ : A →+* A) (x : Matrix m m A) (y : Matrix n n A) :
    cT σ (blkMat e x y) = blkMat e (cT σ x) (cT σ y) := by
  rw [cT, blkMat_map e _ (map_zero σ)]
  simp [blkMat, cT, fromBlocks_transpose]
theorem blkMat_inj {x x' : Matrix m m A} {y y' : Matrix n n A} : blkMat e x y = blkMat e x' y' ↔ x = x' ∧ y = y' := by
  refine ⟨fun h => ?_, fun h => by rw [h.1, h.2]⟩
  have := congrArg (fun X => X.submatrix e e) h
  simpa [submatrix_blkMat] using this
variable [Fintype m] [Fintype n] [Fintype ι]
theorem blkMat_mul (x x' : Matrix m m A) (y y' : Matrix n n A) :
    blkMat e x y * blkMat e x' y' = blkMat e (x * x') (y * y') := by
  simp [blkMat, submatrix_mul_equiv, fromBlocks_multiply]
theorem mulVec_pairVec (M : Matrix ι ι A) (x : m → A) (y : n → A) : M *ᵥ pairVec e x y =
    pairVec e ((M.submatrix e e).toBlocks₁₁ *ᵥ x + (M.submatrix e e).toBlocks₁₂ *ᵥ y)
      ((M.submatrix e e).toBlocks₂₁ *ᵥ x + (M.submatrix e e).toBlocks₂₂ *ᵥ y) := by
  funext j
  obtain ⟨i | i, rfl⟩ := e.surjective j <;>
    simp [mulVec, dotProduct, ← e.sum_comp, toBlocks₁₁, toBlocks₁₂, toBlocks₂₁, toBlocks₂₂]
variable [DecidableEq m] [DecidableEq n] [DecidableEq ι]
omit [Fintype m] [Fintype n] [Fintype ι] in
theorem blkMat_one : blkMat e (1 : Matrix m m A) (1 : Matrix n n A) = 1 := by simp [blkMat]
def blkGL : GL m A × GL n A →* GL ι A where
  toFun g := ⟨blkMat e g.1.1 g.2.1, blkMat e (g.1⁻¹).1 (g.2⁻¹).1, by simp [blkMat_mul, blkMat_one],
    by simp [blkMat_mul, blkMat_one]⟩
  map_one' := Units.ext (blkMat_one e)
  map_mul' _ _ := Units.ext (blkMat_mul e _ _ _ _).symm
@[simp] theorem val_blkGL (g : GL m A × GL n A) : (blkGL e g).1 = blkMat e g.1.1 g.2.1 := rfl
theorem blkGL_mem_UJ {σ : A →+* A} {J : Matrix m m A} {J' : Matrix n n A} {x : GL m A} {y : GL n A} :
    blkGL e (x, y) ∈ UJ σ (blkMat e J J') ↔ x ∈ UJ σ J ∧ y ∈ UJ σ J' := by
  change cT σ (blkMat e x.1 y.1) * _ * blkMat e x.1 y.1 = _ ↔ _
  rw [cT_blkMat, blkMat_mul, blkMat_mul, blkMat_inj]
  rfl
theorem UJ_neg (σ : A →+* A) (J : Matrix n n A) : UJ σ (-J) = UJ σ J := by
  ext g
  change cT σ g.1 * (-J) * g.1 = -J ↔ cT σ g.1 * J * g.1 = J
  rw [Matrix.mul_neg, Matrix.neg_mul, neg_inj]
omit [Fintype m] [Fintype n] [Fintype ι] [DecidableEq m] [DecidableEq n] [DecidableEq ι]
def sumLat {O X : Type} [CommRing O] [AddCommGroup X] [Module O X] (L : Submodule O (m → X)) (L' : Submodule O (n → X)) :
    Submodule O (ι → X) :=
  L.comap (LinearMap.funLeft O X (e ∘ .inl)) ⊓ L'.comap (LinearMap.funLeft O X (e ∘ .inr))
end Block
section Siegel
variable (e : n ⊕ n ≃ ι)
def dblGram (J : Matrix n n A) : Matrix ι ι A := blkMat e J (-J)
variable (A) in

def diagSub : Submodule A (ι → A) :=
  LinearMap.eqLocus (LinearMap.funLeft A A (e ∘ .inl)) (LinearMap.funLeft A A (e ∘ .inr))
variable (A) in

def antiSub : Submodule A (ι → A) :=
  LinearMap.eqLocus (LinearMap.funLeft A A (e ∘ .inl)) (-LinearMap.funLeft A A (e ∘ .inr))
theorem pairVec_mem_diagSub {x y : n → A} : pairVec e x y ∈ diagSub A e ↔ x = y := by
  simp [diagSub, funext_iff, LinearMap.funLeft_apply]
def leviMat (M : Matrix ι ι A) : Matrix n n A := (M.submatrix e e).toBlocks₁₁ + (M.submatrix e e).toBlocks₁₂
def quotMat (M : Matrix ι ι A) : Matrix n n A := (M.submatrix e e).toBlocks₁₁ - (M.submatrix e e).toBlocks₂₁
def KeepsDiag (M : Matrix ι ι A) : Prop :=
  (M.submatrix e e).toBlocks₂₁ + (M.submatrix e e).toBlocks₂₂ = leviMat e M
theorem leviMat_blkMat (x y : Matrix n n A) : leviMat e (blkMat e x y) = x := by simp [leviMat, submatrix_blkMat]
theorem keepsDiag_iff {M : Matrix ι ι A} : KeepsDiag e M ↔ ∀ i j,
    M (e (.inr i)) (e (.inl j)) + M (e (.inr i)) (e (.inr j)) =
      M (e (.inl i)) (e (.inl j)) + M (e (.inl i)) (e (.inr j)) := by
  exact Matrix.ext_iff.symm
theorem KeepsDiag.map {M : Matrix ι ι A} (h : KeepsDiag e M) (f : A →+* B) : KeepsDiag e (M.map f) :=
  (keepsDiag_iff e).2 fun i j => by simpa using congrArg f ((keepsDiag_iff e).1 h i j)
variable [Fintype n] [Fintype ι]
variable {e}
theorem KeepsDiag.mulVec_diag {M : Matrix ι ι A} (h : KeepsDiag e M) (x : n → A) :
    M *ᵥ pairVec e x x = pairVec e (leviMat e M *ᵥ x) (leviMat e M *ᵥ x) := by
  rw [mulVec_pairVec, ← add_mulVec, ← add_mulVec, h, leviMat]
theorem KeepsDiag.quotMat_eq {M : Matrix ι ι A} (h : KeepsDiag e M) :
    quotMat e M = (M.submatrix e e).toBlocks₂₂ - (M.submatrix e e).toBlocks₁₂ := by
  rw [quotMat, sub_eq_sub_iff_add_eq_add, ← leviMat, ← h, add_comm]
theorem KeepsDiag.mulVec_quot {M : Matrix ι ι A} (h : KeepsDiag e M) (x y : n → A) (i : n) :
    (M *ᵥ pairVec e x y) (e (.inl i)) - (M *ᵥ pairVec e x y) (e (.inr i)) = (quotMat e M *ᵥ (x - y)) i := by
  rw [mulVec_sub]
  nth_rewrite 2 [h.quotMat_eq]
  simp only [mulVec_pairVec, pairVec_inl, pairVec_inr, quotMat, sub_mulVec, Pi.add_apply, Pi.sub_apply]
  ring
variable [DecidableEq n] [DecidableEq ι]
theorem KeepsDiag.det_eq {M : Matrix ι ι A} (h : KeepsDiag e M) : M.det = (leviMat e M).det * (quotMat e M).det := by
  have h1 : fromBlocks (1 : Matrix n n A) 0 (-1) 1 * M.submatrix e e * fromBlocks (1 : Matrix n n A) 0 1 1 =
      fromBlocks (leviMat e M) (M.submatrix e e).toBlocks₁₂ 0 (quotMat e M) := by
    rw [h.quotMat_eq]
    conv_lhs => rw [← fromBlocks_toBlocks (M.submatrix e e)]
    simp only [fromBlocks_multiply, Matrix.one_mul, Matrix.zero_mul, Matrix.mul_one, Matrix.mul_zero, add_zero,
      zero_add, Matrix.neg_mul, fromBlocks_inj]
    refine ⟨rfl, trivial, ?_, by abel⟩
    rw [add_add_add_comm, ← neg_add, ← leviMat, ← h, neg_add_cancel]
  simpa using congrArg det h1
theorem keepsDiag_of_mulVec {M : Matrix ι ι A} (h : ∀ w ∈ diagSub A e, M *ᵥ w ∈ diagSub A e) : KeepsDiag e M := by
  refine Matrix.ext_of_mulVec_single fun j => ?_
  have := h _ ((pairVec_mem_diagSub e).2 (rfl : (Pi.single j 1 : n → A) = _))
  rw [mulVec_pairVec, pairVec_mem_diagSub] at this
  rw [leviMat, add_mulVec, add_mulVec, this]
theorem mem_stabGL_diagSub {p : GL ι A} : p ∈ stabGL (diagSub A e) ↔ KeepsDiag e p.1 := by
  refine ⟨fun h => keepsDiag_of_mulVec fun w hw => (h w).1 hw, fun h w => ?_⟩
  have hu : IsUnit (quotMat e p.1).det := by
    have := (isUnit_iff_isUnit_det _).1 p.isUnit
    rw [h.det_eq] at this
    exact isUnit_of_mul_isUnit_right this
  obtain ⟨x, y, rfl⟩ : ∃ x y, w = pairVec e x y := ⟨_, _, (pairVec_eta e w).symm⟩
  rw [pairVec_mem_diagSub, ← pairVec_eta e (p.1 *ᵥ _), pairVec_mem_diagSub, ← sub_eq_zero,
    ← sub_eq_zero (a := fun i => (p.1 *ᵥ pairVec e x y) (e (.inl i))),
    show ((fun i => (p.1 *ᵥ pairVec e x y) (e (.inl i))) - fun i => (p.1 *ᵥ pairVec e x y) (e (.inr i))) =
      quotMat e p.1 *ᵥ (x - y) from funext (h.mulVec_quot x y)]
  refine ⟨fun h0 => by rw [h0, mulVec_zero], fun h0 => ?_⟩
  have := congrArg (fun v => (quotMat e p.1)⁻¹ *ᵥ v) h0
  simpa [mulVec_mulVec, nonsing_inv_mul _ hu] using this
theorem leviMat_mul {M N : Matrix ι ι A} (hM : KeepsDiag e M) (hN : KeepsDiag e N) :
    leviMat e (M * N) = leviMat e M * leviMat e N := by
  refine Matrix.ext_of_mulVec_single fun j => funext fun i => ?_
  have h1 := congrFun (mulVec_pairVec e (M * N) (Pi.single j 1) (Pi.single j 1)) (e (.inl i))
  rw [← mulVec_mulVec, hN.mulVec_diag, hM.mulVec_diag, pairVec_inl, pairVec_inl, ← add_mulVec, mulVec_mulVec] at h1
  exact h1.symm
variable (e)
def leviGL : stabGL (diagSub A e) →* GL n A :=
  MonoidHom.toHomUnits
    { toFun := fun p => leviMat e p.1.1
      map_one' := by rw [← leviMat_blkMat e (1 : Matrix n n A) 1, blkMat_one]; rfl
      map_mul' := fun p q => leviMat_mul (mem_stabGL_diagSub.1 p.2) (mem_stabGL_diagSub.1 q.2) }
@[simp] theorem val_leviGL (p : stabGL (diagSub A e)) : (leviGL e p).1 = leviMat e p.1.1 := rfl
def rightAct (l : ι → A) (M : Matrix ι ι A) : ι → A := l ᵥ* (blkMat e 1 (-1) * M * blkMat e 1 (-1))
def rowEval (l w : ι → A) : A := l ⬝ᵥ (blkMat e (1 : Matrix n n A) (-1) *ᵥ w)
end Siegel
section Levi
variable (e : n ⊕ n ≃ ι) [Fintype n] [Fintype ι] [DecidableEq n] [DecidableEq ι]
variable [Invertible (2 : A)]
def cayley : GL ι A :=
  ⟨(fromBlocks 1 1 1 (-1)).submatrix e.symm e.symm, ⅟(2 : A) • (fromBlocks 1 1 1 (-1)).submatrix e.symm e.symm, by
    rw [Matrix.mul_smul, submatrix_mul_equiv, fromBlocks_multiply, ← blkMat_one e, blkMat]
    refine congrArg (fun X : Matrix (n ⊕ n) (n ⊕ n) A => X.submatrix e.symm e.symm) (a₁ := ⅟(2 : A) • fromBlocks _ _ _ _) ?_
    simp [fromBlocks_smul, ← two_smul A, smul_smul], by
    rw [Matrix.smul_mul, submatrix_mul_equiv, fromBlocks_multiply, ← blkMat_one e, blkMat]
    refine congrArg (fun X : Matrix (n ⊕ n) (n ⊕ n) A => X.submatrix e.symm e.symm) (a₁ := ⅟(2 : A) • fromBlocks _ _ _ _) ?_
    simp [fromBlocks_smul, ← two_smul A, smul_smul]⟩
def leviElt : GL n A × GL n A →* GL ι A := (MulAut.conj (cayley e)).toMonoidHom.comp (blkGL e)
end Levi
section Group
variable (e : n ⊕ n ≃ ι) [Fintype n] [Fintype ι] [DecidableEq n] [DecidableEq ι] {G : Type} [Group G]
  (mat : G →* GL ι A)
def siegelOf : Subgroup G := (stabGL (diagSub A e)).comap mat
def leviOf : siegelOf e mat →* GL n A := (leviGL e).comp (mat.subgroupComap _)
def aOf : siegelOf e mat →* Aˣ := GeneralLinearGroup.det.comp (leviOf e mat)
def unipOf : Subgroup G := (leviOf e mat).ker.map (siegelOf e mat).subtype
def leviSubOf : Subgroup G := siegelOf e mat ⊓ (stabGL (antiSub A e)).comap mat
variable {e mat}
variable [TopologicalSpace A] [IsTopologicalRing A] [TopologicalSpace G]
end Group
section Series
open scoped NNReal
open MeasureTheory
variable (e : n ⊕ n ≃ ι) [Fintype n] [Fintype ι] [DecidableEq n] [DecidableEq ι] {G : Type} [Group G]
  (mat : G →* GL ι A) (ν : Aˣ →* ℝ≥0) (K : Subgroup G)
def absAOf : siegelOf e mat →* ℝ≥0 := ν.comp (aOf e mat)
def IwasawaOf : Prop := IsIwasawa (absAOf e mat ν) K
def hgtOf : G → ℝ≥0 := iwAbs (absAOf e mat ν) K
def degPSOf [TopologicalSpace G] (μ : Aˣ →* Circle) (s : ℂ) : Submodule ℂ (G → ℂ) :=
  indSpace (absAOf e mat ν) K (μ.comp (aOf e mat)) (s + (Fintype.card n : ℂ) / 2)
def flatOf (Φ : G → ℂ) (s₀ s : ℂ) : G → ℂ := flatSec (absAOf e mat ν) K Φ s₀ s
variable {e mat ν K}
variable [TopologicalSpace A] [IsTopologicalRing A] [T2Space A] [TopologicalSpace G] [IsTopologicalGroup G]
end Series
section Io
variable [Fintype m] [Fintype n] [Fintype ι] [DecidableEq m] [DecidableEq n] [DecidableEq ι] (σ : A →+* A)
def sumU (e : m ⊕ n ≃ ι) {J : Matrix m m A} {J' : Matrix n n A} {Q : Matrix ι ι A} (h : Q = blkMat e J J') :
    UJ σ J × UJ σ J' →* UJ σ Q :=
  ((blkGL e).comp ((UJ σ J).subtype.prodMap (UJ σ J').subtype)).codRestrict _ fun g =>
    h ▸ (blkGL_mem_UJ e).2 ⟨g.1.2, g.2.2⟩
def ioU (e : n ⊕ n ≃ ι) {J : Matrix n n A} {Q : Matrix ι ι A} (h : Q = dblGram e J) : UJ σ J × UJ σ J →* UJ σ Q :=
  ((blkGL e).comp ((UJ σ J).subtype.prodMap (UJ σ J).subtype)).codRestrict _ fun g =>
    h ▸ (blkGL_mem_UJ e).2 ⟨g.1.2, (UJ_neg σ J).symm ▸ g.2.2⟩
end Io
example (g : ℤ) : leviMat (Equiv.refl (Unit ⊕ Unit)) (blkMat (Equiv.refl _) (of fun _ _ => g) (of fun _ _ => g)) () () = g ∧
    leviMat (Equiv.refl (Unit ⊕ Unit)) (fromBlocks (0 : Matrix Unit Unit ℤ) 1 1 0) = 1 ∧
    quotMat (Equiv.refl (Unit ⊕ Unit)) (fromBlocks (0 : Matrix Unit Unit ℤ) 1 1 0) = -1 := by
  simp [leviMat, quotMat, blkMat]
end GlobalTheory.Doubling
end



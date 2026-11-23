-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LeviBlocksParabolicInductionFiniteLength
-- name    : Development_AbelianVarietyTheory_Proofs_DivisorProofs_LeviBlocksParabolicInductionFiniteLength
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T17:44:35.870945+00:00
-- url     : https://prove2.me/theorems/1c5ec22d-6766-401f-9c01-bca103b58fbd
-- title:
--   Levi Blocks Parabolic Induction Finite Length
-- statement:
--   Definitions and structural lemmas for Levi Blocks Parabolic Induction Finite Length, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/LeviBlocksParabolicInductionFiniteLength.lean

import Mathlib
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__IrreducibleAdmissibleGL_69e19a0de021488a
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__StandardFunctorsFiniteLength_93eb2991d501e04b
import Theorems.Thm_GlobalTheory_SmGL_IsSmoothChar_comp
import Theorems.Thm_GlobalTheory_SmGL_IsSubquotient_trans
import Theorems.Thm_GlobalTheory_SmGL_deltaHalf_apply
import Theorems.Thm_GlobalTheory_SmGL_parInd_law

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory.PRep GlobalTheory.SmGL Matrix
namespace GlobalTheory.BlockReorder
variable {α n : Type} {m : α → Type} [Fintype α] [LinearOrder α] [∀ a, Fintype (m a)]
  [∀ a, DecidableEq (m a)] [Fintype n] [DecidableEq n]
abbrev NonemptyBlockIndex (m : α → Type) [∀ a, Fintype (m a)] : Type := {a : α // 0 < Fintype.card (m a)}
abbrev numBlocks (m : α → Type) [Fintype α] [LinearOrder α] [∀ a, Fintype (m a)] : ℕ := Fintype.card (NonemptyBlockIndex m)
def neOrder (m : α → Type) [Fintype α] [LinearOrder α] [∀ a, Fintype (m a)] : Fin (numBlocks m) ≃o NonemptyBlockIndex m :=
  monoEquivOfFin (NonemptyBlockIndex m) rfl
def blockSize (m : α → Type) [Fintype α] [LinearOrder α] [∀ a, Fintype (m a)] (i : Fin (numBlocks m)) : ℕ :=
  Fintype.card (m (neOrder m i).1)
def blockNum (i : Fin (numBlocks m)) : Fin (blockSize m i) ≃ m (neOrder m i).1 := (Fintype.equivFin _).symm
def stdSigma (m : α → Type) [Fintype α] [LinearOrder α] [∀ a, Fintype (m a)] :
    (Σ i, Fin (blockSize m i)) ≃ (Σ a, m a) :=
  ((Equiv.sigmaCongrRight blockNum).trans (Equiv.sigmaCongrLeft (β := fun b : NonemptyBlockIndex m => m b.1) (neOrder m).toEquiv)).trans
    (Equiv.sigmaSubtypeEquivOfSubset m (fun a => 0 < Fintype.card (m a))
      fun _ x => Fintype.card_pos_iff.2 ⟨x⟩)
@[simp] theorem stdSigma_apply (i : Fin (numBlocks m)) (u : Fin (blockSize m i)) :
    stdSigma m ⟨i, u⟩ = ⟨(neOrder m i).1, blockNum i u⟩ := rfl
def stdIdx (e : (Σ a, m a) ≃ n) : Fin (∑ i, blockSize m i) ≃ n :=
  finSigmaFinEquiv.symm.trans ((stdSigma m).trans e)
@[simp] theorem stdIdx_symm_apply (e : (Σ a, m a) ≃ n) (i : Fin (numBlocks m)) (u : Fin (blockSize m i)) :
    (stdIdx e).symm (e ⟨(neOrder m i).1, blockNum i u⟩) = finSigmaFinEquiv ⟨i, u⟩ := by
  rw [Equiv.symm_apply_eq, stdIdx]
  simp
variable (R : Type) [CommRing R]
def glIso (e : (Σ a, m a) ≃ n) : GL (Fin (∑ i, blockSize m i)) R ≃* GL n R :=
  Units.mapEquiv (reindexAlgEquiv R R (stdIdx e)).toMulEquiv
variable {R}
theorem val_glIso (e : (Σ a, m a) ≃ n) (g : GL (Fin (∑ i, blockSize m i)) R) (x y : n) :
    (glIso R e g : Matrix n n R) x y = (g : Matrix _ _ R) ((stdIdx e).symm x) ((stdIdx e).symm y) := rfl
variable (R)
theorem glIso_mem_parab (e : (Σ a, m a) ≃ n) {g : GL (Fin (∑ i, blockSize m i)) R}
    (hg : g ∈ parab R (finSigmaFinEquiv : (Σ i, Fin (blockSize m i)) ≃ _)) : glIso R e g ∈ parab R e := by
  refine mem_parab.2 fun x y hxy => ?_
  obtain ⟨⟨i, u⟩, rfl⟩ := ((stdSigma m).trans e).surjective x
  obtain ⟨⟨j, v⟩, rfl⟩ := ((stdSigma m).trans e).surjective y
  simp only [Equiv.trans_apply, stdSigma_apply, blk_apply] at hxy
  have hji : j < i := (neOrder m).lt_iff_lt.1 (Subtype.coe_lt_coe.1 hxy)
  simp only [Equiv.trans_apply, stdSigma_apply, val_glIso, stdIdx_symm_apply]
  exact mem_parab_iff.1 hg i j u v hji
def leviMap (e : (Σ a, m a) ≃ n) : Levi R (fun i => Fin (blockSize m i)) →* Levi R m :=
  (leviProj R e).comp (((glIso R e).toMonoidHom.comp (leviEmb R finSigmaFinEquiv)).codRestrict (parab R e)
    fun g => glIso_mem_parab R e (leviEmb_mem_parab R _ g))
variable {R}
theorem leviMap_apply (e : (Σ a, m a) ≃ n) (g : Levi R (fun i => Fin (blockSize m i))) (a : α) (x y : m a) :
    (leviMap R e g a : Matrix (m a) (m a) R) x y =
      (leviEmb R finSigmaFinEquiv g : Matrix _ _ R) ((stdIdx e).symm (e ⟨a, x⟩)) ((stdIdx e).symm (e ⟨a, y⟩)) :=
  rfl
@[simp] theorem leviMap_apply_num (e : (Σ a, m a) ≃ n) (g : Levi R (fun i => Fin (blockSize m i))) (i : Fin (numBlocks m))
    (u v : Fin (blockSize m i)) :
    (leviMap R e g (neOrder m i).1 : Matrix _ _ R) (blockNum i u) (blockNum i v) = (g i : Matrix _ _ R) u v := by
  rw [leviMap_apply, stdIdx_symm_apply, stdIdx_symm_apply, leviEmb_apply_same]
theorem levi_ext {g h : Levi R m}
    (H : ∀ (i : Fin (numBlocks m)) (u v : Fin (blockSize m i)),
      (g (neOrder m i).1 : Matrix _ _ R) (blockNum i u) (blockNum i v) = (h (neOrder m i).1 : Matrix _ _ R) (blockNum i u) (blockNum i v)) :
    g = h := by
  funext a
  refine Units.ext (Matrix.ext fun x y => ?_)
  obtain ⟨i, hi⟩ := (neOrder m).surjective ⟨a, Fintype.card_pos_iff.2 ⟨x⟩⟩
  have ha : (neOrder m i).1 = a := congrArg Subtype.val hi
  subst ha
  obtain ⟨u, rfl⟩ := (blockNum i).surjective x
  obtain ⟨v, rfl⟩ := (blockNum i).surjective y
  exact H i u v
theorem leviProj_glIso (e : (Σ a, m a) ≃ n)
    (p : parab R (finSigmaFinEquiv : (Σ i, Fin (blockSize m i)) ≃ _)) :
    leviProj R e ⟨glIso R e p, glIso_mem_parab R e p.2⟩ =
      leviMap R e (leviProj R finSigmaFinEquiv p) := by
  refine levi_ext fun i u v => ?_
  rw [leviMap_apply_num, leviProj_apply, leviProj_apply]
  simp only [val_glIso, stdIdx_symm_apply]
theorem continuous_glIso [TopologicalSpace R] (e : (Σ a, m a) ≃ n) : Continuous (glIso R e) := by
  refine Units.continuous_iff.2 ⟨continuous_matrix fun x y => ?_, continuous_matrix fun x y => ?_⟩
  · exact Units.continuous_val.matrix_elem _ _
  · have : ∀ g : GL (Fin (∑ i, blockSize m i)) R, (((glIso R e g)⁻¹ : GL n R) : Matrix n n R) x y =
        ((g⁻¹ : GL _ R) : Matrix _ _ R) ((stdIdx e).symm x) ((stdIdx e).symm y) := fun g => by
      rw [← map_inv]; rfl
    simp only [this]
    exact Units.continuous_coe_inv.matrix_elem _ _
end GlobalTheory.BlockReorder
namespace GlobalTheory.BlockReorder
variable {α n : Type} {m : α → Type} [Fintype α] [LinearOrder α] [∀ a, Fintype (m a)]
  [∀ a, DecidableEq (m a)] [Fintype n] [DecidableEq n]
theorem prod_neOrder {M : Type} [CommMonoid M] (F : α → M) (hF : ∀ a, Fintype.card (m a) = 0 → F a = 1) :
    ∏ a, F a = ∏ i : Fin (numBlocks m), F (neOrder m i).1 := by
  rw [← Finset.prod_filter_of_ne (p := fun a => 0 < Fintype.card (m a))
    (fun a _ h => Nat.pos_of_ne_zero fun h0 => h (hF a h0)),
    ← Finset.prod_subtype_eq_prod_filter, Finset.subtype_univ]
  exact ((neOrder m).toEquiv.prod_comp (fun b : NonemptyBlockIndex m => F b.1)).symm
theorem sum_neOrder {M : Type} [AddCommMonoid M] (F : α → M) (hF : ∀ a, Fintype.card (m a) = 0 → F a = 0) :
    ∑ a, F a = ∑ i : Fin (numBlocks m), F (neOrder m i).1 := by
  rw [← Finset.sum_filter_of_ne (p := fun a => 0 < Fintype.card (m a))
    (fun a _ h => Nat.pos_of_ne_zero fun h0 => h (hF a h0)),
    ← Finset.sum_subtype_eq_sum_filter, Finset.subtype_univ]
  exact ((neOrder m).toEquiv.sum_comp (fun b : NonemptyBlockIndex m => F b.1)).symm
theorem modExp_neOrder (i : Fin (numBlocks m)) : modExp m (neOrder m i).1 = modExp (fun j => Fin (blockSize m j)) i := by
  unfold modExp
  simp only [Finset.sum_filter]
  rw [sum_neOrder (m := m) (fun b => if (neOrder m i).1 < b then (Fintype.card (m b) : ℤ) else 0)
      (fun b hb => by simp [hb]),
    sum_neOrder (m := m) (fun b => if b < (neOrder m i).1 then (Fintype.card (m b) : ℤ) else 0)
      (fun b hb => by simp [hb])]
  have hc : ∀ j : Fin (numBlocks m), (Fintype.card (Fin (blockSize m j)) : ℤ) = Fintype.card (m (neOrder m j).1) :=
    fun j => by rw [Fintype.card_fin]; rfl
  simp only [hc, OrderIso.lt_iff_lt, Subtype.coe_lt_coe]
variable {R : Type} [CommRing R]
theorem det_eq_one_of_card_eq_zero {a : α} (h : Fintype.card (m a) = 0) (g : GL (m a) R) :
    Matrix.GeneralLinearGroup.det g = 1 := by
  haveI : IsEmpty (m a) := Fintype.card_eq_zero_iff.1 h
  ext
  simp [Matrix.det_isEmpty]
theorem det_leviMap (e : (Σ a, m a) ≃ n) (g : Levi R (fun i => Fin (blockSize m i))) (i : Fin (numBlocks m)) :
    Matrix.GeneralLinearGroup.det (leviMap R e g (neOrder m i).1) = Matrix.GeneralLinearGroup.det (g i) := by
  ext
  simp only [Matrix.GeneralLinearGroup.val_det_apply]
  have : (leviMap R e g (neOrder m i).1 : Matrix _ _ R) =
      (g i : Matrix _ _ R).submatrix (blockNum i).symm (blockNum i).symm := by
    ext x y
    obtain ⟨u, rfl⟩ := (blockNum i).surjective x
    obtain ⟨v, rfl⟩ := (blockNum i).surjective y
    simp
  rw [this, Matrix.det_submatrix_equiv_self]
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
theorem deltaHalf_leviMap (e : (Σ a, m a) ≃ n) (g : Levi k (fun i => Fin (blockSize m i))) :
    deltaHalf k m (leviMap k e g) = deltaHalf k (fun i => Fin (blockSize m i)) g := by
  rw [deltaHalf_apply, deltaHalf_apply, prod_neOrder (m := m) _ fun a ha => by
    rw [det_eq_one_of_card_eq_zero ha, map_one]]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [det_leviMap, modExp_neOrder]
end GlobalTheory.BlockReorder
namespace GlobalTheory.BlockReorder
variable {α n : Type} {m : α → Type} [Fintype α] [LinearOrder α] [∀ a, Fintype (m a)]
  [∀ a, DecidableEq (m a)] [Fintype n] [DecidableEq n]
  {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {W : Type} [AddCommGroup W] [Module ℂ W]
def pullInd (e : (Σ a, m a) ≃ n) (ρ : Representation ℂ (Levi k m) W) :
    IndSp e ρ →ₗ[ℂ] IndSp (finSigmaFinEquiv : (Σ i, Fin (blockSize m i)) ≃ _) (ρ.comp (leviMap k e)) where
  toFun f := ⟨⟨fun g => f.1.1 (glIso k e g), fun p g => by
      show f.1.1 (glIso k e ((p : GL _ k) * g)) =
        (deltaHalf k (fun i => Fin (blockSize m i)) (leviProj k finSigmaFinEquiv p) : ℂ) •
          ρ (leviMap k e (leviProj k finSigmaFinEquiv p)) (f.1.1 (glIso k e g))
      rw [map_mul, ← deltaHalf_leviMap e, ← leviProj_glIso]
      exact parInd_law e ρ f ⟨glIso k e p, glIso_mem_parab k e p.2⟩ (glIso k e g)⟩,
    mem_smoothPart_of_nhds (Filter.mem_of_superset
      ((continuous_glIso e).continuousAt.preimage_mem_nhds
        (by rw [map_one]; exact IsOpen.mem_nhds f.2 (by simp))) fun g hg => by
      have hg' : ind (parab k e) ((twist ρ (deltaHalf k m)).comp (leviProj k e)) (glIso k e g) f.1 = f.1 := hg
      apply Subtype.ext
      funext x
      show f.1.1 (glIso k e (x * g)) = f.1.1 (glIso k e x)
      rw [map_mul]
      exact congrFun (congrArg Subtype.val hg') (glIso k e x))⟩
  map_add' f f' := rfl
  map_smul' c f := rfl
def pullMap (e : (Σ a, m a) ≃ n) (ρ : Representation ℂ (Levi k m) W) :
    Representation.IntertwiningMap ((parInd e ρ).comp (glIso k e).toMonoidHom)
      (parInd (finSigmaFinEquiv : (Σ i, Fin (blockSize m i)) ≃ _) (ρ.comp (leviMap k e))) where
  toLinearMap := pullInd e ρ
  isIntertwining' g := by
    refine LinearMap.ext fun f => Subtype.ext (Subtype.ext (funext fun x => ?_))
    show f.1.1 (glIso k e x * glIso k e g) = f.1.1 (glIso k e (x * g))
    rw [map_mul]
end GlobalTheory.BlockReorder
namespace GlobalTheory
end GlobalTheory



-- Prove2me | Definitions.Def_LeanPool_OrderClosures_BanLat_Operators_Hom
-- name    : LeanPool_OrderClosures_BanLat_Operators_Hom
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T10:23:26.173528+00:00
-- url     : https://prove2.me/theorems/9dc6b718-8555-41eb-a275-e1fddfbf690f
-- title:
--   Hom
-- statement:
--   Definitions and structural lemmas for Hom, from Antonio Avilés; Mitchell A. Taylor; Pedro Tradacete; David Muñoz-Lahoz; LeanPool contributors's pinned Order closure, order adherence and Fatou norms development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/BanLat/Operators/Hom.lean

module
public import Definitions.Def_LeanPool_OrderClosures_BanLat_Operators_Positive
public import Definitions.Def_LeanPool_OrderClosures_BanLat_LLexpr
public import Mathlib.Analysis.Normed.Operator.LinearIsometry
public import Theorems.Thm_LLexpr_NormalForm_eval_add
public import Theorems.Thm_LLexpr_NormalForm_eval_inf
public import Theorems.Thm_LLexpr_NormalForm_eval_negate
public import Theorems.Thm_LLexpr_NormalForm_eval_smul
public import Theorems.Thm_LLexpr_NormalForm_eval_sup
public import Theorems.Thm_LLexpr_NormalForm_eval_var
public import Theorems.Thm_LLexpr_NormalForm_eval_zero
public import Theorems.Thm_LLexpr_SupLinearCombination_eval_add
public import Theorems.Thm_LLexpr_SupLinearCombination_eval_singleton
public import Theorems.Thm_LLexpr_SupLinearCombination_eval_smul
public import Theorems.Thm_LLexpr_SupLinearCombination_eval_sup
public import Theorems.Thm_LLexpr_eval_add
public import Theorems.Thm_LLexpr_eval_inf
public import Theorems.Thm_LLexpr_eval_reindexExpr
public import Theorems.Thm_LLexpr_eval_smul
public import Theorems.Thm_LLexpr_eval_sup
public import Theorems.Thm_LLexpr_eval_var
public import Theorems.Thm_LLexpr_eval_zero
public import Theorems.Thm_LLexpr_normalize_eval
public import Theorems.Thm_NormedVectorLattice_continuous_inf
public import Theorems.Thm_NormedVectorLattice_continuous_sup
public import Theorems.Thm_Positive_continuous
public import Theorems.Thm_Positive_extension_apply
public import Theorems.Thm_Positive_extension_nonneg
public import Theorems.Thm_Positive_extension_positive
public import Theorems.Thm_Positive_monotone_iff
attribute [local simp] LLexpr.NormalForm.eval_add
attribute [local simp] LLexpr.NormalForm.eval_inf
attribute [local simp] LLexpr.NormalForm.eval_negate
attribute [local simp] LLexpr.NormalForm.eval_smul
attribute [local simp] LLexpr.NormalForm.eval_sup
attribute [local simp] LLexpr.NormalForm.eval_var
attribute [local simp] LLexpr.NormalForm.eval_zero
attribute [local simp] LLexpr.SupLinearCombination.eval_add
attribute [local simp] LLexpr.SupLinearCombination.eval_singleton
attribute [local simp] LLexpr.SupLinearCombination.eval_smul
attribute [local simp] LLexpr.SupLinearCombination.eval_sup
attribute [local simp] LLexpr.eval_add
attribute [local simp] LLexpr.eval_inf
attribute [local simp] LLexpr.eval_reindexExpr
attribute [local simp] LLexpr.eval_smul
attribute [local simp] LLexpr.eval_sup
attribute [local simp] LLexpr.eval_var
attribute [local simp] LLexpr.eval_zero
attribute [local simp] LLexpr.normalize_eval
attribute [local simp] Positive.extension_apply


set_option autoImplicit true
@[expose] public section
@[expose] public section
structure VecLatHom (X : Type*) (Y : Type*) [AddCommGroup X] [AddCommGroup Y]
  [Lattice X] [Lattice Y] [IsOrderedAddMonoid X] [IsOrderedAddMonoid Y]
  [VectorLattice X] [VectorLattice Y] extends X →ₗ[ℝ] Y, LatticeHom X Y
variable {X : Type*} {Y : Type*} [AddCommGroup X] [AddCommGroup Y]
  [Lattice X] [Lattice Y] [IsOrderedAddMonoid X] [IsOrderedAddMonoid Y]
  [VectorLattice X] [VectorLattice Y]
structure IsVecLatHom (f : X → Y) extends IsLinearMap ℝ f where
  map_sup' : ∀ x y : X, f (x ⊔ y) = (f x) ⊔ (f y)
  map_inf' : ∀ x y : X, f (x ⊓ y) = (f x) ⊓ (f y)
namespace VecLatHom
instance instFunLike : FunLike (VecLatHom X Y) X Y where
  coe f := f.toFun
  coe_injective f g h := by
    dsimp at h
    cases f
    cases g
    congr
    exact LinearMap.ext_iff.mpr (congrFun h)
def ofIsVecLatHom (f : X → Y) (h : IsVecLatHom f) : VecLatHom X Y where
  toFun := f
  map_add' := h.map_add
  map_smul' := h.map_smul
  map_sup' := h.map_sup'
  map_inf' := h.map_inf'
instance instLatticeHomClass : LatticeHomClass (VecLatHom X Y) X Y where
  map_inf := by
    intro f a b
    exact f.toLatticeHom.map_inf' a b
  map_sup := by
    intro f a b
    exact f.toLatticeHom.map_sup' a b
instance instLinearMapClass : LinearMapClass (VecLatHom X Y) ℝ X Y where
  map_add := by
    intro f a b
    exact f.toLinearMap.map_add a b
  map_smulₛₗ := by
    intro f c x
    simp only [RingHom.id_apply]
    exact f.toLinearMap.map_smul c x
theorem toFun_eq_coe {f : VecLatHom X Y} : f.toFun = (f : X → Y) := rfl
theorem monotone (f : VecLatHom X Y) : Monotone f := by
  intro x y hxy
  have : x ⊔ y = y := by simp [hxy]
  rw [← sup_eq_right, ← map_sup f x y, this]
def id : VecLatHom X X :=
  { LinearMap.id with
    map_sup' := fun _ _ => rfl
    map_inf' := fun _ _ => rfl }
def ofAbs (f : X →ₗ[ℝ] Y) (abs : ∀ x : X, f |x| = |f x|) : VecLatHom X Y :=
  { f with
    map_sup' := fun a b => by
      change f (a ⊔ b) = f a ⊔ f b
      rw [sup_eq_half_smul_add_add_abs_sub' ℝ, map_smul, map_add, map_add,
          abs (b - a), map_sub, ← sup_eq_half_smul_add_add_abs_sub' ℝ]
    map_inf' := fun a b => by
      change f (a ⊓ b) = f a ⊓ f b
      rw [inf_eq_half_smul_add_sub_abs_sub' ℝ, map_smul, map_sub, map_add,
          abs (b - a), map_sub, ← inf_eq_half_smul_add_sub_abs_sub' ℝ] }
def comp {Z : Type*} [AddCommGroup Z] [Lattice Z] [IsOrderedAddMonoid Z]
  [VectorLattice Z] (g : VecLatHom Y Z) (f : VecLatHom X Y) :
  VecLatHom X Z :=
  {LinearMap.comp g.toLinearMap f.toLinearMap with
    map_sup' := by
      intro x y
      simp only [AddHom.toFun_eq_coe, LinearMap.coe_toAddHom, LinearMap.coe_comp,
        Function.comp_apply]
      change g ( f (x ⊔ y) ) = (g (f x)) ⊔ (g (f y))
      simp only [map_sup]
    map_inf' := by
      intro x y
      simp only [AddHom.toFun_eq_coe, LinearMap.coe_toAddHom, LinearMap.coe_comp,
        Function.comp_apply]
      change g ( f (x ⊓ y) ) = (g (f x)) ⊓ (g (f y))
      simp only [map_inf]
  }
noncomputable def symm (f : VecLatHom X Y) (h : Function.Bijective f) : VecLatHom Y X :=
  {(LinearEquiv.ofBijective f.toLinearMap h).symm with
    map_sup' := by
      intro a b
      change
        (LinearEquiv.ofBijective f.toLinearMap h).symm (a ⊔ b) =
        (LinearEquiv.ofBijective f.toLinearMap h).symm a ⊔
        (LinearEquiv.ofBijective f.toLinearMap h).symm b
      rw [LinearEquiv.symm_apply_eq]
      change
        a ⊔ b = f ( (LinearEquiv.ofBijective f.toLinearMap h).symm a ⊔
        (LinearEquiv.ofBijective f.toLinearMap h).symm b)
      rw [map_sup]
      change
        a ⊔ b = LinearEquiv.ofBijective f.toLinearMap h
                ((LinearEquiv.ofBijective f.toLinearMap h).symm a) ⊔
                LinearEquiv.ofBijective f.toLinearMap h
                ((LinearEquiv.ofBijective f.toLinearMap h).symm b)
      rw [LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
    map_inf' := by
      intro a b
      change
        (LinearEquiv.ofBijective f.toLinearMap h).symm (a ⊓ b) =
        (LinearEquiv.ofBijective f.toLinearMap h).symm a ⊓
        (LinearEquiv.ofBijective f.toLinearMap h).symm b
      rw [LinearEquiv.symm_apply_eq]
      change
        a ⊓ b = f ( (LinearEquiv.ofBijective f.toLinearMap h).symm a ⊓
        (LinearEquiv.ofBijective f.toLinearMap h).symm b)
      rw [map_inf]
      change
        a ⊓ b = LinearEquiv.ofBijective f.toLinearMap h
                ((LinearEquiv.ofBijective f.toLinearMap h).symm a) ⊓
                LinearEquiv.ofBijective f.toLinearMap h
                ((LinearEquiv.ofBijective f.toLinearMap h).symm b)
      rw [LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
  }
end VecLatHom
namespace LLexpr
variable {n : ℕ}
end LLexpr
namespace IsVecLatHom
def mk' (f : X → Y) (vlh : IsVecLatHom f) : VecLatHom X Y :=
  VecLatHom.ofIsVecLatHom f vlh
@[simp]
theorem mk'_apply {f : X → Y} (vlh : IsVecLatHom f) (x : X) :
    mk' f vlh x = f x := rfl
end IsVecLatHom
structure VecLatEquiv (X : Type*) (Y : Type*) [AddCommGroup X] [AddCommGroup Y]
    [Lattice X] [Lattice Y] [IsOrderedAddMonoid X] [IsOrderedAddMonoid Y]
    [VectorLattice X] [VectorLattice Y] extends X ≃ₗ[ℝ] Y, LatticeHom X Y
namespace VecLatEquiv
instance instFunLike : FunLike (VecLatEquiv X Y) X Y where
  coe e := e.toFun
  coe_injective := by
    intro f g h
    cases f; cases g
    congr 1
    exact LinearEquiv.ext (congrFun h)
def toVecLatHom (e : VecLatEquiv X Y) : VecLatHom X Y :=
  { e.toLinearMap with
    map_sup' := e.map_sup'
    map_inf' := e.map_inf' }
def refl : VecLatEquiv X X :=
  { LinearEquiv.refl ℝ X with
    map_sup' := fun _ _ => rfl
    map_inf' := fun _ _ => rfl }
def symm (e : VecLatEquiv X Y) : VecLatEquiv Y X :=
  { e.toLinearEquiv.symm with
    map_sup' := fun a b => by
      have h := e.map_sup' (e.toLinearEquiv.symm a) (e.toLinearEquiv.symm b)
      simp only [AddHom.toFun_eq_coe, LinearMap.coe_toAddHom, LinearEquiv.coe_coe,
        LinearEquiv.apply_symm_apply] at h
      change e.toLinearEquiv.symm (a ⊔ b) = e.toLinearEquiv.symm a ⊔ e.toLinearEquiv.symm b
      exact e.toLinearEquiv.injective (by rw [LinearEquiv.apply_symm_apply]; exact h.symm)
    map_inf' := fun a b => by
      have h := e.map_inf' (e.toLinearEquiv.symm a) (e.toLinearEquiv.symm b)
      simp only [AddHom.toFun_eq_coe, LinearMap.coe_toAddHom, LinearEquiv.coe_coe,
        LinearEquiv.apply_symm_apply] at h
      change e.toLinearEquiv.symm (a ⊓ b) = e.toLinearEquiv.symm a ⊓ e.toLinearEquiv.symm b
      exact e.toLinearEquiv.injective (by rw [LinearEquiv.apply_symm_apply]; exact h.symm) }
def trans {Z : Type*} [AddCommGroup Z] [Lattice Z] [IsOrderedAddMonoid Z] [VectorLattice Z]
    (e₁ : VecLatEquiv X Y) (e₂ : VecLatEquiv Y Z) : VecLatEquiv X Z :=
  { e₁.toLinearEquiv.trans e₂.toLinearEquiv with
    map_sup' := fun a b => by
      change e₂.toFun (e₁.toFun (a ⊔ b)) = e₂.toFun (e₁.toFun a) ⊔ e₂.toFun (e₁.toFun b)
      rw [e₁.map_sup', e₂.map_sup']
    map_inf' := fun a b => by
      change e₂.toFun (e₁.toFun (a ⊓ b)) = e₂.toFun (e₁.toFun a) ⊓ e₂.toFun (e₁.toFun b)
      rw [e₁.map_inf', e₂.map_inf'] }
end VecLatEquiv
namespace Positive
variable {X Y : Type*} [AddCommGroup X] [AddCommGroup Y] [Lattice X] [Lattice Y]
  [IsOrderedAddMonoid X] [IsOrderedAddMonoid Y] [VectorLattice X] [VectorLattice Y]
  [IsVLArchimedean Y] {τ : X → Y}
  (hτ_nn : ∀ x, 0 ≤ x → 0 ≤ τ x)
  (hτ_add : ∀ x y, 0 ≤ x → 0 ≤ y → τ (x + y) = τ x + τ y)
noncomputable def extensionEquiv
    (hτ_inj : ∀ x y, 0 ≤ x → 0 ≤ y → τ x = τ y → x = y)
    (hτ_surj : ∀ y, 0 ≤ y → ∃ x, 0 ≤ x ∧ τ x = y) :
    VecLatEquiv X Y := by
  set T := extension hτ_nn hτ_add
  have hT_inj : Function.Injective T := by
    intro a b hab
    have h : T (a - b) = 0 := by
      rw [map_sub]; exact sub_eq_zero.mpr hab
    rw [extension_apply] at h
    have heq : (a - b)⁺ = (a - b)⁻ :=
      hτ_inj _ _ (posPart_nonneg _) (negPart_nonneg _) (sub_eq_zero.mp h)
    have hsub := posPart_sub_negPart (a - b)
    rw [heq, sub_self] at hsub
    exact sub_eq_zero.mp hsub.symm
  have hT_surj : Function.Surjective T := by
    intro y
    obtain ⟨a, ha, haτ⟩ := hτ_surj y⁺ (posPart_nonneg y)
    obtain ⟨b, hb, hbτ⟩ := hτ_surj y⁻ (negPart_nonneg y)
    exact ⟨a - b, by
      rw [map_sub, extension_nonneg hτ_nn hτ_add ha,
        extension_nonneg hτ_nn hτ_add hb, haτ, hbτ,
        posPart_sub_negPart]⟩
  -- T is order-reflecting: 0 ≤ Tx → 0 ≤ x
  have hT_bipos : ∀ x, 0 ≤ T x → 0 ≤ x := by
    intro x hTx
    rw [extension_apply] at hTx
    have hτle : τ x⁻ ≤ τ x⁺ := sub_nonneg.mp hTx
    obtain ⟨c, hc, hcτ⟩ := hτ_surj _ hTx
    have hsum : τ (x⁻ + c) = τ x⁺ := by
      rw [hτ_add _ _ (negPart_nonneg _) hc, hcτ, add_sub_cancel]
    have heq : x⁻ + c = x⁺ :=
      hτ_inj _ _ (add_nonneg (negPart_nonneg _) hc) (posPart_nonneg _) hsum
    have hle : x⁻ ≤ x⁺ := heq ▸ le_add_of_nonneg_right hc
    have : x⁻ = 0 := (inf_eq_left.mpr hle).symm.trans
      ((inf_comm x⁻ x⁺).trans (posPart_inf_negPart_eq_zero x))
    rw [← posPart_sub_negPart x, this, sub_zero]
    exact posPart_nonneg _
  -- T⁻¹ is monotone (from bipositivity + positivity)
  have hT_inv_mono : ∀ a b, T a ≤ T b → a ≤ b := by
    intro a b hab
    have : 0 ≤ T (b - a) := by rw [map_sub]; exact sub_nonneg.mpr hab
    exact sub_nonneg.mp (hT_bipos _ this)
  have hT_mono : Monotone T := monotone_iff.mpr (extension_positive hτ_nn hτ_add)
  -- T preserves ⊔
  have hT_sup : ∀ a b, T (a ⊔ b) = T a ⊔ T b := by
    intro a b
    apply le_antisymm
    · obtain ⟨c, hc⟩ := hT_surj (T a ⊔ T b)
      have hca : a ≤ c := hT_inv_mono _ _ (hc ▸ le_sup_left)
      have hcb : b ≤ c := hT_inv_mono _ _ (hc ▸ le_sup_right)
      rw [← hc]; exact hT_mono (sup_le hca hcb)
    · exact sup_le (hT_mono le_sup_left) (hT_mono le_sup_right)
  -- T preserves ⊓
  have hT_inf : ∀ a b, T (a ⊓ b) = T a ⊓ T b := by
    intro a b
    apply le_antisymm
    · exact le_inf (hT_mono inf_le_left) (hT_mono inf_le_right)
    · obtain ⟨c, hc⟩ := hT_surj (T a ⊓ T b)
      have hca : c ≤ a := hT_inv_mono _ _ (hc ▸ inf_le_left)
      have hcb : c ≤ b := hT_inv_mono _ _ (hc ▸ inf_le_right)
      rw [← hc]; exact hT_mono (le_inf hca hcb)
  exact
    { (LinearEquiv.ofBijective T ⟨hT_inj, hT_surj⟩) with
      map_sup' := hT_sup
      map_inf' := hT_inf }
end Positive
namespace VecLatEquiv
variable {X Y : Type*} [NormedAddCommGroup X] [NormedAddCommGroup Y]
  [Lattice X] [Lattice Y] [IsOrderedAddMonoid X] [IsOrderedAddMonoid Y]
  [BanachLattice X] [BanachLattice Y]
noncomputable def toContinuousLinearEquiv (e : VecLatEquiv X Y) : X ≃L[ℝ] Y :=
  ContinuousLinearEquiv.mk e.toLinearEquiv
    (Positive.continuous (Positive.monotone_iff.mp e.toVecLatHom.monotone))
    (Positive.continuous (Positive.monotone_iff.mp e.symm.toVecLatHom.monotone))
end VecLatEquiv
structure BanachLatEquiv (X Y : Type*)
    [NormedAddCommGroup X] [NormedAddCommGroup Y]
    [Lattice X] [Lattice Y]
    [IsOrderedAddMonoid X] [IsOrderedAddMonoid Y]
    [BanachLattice X] [BanachLattice Y]
    extends X ≃ₗᵢ[ℝ] Y, LatticeHom X Y
namespace BanachLatEquiv
variable {X Y : Type*}
  [NormedAddCommGroup X] [NormedAddCommGroup Y]
  [Lattice X] [Lattice Y]
  [IsOrderedAddMonoid X] [IsOrderedAddMonoid Y]
  [BanachLattice X] [BanachLattice Y]
instance instFunLike : FunLike (BanachLatEquiv X Y) X Y where
  coe e := e.toFun
  coe_injective := by
    intro f g h
    cases f; cases g
    congr 1
    exact LinearIsometryEquiv.toLinearEquiv_injective
      (LinearEquiv.toEquiv_injective (Equiv.coe_inj.mp h))
noncomputable def toContinuousLinearEquiv (e : BanachLatEquiv X Y) : X ≃L[ℝ] Y :=
  e.toLinearIsometryEquiv.toContinuousLinearEquiv
def toVecLatEquiv (e : BanachLatEquiv X Y) : VecLatEquiv X Y :=
  { e.toLinearIsometryEquiv.toLinearEquiv with
    map_sup' := e.map_sup'
    map_inf' := e.map_inf' }
def symm (e : BanachLatEquiv X Y) : BanachLatEquiv Y X where
  toLinearIsometryEquiv := e.toLinearIsometryEquiv.symm
  map_sup' := e.toVecLatEquiv.symm.map_sup'
  map_inf' := e.toVecLatEquiv.symm.map_inf'
def refl (X : Type*) [NormedAddCommGroup X] [Lattice X] [IsOrderedAddMonoid X]
    [BanachLattice X] : BanachLatEquiv X X where
  toLinearIsometryEquiv := LinearIsometryEquiv.refl ℝ X
  map_sup' := fun _ _ => rfl
  map_inf' := fun _ _ => rfl
def trans {Z : Type*} [NormedAddCommGroup Z] [Lattice Z] [IsOrderedAddMonoid Z]
    [BanachLattice Z] (e₁ : BanachLatEquiv X Y) (e₂ : BanachLatEquiv Y Z) :
    BanachLatEquiv X Z where
  toLinearIsometryEquiv := e₁.toLinearIsometryEquiv.trans e₂.toLinearIsometryEquiv
  map_sup' := (e₁.toVecLatEquiv.trans e₂.toVecLatEquiv).map_sup'
  map_inf' := (e₁.toVecLatEquiv.trans e₂.toVecLatEquiv).map_inf'
end BanachLatEquiv
section Completion
open UniformSpace
variable {X : Type*} [NormedAddCommGroup X] [Lattice X] [IsOrderedAddMonoid X]
  [NormedVectorLattice X]
noncomputable def toCompletionVecLatHom : VecLatHom X (Completion X) where
  toFun := ((↑) : X → Completion X)
  map_add' := Completion.coe_add
  map_smul' := Completion.coe_smul
  map_sup' := coe_sup_completion
  map_inf' := coe_inf_completion
noncomputable def banachLatEquivCompletionOfDenseIsometry
    {Y : Type*} [NormedAddCommGroup Y] [Lattice Y] [IsOrderedAddMonoid Y] [BanachLattice Y]
    (T : VecLatHom X Y) (hT_norm : ∀ x, ‖T x‖ = ‖x‖) (hT_dense : DenseRange ⇑T) :
    BanachLatEquiv (Completion X) Y := by
  let Tli : X →ₗᵢ[ℝ] Y := { toLinearMap := T.toLinearMap, norm_map' := hT_norm }
  have huc : UniformContinuous ⇑Tli := Tli.isometry.uniformContinuous
  let Tc : Completion X →ₗᵢ[ℝ] Y :=
    { toFun := Completion.extension Tli
      map_add' := fun z w => by
        refine Completion.induction_on₂ z w (isClosed_eq ?_ ?_) (fun x y => ?_)
        · exact Completion.continuous_extension.comp continuous_add
        · exact (Completion.continuous_extension.comp continuous_fst).add
            (Completion.continuous_extension.comp continuous_snd)
        · rw [← Completion.coe_add, Completion.extension_coe huc, Completion.extension_coe huc,
            Completion.extension_coe huc, map_add]
      map_smul' := fun r z => by
        refine Completion.induction_on z (isClosed_eq ?_ ?_) (fun x => ?_)
        · exact Completion.continuous_extension.comp (continuous_const_smul r)
        · exact (continuous_const_smul r).comp Completion.continuous_extension
        · rw [← Completion.coe_smul, Completion.extension_coe huc, Completion.extension_coe huc,
            map_smul, RingHom.id_apply]
      norm_map' := fun z => by
        refine Completion.induction_on z (isClosed_eq ?_ ?_) (fun x => ?_)
        · exact continuous_norm.comp Completion.continuous_extension
        · exact continuous_norm
        · change ‖Completion.extension (⇑Tli) (x : Completion X)‖ = ‖(x : Completion X)‖
          rw [Completion.extension_coe huc, Tli.norm_map, Completion.norm_coe] }
  have hTc_coe : ∀ a : X, Tc (a : Completion X) = T a := fun a =>
    Completion.extension_coe huc a
  have hdense : DenseRange ⇑Tc := by
    refine hT_dense.mono ?_
    rintro _ ⟨x, rfl⟩
    exact ⟨(x : Completion X), hTc_coe x⟩
  have hsurj : Function.Surjective ⇑Tc := by
    have hclosed : IsClosed (Set.range ⇑Tc) := Tc.isometry.isClosedEmbedding.isClosed_range
    rw [← Set.range_eq_univ, ← hclosed.closure_eq, hdense.closure_range]
  refine
    { toLinearIsometryEquiv := LinearIsometryEquiv.ofSurjective Tc hsurj
      map_sup' := fun z w => ?_
      map_inf' := fun z w => ?_ }
  · change Tc (z ⊔ w) = Tc z ⊔ Tc w
    refine Completion.induction_on₂ z w (isClosed_eq ?_ ?_) (fun x y => ?_)
    · exact Tc.continuous.comp ContinuousSup.continuous_sup
    · exact ContinuousSup.continuous_sup.comp
        ((Tc.continuous.comp continuous_fst).prodMk (Tc.continuous.comp continuous_snd))
    · rw [← coe_sup_completion, hTc_coe, hTc_coe, hTc_coe]
      exact T.map_sup' x y
  · change Tc (z ⊓ w) = Tc z ⊓ Tc w
    refine Completion.induction_on₂ z w (isClosed_eq ?_ ?_) (fun x y => ?_)
    · exact Tc.continuous.comp ContinuousInf.continuous_inf
    · exact ContinuousInf.continuous_inf.comp
        ((Tc.continuous.comp continuous_fst).prodMk (Tc.continuous.comp continuous_snd))
    · rw [← coe_inf_completion, hTc_coe, hTc_coe, hTc_coe]
      exact T.map_inf' x y
end Completion



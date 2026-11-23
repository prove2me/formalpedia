-- Prove2me | Definitions.Def_GroundTheory_AutomorphicForms_RestrictedProductMatrix
-- name    : GroundTheory_AutomorphicForms_RestrictedProductMatrix
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T08:21:18.995537+00:00
-- url     : https://prove2.me/theorems/c109be6b-325c-4d3c-bd38-0d30ea032c78
-- title:
--   Restricted Product Matrix
-- statement:
--   Definitions and structural lemmas for Restricted Product Matrix, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/RestrictedProductMatrix.lean

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_Restricted
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_finiteEmbedding
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_finiteProj
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_finiteProj_diagonal
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_infiniteEmbedding
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_infiniteProj
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_infiniteProj_diagonal
import Theorems.Thm_GroundTheory_Global_IdeleGroup_finiteAdeleSingle_apply_self
import Theorems.Thm_GroundTheory_Global_IdeleGroup_finiteProj_finiteEmbedding
import Theorems.Thm_GroundTheory_Global_IdeleGroup_finiteUnitsEquiv_apply
import Theorems.Thm_GroundTheory_Global_IdeleGroup_infiniteProj_infiniteEmbedding
import Theorems.Thm_GroundTheory_Global_IdeleGroup_prodRestrictedEquiv_apply_fst
import Theorems.Thm_GroundTheory_Global_IdeleGroup_prodRestrictedEquiv_apply_snd
import Theorems.Thm_GroundTheory_Global_RestrictedProduct_continuousUnitsEquiv_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Global.IdeleGroup.coe_finiteEmbedding
attribute [local simp] GroundTheory.Global.IdeleGroup.coe_finiteProj
attribute [local simp] GroundTheory.Global.IdeleGroup.coe_finiteProj_diagonal
attribute [local simp] GroundTheory.Global.IdeleGroup.coe_infiniteEmbedding
attribute [local simp] GroundTheory.Global.IdeleGroup.coe_infiniteProj
attribute [local simp] GroundTheory.Global.IdeleGroup.coe_infiniteProj_diagonal
attribute [local simp] GroundTheory.Global.IdeleGroup.finiteAdeleSingle_apply_self
attribute [local simp] GroundTheory.Global.IdeleGroup.finiteProj_finiteEmbedding
attribute [local simp] GroundTheory.Global.IdeleGroup.finiteUnitsEquiv_apply
attribute [local simp] GroundTheory.Global.IdeleGroup.infiniteProj_infiniteEmbedding
attribute [local simp] GroundTheory.Global.IdeleGroup.prodRestrictedEquiv_apply_fst
attribute [local simp] GroundTheory.Global.IdeleGroup.prodRestrictedEquiv_apply_snd
attribute [local simp] GroundTheory.Global.RestrictedProduct.continuousUnitsEquiv_apply


set_option autoImplicit false
namespace GroundTheory.Automorphic
open Filter Topology Set
open scoped RestrictedProduct
noncomputable section
section Units
variable {A B : Type*} [Monoid A] [Monoid B] [TopologicalSpace A] [TopologicalSpace B]
def unitsCongr (e : A ≃* B) (he : Continuous e) (he' : Continuous e.symm) : Aˣ ≃ₜ* Bˣ where
  toMulEquiv := Units.mapEquiv e
  continuous_toFun :=
    Units.continuous_iff.2 ⟨he.comp Units.continuous_val, he.comp Units.continuous_coe_inv⟩
  continuous_invFun :=
    Units.continuous_iff.2 ⟨he'.comp Units.continuous_val, he'.comp Units.continuous_coe_inv⟩
@[simp]
theorem coe_unitsCongr_apply (e : A ≃* B) (he : Continuous e) (he' : Continuous e.symm) (u : Aˣ) :
    ((unitsCongr e he he' u : Bˣ) : B) = e u :=
  rfl
end Units
section Prod
variable (m : Type*) [Fintype m] (R₁ R₂ : Type*) [Ring R₁] [Ring R₂]
def matrixProdRingEquiv : Matrix m m (R₁ × R₂) ≃+* Matrix m m R₁ × Matrix m m R₂ where
  toFun M := (M.map Prod.fst, M.map Prod.snd)
  invFun p := Matrix.of fun a b => (p.1 a b, p.2 a b)
  left_inv M := rfl
  right_inv p := rfl
  map_mul' M N := by
    ext a b
    · change ((M * N) a b).1 = (M.map Prod.fst * N.map Prod.fst) a b
      simp [Matrix.mul_apply, Prod.fst_sum]
    · change ((M * N) a b).2 = (M.map Prod.snd * N.map Prod.snd) a b
      simp [Matrix.mul_apply, Prod.snd_sum]
  map_add' M N := rfl
@[simp]
theorem matrixProdRingEquiv_apply_fst (M : Matrix m m (R₁ × R₂)) (a b : m) :
    (matrixProdRingEquiv m R₁ R₂ M).1 a b = (M a b).1 :=
  rfl
@[simp]
theorem matrixProdRingEquiv_apply_snd (M : Matrix m m (R₁ × R₂)) (a b : m) :
    (matrixProdRingEquiv m R₁ R₂ M).2 a b = (M a b).2 :=
  rfl
variable [TopologicalSpace R₁] [TopologicalSpace R₂]
theorem continuous_matrixProdRingEquiv : Continuous (matrixProdRingEquiv m R₁ R₂) :=
  (continuous_pi fun a => continuous_pi fun b =>
      continuous_fst.comp ((continuous_apply b).comp (continuous_apply a))).prodMk
    (continuous_pi fun a => continuous_pi fun b =>
      continuous_snd.comp ((continuous_apply b).comp (continuous_apply a)))
theorem continuous_matrixProdRingEquiv_symm : Continuous (matrixProdRingEquiv m R₁ R₂).symm :=
  continuous_pi fun a => continuous_pi fun b =>
    ((continuous_apply_apply a b).comp continuous_fst).prodMk
      ((continuous_apply_apply a b).comp continuous_snd)
variable [DecidableEq m]
def glProdEquiv : GL m (R₁ × R₂) ≃ₜ* GL m R₁ × GL m R₂ :=
  (unitsCongr (matrixProdRingEquiv m R₁ R₂).toMulEquiv (continuous_matrixProdRingEquiv m R₁ R₂)
    (continuous_matrixProdRingEquiv_symm m R₁ R₂)).trans
    { toMulEquiv := MulEquiv.prodUnits
      continuous_toFun := (Homeomorph.prodUnits (α := Matrix m m R₁)
        (β := Matrix m m R₂)).continuous_toFun
      continuous_invFun := (Homeomorph.prodUnits (α := Matrix m m R₁)
        (β := Matrix m m R₂)).continuous_invFun }
@[simp]
theorem glProdEquiv_apply_fst (g : GL m (R₁ × R₂)) (a b : m) :
    (glProdEquiv m R₁ R₂ g).1 a b = (g a b).1 :=
  rfl
@[simp]
theorem glProdEquiv_apply_snd (g : GL m (R₁ × R₂)) (a b : m) :
    (glProdEquiv m R₁ R₂ g).2 a b = (g a b).2 :=
  rfl
end Prod
section Pi
variable (m : Type*) [Fintype m] {ι : Type*} (R : ι → Type*) [∀ j, Ring (R j)]
def matrixPiRingEquiv : Matrix m m (Π j, R j) ≃+* Π j, Matrix m m (R j) where
  toFun M j := Matrix.of fun a b => M a b j
  invFun p := Matrix.of fun a b j => p j a b
  left_inv M := rfl
  right_inv p := rfl
  map_mul' M N := by
    ext j a b
    simp [Matrix.mul_apply, Finset.sum_apply]
  map_add' M N := rfl
@[simp]
theorem matrixPiRingEquiv_apply (M : Matrix m m (Π j, R j)) (j : ι) (a b : m) :
    matrixPiRingEquiv m R M j a b = M a b j :=
  rfl
variable [∀ j, TopologicalSpace (R j)]
theorem continuous_matrixPiRingEquiv : Continuous (matrixPiRingEquiv m R) :=
  continuous_pi fun j => continuous_pi fun a => continuous_pi fun b =>
    (continuous_apply j).comp ((continuous_apply b).comp (continuous_apply a))
theorem continuous_matrixPiRingEquiv_symm : Continuous (matrixPiRingEquiv m R).symm :=
  continuous_pi fun a => continuous_pi fun b => continuous_pi fun j =>
    (continuous_apply b).comp ((continuous_apply a).comp (continuous_apply j))
variable [DecidableEq m]
def glPiEquiv : GL m (Π j, R j) ≃ₜ* Π j, GL m (R j) :=
  (unitsCongr (matrixPiRingEquiv m R).toMulEquiv (continuous_matrixPiRingEquiv m R)
    (continuous_matrixPiRingEquiv_symm m R)).trans ContinuousMulEquiv.piUnits
@[simp]
theorem glPiEquiv_apply (g : GL m (Π j, R j)) (j : ι) (a b : m) :
    glPiEquiv m R g j a b = g a b j :=
  rfl
end Pi
namespace RestrictedProduct
variable {ι : Type*} {R : ι → Type*} [∀ i, TopologicalSpace (R i)]
def congrSets {A A' : (i : ι) → Set (R i)} (h : ∀ i, A i = A' i) :
    Πʳ i, [R i, A i] ≃ₜ Πʳ i, [R i, A' i] where
  toFun x := _root_.RestrictedProduct.mk x.1 (x.2.mono fun i hi =>
    (congrArg (x.1 i ∈ ·) (h i)).mp hi)
  invFun x := _root_.RestrictedProduct.mk x.1 (x.2.mono fun i hi =>
    (congrArg (x.1 i ∈ ·) (h i)).mpr hi)
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun :=
    _root_.RestrictedProduct.mapAlong_continuous R R id tendsto_id (A₁ := A) (A₂ := A')
      (fun _ x => x) (.of_forall fun i x hx => (congrArg (x ∈ ·) (h i)).mp hx)
      fun _ => continuous_id
  continuous_invFun :=
    _root_.RestrictedProduct.mapAlong_continuous R R id tendsto_id (A₁ := A') (A₂ := A)
      (fun _ x => x) (.of_forall fun i x hx => (congrArg (x ∈ ·) (h i)).mpr hx)
      fun _ => continuous_id
@[simp]
theorem congrSets_apply {A A' : (i : ι) → Set (R i)} (h : ∀ i, A i = A' i)
    (x : Πʳ i, [R i, A i]) (i : ι) : congrSets h x i = x i :=
  rfl
def congrSetsMul [∀ i, Monoid (R i)] {S S' : ι → Type*} [∀ i, SetLike (S i) (R i)]
    [∀ i, SubmonoidClass (S i) (R i)] [∀ i, SetLike (S' i) (R i)]
    [∀ i, SubmonoidClass (S' i) (R i)] {B : Π i, S i} {B' : Π i, S' i}
    (h : ∀ i, (B i : Set (R i)) = B' i) :
    Πʳ i, [R i, B i] ≃ₜ* Πʳ i, [R i, B' i] where
  toEquiv := (congrSets h).toEquiv
  map_mul' _ _ := rfl
  continuous_toFun := (congrSets h).continuous
  continuous_invFun := (congrSets h).symm.continuous
@[simp]
theorem congrSetsMul_apply [∀ i, Monoid (R i)] {S S' : ι → Type*} [∀ i, SetLike (S i) (R i)]
    [∀ i, SubmonoidClass (S i) (R i)] [∀ i, SetLike (S' i) (R i)]
    [∀ i, SubmonoidClass (S' i) (R i)] {B : Π i, S i} {B' : Π i, S' i}
    (h : ∀ i, (B i : Set (R i)) = B' i) (x : Πʳ i, [R i, B i]) (i : ι) :
    congrSetsMul h x i = x i :=
  rfl
section Pi
variable (m : Type*) [Finite m] {A : (i : ι) → Set (R i)}
def piEquiv (hA : ∀ i, IsOpen (A i)) :
    (m → Πʳ i, [R i, A i]) ≃ₜ Πʳ i, [m → R i, Set.pi univ fun _ => A i] where
  toFun x := _root_.RestrictedProduct.mk (A := fun i => Set.pi univ fun _ => A i)
    (fun i a => x a i)
    (((eventually_all (ι := m)).2 fun a => (x a).2).mono fun _ hi a _ => hi a)
  invFun y a := _root_.RestrictedProduct.mk (A := A) (fun i => y i a)
    (y.2.mono fun _ hi => hi a (mem_univ a))
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := by
    refine (_root_.RestrictedProduct.continuous_dom_pi (A := fun _ i => R i)
      (C := fun _ i => A i) fun _ => hA).2 fun S hS => ?_
    exact (_root_.RestrictedProduct.continuous_inclusion hS).comp
      (f := fun x : (m → Πʳ i, [R i, A i]_[𝓟 S]) =>
        _root_.RestrictedProduct.mk (A := fun i => Set.pi univ fun _ => A i) (𝓕 := 𝓟 S)
          (fun i a => x a i) (eventually_principal.2 fun i hi a _ =>
            eventually_principal.1 (x a).2 i hi))
      (_root_.RestrictedProduct.continuous_rng_of_principal.2
        (continuous_pi fun i => continuous_pi fun a =>
          (_root_.RestrictedProduct.continuous_eval i).comp (continuous_apply a)))
  continuous_invFun := continuous_pi fun a =>
    _root_.RestrictedProduct.mapAlong_continuous (fun i => m → R i) R id tendsto_id
      (A₁ := fun i => Set.pi univ fun _ => A i) (A₂ := A)
      (fun _ y => y a) (.of_forall fun _ _ hy => hy a (mem_univ a)) fun _ => continuous_apply a
@[simp]
theorem piEquiv_apply (hA : ∀ i, IsOpen (A i)) (x : m → Πʳ i, [R i, A i]) (i : ι) (a : m) :
    piEquiv m hA x i a = x a i :=
  rfl
end Pi
section Matrix
variable (m : Type*) [Fintype m] [DecidableEq m]
def matrixHomeomorphSets {A : (i : ι) → Set (R i)} (hA : ∀ i, IsOpen (A i)) :
    Matrix m m (Πʳ i, [R i, A i]) ≃ₜ Πʳ i, [Matrix m m (R i), {M | ∀ a b, M a b ∈ A i}] :=
  ((Homeomorph.piCongrRight fun _ : m => piEquiv m hA).trans
    (piEquiv m fun i => isOpen_set_pi finite_univ fun _ _ => hA i)).trans
    (congrSets fun _ => Set.ext fun _ =>
      ⟨fun h a b => h a (mem_univ a) b (mem_univ b), fun h a _ b _ => h a b⟩)
variable [∀ i, Ring (R i)] {S : ι → Type*} [∀ i, SetLike (S i) (R i)]
  [∀ i, SubringClass (S i) (R i)] {B : Π i, S i} {C : Π i, Subring (Matrix m m (R i))}
def matrixRingEquiv (hC : ∀ i (M : Matrix m m (R i)), M ∈ C i ↔ ∀ a b, M a b ∈ B i) :
    Matrix m m (Πʳ i, [R i, B i]) ≃+* Πʳ i, [Matrix m m (R i), C i] where
  toFun M := _root_.RestrictedProduct.mk (A := fun i => (C i : Set (Matrix m m (R i))))
    (fun i => Matrix.of fun a b => M a b i)
    (((eventually_all (ι := m)).2 fun a => (eventually_all (ι := m)).2 fun b =>
      (M a b).2).mono fun i hi => (hC i _).2 fun a b => hi a b)
  invFun x := Matrix.of fun a b =>
    _root_.RestrictedProduct.mk (A := fun i => (B i : Set (R i))) (fun i => x i a b)
      (x.2.mono fun i hi => (hC i _).1 hi a b)
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' M N := by
    ext i a b
    change (M * N) a b i = ((Matrix.of fun a b => M a b i) * Matrix.of fun a b => N a b i) a b
    simp only [Matrix.mul_apply, Matrix.of_apply]
    exact map_sum (_root_.RestrictedProduct.evalRingHom R i) _ _
  map_add' _ _ := rfl
omit [∀ i, TopologicalSpace (R i)] in
@[simp]
theorem matrixRingEquiv_apply (hC : ∀ i (M : Matrix m m (R i)), M ∈ C i ↔ ∀ a b, M a b ∈ B i)
    (M : Matrix m m (Πʳ i, [R i, B i])) (i : ι) (a b : m) :
    matrixRingEquiv m hC M i a b = M a b i :=
  rfl
omit [∀ i, TopologicalSpace (R i)] [∀ i, SubringClass (S i) (R i)] in
theorem coe_eq_setOf (hC : ∀ i (M : Matrix m m (R i)), M ∈ C i ↔ ∀ a b, M a b ∈ B i) (i : ι) :
    (C i : Set (Matrix m m (R i))) = {M | ∀ a b, M a b ∈ B i} :=
  Set.ext fun M => hC i M
def matrixHomeomorph (hC : ∀ i (M : Matrix m m (R i)), M ∈ C i ↔ ∀ a b, M a b ∈ B i)
    (hB : ∀ i, IsOpen (B i : Set (R i))) :
    Matrix m m (Πʳ i, [R i, B i]) ≃ₜ Πʳ i, [Matrix m m (R i), C i] :=
  (matrixHomeomorphSets m hB).trans (congrSets fun i => (coe_eq_setOf m hC i).symm)
omit [∀ i, SubringClass (S i) (R i)] in

theorem isOpen_coe_of_forall (hC : ∀ i (M : Matrix m m (R i)), M ∈ C i ↔ ∀ a b, M a b ∈ B i)
    (hB : ∀ i, IsOpen (B i : Set (R i))) (i : ι) : IsOpen (C i : Set (Matrix m m (R i))) := by
  rw [coe_eq_setOf m hC i]
  simp only [Set.ofPred_forall]
  exact isOpen_iInter_of_finite fun a => isOpen_iInter_of_finite fun b =>
    (hB i).preimage ((continuous_apply b).comp (continuous_apply a))
def matrixUnitsEquiv (hC : ∀ i (M : Matrix m m (R i)), M ∈ C i ↔ ∀ a b, M a b ∈ B i)
    (hB : ∀ i, IsOpen (B i : Set (R i))) :
    GL m (Πʳ i, [R i, B i]) ≃ₜ* Πʳ i, [GL m (R i), (Submonoid.ofClass (C i)).units] :=
  (unitsCongr (matrixRingEquiv m hC).toMulEquiv (matrixHomeomorph m hC hB).continuous
    (matrixHomeomorph m hC hB).symm.continuous).trans
    (GroundTheory.Global.RestrictedProduct.continuousUnitsEquiv (isOpen_coe_of_forall m hC hB))
end Matrix
end RestrictedProduct
end
end GroundTheory.Automorphic



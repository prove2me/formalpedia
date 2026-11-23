-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_IsLocallyConstantRankAtStalkEigenSub
-- name    : Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_IsLocallyConstantRankAtStalkEigenSub
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T03:49:25.061144+00:00
-- url     : https://prove2.me/theorems/ffdc88d5-c18a-4853-8c0c-414aa45cf236
-- title:
--   Is Locally Constant Rank At Stalk Eigen Sub
-- statement:
--   Definitions and structural lemmas for Is Locally Constant Rank At Stalk Eigen Sub, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HermitianTraceForms/IsLocallyConstantRankAtStalkEigenSub.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct NumberField
open Polynomial
namespace GlobalTheory
namespace EigenSplit
section Algebra
variable {O : Type*} [CommRing O] {R : Type*} [CommRing R] {ι : Type*}
noncomputable def splitMap (σ : ι → O →+* R) : R ⊗[ℤ] O →ₐ[R] (ι → R) :=
  Algebra.TensorProduct.lift (Algebra.ofId R (ι → R)) (RingHom.pi σ).toIntAlgHom
    (fun _ _ => Commute.all _ _)
@[simp] theorem splitMap_tmul (σ : ι → O →+* R) (r : R) (a : O) (i : ι) :
    splitMap σ (r ⊗ₜ a) i = r * σ i a := by
  simp [splitMap, Algebra.ofId_apply]
def IsSplitting (σ : ι → O →+* R) : Prop := Function.Bijective (splitMap σ)
noncomputable def splitEquiv {σ : ι → O →+* R} (h : IsSplitting σ) : R ⊗[ℤ] O ≃ₐ[R] (ι → R) :=
  AlgEquiv.ofBijective (splitMap σ) h
@[simp] theorem splitEquiv_apply {σ : ι → O →+* R} (h : IsSplitting σ) (t : R ⊗[ℤ] O) :
    splitEquiv h t = splitMap σ t := rfl
noncomputable def splitEquivComm {σ : ι → O →+* R} (h : IsSplitting σ) :
    O ⊗[ℤ] R ≃+* (ι → R) :=
  (Algebra.TensorProduct.comm ℤ O R).toRingEquiv.trans (splitEquiv h).toRingEquiv
@[simp] theorem splitEquivComm_tmul {σ : ι → O →+* R} (h : IsSplitting σ) (a : O) (r : R)
    (i : ι) : splitEquivComm h (a ⊗ₜ r) i = σ i a * r := by
  simp [splitEquivComm, mul_comm]
variable [DecidableEq ι]
noncomputable def idem {σ : ι → O →+* R} (h : IsSplitting σ) (i : ι) : R ⊗[ℤ] O :=
  (splitEquiv h).symm (Pi.single i 1)
@[simp] theorem splitMap_idem {σ : ι → O →+* R} (h : IsSplitting σ) (i : ι) :
    splitMap σ (idem h i) = Pi.single i 1 :=
  (splitEquiv h).apply_symm_apply _
theorem mul_idem {σ : ι → O →+* R} (h : IsSplitting σ) (i : ι) (t : R ⊗[ℤ] O) :
    t * idem h i = splitMap σ t i • idem h i := by
  apply h.1
  ext j
  rcases eq_or_ne j i with rfl | hj
  · simp
  · simp [hj]
theorem one_tmul_mul_idem {σ : ι → O →+* R} (h : IsSplitting σ) (i : ι) (a : O) :
    (1 ⊗ₜ a) * idem h i = σ i a • idem h i := by
  rw [mul_idem]; simp
theorem completeOrthogonalIdempotents_idem [Fintype ι] {σ : ι → O →+* R} (h : IsSplitting σ) :
    CompleteOrthogonalIdempotents (idem h) :=
  (CompleteOrthogonalIdempotents.single (fun _ : ι => R)).map
    (f := ((splitEquiv h).symm : (ι → R) →+* R ⊗[ℤ] O))
theorem isSplitting_of_idem [Fintype ι] {σ : ι → O →+* R} (e : ι → R ⊗[ℤ] O)
    (h1 : ∀ i, splitMap σ (e i) = Pi.single i 1) (h2 : ∑ i, e i = 1)
    (h3 : ∀ i a, (1 ⊗ₜ a) * e i = σ i a • e i) : IsSplitting σ := by
  have h4 : ∀ i t, t * e i = splitMap σ t i • e i := by
    intro i t
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul r a =>
      have : (r ⊗ₜ[ℤ] a : R ⊗[ℤ] O) = r • (1 ⊗ₜ[ℤ] a) := by
        simp [TensorProduct.smul_tmul']
      rw [splitMap_tmul, this, smul_mul_assoc, h3, smul_smul]
    | add x y hx hy => simp [add_mul, hx, hy, add_smul]
  refine ⟨(injective_iff_map_eq_zero _).2 fun t ht => ?_, fun v => ⟨∑ i, v i • e i, ?_⟩⟩
  · rw [← mul_one t, ← h2, Finset.mul_sum]
    simp [h4, ht]
  · ext j
    simp [h1, Pi.single_apply]
omit [DecidableEq ι] in

theorem IsSplitting.map [Finite ι] {σ : ι → O →+* R} (h : IsSplitting σ) {R' : Type*}
    [CommRing R'] (f : R →+* R') : IsSplitting (fun i => f.comp (σ i)) := by
  classical
  have := Fintype.ofFinite ι
  let F : R ⊗[ℤ] O →ₐ[ℤ] R' ⊗[ℤ] O := Algebra.TensorProduct.map f.toIntAlgHom (AlgHom.id ℤ O)
  have hF : ∀ t i, splitMap (fun i => f.comp (σ i)) (F t) i = f (splitMap σ t i) := by
    intro t i
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul r a => simp [F]
    | add x y hx hy => simp [hx, hy]
  have hF' : ∀ (r : R) t, F (r • t) = f r • F t := by
    intro r t
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul s a => simp [F, TensorProduct.smul_tmul']
    | add x y hx hy => simp [hx, hy]
  refine isSplitting_of_idem (fun i => F (idem h i)) (fun i => ?_) ?_ (fun i a => ?_)
  · ext j
    rw [hF, splitMap_idem]
    rcases eq_or_ne j i with rfl | hj
    · simp
    · simp [hj]
  · rw [← map_sum, (completeOrthogonalIdempotents_idem h).complete, map_one]
  · have : ((1 : R') ⊗ₜ[ℤ] a) = F (1 ⊗ₜ a) := by simp [F]
    rw [this, ← map_mul, one_tmul_mul_idem, hF']
    rfl
omit [DecidableEq ι] in

theorem IsSplitting.injective [Nontrivial R] {σ : ι → O →+* R} (h : IsSplitting σ) :
    Function.Injective σ := by
  classical
  intro i j hij
  by_contra hne
  have : ∀ t, splitMap σ t i = splitMap σ t j := by
    intro t
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul r a => simp [hij]
    | add x y hx hy => simp [hx, hy]
  have h2 := this (idem h i)
  simp [Ne.symm hne] at h2
end Algebra
section Module
variable {O : Type*} [CommRing O] {R : Type*} [CommRing R] {ι : Type*}
  {N : Type*} [AddCommGroup N] [Module R N] {N' : Type*} [AddCommGroup N'] [Module R N']
  {N'' : Type*} [AddCommGroup N''] [Module R N'']
def eigenSub (ρ : O →+* Module.End R N) (χ : O →+* R) : Submodule R N :=
  ⨅ a, (ρ a).eigenspace (χ a)
theorem mem_eigenSub {ρ : O →+* Module.End R N} {χ : O →+* R} {x : N} :
    x ∈ eigenSub ρ χ ↔ ∀ a, ρ a x = χ a • x := by
  simp [eigenSub]
noncomputable def tensorAction (ρ : O →+* Module.End R N) : R ⊗[ℤ] O →ₐ[R] Module.End R N :=
  Algebra.TensorProduct.lift (Algebra.ofId R _) ρ.toIntAlgHom
    (fun r a => show Commute (Algebra.ofId R (Module.End R N) r) (ρ.toIntAlgHom a) from
      Algebra.commute_algebraMap_left r _)
@[simp] theorem tensorAction_tmul (ρ : O →+* Module.End R N) (r : R) (a : O) (x : N) :
    tensorAction ρ (r ⊗ₜ a) x = r • ρ a x := by
  rw [tensorAction, Algebra.TensorProduct.lift_tmul]
  simp [Algebra.ofId_apply]
theorem tensorAction_of_mem {ρ : O →+* Module.End R N} {σ : ι → O →+* R} {i : ι} {x : N}
    (hx : x ∈ eigenSub ρ (σ i)) (t : R ⊗[ℤ] O) :
    tensorAction ρ t x = splitMap σ t i • x := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul r a => simp [mem_eigenSub.1 hx a, smul_smul]
  | add s t hs ht => simp [hs, ht, add_smul]
def IsEquivariant (ρ : O →+* Module.End R N) (ρ' : O →+* Module.End R N') (f : N →ₗ[R] N') :
    Prop :=
  ∀ a x, f (ρ a x) = ρ' a (f x)
theorem IsEquivariant.comp {ρ : O →+* Module.End R N} {ρ' : O →+* Module.End R N'}
    {ρ'' : O →+* Module.End R N''} {g : N' →ₗ[R] N''} {f : N →ₗ[R] N'}
    (hg : IsEquivariant ρ' ρ'' g) (hf : IsEquivariant ρ ρ' f) : IsEquivariant ρ ρ'' (g ∘ₗ f) :=
  fun a x => by simp [hf a, hg a]
theorem IsEquivariant.tensorAction {ρ : O →+* Module.End R N} {ρ' : O →+* Module.End R N'}
    {f : N →ₗ[R] N'} (hf : IsEquivariant ρ ρ' f) (t : R ⊗[ℤ] O) (x : N) :
    f (tensorAction ρ t x) = tensorAction ρ' t (f x) := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul r a => simp [hf a]
  | add s t hs ht => simp [hs, ht]
theorem IsEquivariant.map_mem {ρ : O →+* Module.End R N} {ρ' : O →+* Module.End R N'}
    {f : N →ₗ[R] N'} (hf : IsEquivariant ρ ρ' f) {χ : O →+* R} {x : N}
    (hx : x ∈ eigenSub ρ χ) : f x ∈ eigenSub ρ' χ :=
  mem_eigenSub.2 fun a => by rw [← hf a, mem_eigenSub.1 hx a, map_smul]
def IsEquivariant.eigenMap {ρ : O →+* Module.End R N} {ρ' : O →+* Module.End R N'}
    {f : N →ₗ[R] N'} (hf : IsEquivariant ρ ρ' f) (χ : O →+* R) :
    eigenSub ρ χ →ₗ[R] eigenSub ρ' χ :=
  f.restrict fun _ hx => hf.map_mem hx
@[simp] theorem IsEquivariant.coe_eigenMap {ρ : O →+* Module.End R N}
    {ρ' : O →+* Module.End R N'} {f : N →ₗ[R] N'} (hf : IsEquivariant ρ ρ' f) (χ : O →+* R)
    (x : eigenSub ρ χ) : (hf.eigenMap χ x : N') = f x := rfl
section Split
variable [DecidableEq ι] {σ : ι → O →+* R} (h : IsSplitting σ) (ρ : O →+* Module.End R N)
noncomputable def proj (i : ι) : Module.End R N := tensorAction ρ (idem h i)
theorem proj_mem (i : ι) (x : N) : proj h ρ i x ∈ eigenSub ρ (σ i) := by
  refine mem_eigenSub.2 fun a => ?_
  have : ρ a (proj h ρ i x) = tensorAction ρ ((1 ⊗ₜ a) * idem h i) x := by
    simp [proj]
  rw [this, one_tmul_mul_idem]
  simp [proj]
variable {ρ} in
theorem proj_of_mem {i : ι} {x : N} (hx : x ∈ eigenSub ρ (σ i)) : proj h ρ i x = x := by
  simp [proj, tensorAction_of_mem hx]
variable {ρ} in
theorem proj_of_mem_ne {i j : ι} (hij : j ≠ i) {x : N} (hx : x ∈ eigenSub ρ (σ j)) :
    proj h ρ i x = 0 := by
  simp [proj, tensorAction_of_mem hx, hij]
theorem completeOrthogonalIdempotents_proj [Fintype ι] :
    CompleteOrthogonalIdempotents (proj h ρ) :=
  (completeOrthogonalIdempotents_idem h).map
    (f := (tensorAction ρ : R ⊗[ℤ] O →+* Module.End R N))
theorem sum_proj [Fintype ι] (x : N) : ∑ i, proj h ρ i x = x := by
  have := congrArg (fun p : Module.End R N => p x)
    (completeOrthogonalIdempotents_proj h ρ).complete
  simpa using this
variable {ρ} in
theorem IsEquivariant.proj {ρ' : O →+* Module.End R N'} {f : N →ₗ[R] N'}
    (hf : IsEquivariant ρ ρ' f) (i : ι) (x : N) : f (proj h ρ i x) = proj h ρ' i (f x) :=
  hf.tensorAction _ _
noncomputable def projTo (i : ι) : N →ₗ[R] eigenSub ρ (σ i) :=
  (proj h ρ i).codRestrict _ (proj_mem h ρ i)
@[simp] theorem coe_projTo (i : ι) (x : N) : (projTo h ρ i x : N) = proj h ρ i x := rfl
theorem projTo_comp_subtype (i : ι) :
    projTo h ρ i ∘ₗ (eigenSub ρ (σ i)).subtype = LinearMap.id := by
  ext x
  simp [proj_of_mem h x.2]
noncomputable def eigenEquiv [Fintype ι] : N ≃ₗ[R] (∀ i, eigenSub ρ (σ i)) :=
  LinearEquiv.ofLinearMap (LinearMap.pi (projTo h ρ))
    (∑ i, (eigenSub ρ (σ i)).subtype ∘ₗ LinearMap.proj i)
    (by
      refine LinearMap.ext fun v => funext fun i => Subtype.ext ?_
      simp only [LinearMap.comp_apply, LinearMap.pi_apply, coe_projTo, LinearMap.sum_apply,
        map_sum, LinearMap.id_apply, Submodule.coe_sum]
      rw [Finset.sum_eq_single i]
      · exact proj_of_mem h (v i).2
      · intro j _ hj; exact proj_of_mem_ne h hj (v j).2
      · simp)
    (by
      ext x
      simpa using sum_proj h ρ x)
@[simp] theorem coe_eigenEquiv_apply [Fintype ι] (x : N) (i : ι) :
    (eigenEquiv h ρ x i : N) = proj h ρ i x := rfl
end Split
section Exact
variable {σ : ι → O →+* R} (h : IsSplitting σ) {ρ : O →+* Module.End R N}
  {ρ' : O →+* Module.End R N'} {ρ'' : O →+* Module.End R N''}
include h
variable (ρ)
end Exact
end Module
section BaseChange
variable {O : Type*} [CommRing O] {R : Type*} [CommRing R] {ι : Type*}
  {N : Type*} [AddCommGroup N] [Module R N] {R' : Type*} [CommRing R'] [Algebra R R']
  {M : Type*} [AddCommGroup M] [Module R M] [Module R' M] [IsScalarTower R R' M]
  {ρ : O →+* Module.End R N} {ρ' : O →+* Module.End R' M} {f : N →ₗ[R] M}
theorem map_mem_eigenSub_algebraMap (hf : ∀ a x, f (ρ a x) = ρ' a (f x)) {χ : O →+* R} {x : N}
    (hx : x ∈ eigenSub ρ χ) : f x ∈ eigenSub ρ' ((algebraMap R R').comp χ) :=
  mem_eigenSub.2 fun a => by
    rw [← hf a, mem_eigenSub.1 hx a, map_smul]
    simp
def eigenMapAlgebra (hf : ∀ a x, f (ρ a x) = ρ' a (f x)) (χ : O →+* R) :
    eigenSub ρ χ →ₗ[R] eigenSub ρ' ((algebraMap R R').comp χ) where
  toFun x := ⟨f x, map_mem_eigenSub_algebraMap hf x.2⟩
  map_add' x y := Subtype.ext (by simp)
  map_smul' r x := Subtype.ext (by simp)
@[simp] theorem coe_eigenMapAlgebra (hf : ∀ a x, f (ρ a x) = ρ' a (f x)) (χ : O →+* R)
    (x : eigenSub ρ χ) : (eigenMapAlgebra hf χ x : M) = f x := rfl
variable {σ : ι → O →+* R}
theorem map_proj_algebraMap [Finite ι] [DecidableEq ι] (h : IsSplitting σ)
    (hf : ∀ a x, f (ρ a x) = ρ' a (f x)) (i : ι) (x : N) :
    f (proj h ρ i x) = proj (h.map (algebraMap R R')) ρ' i (f x) := by
  have := Fintype.ofFinite ι
  conv_rhs => rw [← sum_proj h ρ x, map_sum, map_sum]
  rw [Finset.sum_eq_single i]
  · exact (proj_of_mem (h.map (algebraMap R R'))
      (map_mem_eigenSub_algebraMap hf (proj_mem h ρ i x))).symm
  · intro j _ hj
    exact proj_of_mem_ne (h.map (algebraMap R R')) hj
      (map_mem_eigenSub_algebraMap hf (proj_mem h ρ j x))
  · simp
theorem isBaseChange_eigenMapAlgebra [Finite ι] (h : IsSplitting σ)
    (hf : ∀ a x, f (ρ a x) = ρ' a (f x)) (hb : IsBaseChange R' f) (i : ι) :
    IsBaseChange R' (eigenMapAlgebra hf (σ i)) := by
  classical
  let h' := h.map (algebraMap R R')
  let F : R' ⊗[R] eigenSub ρ (σ i) →ₗ[R'] eigenSub ρ' ((algebraMap R R').comp (σ i)) :=
    (eigenMapAlgebra hf (σ i)).liftBaseChange R'
  have h1 : ∀ t, (F t : M) = hb.equiv ((eigenSub ρ (σ i)).subtype.baseChange R' t) := by
    intro t
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul r x => simp [F, IsBaseChange.equiv_tmul]
    | add s t hs ht => simp [hs, ht]
  have h2 : ∀ t, (F ((projTo h ρ i).baseChange R' t) : M) = proj h' ρ' i (hb.equiv t) := by
    intro t
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul r x => simp [F, IsBaseChange.equiv_tmul, map_proj_algebraMap h hf]
    | add s t hs ht => simp [hs, ht]
  have h3 : ∀ t, (projTo h ρ i).baseChange R' ((eigenSub ρ (σ i)).subtype.baseChange R' t) = t := by
    intro t
    rw [← LinearMap.comp_apply, ← LinearMap.baseChange_comp, projTo_comp_subtype]
    simp
  have hF : Function.Bijective F := by
    constructor
    · intro s t hst
      have := congrArg Subtype.val hst
      rw [h1, h1] at this
      rw [← h3 s, ← h3 t, hb.equiv.injective this]
    · intro y
      refine ⟨(projTo h ρ i).baseChange R' (hb.equiv.symm y), Subtype.ext ?_⟩
      rw [h2, LinearEquiv.apply_symm_apply]
      exact proj_of_mem h' y.2
  exact IsBaseChange.of_equiv (LinearEquiv.ofBijective F hF) fun x => by simp [F]
variable (R') (ρ)
noncomputable def baseChangeAction : O →+* Module.End R' (R' ⊗[R] N) :=
  (Module.End.baseChangeHom R R' N).toRingHom.comp ρ
@[simp] theorem baseChangeAction_apply (a : O) :
    baseChangeAction R' ρ a = (ρ a).baseChange R' := rfl
theorem mk_equivariant (a : O) (x : N) :
    TensorProduct.mk R R' N 1 (ρ a x) = baseChangeAction R' ρ a (TensorProduct.mk R R' N 1 x) := by
  simp
noncomputable def eigenBaseChangeEquiv [Finite ι] (h : IsSplitting σ) (i : ι) :
    R' ⊗[R] eigenSub ρ (σ i) ≃ₗ[R']
      eigenSub (baseChangeAction R' ρ) ((algebraMap R R').comp (σ i)) :=
  (isBaseChange_eigenMapAlgebra h (mk_equivariant R' ρ) (TensorProduct.isBaseChange R N R') i).equiv
end BaseChange
section Charpoly
variable {O : Type*} [CommRing O] {R : Type*} [CommRing R] {ι : Type*} [Fintype ι]
  {N : Type*} [AddCommGroup N] [Module R N]
variable {σ : ι → O →+* R} (h : IsSplitting σ) (ρ : O →+* Module.End R N)
  [Module.Free R N] [Module.Finite R N]
include h
end Charpoly
section Stalk
variable {O : Type*} [CommRing O] {R : Type*} [CommRing R] {ι : Type*} [Fintype ι]
  {N : Type*} [AddCommGroup N] [Module R N]
  {σ : ι → O →+* R} (h : IsSplitting σ) (ρ : O →+* Module.End R N)
include h
end Stalk
section Discr
variable {E : Type*} [Field E] [NumberField E] {R : Type*} [CommRing R] {ι : Type*} [Fintype ι]
  [DecidableEq ι]
noncomputable def conjugateHom (L : Type*) [Field L] (R : Type*) [CommRing R] [Algebra (𝓞 L) R]
    (φ : E →+* L) : 𝓞 E →+* R :=
  (algebraMap (𝓞 L) R).comp (NumberField.RingOfIntegers.mapRingHom φ)
end Discr
end EigenSplit
end GlobalTheory



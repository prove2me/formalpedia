-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_RelativeJacquetPiExteriorTensorEquivNormalized
-- name    : Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_RelativeJacquetPiExteriorTensorEquivNormalized
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T17:26:27.760498+00:00
-- url     : https://prove2.me/theorems/caa99f32-0205-45a3-ae23-79533a3a8719
-- title:
--   Relative Jacquet Pi Exterior Tensor Equiv Normalized
-- statement:
--   Definitions and structural lemmas for Relative Jacquet Pi Exterior Tensor Equiv Normalized, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/RelativeJacquetPiExteriorTensorEquivNormalized.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsSubquotientOfEquiv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.JacStages
noncomputable section
namespace GlobalTheory.JacPiTensor
section Gen
variable {ι : Type} [Fintype ι] [dec0 : DecidableEq ι] {M : ι → Type} [∀ i, AddCommGroup (M i)] [∀ i, Module ℂ (M i)]
  {N : Type} [AddCommGroup N] [Module ℂ N] (p : ∀ i, Submodule ℂ (M i))
def qlift (i : ι) (q : M i ⧸ p i) : M i := (Submodule.Quotient.mk_surjective (p i) q).choose
theorem mk_qlift (i : ι) (q : M i ⧸ p i) : Submodule.Quotient.mk (qlift p i q) = q :=
  (Submodule.Quotient.mk_surjective (p i) q).choose_spec
variable {p}
theorem position_eq (f : MultilinearMap ℂ M N) (hf : ∀ v i, ∀ w ∈ p i, f (Function.update v i w) = 0)
    (v : ∀ i, M i) (i : ι) {u u' : M i} (h : u - u' ∈ p i) :
    f (Function.update v i u) = f (Function.update v i u') := by
  rw [← sub_eq_zero, ← f.map_update_sub]
  exact hf v i _ h
def descend (f : MultilinearMap ℂ M N) (hf : ∀ v i, ∀ w ∈ p i, f (Function.update v i w) = 0) :
    MultilinearMap ℂ (fun i => M i ⧸ p i) N where
  toFun q := f fun i => qlift p i (q i)
  map_update_add' {dec} q i a b := by
    obtain rfl : dec = dec0 := Subsingleton.elim _ _
    have e : ∀ c : M i ⧸ p i, (fun j => qlift p j (Function.update q i c j)) =
        Function.update (fun j => qlift p j (q j)) i (qlift p i c) := fun c =>
      funext fun j => Function.apply_update (fun j => qlift p j) q i c j
    simp only [e]
    rw [position_eq f hf _ i (u' := qlift p i a + qlift p i b), f.map_update_add]
    rw [← Submodule.Quotient.eq, Submodule.Quotient.mk_add, mk_qlift, mk_qlift, mk_qlift]
  map_update_smul' {dec} q i c a := by
    obtain rfl : dec = dec0 := Subsingleton.elim _ _
    have e : ∀ c : M i ⧸ p i, (fun j => qlift p j (Function.update q i c j)) =
        Function.update (fun j => qlift p j (q j)) i (qlift p i c) := fun c =>
      funext fun j => Function.apply_update (fun j => qlift p j) q i c j
    simp only [e]
    rw [position_eq f hf _ i (u' := c • qlift p i a), f.map_update_smul]
    rw [← Submodule.Quotient.eq, Submodule.Quotient.mk_smul, mk_qlift, mk_qlift]
theorem descend_mk (f : MultilinearMap ℂ M N) (hf : ∀ v i, ∀ w ∈ p i, f (Function.update v i w) = 0)
    (x : ∀ i, M i) : descend f hf (fun i => Submodule.Quotient.mk (x i)) = f x := by
  show f (fun i => qlift p i (Submodule.Quotient.mk (x i))) = f x
  have key : ∀ s : Finset ι,
      f (fun i => if i ∈ s then qlift p i (Submodule.Quotient.mk (x i)) else x i) = f x := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | insert a s ha ih =>
      rw [← ih]
      set F : ∀ i, M i := fun i => if i ∈ s then qlift p i (Submodule.Quotient.mk (x i)) else x i
      have h1 : (fun i => if i ∈ insert a s then qlift p i (Submodule.Quotient.mk (x i)) else x i) =
          Function.update F a (qlift p a (Submodule.Quotient.mk (x a))) := by
        funext i
        by_cases hi : i = a
        · subst hi; simp
        · simp [Function.update_of_ne hi, F, Finset.mem_insert, hi]
      have h2 : F = Function.update F a (x a) := by
        funext i
        by_cases hi : i = a
        · subst hi; simp [F, ha]
        · simp [Function.update_of_ne hi]
      rw [h1]
      conv_rhs => rw [h2]
      refine position_eq f hf F a ?_
      rw [← Submodule.Quotient.eq, mk_qlift]
  simpa using key Finset.univ
end Gen
end GlobalTheory.JacPiTensor
noncomputable section
namespace GlobalTheory.JacPiTensor
open scoped TensorProduct
section Spec
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {s : ℕ} {d : Fin s → ℕ} {t : Fin s → ℕ} {d' : ∀ a, Fin (t a) → ℕ}
  (e' : ∀ a, (Σ b, Fin (d' a b)) ≃ Fin (d a)) {X : Fin s → Type} [∀ a, AddCommGroup (X a)]
  [∀ a, Module ℂ (X a)] (ρ : ∀ a, Representation ℂ (GL (Fin (d a)) k) (X a))
theorem piTensor_mulSingle (a : Fin s) (g : GL (Fin (d a)) k) (x : ∀ j, X j) :
    piTensor ρ (Pi.mulSingle a g) (PiTensorProduct.tprod ℂ x) =
      PiTensorProduct.tprod ℂ (Function.update x a (ρ a g (x a))) := by
  rw [piTensor_tprod]
  congr 1
  funext j
  by_cases h : j = a
  · subst h; simp
  · simp [Pi.mulSingle_eq_of_ne h, Function.update_of_ne h]
def qf : MultilinearMap ℂ X (Jacquet (piTensor ρ) (relUnipD k e')) :=
  (twKer (piTensor ρ) (relUnipD k e') 1).mkQ.compMultilinearMap (PiTensorProduct.tprod ℂ)
theorem qf_update (v : ∀ a, X a) (i : Fin s) (w : X i)
    (hw : w ∈ twKer (ρ i) (unipRad k (e' i)) 1) : qf e' ρ (Function.update v i w) = 0 := by
  have hle : twKer (ρ i) (unipRad k (e' i)) 1 ≤
      (twKer (piTensor ρ) (relUnipD k e') 1).comap ((PiTensorProduct.tprod ℂ).toLinearMap v i) := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨n, y, rfl⟩
    have hmem : (Pi.mulSingle i (n : GL (Fin (d i)) k) : ∀ a, GL (Fin (d a)) k) ∈ relUnipD k e' := by
      refine (Subgroup.mem_pi _).2 fun j _ => ?_
      by_cases h : j = i
      · subst h; simpa using n.2
      · rw [Pi.mulSingle_eq_of_ne h]; exact one_mem _
    simp only [SetLike.mem_coe, Submodule.mem_comap, MultilinearMap.toLinearMap_apply,
      MonoidHom.one_apply, Units.val_one, one_smul, MultilinearMap.map_update_sub]
    refine Submodule.subset_span ⟨⟨_, hmem⟩, PiTensorProduct.tprod ℂ (Function.update v i y), ?_⟩
    simp only [MonoidHom.one_apply, Units.val_one, one_smul]
    rw [piTensor_mulSingle]
    simp
  have := hle hw
  simp only [Submodule.mem_comap, MultilinearMap.toLinearMap_apply] at this
  simp [qf, (Submodule.Quotient.mk_eq_zero _).2 this]
end Spec
end GlobalTheory.JacPiTensor
noncomputable section
namespace GlobalTheory.JacPiTensor
open scoped TensorProduct
section Spec2
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {s : ℕ} {d : Fin s → ℕ} {t : Fin s → ℕ} {d' : ∀ a, Fin (t a) → ℕ}
  (e' : ∀ a, (Σ b, Fin (d' a b)) ≃ Fin (d a)) {X : Fin s → Type} [∀ a, AddCommGroup (X a)]
  [∀ a, Module ℂ (X a)] (ρ : ∀ a, Representation ℂ (GL (Fin (d a)) k) (X a))
def qmap : (⨂[ℂ] a, X a) →ₗ[ℂ] ⨂[ℂ] a, Jacquet (ρ a) (unipRad k (e' a)) :=
  PiTensorProduct.map fun a => (twKer (ρ a) (unipRad k (e' a)) 1).mkQ
theorem qmap_tprod (x : ∀ a, X a) :
    qmap e' ρ (PiTensorProduct.tprod ℂ x) =
      PiTensorProduct.tprod ℂ fun a => (Submodule.Quotient.mk (x a) : Jacquet (ρ a) (unipRad k (e' a))) := by
  simp [qmap, PiTensorProduct.map_tprod]
theorem qmap_comp (u : ∀ a, GL (Fin (d a)) k) (hu : u ∈ relUnipD k e') :
    qmap e' ρ ∘ₗ piTensor ρ u = qmap e' ρ := by
  refine PiTensorProduct.ext (MultilinearMap.ext fun x => ?_)
  simp only [LinearMap.compMultilinearMap_apply, LinearMap.comp_apply, piTensor_tprod, qmap_tprod]
  congr 1
  funext a
  refine (Submodule.Quotient.eq _).2 (Submodule.subset_span ⟨⟨u a, (Subgroup.mem_pi _).1 hu a trivial⟩, x a, ?_⟩)
  simp
theorem twKer_le_ker : twKer (piTensor ρ) (relUnipD k e') 1 ≤ LinearMap.ker (qmap e' ρ) := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨u, z, rfl⟩
  simp only [SetLike.mem_coe, LinearMap.mem_ker, MonoidHom.one_apply, Units.val_one, one_smul, map_sub]
  rw [← LinearMap.comp_apply, qmap_comp e' ρ u u.2, sub_self]
def fwd : Jacquet (piTensor ρ) (relUnipD k e') →ₗ[ℂ] ⨂[ℂ] a, Jacquet (ρ a) (unipRad k (e' a)) :=
  (twKer (piTensor ρ) (relUnipD k e') 1).liftQ (qmap e' ρ) (twKer_le_ker e' ρ)
def bwd : (⨂[ℂ] a, Jacquet (ρ a) (unipRad k (e' a))) →ₗ[ℂ] Jacquet (piTensor ρ) (relUnipD k e') :=
  PiTensorProduct.lift (descend (qf e' ρ) (qf_update e' ρ))
theorem bwd_tprod (q : ∀ a, Jacquet (ρ a) (unipRad k (e' a))) :
    bwd e' ρ (PiTensorProduct.tprod ℂ q) = Submodule.Quotient.mk (PiTensorProduct.tprod ℂ
      fun i => qlift (fun a => twKer (ρ a) (unipRad k (e' a)) 1) i (q i)) := by
  rw [bwd, PiTensorProduct.lift.tprod]
  rfl
theorem bwd_tprod_mk (x : ∀ a, X a) :
    bwd e' ρ (PiTensorProduct.tprod ℂ fun a => (Submodule.Quotient.mk (x a) : Jacquet (ρ a) (unipRad k (e' a)))) =
      Submodule.Quotient.mk (PiTensorProduct.tprod ℂ x) := by
  rw [bwd, PiTensorProduct.lift.tprod, descend_mk]
  rfl
theorem fwd_mk_tprod' (x : ∀ a, X a) :
    fwd e' ρ (Submodule.Quotient.mk (PiTensorProduct.tprod ℂ x)) =
      PiTensorProduct.tprod ℂ fun a => (Submodule.Quotient.mk (x a) : Jacquet (ρ a) (unipRad k (e' a))) := by
  simp only [fwd, Submodule.liftQ_apply, qmap_tprod]
def jacEquiv : Jacquet (piTensor ρ) (relUnipD k e') ≃ₗ[ℂ] ⨂[ℂ] a, Jacquet (ρ a) (unipRad k (e' a)) :=
  LinearEquiv.ofLinear (fwd e' ρ) (bwd e' ρ)
    (by
      refine PiTensorProduct.ext (MultilinearMap.ext fun q => ?_)
      rw [LinearMap.compMultilinearMap_apply, LinearMap.comp_apply, bwd_tprod, fwd_mk_tprod']
      simp only [mk_qlift, LinearMap.compMultilinearMap_apply, LinearMap.id_apply])
    (by
      refine Submodule.linearMap_qext _ (PiTensorProduct.ext (MultilinearMap.ext fun x => ?_))
      rw [LinearMap.compMultilinearMap_apply, LinearMap.comp_apply, LinearMap.comp_apply, Submodule.mkQ_apply,
        fwd_mk_tprod', bwd_tprod_mk, LinearMap.compMultilinearMap_apply, LinearMap.comp_apply, LinearMap.id_apply,
        Submodule.mkQ_apply])
end Spec2
end GlobalTheory.JacPiTensor
namespace GlobalTheory.JacStages
end GlobalTheory.JacStages



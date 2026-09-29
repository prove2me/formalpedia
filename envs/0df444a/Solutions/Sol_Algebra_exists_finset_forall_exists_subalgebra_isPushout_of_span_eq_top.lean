-- Prove2me | solution 1 for Algebra.exists_finset_forall_exists_subalgebra_isPushout_of_span_eq_top
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/8a17fb98-3536-53fa-ab35-f98545483a49

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Algebra_exists_finset_forall_exists_subalgebra_isPushout_of_span_eq_top

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped TensorProduct

namespace P2mKcDescent

variable {S T : Type} [CommRing S] [CommRing T] [Algebra S T]
variable {ι : Type} (g : ι → T) (σ : T →ₗ[S] (ι → S)) (S₀ : Subalgebra ℤ S)

abbrev spanG : Submodule S₀ T := Submodule.span S₀ (Set.range g)

theorem g_mem_spanG (i : ι) : g i ∈ spanG g S₀ := Submodule.subset_span ⟨i, rfl⟩

theorem mem_spanG_of_coeff [Fintype ι] (hσ : ∀ t, ∑ i, σ t i • g i = t) (t : T)
    (ht : ∀ k, σ t k ∈ S₀) : t ∈ spanG g S₀ := by
  rw [← hσ t]
  refine Submodule.sum_mem _ fun k _ => ?_
  have : σ t k • g k = (⟨σ t k, ht k⟩ : S₀) • g k := rfl
  rw [this]
  exact Submodule.smul_mem _ _ (g_mem_spanG g S₀ k)

theorem coeff_mem_of_mem_spanG (hgc : ∀ i k, σ (g i) k ∈ S₀) {t : T} (ht : t ∈ spanG g S₀)
    (k : ι) : σ t k ∈ S₀ := by
  induction ht using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨i, rfl⟩ := hx
    exact hgc i k
  | zero => simp
  | add x y _ _ hx hy =>
    rw [map_add, Pi.add_apply]
    exact add_mem hx hy
  | smul a x _ hx =>
    have : (a • x : T) = (a : S) • x := rfl
    rw [this, map_smul, Pi.smul_apply, smul_eq_mul]
    exact mul_mem a.2 hx

theorem one_mem_spanG [Fintype ι] (hσ : ∀ t, ∑ i, σ t i • g i = t) (h1 : ∀ k, σ 1 k ∈ S₀) :
    (1 : T) ∈ spanG g S₀ :=
  mem_spanG_of_coeff g σ S₀ hσ 1 h1

theorem mul_mem_spanG [Fintype ι] (hσ : ∀ t, ∑ i, σ t i • g i = t)
    (hm : ∀ i j k, σ (g i * g j) k ∈ S₀)
    (x y : T) (hx : x ∈ spanG g S₀) (hy : y ∈ spanG g S₀) : x * y ∈ spanG g S₀ := by
  induction hx using Submodule.span_induction generalizing y with
  | mem x hx' =>
    obtain ⟨i, rfl⟩ := hx'
    induction hy using Submodule.span_induction with
    | mem y hy' =>
      obtain ⟨j, rfl⟩ := hy'
      exact mem_spanG_of_coeff g σ S₀ hσ _ (hm i j)
    | zero => simp
    | add y z _ _ hy hz =>
      rw [mul_add]
      exact add_mem hy hz
    | smul a y _ hy' =>
      rw [mul_smul_comm]
      exact Submodule.smul_mem _ _ hy'
  | zero => simp
  | add x x' _ _ hx hx' =>
    rw [add_mul]
    exact add_mem (hx y hy) (hx' y hy)
  | smul a x _ hx =>
    rw [smul_mul_assoc]
    exact Submodule.smul_mem _ _ (hx y hy)

def model [Fintype ι] (hσ : ∀ t, ∑ i, σ t i • g i = t) (h1 : ∀ k, σ 1 k ∈ S₀)
    (hm : ∀ i j k, σ (g i * g j) k ∈ S₀) : Subalgebra S₀ T :=
  (spanG g S₀).toSubalgebra (one_mem_spanG g σ S₀ hσ h1) (mul_mem_spanG g σ S₀ hσ hm)

theorem model_toSubmodule [Fintype ι] (hσ : ∀ t, ∑ i, σ t i • g i = t) (h1 : ∀ k, σ 1 k ∈ S₀)
    (hm : ∀ i j k, σ (g i * g j) k ∈ S₀) :
    Subalgebra.toSubmodule (model g σ S₀ hσ h1 hm) = spanG g S₀ :=
  Submodule.toSubalgebra_toSubmodule _ _ _

def g' (i : ι) : spanG g S₀ := ⟨g i, g_mem_spanG g S₀ i⟩

@[scoped simp] theorem coe_g' (i : ι) : ((g' g S₀ i : spanG g S₀) : T) = g i := rfl

noncomputable def pi0 [Fintype ι] : (ι → S₀) →ₗ[S₀] spanG g S₀ :=
  Fintype.linearCombination S₀ (g' g S₀)

theorem pi0_apply [Fintype ι] (v : ι → S₀) : pi0 g S₀ v = ∑ i, v i • g' g S₀ i :=
  Fintype.linearCombination_apply _ _ _

theorem coe_pi0 [Fintype ι] (v : ι → S₀) :
    ((pi0 g S₀ v : spanG g S₀) : T) = ∑ i, (v i : S) • g i := by
  rw [pi0_apply, Submodule.coe_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rfl

noncomputable def sigma0 (hgc : ∀ i k, σ (g i) k ∈ S₀) : spanG g S₀ →ₗ[S₀] (ι → S₀) where
  toFun x := fun k => ⟨σ x k, coeff_mem_of_mem_spanG g σ S₀ hgc x.2 k⟩
  map_add' x y := by
    funext k
    apply Subtype.ext
    change σ ((x : T) + y) k = σ x k + σ y k
    rw [map_add, Pi.add_apply]
  map_smul' a x := by
    funext k
    apply Subtype.ext
    change σ ((a : S) • (x : T)) k = (a : S) * σ x k
    rw [map_smul, Pi.smul_apply, smul_eq_mul]

@[scoped simp] theorem coe_sigma0_apply (hgc : ∀ i k, σ (g i) k ∈ S₀) (x : spanG g S₀) (k : ι) :
    ((sigma0 g σ S₀ hgc x k : S₀) : S) = σ x k := rfl

theorem pi0_sigma0 [Fintype ι] (hσ : ∀ t, ∑ i, σ t i • g i = t) (hgc : ∀ i k, σ (g i) k ∈ S₀)
    (x : spanG g S₀) : pi0 g S₀ (sigma0 g σ S₀ hgc x) = x := by
  apply Subtype.ext
  rw [coe_pi0]
  simp only [coe_sigma0_apply]
  exact hσ x

theorem pi0_comp_sigma0 [Fintype ι] (hσ : ∀ t, ∑ i, σ t i • g i = t)
    (hgc : ∀ i k, σ (g i) k ∈ S₀) :
    (pi0 g S₀).comp (sigma0 g σ S₀ hgc) = LinearMap.id :=
  LinearMap.ext fun x => pi0_sigma0 g σ S₀ hσ hgc x

theorem projective_spanG [Fintype ι] (hσ : ∀ t, ∑ i, σ t i • g i = t)
    (hgc : ∀ i k, σ (g i) k ∈ S₀) : Module.Projective S₀ (spanG g S₀) :=
  Module.Projective.of_split (sigma0 g σ S₀ hgc) (pi0 g S₀) (pi0_comp_sigma0 g σ S₀ hσ hgc)

theorem finite_spanG [Finite ι] : Module.Finite S₀ (spanG g S₀) :=
  Module.Finite.span_of_finite S₀ (Set.finite_range g)

theorem free_spanG (hli : LinearIndependent S g) : Module.Free S₀ (spanG g S₀) :=
  Module.Free.of_basis (Module.Basis.span (hli.restrict_scalars' S₀))

noncomputable def psi [Fintype ι] : T →ₗ[S] S ⊗[S₀] spanG g S₀ :=
  ∑ k : ι, (LinearMap.toSpanSingleton S (S ⊗[S₀] spanG g S₀) (1 ⊗ₜ g' g S₀ k)).comp
    ((LinearMap.proj k).comp σ)

theorem psi_apply [Fintype ι] (t : T) :
    psi g σ S₀ t = ∑ k : ι, σ t k ⊗ₜ[S₀] g' g S₀ k := by
  rw [psi, LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [LinearMap.comp_apply, LinearMap.comp_apply, LinearMap.toSpanSingleton_apply,
    LinearMap.proj_apply, TensorProduct.smul_tmul', smul_eq_mul, mul_one]

noncomputable def theta : S ⊗[S₀] spanG g S₀ →ₗ[S] T :=
  ((spanG g S₀).subtype).liftBaseChange S

@[scoped simp] theorem theta_tmul (s : S) (x : spanG g S₀) :
    theta g S₀ (s ⊗ₜ x) = s • (x : T) :=
  LinearMap.liftBaseChange_tmul _ _ _ _

theorem sum_tmul_eq_one_tmul [Fintype ι] (hσ : ∀ t, ∑ i, σ t i • g i = t)
    (hgc : ∀ i k, σ (g i) k ∈ S₀) (x : spanG g S₀) :
    ∑ k : ι, σ x k ⊗ₜ[S₀] g' g S₀ k = (1 : S) ⊗ₜ[S₀] x := by
  have hx : ∀ k, σ x k ⊗ₜ[S₀] g' g S₀ k =
      (1 : S) ⊗ₜ[S₀] ((sigma0 g σ S₀ hgc x k) • g' g S₀ k) := by
    intro k
    rw [TensorProduct.tmul_smul, TensorProduct.smul_tmul']
    congr 1
    change σ x k = ((sigma0 g σ S₀ hgc x k : S₀) : S) * 1
    rw [mul_one]
    rfl
  simp_rw [hx]
  rw [← TensorProduct.tmul_sum, ← pi0_apply, pi0_sigma0 g σ S₀ hσ hgc x]

theorem psi_comp_theta [Fintype ι] (hσ : ∀ t, ∑ i, σ t i • g i = t)
    (hgc : ∀ i k, σ (g i) k ∈ S₀) :
    (psi g σ S₀).comp (theta g S₀) = LinearMap.id := by
  refine TensorProduct.AlgebraTensorModule.ext fun s x => ?_
  rw [LinearMap.comp_apply, LinearMap.id_apply, theta_tmul, map_smul, psi_apply,
    sum_tmul_eq_one_tmul g σ S₀ hσ hgc, TensorProduct.smul_tmul', smul_eq_mul, mul_one]

theorem theta_injective [Fintype ι] (hσ : ∀ t, ∑ i, σ t i • g i = t)
    (hgc : ∀ i k, σ (g i) k ∈ S₀) : Function.Injective (theta g S₀) := by
  intro a b hab
  have h := LinearMap.congr_fun (psi_comp_theta g σ S₀ hσ hgc) a
  have h' := LinearMap.congr_fun (psi_comp_theta g σ S₀ hσ hgc) b
  rw [LinearMap.comp_apply, LinearMap.id_apply] at h h'
  rw [← h, ← h', hab]

theorem theta_surjective (hg : Submodule.span S (Set.range g) = ⊤) :
    Function.Surjective (theta g S₀) := by
  rw [← LinearMap.range_eq_top, eq_top_iff, ← hg, Submodule.span_le]
  rintro _ ⟨i, rfl⟩
  exact ⟨1 ⊗ₜ g' g S₀ i, by rw [theta_tmul, one_smul]; rfl⟩

noncomputable def thetaEquiv [Fintype ι] (hσ : ∀ t, ∑ i, σ t i • g i = t)
    (hgc : ∀ i k, σ (g i) k ∈ S₀) (hg : Submodule.span S (Set.range g) = ⊤) :
    S ⊗[S₀] spanG g S₀ ≃ₗ[S] T :=
  LinearEquiv.ofBijective (theta g S₀) ⟨theta_injective g σ S₀ hσ hgc, theta_surjective g S₀ hg⟩

theorem isBaseChange_subtype [Fintype ι] (hσ : ∀ t, ∑ i, σ t i • g i = t)
    (hgc : ∀ i k, σ (g i) k ∈ S₀) (hg : Submodule.span S (Set.range g) = ⊤) :
    IsBaseChange S ((spanG g S₀).subtype) :=
  IsBaseChange.of_equiv (thetaEquiv g σ S₀ hσ hgc hg) fun x => by
    change theta g S₀ ((1 : S) ⊗ₜ x) = x
    rw [theta_tmul, one_smul]

set_option synthInstance.maxHeartbeats 1600000 in
theorem isPushout_model [Fintype ι] (hσ : ∀ t, ∑ i, σ t i • g i = t) (h1 : ∀ k, σ 1 k ∈ S₀)
    (hm : ∀ i j k, σ (g i * g j) k ∈ S₀) (hgc : ∀ i k, σ (g i) k ∈ S₀)
    (hg : Submodule.span S (Set.range g) = ⊤) :
    Algebra.IsPushout S₀ S (model g σ S₀ hσ h1 hm) T := by
  rw [Algebra.isPushout_iff]
  have : (IsScalarTower.toAlgHom S₀ (model g σ S₀ hσ h1 hm) T).toLinearMap =
      (spanG g S₀).subtype := by
    refine LinearMap.ext fun x => ?_
    rfl
  rw [this]
  exact isBaseChange_subtype g σ S₀ hσ hgc hg

theorem finite_model [Fintype ι] (hσ : ∀ t, ∑ i, σ t i • g i = t) (h1 : ∀ k, σ 1 k ∈ S₀)
    (hm : ∀ i j k, σ (g i * g j) k ∈ S₀) : Module.Finite S₀ (model g σ S₀ hσ h1 hm) :=
  finite_spanG g S₀

theorem projective_model [Fintype ι] (hσ : ∀ t, ∑ i, σ t i • g i = t) (h1 : ∀ k, σ 1 k ∈ S₀)
    (hm : ∀ i j k, σ (g i * g j) k ∈ S₀) (hgc : ∀ i k, σ (g i) k ∈ S₀) :
    Module.Projective S₀ (model g σ S₀ hσ h1 hm) :=
  projective_spanG g σ S₀ hσ hgc

theorem free_model [Fintype ι] (hσ : ∀ t, ∑ i, σ t i • g i = t) (h1 : ∀ k, σ 1 k ∈ S₀)
    (hm : ∀ i j k, σ (g i * g j) k ∈ S₀) (hli : LinearIndependent S g) :
    Module.Free S₀ (model g σ S₀ hσ h1 hm) :=
  free_spanG g S₀ hli

theorem main [Module.Projective S T] [Finite ι]
    (hg : Submodule.span S (Set.range g) = ⊤) :
    ∃ c : Finset S, ∀ S₀ : Subalgebra ℤ S, ↑c ⊆ (S₀ : Set S) →
      ∃ T₀ : Subalgebra S₀ T, Subalgebra.toSubmodule T₀ = Submodule.span S₀ (Set.range g) ∧
        Module.Finite S₀ T₀ ∧ Module.Projective S₀ T₀ ∧
        (LinearIndependent S g → Module.Free S₀ T₀) ∧ Algebra.IsPushout S₀ S T₀ T := by
  classical
  cases nonempty_fintype ι
  have hsurj : Function.Surjective (Fintype.linearCombination S g) := by
    rw [← LinearMap.range_eq_top, Fintype.range_linearCombination, hg]
  obtain ⟨σ, hσ'⟩ :=
    Module.projective_lifting_property (Fintype.linearCombination S g) LinearMap.id hsurj
  have hσ : ∀ t, ∑ i, σ t i • g i = t := fun t => by
    have := LinearMap.congr_fun hσ' t
    rwa [LinearMap.comp_apply, Fintype.linearCombination_apply, LinearMap.id_apply] at this

  let c : Finset S := ((Finset.univ.image fun k : ι => σ 1 k) ∪
    (Finset.univ.image fun p : (ι × ι) × ι => σ (g p.1.1 * g p.1.2) p.2)) ∪
    (Finset.univ.image fun p : ι × ι => σ (g p.1) p.2)
  refine ⟨c, fun S₀ hc => ?_⟩
  have h1 : ∀ k, σ 1 k ∈ S₀ := fun k => hc (by
    simp only [c, Finset.coe_union, Finset.coe_image, Finset.coe_univ, Set.image_univ,
      Set.mem_union, Set.mem_range]
    exact Or.inl (Or.inl ⟨k, rfl⟩))
  have hm : ∀ i j k, σ (g i * g j) k ∈ S₀ := fun i j k => hc (by
    simp only [c, Finset.coe_union, Finset.coe_image, Finset.coe_univ, Set.image_univ,
      Set.mem_union, Set.mem_range]
    exact Or.inl (Or.inr ⟨((i, j), k), rfl⟩))
  have hgc : ∀ i k, σ (g i) k ∈ S₀ := fun i k => hc (by
    simp only [c, Finset.coe_union, Finset.coe_image, Finset.coe_univ, Set.image_univ,
      Set.mem_union, Set.mem_range]
    exact Or.inr ⟨(i, k), rfl⟩)
  exact ⟨model g σ S₀ hσ h1 hm, model_toSubmodule g σ S₀ hσ h1 hm, finite_model g σ S₀ hσ h1 hm,
    projective_model g σ S₀ hσ h1 hm hgc, fun hli => free_model g σ S₀ hσ h1 hm hli,
    isPushout_model g σ S₀ hσ h1 hm hgc hg⟩

end P2mKcDescent
p2m_reactivate "P2MW.S_Algebra_exists_finset_forall_exists_subalgebra_isPushout_of_span_eq_top.P2mKcDescent"

theorem solution
    {S T : Type} [CommRing S] [CommRing T] [Algebra S T] [Module.Projective S T]
    {ι : Type} [Finite ι] (g : ι → T) (hg : Submodule.span S (Set.range g) = ⊤) :
    ∃ c : Finset S, ∀ S₀ : Subalgebra ℤ S, ↑c ⊆ (S₀ : Set S) →
      ∃ T₀ : Subalgebra S₀ T, Subalgebra.toSubmodule T₀ = Submodule.span S₀ (Set.range g) ∧
        Module.Finite S₀ T₀ ∧ Module.Projective S₀ T₀ ∧
        (LinearIndependent S g → Module.Free S₀ T₀) ∧ Algebra.IsPushout S₀ S T₀ T :=
  P2mKcDescent.main g hg

end S_Algebra_exists_finset_forall_exists_subalgebra_isPushout_of_span_eq_top
end P2MW
export P2MW.S_Algebra_exists_finset_forall_exists_subalgebra_isPushout_of_span_eq_top (solution)

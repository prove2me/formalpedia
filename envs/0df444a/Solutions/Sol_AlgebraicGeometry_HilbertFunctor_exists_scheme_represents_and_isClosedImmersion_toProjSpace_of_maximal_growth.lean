-- Prove2me | solution 1 for AlgebraicGeometry.HilbertFunctor.exists_scheme_represents_and_isClosedImmersion_toProjSpace_of_maximal_growth
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.935278+00:00
-- url     : https://prove2.me/submissions/aac84bb2-9c8a-5367-93e2-c58e087be916

import Mathlib
import Definitions.Def_AlgebraicGeometry_ProjSpace
import Definitions.Def_AlgebraicGeometry_HilbertFunctor
import Theorems.Thm_Module_Grassmannian_exists_scheme_represents_and_isClosedImmersion_toProjSpace
import Theorems.Thm_AlgebraicGeometry_HilbertFunctor_exists_point_I_eq_map
import Theorems.Thm_AlgebraicGeometry_HilbertFunctor_exists_ideal_forall_projective_piece_succ_iff
import Theorems.Thm_AlgebraicGeometry_HilbertFunctor_Point_I_eq_span_of_forall_finrank_piece_succ_le
import Theorems.Thm_AlgebraicGeometry_HilbertFunctor_exists_point_I_eq_of_projective_piece_succ
import Theorems.Thm_AlgebraicGeometry_Scheme_exists_isClosedImmersion_represents_of_forall_exists_ideal
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_HilbertFunctor_exists_scheme_represents_and_isClosedImmersion_toProjSpace_of_maximal_growth
p2m_attr_erase "simp" "CategoryTheory.Functor.OverTotal.ofFibre_fst CategoryTheory.Functor.overTotal_map_fst"

set_option autoImplicit false

open MvPolynomial CategoryTheory AlgebraicGeometry AlgebraicGeometry.HilbertFunctor
open scoped TensorProduct

attribute [local instance] MvPolynomial.gradedAlgebra

namespace HilbRepGotz

variable {R₀ : Type} [CommRing R₀] {n : ℕ} {m : ℕ}

variable (R₀ n m) in

abbrev Sm : Type := ↥(homogeneousSubmodule (Fin (n + 1)) R₀ m)

theorem finite_homogeneousSubmodule (R : Type) [CommRing R] (d : ℕ) :
    Module.Finite R ↥(homogeneousSubmodule (Fin (n + 1)) R d) := by
  rw [MvPolynomial.homogeneousSubmodule_eq_finsupp_supported]
  haveI : Finite {x : Fin (n + 1) →₀ ℕ | x.degree = d} :=
    ((Finsupp.finite_of_degree_le d).subset fun x (hx : x.degree = d) => le_of_eq hx).to_subtype
  exact Module.Finite.of_basis (MvPolynomial.basisRestrictSupport R {x : Fin (n + 1) →₀ ℕ | x.degree = d})

scoped instance instFiniteSm : Module.Finite R₀ (Sm R₀ n m) := finite_homogeneousSubmodule R₀ m

private theorem _root_.HilbRepGotz.finite_piece (R : Type) [CommRing R] (J : Ideal (MvPolynomial (Fin (n + 1)) R)) (d : ℕ) :
    Module.Finite R (piece J d) := by
  haveI := finite_homogeneousSubmodule (n := n) R d
  exact Module.Finite.quotient R _

p2m_export "HilbRepGotz" "finite_piece"
theorem degree_eq_of_mem_support {R : Type} [CommRing R] {p : MvPolynomial (Fin (n + 1)) R} {d : ℕ}
    (hp : p.IsHomogeneous d) {s : Fin (n + 1) →₀ ℕ} (hs : s ∈ p.support) : s.degree = d := by
  have h := hp (mem_support_iff.mp hs)
  have : (Finsupp.degree s : ℕ) = Finsupp.weight (fun _ => 1) s := by
    rw [Finsupp.degree_eq_weight_one]
  rw [this]
  exact h

section Theta

variable (A : Type) [CommRing A] [Algebra R₀ A]

variable (R₀ n m) in

noncomputable def theta : A ⊗[R₀] Sm R₀ n m →ₗ[A] MvPolynomial (Fin (n + 1)) A :=
  (MvPolynomial.algebraTensorAlgEquiv (σ := Fin (n + 1)) R₀ A).toLinearEquiv.toLinearMap ∘ₗ
    ((homogeneousSubmodule (Fin (n + 1)) R₀ m).subtype.baseChange A)

theorem theta_tmul (a : A) (p : Sm R₀ n m) :
    theta R₀ n m A (a ⊗ₜ[R₀] p) = a • MvPolynomial.map (algebraMap R₀ A) (p : MvPolynomial (Fin (n + 1)) R₀) := by
  simp [theta, LinearMap.baseChange_tmul, MvPolynomial.algebraTensorAlgEquiv_tmul]

theorem theta_mem (x : A ⊗[R₀] Sm R₀ n m) : theta R₀ n m A x ∈ homogeneousSubmodule (Fin (n + 1)) A m := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a p =>
    rw [theta_tmul]
    exact Submodule.smul_mem _ a ((show (p : MvPolynomial (Fin (n + 1)) R₀).IsHomogeneous m from p.2).map _)
  | add x y hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy

variable (R₀ m) in

noncomputable def w : (Fin (n + 1) →₀ ℕ) → A ⊗[R₀] Sm R₀ n m := fun s =>
  if hs : s.degree = m then
    (1 : A) ⊗ₜ[R₀] (⟨monomial s (1 : R₀), isHomogeneous_monomial (1 : R₀) hs⟩ : Sm R₀ n m)
  else 0

variable (R₀ m) in

noncomputable def lam : MvPolynomial (Fin (n + 1)) A →ₗ[A] A ⊗[R₀] Sm R₀ n m :=
  (MvPolynomial.basisMonomials (Fin (n + 1)) A).constr A (w R₀ m A)

theorem lam_monomial (s : Fin (n + 1) →₀ ℕ) (a : A) : lam R₀ m A (monomial s a) = a • w R₀ m A s := by
  have h1 : (monomial s a : MvPolynomial (Fin (n + 1)) A) = a • (MvPolynomial.basisMonomials (Fin (n + 1)) A) s := by
    rw [MvPolynomial.coe_basisMonomials, smul_monomial, smul_eq_mul, mul_one]
  rw [h1, map_smul, lam, Module.Basis.constr_basis]

theorem lam_map (p : Sm R₀ n m) :
    lam R₀ m A (MvPolynomial.map (algebraMap R₀ A) (p : MvPolynomial (Fin (n + 1)) R₀)) = (1 : A) ⊗ₜ[R₀] p := by
  classical
  have hp : (p : MvPolynomial (Fin (n + 1)) R₀).IsHomogeneous m := p.2
  have hw : ∀ s : Fin (n + 1) →₀ ℕ,
      (monomial s (coeff s (p : MvPolynomial (Fin (n + 1)) R₀)) : MvPolynomial (Fin (n + 1)) R₀).IsHomogeneous m := by
    intro s
    by_cases hs : coeff s (p : MvPolynomial (Fin (n + 1)) R₀) = 0
    · rw [hs, monomial_zero]
      exact isHomogeneous_zero _ _ _
    · exact isHomogeneous_monomial _ (degree_eq_of_mem_support hp (mem_support_iff.mpr hs))
  let u : (Fin (n + 1) →₀ ℕ) → Sm R₀ n m := fun s => ⟨monomial s (coeff s (p : MvPolynomial (Fin (n + 1)) R₀)), hw s⟩
  have hp_sum : p = ∑ s ∈ (p : MvPolynomial (Fin (n + 1)) R₀).support, u s := by
    apply Subtype.ext
    simp only [u, AddSubmonoidClass.coe_finsetSum]
    exact (p : MvPolynomial (Fin (n + 1)) R₀).as_sum
  have hmap : MvPolynomial.map (algebraMap R₀ A) (p : MvPolynomial (Fin (n + 1)) R₀) =
      ∑ s ∈ (p : MvPolynomial (Fin (n + 1)) R₀).support,
        monomial s (algebraMap R₀ A (coeff s (p : MvPolynomial (Fin (n + 1)) R₀))) := by
    conv_lhs => rw [(p : MvPolynomial (Fin (n + 1)) R₀).as_sum]
    simp only [map_sum, map_monomial]
  have hterm : ∀ s ∈ (p : MvPolynomial (Fin (n + 1)) R₀).support,
      lam R₀ m A (monomial s (algebraMap R₀ A (coeff s (p : MvPolynomial (Fin (n + 1)) R₀)))) =
        (1 : A) ⊗ₜ[R₀] u s := by
    intro s hs
    have hsd : s.degree = m := degree_eq_of_mem_support hp hs
    rw [lam_monomial]
    simp only [w, dif_pos hsd]
    rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one,
      show algebraMap R₀ A (coeff s (p : MvPolynomial (Fin (n + 1)) R₀)) =
        coeff s (p : MvPolynomial (Fin (n + 1)) R₀) • (1 : A) by rw [Algebra.smul_def, mul_one],
      TensorProduct.smul_tmul]
    congr 1
    apply Subtype.ext
    change coeff s (p : MvPolynomial (Fin (n + 1)) R₀) • monomial s (1 : R₀) = monomial s (coeff s (p : MvPolynomial (Fin (n + 1)) R₀))
    rw [smul_monomial, smul_eq_mul, mul_one]
  rw [hmap, map_sum, Finset.sum_congr rfl hterm, ← TensorProduct.tmul_sum, ← hp_sum]

theorem lam_theta (x : A ⊗[R₀] Sm R₀ n m) : lam R₀ m A (theta R₀ n m A x) = x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a p => rw [theta_tmul, map_smul, lam_map, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  | add x y hx hy => rw [map_add, map_add, hx, hy]

theorem theta_injective : Function.Injective (theta R₀ n m A) :=
  Function.LeftInverse.injective (lam_theta A)

variable (R₀) in
theorem theta_surjective (q : MvPolynomial (Fin (n + 1)) A) (hq : q.IsHomogeneous m) :
    ∃ x : A ⊗[R₀] Sm R₀ n m, theta R₀ n m A x = q := by
  classical
  refine ⟨∑ s ∈ q.support, coeff s q • w R₀ m A s, ?_⟩
  rw [map_sum]
  conv_rhs => rw [q.as_sum]
  refine Finset.sum_congr rfl fun s hs => ?_
  have hsd : s.degree = m := degree_eq_of_mem_support hq hs
  simp only [w, dif_pos hsd, map_smul, theta_tmul, one_smul, map_monomial, map_one, smul_monomial, smul_eq_mul,
    mul_one]

variable (R₀ n m) in

noncomputable def thetaE : A ⊗[R₀] Sm R₀ n m ≃ₗ[A] ↥(homogeneousSubmodule (Fin (n + 1)) A m) :=
  LinearEquiv.ofBijective ((theta R₀ n m A).codRestrict _ (theta_mem A))
    ⟨fun x y hxy => theta_injective A (congrArg Subtype.val hxy),
     fun q => by
      obtain ⟨x, hx⟩ := theta_surjective R₀ A (q : MvPolynomial (Fin (n + 1)) A) q.2
      exact ⟨x, Subtype.ext hx⟩⟩

@[scoped simp] theorem thetaE_apply_coe (x : A ⊗[R₀] Sm R₀ n m) :
    ((thetaE R₀ n m A x : ↥(homogeneousSubmodule (Fin (n + 1)) A m)) : MvPolynomial (Fin (n + 1)) A) =
      theta R₀ n m A x := rfl

end Theta

section SpanPiece

variable {A : Type} [CommRing A]

theorem decompose_eq (q : MvPolynomial (Fin (n + 1)) A) (d : ℕ) :
    (DirectSum.decompose (homogeneousSubmodule (Fin (n + 1)) A) q d : MvPolynomial (Fin (n + 1)) A) =
      homogeneousComponent d q :=
  MvPolynomial.decomposition.decompose'_apply q d

theorem homogeneousComponent_mem_of_mem_span (V : Submodule A (MvPolynomial (Fin (n + 1)) A))
    (hV : V ≤ (homogeneousSubmodule (Fin (n + 1)) A m))
    {q : MvPolynomial (Fin (n + 1)) A} (hq : q ∈ Ideal.span (V : Set (MvPolynomial (Fin (n + 1)) A))) :
    homogeneousComponent m q ∈ V ∧ ∀ d, d < m → homogeneousComponent d q = 0 := by
  revert hq
  refine fun hq => Submodule.span_induction
    (p := fun q _ => homogeneousComponent m q ∈ V ∧ ∀ d, d < m → homogeneousComponent d q = 0) ?_ ?_ ?_ ?_ hq
  · intro v hv
    have hvm : v ∈ homogeneousSubmodule (Fin (n + 1)) A m := hV hv
    refine ⟨?_, fun d hd => ?_⟩
    · rw [homogeneousComponent_of_mem hvm, if_pos rfl]; exact hv
    · rw [homogeneousComponent_of_mem hvm, if_neg (Nat.ne_of_lt hd)]
  · exact ⟨by simp, fun d _ => by simp⟩
  · intro x y _ _ hx hy
    exact ⟨by simpa [map_add] using V.add_mem hx.1 hy.1, fun d hd => by simp [map_add, hx.2 d hd, hy.2 d hd]⟩
  · intro g x _ hx
    have key : ∀ d, d ≤ m → homogeneousComponent d (g • x) =
        homogeneousComponent 0 g * homogeneousComponent d x := by
      intro d hd
      rw [smul_eq_mul, ← sum_homogeneousComponent g, Finset.sum_mul, map_sum]
      rw [Finset.sum_eq_single 0]
      · have h0 : homogeneousComponent 0 g ∈ homogeneousSubmodule (Fin (n + 1)) A 0 := homogeneousComponent_mem 0 g
        have := DirectSum.coe_decompose_mul_of_left_mem_of_le (𝒜 := homogeneousSubmodule (Fin (n + 1)) A)
          (b := x) h0 (Nat.zero_le d)
        rw [decompose_eq, decompose_eq, Nat.sub_zero] at this
        rw [this, sum_homogeneousComponent]
      · intro i _ hi
        have hgi : homogeneousComponent i g ∈ homogeneousSubmodule (Fin (n + 1)) A i := homogeneousComponent_mem i g
        by_cases hid : i ≤ d
        · have := DirectSum.coe_decompose_mul_of_left_mem_of_le (𝒜 := homogeneousSubmodule (Fin (n + 1)) A)
            (b := x) hgi hid
          rw [decompose_eq, decompose_eq] at this
          rw [this, hx.2 (d - i) (by omega), mul_zero]
        · have := DirectSum.coe_decompose_mul_of_left_mem_of_not_le (𝒜 := homogeneousSubmodule (Fin (n + 1)) A)
            (b := x) hgi hid
          rw [decompose_eq] at this
          exact this
      · intro h
        simp at h
    refine ⟨?_, fun d hd => ?_⟩
    · rw [key m le_rfl, homogeneousComponent_zero, ← smul_eq_C_mul]
      exact V.smul_mem _ hx.1
    · rw [key d hd.le, hx.2 d hd, mul_zero]

theorem mem_of_mem_span_of_isHomogeneous (V : Submodule A (MvPolynomial (Fin (n + 1)) A))
    (hV : V ≤ (homogeneousSubmodule (Fin (n + 1)) A m))
    {q : MvPolynomial (Fin (n + 1)) A} (hq : q ∈ Ideal.span (V : Set (MvPolynomial (Fin (n + 1)) A)))
    (hqm : q.IsHomogeneous m) : q ∈ V := by
  have := (homogeneousComponent_mem_of_mem_span V hV hq).1
  rwa [homogeneousComponent_of_mem (show q ∈ homogeneousSubmodule (Fin (n + 1)) A m from hqm), if_pos rfl] at this

end SpanPiece

section IdealOf

variable (A : Type) [CommRing A] [Algebra R₀ A]

noncomputable def formsOf (N : Submodule A (A ⊗[R₀] Sm R₀ n m)) : Submodule A (MvPolynomial (Fin (n + 1)) A) :=
  N.map (theta R₀ n m A)

theorem formsOf_le (N : Submodule A (A ⊗[R₀] Sm R₀ n m)) :
    formsOf A N ≤ homogeneousSubmodule (Fin (n + 1)) A m := by
  rintro _ ⟨x, -, rfl⟩
  exact theta_mem A x

noncomputable def idealOf (N : Submodule A (A ⊗[R₀] Sm R₀ n m)) : Ideal (MvPolynomial (Fin (n + 1)) A) :=
  Ideal.span (formsOf A N : Set (MvPolynomial (Fin (n + 1)) A))

theorem idealOf_generated (N : Submodule A (A ⊗[R₀] Sm R₀ n m)) :
    ∃ s : Set (MvPolynomial (Fin (n + 1)) A), (∀ p ∈ s, p.IsHomogeneous m) ∧ idealOf A N = Ideal.span s :=
  ⟨formsOf A N, fun p hp => formsOf_le A N hp, rfl⟩

theorem theta_mem_idealOf {N : Submodule A (A ⊗[R₀] Sm R₀ n m)} {x : A ⊗[R₀] Sm R₀ n m} (hx : x ∈ N) :
    theta R₀ n m A x ∈ idealOf A N :=
  Ideal.subset_span ⟨x, hx, rfl⟩

noncomputable abbrev K (N : Submodule A (A ⊗[R₀] Sm R₀ n m)) : Submodule A ↥(homogeneousSubmodule (Fin (n + 1)) A m) :=
  Submodule.comap (homogeneousSubmodule (Fin (n + 1)) A m).subtype ((idealOf A N).restrictScalars A)

theorem map_thetaE_eq_K (N : Submodule A (A ⊗[R₀] Sm R₀ n m)) :
    N.map (thetaE R₀ n m A).toLinearMap = K A N := by
  ext q
  constructor
  · rintro ⟨x, hx, rfl⟩
    simp only [Submodule.mem_comap, Submodule.coe_subtype, Submodule.restrictScalars_mem, LinearEquiv.coe_coe,
      thetaE_apply_coe]
    exact theta_mem_idealOf A hx
  · intro hq
    have hq' : (q : MvPolynomial (Fin (n + 1)) A) ∈ idealOf A N := by simpa using hq
    have hqV : (q : MvPolynomial (Fin (n + 1)) A) ∈ formsOf A N :=
      mem_of_mem_span_of_isHomogeneous (formsOf A N) (formsOf_le A N) hq' q.2
    obtain ⟨x, hx, hxq⟩ := hqV
    exact ⟨x, hx, Subtype.ext hxq⟩

noncomputable def pieceEquiv (N : Submodule A (A ⊗[R₀] Sm R₀ n m)) :
    ((A ⊗[R₀] Sm R₀ n m) ⧸ N) ≃ₗ[A] piece (idealOf A N) m :=
  Submodule.Quotient.equiv N (K A N) (thetaE R₀ n m A) (map_thetaE_eq_K A N)

theorem comap_K_eq (N : Submodule A (A ⊗[R₀] Sm R₀ n m)) :
    (K A N).comap (thetaE R₀ n m A).toLinearMap = N := by
  rw [← map_thetaE_eq_K, Submodule.comap_map_eq_of_injective (thetaE R₀ n m A).injective]

end IdealOf

section Natural

variable {k : ℕ} {A B : Type} [CommRing A] [CommRing B] [Algebra R₀ A] [Algebra R₀ B]

theorem theta_cancel_tmul [Algebra A B] [IsScalarTower R₀ A B] (b : B) (x : A ⊗[R₀] Sm R₀ n m) :
    theta R₀ n m B (TensorProduct.AlgebraTensorModule.cancelBaseChange R₀ A B B (Sm R₀ n m) (b ⊗ₜ[A] x)) =
      b • MvPolynomial.map (algebraMap A B) (theta R₀ n m A x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a p =>
    rw [TensorProduct.AlgebraTensorModule.cancelBaseChange_tmul, theta_tmul, theta_tmul,
      MvPolynomial.smul_eq_C_mul (MvPolynomial.map (algebraMap R₀ A) _) a, map_mul, MvPolynomial.map_C,
      MvPolynomial.map_map, ← IsScalarTower.algebraMap_eq R₀ A B, ← MvPolynomial.smul_eq_C_mul,
      Algebra.smul_def a b, mul_comm, ← smul_eq_mul, smul_assoc]
  | add x y hx hy => simp [TensorProduct.tmul_add, map_add, hx, hy, smul_add]

theorem idealOf_map (φ : A →ₐ[R₀] B) (N : Module.Grassmannian A (A ⊗[R₀] Sm R₀ n m) k) :
    idealOf B (Module.Grassmannian.map φ N).toSubmodule =
      (idealOf A N.toSubmodule).map (MvPolynomial.map φ.toRingHom) := by
  letI : Algebra A B := φ.toAlgebra
  letI : IsScalarTower R₀ A B := IsScalarTower.of_algebraMap_eq' <| IsScalarTower.algebraMap_eq R₀ A B
  have hφ : (algebraMap A B) = φ.toRingHom := rfl
  have hker : (Module.Grassmannian.map φ N).toSubmodule =
      LinearMap.ker (Module.Grassmannian.baseChangeMkQ B N.toSubmodule) :=
    Module.Grassmannian.map_toSubmodule φ N
  apply le_antisymm
  ·
    rw [idealOf, Ideal.span_le]
    rintro _ ⟨y, hy, rfl⟩
    rw [hker] at hy
    have hy' : (TensorProduct.AlgebraTensorModule.cancelBaseChange R₀ A B B (Sm R₀ n m)).symm y ∈
        LinearMap.ker (LinearMap.lTensor B N.toSubmodule.mkQ) := by
      rw [LinearMap.mem_ker, ← LinearMap.baseChange_eq_ltensor]
      simpa [Module.Grassmannian.baseChangeMkQ] using hy
    rw [lTensor_mkQ] at hy'
    obtain ⟨t, ht⟩ := hy'
    have hyt : y = TensorProduct.AlgebraTensorModule.cancelBaseChange R₀ A B B (Sm R₀ n m)
        (LinearMap.lTensor B N.toSubmodule.subtype t) := by
      rw [ht, LinearEquiv.apply_symm_apply]
    rw [hyt]
    clear hyt ht hy
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul b x =>
      rw [SetLike.mem_coe, LinearMap.lTensor_tmul, theta_cancel_tmul, Submodule.coe_subtype, hφ,
        MvPolynomial.smul_eq_C_mul]
      exact Ideal.mul_mem_left _ _ (Ideal.mem_map_of_mem _ (theta_mem_idealOf A x.2))
    | add x y hx hy =>
      simp only [map_add, SetLike.mem_coe] at hx hy ⊢
      exact Ideal.add_mem _ hx hy
  ·
    rw [Ideal.map_le_iff_le_comap, idealOf, Ideal.span_le]
    rintro _ ⟨x, hx, rfl⟩
    rw [SetLike.mem_coe, Ideal.mem_comap]
    have hmem : TensorProduct.AlgebraTensorModule.cancelBaseChange R₀ A B B (Sm R₀ n m) ((1 : B) ⊗ₜ[A] x) ∈
        (Module.Grassmannian.map φ N).toSubmodule := by
      rw [hker, LinearMap.mem_ker]
      simp [Module.Grassmannian.baseChangeMkQ, (Submodule.Quotient.mk_eq_zero _).mpr hx]
    have := theta_mem_idealOf B hmem
    rwa [theta_cancel_tmul, one_smul, hφ] at this

end Natural

section Points

variable (h : ℕ → ℕ) (A : Type) [CommRing A] [Algebra R₀ A]

variable (R₀ n m) in

abbrev FG : Type := Module.Grassmannian A (A ⊗[R₀] Sm R₀ n m) (h m)

def W (N : FG R₀ n m h A) : Prop :=
  Module.Projective A (piece (idealOf A N.toSubmodule) (m + 1)) ∧
    ∀ 𝔮 : PrimeSpectrum A, Module.rankAtStalk (piece (idealOf A N.toSubmodule) (m + 1)) 𝔮 = h (m + 1)

theorem projective_piece_idealOf (N : FG R₀ n m h A) : Module.Projective A (piece (idealOf A N.toSubmodule) m) :=
  Module.Projective.of_equiv (pieceEquiv A N.toSubmodule)

theorem rankAtStalk_piece_idealOf (N : FG R₀ n m h A) (p : PrimeSpectrum A) :
    Module.rankAtStalk (piece (idealOf A N.toSubmodule) m) p = h m :=
  (congrFun (Module.rankAtStalk_eq_of_equiv (pieceEquiv A N.toSubmodule)) p).symm.trans (N.rankAtStalk_eq p)

variable (m) in

noncomputable abbrev KP (P : Point A n h) : Submodule A ↥(homogeneousSubmodule (Fin (n + 1)) A m) :=
  Submodule.comap (homogeneousSubmodule (Fin (n + 1)) A m).subtype (P.I.restrictScalars A)

variable (R₀ m) in

noncomputable def grOf (P : Point A n h) : FG R₀ n m h A :=
  haveI := P.finite_piece m
  haveI := P.projective_piece m
  let N : Submodule A (A ⊗[R₀] Sm R₀ n m) := (KP m h A P).comap (thetaE R₀ n m A).toLinearMap
  have hN : N.map (thetaE R₀ n m A).toLinearMap = KP m h A P :=
    Submodule.map_comap_eq_of_surjective (thetaE R₀ n m A).surjective _
  let e : ((A ⊗[R₀] Sm R₀ n m) ⧸ N) ≃ₗ[A] piece P.I m := Submodule.Quotient.equiv N (KP m h A P) (thetaE R₀ n m A) hN
  { toSubmodule := N
    finite_quotient := Module.Finite.equiv e.symm
    projective_quotient := Module.Projective.of_equiv e.symm
    rankAtStalk_eq := fun p => (congrFun (Module.rankAtStalk_eq_of_equiv e) p).trans (P.rankAtStalk_piece m p) }

variable (R₀ m) in
theorem grOf_toSubmodule (P : Point A n h) :
    (grOf R₀ m h A P).toSubmodule = (KP m h A P).comap (thetaE R₀ n m A).toLinearMap := rfl

variable (R₀ m) in
theorem formsOf_grOf (P : Point A n h) :
    (formsOf A (grOf R₀ m h A P).toSubmodule : Set (MvPolynomial (Fin (n + 1)) A)) =
      {p | p ∈ P.I ∧ p.IsHomogeneous m} := by
  ext q
  simp only [formsOf, grOf_toSubmodule, Submodule.map_coe, Set.mem_image, SetLike.mem_coe, Submodule.mem_comap,
    LinearEquiv.coe_coe, Submodule.coe_subtype, Submodule.restrictScalars_mem, Set.mem_setOf_eq]
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨by simpa using hx, theta_mem A x⟩
  · rintro ⟨hqI, hqm⟩
    obtain ⟨x, hx⟩ := theta_surjective R₀ A q hqm
    refine ⟨x, ?_, hx⟩
    simpa [hx] using hqI

variable (R₀ m) in
theorem idealOf_grOf (hgen : ∀ P : Point A n h, P.I = Ideal.span {p | p ∈ P.I ∧ p.IsHomogeneous m})
    (P : Point A n h) : idealOf A (grOf R₀ m h A P).toSubmodule = P.I := by
  rw [idealOf, formsOf_grOf R₀ m h A P, ← hgen P]

variable (R₀ m) in
theorem W_grOf (hgen : ∀ P : Point A n h, P.I = Ideal.span {p | p ∈ P.I ∧ p.IsHomogeneous m})
    (P : Point A n h) : W h A (grOf R₀ m h A P) := by
  refine ⟨?_, ?_⟩
  · rw [idealOf_grOf R₀ m h A hgen]; exact P.projective_piece (m + 1)
  · rw [idealOf_grOf R₀ m h A hgen]; exact P.rankAtStalk_piece (m + 1)

theorem grOf_eq_of_I_eq (P : Point A n h) (N : FG R₀ n m h A) (hPN : P.I = idealOf A N.toSubmodule) :
    grOf R₀ m h A P = N := by
  apply Module.Grassmannian.ext
  rw [grOf_toSubmodule R₀ m h A P]
  have : KP m h A P = K A N.toSubmodule := by
    simp only [KP, K, hPN]
  rw [this, comap_K_eq]

variable (R₀ m) in

noncomputable def equivW (hgen : ∀ P : Point A n h, P.I = Ideal.span {p | p ∈ P.I ∧ p.IsHomogeneous m})
    (hpers : ∀ N : FG R₀ n m h A, W h A N → ∃ P : Point A n h, P.I = idealOf A N.toSubmodule) :
    Point A n h ≃ {N : FG R₀ n m h A // W h A N} where
  toFun P := ⟨grOf R₀ m h A P, W_grOf R₀ m h A hgen P⟩
  invFun N := (hpers N.1 N.2).choose
  left_inv P := by
    apply Point.ext
    exact (hpers (grOf R₀ m h A P) (W_grOf R₀ m h A hgen P)).choose_spec.trans (idealOf_grOf R₀ m h A hgen P)
  right_inv N := by
    apply Subtype.ext
    exact grOf_eq_of_I_eq h A _ _ (hpers N.1 N.2).choose_spec

theorem equivW_apply (hgen : ∀ P : Point A n h, P.I = Ideal.span {p | p ∈ P.I ∧ p.IsHomogeneous m})
    (hpers : ∀ N : FG R₀ n m h A, W h A N → ∃ P : Point A n h, P.I = idealOf A N.toSubmodule) (P : Point A n h) :
    (equivW R₀ m h A hgen hpers P).1 = grOf R₀ m h A P := rfl

end Points

end HilbRepGotz
p2m_reactivate "P2MW.S_AlgebraicGeometry_HilbertFunctor_exists_scheme_represents_and_isClosedImmersion_toProjSpace_of_maximal_growth.HilbRepGotz"

open HilbRepGotz in
theorem solution
    (n m : ℕ) (h : ℕ → ℕ) (h₁ : ∀ d, d < m → h d = Nat.choose (n + d) n)
    (h₂ : ∀ e, m ≤ e → ∀ (K : Type) [Field K] (J : Ideal (MvPolynomial (Fin (n + 1)) K)),
      (∃ s : Set (MvPolynomial (Fin (n + 1)) K), (∀ p ∈ s, p.IsHomogeneous e) ∧ J = Ideal.span s) →
      Module.finrank K (piece J e) = h e → Module.finrank K (piece J (e + 1)) ≤ h (e + 1))
    (h₃ : ∀ e, m ≤ e → ∃ (K : Type) (_ : Field K) (J : Ideal (MvPolynomial (Fin (n + 1)) K)),
      (∃ s : Set (MvPolynomial (Fin (n + 1)) K), (∀ p ∈ s, p.IsHomogeneous e) ∧ J = Ideal.span s) ∧
      Module.finrank K (piece J e) = h e ∧ Module.finrank K (piece J (e + 1)) = h (e + 1)) :
    (∀ (A B : Type) [CommRing A] [CommRing B] (φ : A →+* B) (P : Point A n h),
        ∃ Q : Point B n h, Q.I = Ideal.map (MvPolynomial.map φ) P.I) ∧
    ∃ (Hilb : Scheme.{0})
      (pt : ∀ (A : Type) [CommRing A], Point A n h ≃ (Spec (CommRingCat.of A) ⟶ Hilb)),
      (∀ (A B : Type) [CommRing A] [CommRing B] (φ : A →+* B) (P : Point A n h) (Q : Point B n h),
          Q.I = Ideal.map (MvPolynomial.map φ) P.I →
          pt B Q = Spec.map (CommRingCat.ofHom φ) ≫ pt A P) ∧
      ∃ (N : ℕ) (ι : Hilb ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) ℤ)),
        IsClosedImmersion ι := by

  have hbc : ∀ (A B : Type) [CommRing A] [CommRing B] (φ : A →+* B) (P : Point A n h),
      ∃ Q : Point B n h, Q.I = Ideal.map (MvPolynomial.map φ) P.I := by
    intro A B _ _ φ P
    letI : Algebra A B := φ.toAlgebra
    exact AlgebraicGeometry.HilbertFunctor.exists_point_I_eq_map n h A B P
  refine ⟨hbc, ?_⟩

  have hgen : ∀ (A : Type) [CommRing A] (P : Point A n h), P.I = Ideal.span {p | p ∈ P.I ∧ p.IsHomogeneous m} :=
    fun A _ P => AlgebraicGeometry.HilbertFunctor.Point.I_eq_span_of_forall_finrank_piece_succ_le n m h h₁ h₂ A P
  have hpers : ∀ (A : Type) [CommRing A] (N : FG ℤ n m h A), W h A N →
      ∃ P : Point A n h, P.I = idealOf A N.toSubmodule := fun A _ N hW =>
    AlgebraicGeometry.HilbertFunctor.exists_point_I_eq_of_projective_piece_succ n m h h₁ h₂ h₃ A
      (idealOf A N.toSubmodule) (idealOf_generated A N.toSubmodule)
      ⟨projective_piece_idealOf h A N, rankAtStalk_piece_idealOf h A N⟩ hW

  obtain ⟨Gr, p, ptG, hnatG, N₀, ιG, hιG, -⟩ :=
    @Module.Grassmannian.exists_scheme_represents_and_isClosedImmersion_toProjSpace ℤ _ (Sm ℤ n m) _
      (Submodule.module _) instFiniteSm (h m)

  have hclosed : ∀ (A : Type) [CommRing A] [Algebra ℤ A] (N : FG ℤ n m h A),
      ∃ 𝔞 : Ideal A, ∀ (B : Type) [CommRing B] [Algebra ℤ B] (φ : A →ₐ[ℤ] B),
        W h B (Module.Grassmannian.map φ N) ↔ ∀ a ∈ 𝔞, φ a = 0 := by
    intro A _ _ N
    obtain ⟨𝔞, h𝔞⟩ := AlgebraicGeometry.HilbertFunctor.exists_ideal_forall_projective_piece_succ_iff n m (h m)
      (h (m + 1)) (h₂ m le_rfl) A (idealOf A N.toSubmodule) (idealOf_generated A N.toSubmodule)
      (projective_piece_idealOf h A N) (rankAtStalk_piece_idealOf h A N)
    refine ⟨𝔞, fun B _ _ φ => ?_⟩
    letI : Algebra A B := φ.toAlgebra
    have key := h𝔞 B
    rw [W, idealOf_map φ N]
    exact key

  obtain ⟨Z, ι, ptZ, hι, hptZ⟩ :=
    AlgebraicGeometry.Scheme.exists_isClosedImmersion_represents_of_forall_exists_ideal ℤ (FG ℤ n m h)
      (fun A B _ _ _ _ φ N => Module.Grassmannian.map φ N) Gr p ptG hnatG (fun A _ _ N => W h A N) hclosed
  haveI := hι
  haveI := hιG

  let pt : ∀ (A : Type) [CommRing A], Point A n h ≃ (Spec (CommRingCat.of A) ⟶ Z) := fun A _ =>
    (equivW ℤ m h A (hgen A) (hpers A)).trans
      ((ptZ A).trans (Equiv.subtypeUnivEquiv fun g => specZIsTerminal.hom_ext _ _))
  refine ⟨Z, pt, ?_, N₀, ι ≫ ιG, inferInstance⟩
  intro A B _ _ φ P Q hPQ

  have hQ : grOf ℤ m h B Q = Module.Grassmannian.map φ.toIntAlgHom (grOf ℤ m h A P) := by
    apply grOf_eq_of_I_eq
    rw [idealOf_map, idealOf_grOf ℤ m h A (hgen A), hPQ]
    rfl
  rw [← cancel_mono ι]
  change (ptZ B ⟨grOf ℤ m h B Q, _⟩).1 ≫ ι = (Spec.map (CommRingCat.ofHom φ) ≫ (ptZ A ⟨grOf ℤ m h A P, _⟩).1) ≫ ι
  rw [Category.assoc, hptZ, hptZ]
  change (ptG B (grOf ℤ m h B Q)).1 = Spec.map (CommRingCat.ofHom φ.toIntAlgHom.toRingHom) ≫ (ptG A (grOf ℤ m h A P)).1
  rw [← hnatG A B φ.toIntAlgHom (grOf ℤ m h A P), hQ]

end S_AlgebraicGeometry_HilbertFunctor_exists_scheme_represents_and_isClosedImmersion_toProjSpace_of_maximal_growth
end P2MW
export P2MW.S_AlgebraicGeometry_HilbertFunctor_exists_scheme_represents_and_isClosedImmersion_toProjSpace_of_maximal_growth (solution)

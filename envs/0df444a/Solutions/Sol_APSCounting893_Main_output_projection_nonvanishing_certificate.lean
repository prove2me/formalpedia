-- Prove2me | solution 1 for APSCounting893.Main.output_projection_nonvanishing_certificate
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T13:51:09.620215+00:00
-- url     : https://prove2.me/submissions/db7b0ad7-b86a-4a8e-b440-656b63fdb129

import Definitions.Def_APSCounting893_Main_Geometry
import Definitions.Def_APSCounting893_Main_RandomReduction
import Definitions.Def_APSCounting893_Main_Resultant
import Mathlib
import Mathlib.FieldTheory.FinTrdeg
import Mathlib.LinearAlgebra.Dimension.RankNullity
import Mathlib.RingTheory.EssentialFiniteness
import Theorems.Thm_APSCounting893_Main_jacobian_independence_criterion
import Theorems.Thm_APSCounting893_Main_projective_incidence_relation_degree_bound
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_mvPolynomial_exists_coordinate_transcendence_basis
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_mvPolynomial_quotient_dimension_eq_fraction_field_trdeg_toNat
import Theorems.Thm_ringKrullDim_le_of_ringHom_isIntegral
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 4096

section Component_0

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
open MvPolynomial
namespace APSCounting893.Main

lemma eval_homogenize_monomial {R K : Type} [CommRing R] [Field K] {n : ℕ}
    (f : R →+* K) (z : Fin (n + 1) → K) (e : Fin n →₀ ℕ) (c : R) (d : ℕ) :
    MvPolynomial.eval₂ f z (MvPolynomial.monomial
      (Finsupp.single 0 (d - e.sum (fun _ k => k)) + e.mapDomain Fin.succ) c) =
    f c * z 0 ^ (d - e.sum (fun _ k => k)) * e.prod (fun i k => z i.succ ^ k) := by
  classical
  rw [MvPolynomial.eval₂_monomial]
  rw [Finsupp.prod_add_index' (fun _ => pow_zero _) (fun _ _ _ => pow_add _ _ _)]
  rw [Finsupp.prod_single_index (h := fun i k => z i ^ k) (pow_zero (z 0))]
  rw [Finsupp.prod_mapDomain_index (fun _ => pow_zero _) (fun _ _ _ => pow_add _ _ _)]
  ring

lemma finsupp_prod_scaled {K : Type} [Field K] {n : ℕ}
    (e : Fin n →₀ ℕ) (a : K) (x : Fin n → K) :
    e.prod (fun i k => (a * x i) ^ k) =
      a ^ e.sum (fun _ k => k) * e.prod (fun i k => x i ^ k) := by
  classical
  rw [e.prod_fintype _ (fun _ => pow_zero _), e.prod_fintype _ (fun _ => pow_zero _),
    e.sum_fintype _ (fun _ => rfl)]
  simp only [mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]

lemma eval_homogenize_scaled {R K : Type} [CommRing R] [Field K] {n : ℕ}
    (f : R →+* K) (p : MvPolynomial (Fin n) R) (d : ℕ) (hd : p.totalDegree ≤ d)
    (a : K) (x : Fin n → K) :
    MvPolynomial.eval₂ f (Fin.cases a (fun i => a * x i)) (homogenizeAll d p) =
      a ^ d * MvPolynomial.eval₂ f x p := by
  classical
  rw [homogenizeAll, MvPolynomial.eval₂_sum]
  conv_rhs => rw [MvPolynomial.eval₂_eq]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro e he
  rw [eval_homogenize_monomial]
  simp only [Fin.cases_zero, Fin.cases_succ]
  rw [finsupp_prod_scaled]
  have hedeg : e.sum (fun _ k => k) ≤ d := (MvPolynomial.le_totalDegree he).trans hd
  have hpow : a ^ (d - e.sum (fun _ k => k)) * a ^ e.sum (fun _ k => k) = a ^ d := by
    rw [← pow_add, Nat.sub_add_cancel hedeg]
  calc
    f (p.coeff e) * a ^ (d - e.sum (fun _ k => k)) *
        (a ^ e.sum (fun _ k => k) * e.prod (fun i k => x i ^ k)) =
      (a ^ (d - e.sum (fun _ k => k)) * a ^ e.sum (fun _ k => k)) *
        (f (p.coeff e) * e.prod (fun i k => x i ^ k)) := by ring
    _ = _ := by rw [hpow]; rfl

lemma eval_homogenize_dehomogenize {R K : Type} [CommRing R] [Field K] {n : ℕ}
    (f : R →+* K) (p : MvPolynomial (Fin n) R) (d : ℕ) (hd : p.totalDegree ≤ d)
    (z : Fin (n + 1) → K) (hz : z 0 ≠ 0) :
    MvPolynomial.eval₂ f z (homogenizeAll d p) =
      z 0 ^ d * MvPolynomial.eval₂ f (fun i => z i.succ / z 0) p := by
  have heq : Fin.cases (z 0) (fun i => z 0 * (z i.succ / z 0)) = z := by
    funext i
    refine Fin.cases rfl (fun j => ?_) i
    simp [hz, mul_div_cancel₀, mul_comm]
  simpa only [heq] using eval_homogenize_scaled f p d hd (z 0) (fun i => z i.succ / z 0)

end APSCounting893.Main
end Component_0

section Component_1

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency.types false
open MvPolynomial
namespace APSCounting893.Main

lemma projectiveRepresentative_rescaling {K : Type} [Field K] {n : ℕ}
    (z : Fin n → K) (hz : z ≠ 0) :
    ∃ a : K, a ≠ 0 ∧ projectiveRepresentative z = a • z := by
  classical
  have hS : (Finset.univ.filter (fun i : Fin n => z i ≠ 0)).Nonempty := by
    by_contra h
    apply hz
    funext i
    by_contra hi
    exact h ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩⟩
  let j := (Finset.univ.filter (fun i : Fin n => z i ≠ 0)).min' hS
  have hj : z j ≠ 0 := (Finset.mem_filter.mp (Finset.min'_mem _ hS)).2
  refine ⟨(z j)⁻¹, inv_ne_zero hj, ?_⟩
  rw [projectiveRepresentative, dif_pos hS]
  funext i
  simp only [div_eq_mul_inv, Pi.smul_apply, smul_eq_mul]
  exact mul_comm _ _

lemma projectiveRepresentative_ne_zero {K : Type} [Field K] {n : ℕ}
    (z : Fin n → K) (hz : z ≠ 0) : projectiveRepresentative z ≠ 0 := by
  obtain ⟨a, ha, he⟩ := projectiveRepresentative_rescaling z hz
  rw [he]
  exact smul_ne_zero ha hz

lemma homogenizeAll_homogeneous {R : Type} [CommRing R] {n : ℕ}
    (p : MvPolynomial (Fin n) R) (d : ℕ) (hd : p.totalDegree ≤ d) :
    (homogenizeAll d p).IsHomogeneous d := by
  classical
  apply MvPolynomial.IsHomogeneous.sum
  intro e he
  apply MvPolynomial.isHomogeneous_monomial
  rw [map_add, Finsupp.degree_single, Finsupp.degree_mapDomain, Finsupp.degree_eq_sum]
  have hsum : (∑ i : Fin n, e i) = e.sum (fun _ k => k) :=
    (e.sum_fintype (fun _ k => k) (fun _ => rfl)).symm
  rw [hsum]
  exact Nat.sub_add_cancel ((MvPolynomial.le_totalDegree he).trans hd)

lemma homogeneous_eval₂_scaled {R K : Type} [CommRing R] [Field K] {n : ℕ}
    (p : MvPolynomial (Fin n) R) (d : ℕ) (hp : p.IsHomogeneous d)
    (f : R →+* K) (a : K) (z : Fin n → K) :
    MvPolynomial.eval₂ f (fun i => a * z i) p = a ^ d * MvPolynomial.eval₂ f z p := by
  classical
  conv_lhs => rw [MvPolynomial.eval₂_eq]
  conv_rhs => rw [MvPolynomial.eval₂_eq]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro e he
  change f (p.coeff e) * e.prod (fun i k => (a * z i) ^ k) =
    a ^ d * (f (p.coeff e) * e.prod (fun i k => z i ^ k))
  rw [finsupp_prod_scaled]
  have hd := hp.degree_eq_sum_deg_support he
  change d = e.sum (fun _ k => k) at hd
  rw [← hd]
  ring

lemma homogeneous_root_projectiveRepresentative {R K : Type} [CommRing R] [Field K] {n : ℕ}
    (p : MvPolynomial (Fin n) R) (d : ℕ) (hp : p.IsHomogeneous d)
    (f : R →+* K) (z : Fin n → K) (hz : z ≠ 0) (hroot : MvPolynomial.eval₂ f z p = 0) :
    MvPolynomial.eval₂ f (projectiveRepresentative z) p = 0 := by
  obtain ⟨a, ha, he⟩ := projectiveRepresentative_rescaling z hz
  rw [he]
  change MvPolynomial.eval₂ f (fun i => a * z i) p = 0
  rw [homogeneous_eval₂_scaled p d hp f a z, hroot, mul_zero]

end APSCounting893.Main
end Component_1

section Component_2
set_option autoImplicit false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency.types false
open MvPolynomial
namespace APSCounting893.Main

noncomputable def radialPolynomial {K : Type} [Field K] {σ : Type}
    (p : MvPolynomial σ K) (y : σ → K) : Polynomial K :=
  ∑ d ∈ Finset.range (p.totalDegree+1), Polynomial.C (eval y (homogeneousComponent d p)) * Polynomial.X^d

lemma radialPolynomial_eval {K : Type} [Field K] {n : ℕ}
    (p : MvPolynomial (Fin n) K) (y : Fin n → K) (a : K) :
    (radialPolynomial p y).eval a = eval (fun j => a*y j) p := by
  classical
  rw [radialPolynomial,Polynomial.eval_finset_sum]
  conv_rhs => rw [← MvPolynomial.sum_homogeneousComponent p]
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro d hd
  rw [Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X]
  have hh := homogeneous_eval₂_scaled (homogeneousComponent d p) d
    (homogeneousComponent_isHomogeneous d p) (RingHom.id K) a y
  simpa only [MvPolynomial.eval₂_id,mul_comm] using hh.symm

lemma radialPolynomial_coeff {K : Type} [Field K] {σ : Type}
    (p : MvPolynomial σ K) (y : σ → K) (d : ℕ) :
    (radialPolynomial p y).coeff d = eval y (homogeneousComponent d p) := by
  classical
  by_cases hd : d ≤ p.totalDegree
  · simp [radialPolynomial,Polynomial.coeff_C_mul_X_pow,Finset.mem_range,Nat.lt_succ_iff,hd]
  · have hh : homogeneousComponent d p = 0 := homogeneousComponent_eq_zero d p (by omega)
    simp [radialPolynomial,Polynomial.coeff_C_mul_X_pow,Finset.mem_range,Nat.lt_succ_iff,hd,hh]

lemma eval_homogeneousComponent_zero_of_scaled_zero {K : Type} [Field K] [Infinite K] {n : ℕ}
    (p : MvPolynomial (Fin n) K) (y : Fin n → K)
    (hp : ∀ a : K, eval (fun j => a*y j) p = 0) (d : ℕ) :
    eval y (homogeneousComponent d p) = 0 := by
  have hz : radialPolynomial p y = 0 := by
    apply Polynomial.funext
    intro a
    rw [radialPolynomial_eval,hp,Polynomial.eval_zero]
  rw [← radialPolynomial_coeff,hz,Polynomial.coeff_zero]

end APSCounting893.Main
end Component_2

section Component_3

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
open MvPolynomial
namespace APSCounting893.Main

noncomputable def affineEvaluation {K : Type} [Field K] {n : ℕ} (X : Set (Affine K n)) :
    Polynomials K n →ₗ[K] (X → K) where
  toFun p := fun x => MvPolynomial.eval x.val p
  map_add' p q := by funext x; exact map_add (MvPolynomial.eval x.val) p q
  map_smul' c p := by
    funext x
    simp [MvPolynomial.smul_eq_C_mul]

lemma affineFilteredPiece_eq_map {K : Type} [Field K] {n : ℕ}
    (X : Set (Affine K n)) (d : ℕ) :
    affineFilteredPiece X d = (MvPolynomial.restrictTotalDegree (Fin n) K d).map (affineEvaluation X) := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro f ⟨p, hp, rfl⟩
    exact Submodule.mem_map.mpr ⟨p, (MvPolynomial.mem_restrictTotalDegree (Fin n) d p).mpr hp, rfl⟩
  · rintro f ⟨p, hp, rfl⟩
    apply Submodule.subset_span
    exact ⟨p, (MvPolynomial.mem_restrictTotalDegree (Fin n) d p).mp hp, rfl⟩

instance affineFilteredPiece_finite {K : Type} [Field K] {n : ℕ}
    (X : Set (Affine K n)) (d : ℕ) : Module.Finite K (affineFilteredPiece X d) := by
  rw [affineFilteredPiece_eq_map]
  exact Module.Finite.map (MvPolynomial.restrictTotalDegree (Fin n) K d) (affineEvaluation X)

lemma mem_affineFilteredPiece {K : Type} [Field K] {n : ℕ}
    (X : Set (Affine K n)) (d : ℕ) (f : X → K) :
    f ∈ affineFilteredPiece X d ↔ ∃ p : Polynomials K n, p.totalDegree ≤ d ∧
      f = fun x => MvPolynomial.eval x.val p := by
  rw [affineFilteredPiece_eq_map, Submodule.mem_map]
  constructor
  · rintro ⟨p, hp, rfl⟩
    exact ⟨p, (MvPolynomial.mem_restrictTotalDegree (Fin n) d p).mp hp, rfl⟩
  · rintro ⟨p, hp, rfl⟩
    exact ⟨p, (MvPolynomial.mem_restrictTotalDegree (Fin n) d p).mpr hp, rfl⟩

lemma totalDegree_eval₂_bounded {K L : Type} [CommRing K] [CommRing L] {n m : ℕ}
    (f : K →+* L) (g : Fin n → MvPolynomial (Fin m) L) (D : ℕ)
    (hg : ∀ i, (g i).totalDegree ≤ D) (p : MvPolynomial (Fin n) K) :
    (eval₂Hom (MvPolynomial.C.comp f) g p).totalDegree ≤ D * p.totalDegree := by
  classical
  conv_lhs => rw [p.as_sum]
  rw [map_sum]
  apply totalDegree_finsetSum_le
  intro e he
  rw [eval₂Hom_monomial]
  apply (totalDegree_mul _ _).trans
  simp only [RingHom.coe_comp, Function.comp_apply, totalDegree_C, zero_add]
  rw [Finsupp.prod_pow]
  apply (totalDegree_finsetProd _ _).trans
  apply le_trans (Finset.sum_le_sum (fun i _ =>
    (totalDegree_pow _ _).trans (Nat.mul_le_mul_left _ (hg i))))
  rw [← Finset.sum_mul]
  simpa [Finsupp.sum_fintype, Nat.mul_comm] using Nat.mul_le_mul_right D (le_totalDegree he)

end APSCounting893.Main
end Component_3

section Component_4

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
open MvPolynomial
namespace APSCounting893.Main

lemma finsupp_nat_sum_eq {n : ℕ} (e : Fin n →₀ ℕ) :
    e.sum (fun _ v => v) = ∑ i, e i := Finsupp.sum_fintype _ _ (fun _ => rfl)

noncomputable def boundedExponentEquivSum (n d : ℕ) :
    {e : Fin n →₀ ℕ // e.sum (fun _ v => v) ≤ d} ≃
      {f : Fin (n + 1) → ℕ // ∑ i, f i = d} where
  toFun e := ⟨Fin.cons (d - e.val.sum (fun _ v => v)) e.val, by
    rw [Fin.sum_univ_succ]
    have he := e.property
    rw [finsupp_nat_sum_eq] at he
    simp only [Fin.cons_zero, Fin.cons_succ, finsupp_nat_sum_eq]
    omega⟩
  invFun f := ⟨Finsupp.equivFunOnFinite.symm (fun i => f.val i.succ), by
    have hf := f.property
    rw [Fin.sum_univ_succ] at hf
    rw [Finsupp.equivFunOnFinite_symm_sum]
    omega⟩
  left_inv e := by
    apply Subtype.ext
    ext i
    simp
  right_inv f := by
    apply Subtype.ext
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · have hf := f.property
      rw [Fin.sum_univ_succ] at hf
      change d - (Finsupp.equivFunOnFinite.symm (fun j : Fin n => f.val j.succ)).sum (fun _ v => v) = f.val 0
      rw [Finsupp.equivFunOnFinite_symm_sum]
      omega
    · simp

noncomputable def boundedExponentEquivSym (n d : ℕ) :
    {e : Fin n →₀ ℕ // e.sum (fun _ v => v) ≤ d} ≃ Sym (Fin (n + 1)) d :=
  (boundedExponentEquivSum n d).trans (Sym.equivNatSumOfFintype (Fin (n + 1)) d).symm

lemma restrictTotalDegree_finrank (K : Type) [Field K] (n d : ℕ) :
    Module.finrank K (MvPolynomial.restrictTotalDegree (Fin n) K d) = (n + d).choose n := by
  classical
  let E := {e : Fin n →₀ ℕ // e.sum (fun _ v => v) ≤ d}
  let eqv : E ≃ Sym (Fin (n + 1)) d := boundedExponentEquivSym n d
  letI : Fintype E := Fintype.ofEquiv _ eqv.symm
  calc
    Module.finrank K (MvPolynomial.restrictTotalDegree (Fin n) K d) = Fintype.card E :=
      Module.finrank_eq_card_basis (MvPolynomial.basisRestrictSupport K _)
    _ = Fintype.card (Sym (Fin (n + 1)) d) := Fintype.card_congr eqv
    _ = (n + d).choose n := by
      rw [Sym.card_sym_eq_choose]
      simp only [Fintype.card_fin]
      rw [show n + 1 + d - 1 = n + d by omega, Nat.choose_symm_add]

lemma affineEvaluation_univ_injective {K : Type} [Field K] [Infinite K] {n : ℕ} :
    Function.Injective (affineEvaluation (Set.univ : Set (Affine K n))) := by
  intro p q h
  apply MvPolynomial.funext
  intro x
  exact congrFun h ⟨x, Set.mem_univ x⟩

lemma univ_affineHilbertFunction {K : Type} [Field K] [Infinite K] (n d : ℕ) :
    affineHilbertFunction (Set.univ : Set (Affine K n)) d = (n + d).choose n := by
  unfold affineHilbertFunction
  rw [affineFilteredPiece_eq_map]
  rw [← (Submodule.equivMapOfInjective (affineEvaluation (Set.univ : Set (Affine K n)))
    affineEvaluation_univ_injective (MvPolynomial.restrictTotalDegree (Fin n) K d)).finrank_eq]
  exact restrictTotalDegree_finrank K n d

end APSCounting893.Main
end Component_4

section Component_5

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] MvPolynomial.gradedAlgebra
open MvPolynomial
namespace APSCounting893.Main

noncomputable def chartHomogeneousIdeal {K : Type} [Field K] {n : ℕ} (X : Set (Affine K n)) :
    Ideal (Polynomials K (n + 1)) :=
  Ideal.span {p | ∃ d : ℕ, p.IsHomogeneous d ∧ ∀ x ∈ X, eval (Fin.cons 1 x) p = 0}

lemma chartHomogeneousIdeal_isHomogeneous {K : Type} [Field K] {n : ℕ} (X : Set (Affine K n)) :
    (chartHomogeneousIdeal X).IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) K) := by
  apply Ideal.homogeneous_span
  rintro p ⟨d, hd, hx⟩
  exact ⟨d, hd⟩

lemma chartHomogeneousIdeal_le_vanishing {K : Type} [Field K] {n : ℕ} (X : Set (Affine K n)) :
    chartHomogeneousIdeal X ≤ vanishingIdeal K ((fun x : Affine K n => Fin.cons 1 x) '' X) := by
  apply Ideal.span_le.mpr
  rintro p ⟨d, hd, hzero⟩ y ⟨x, hx, rfl⟩
  exact hzero x hx

lemma homogeneous_mem_chartIdeal_iff {K : Type} [Field K] {n : ℕ}
    (X : Set (Affine K n)) (p : Polynomials K (n + 1)) (d : ℕ) (hd : p.IsHomogeneous d) :
    p ∈ chartHomogeneousIdeal X ↔ ∀ x ∈ X, eval (Fin.cons 1 x) p = 0 := by
  constructor
  · intro hp x hx
    exact chartHomogeneousIdeal_le_vanishing X hp (Fin.cons 1 x) ⟨x, hx, rfl⟩
  · intro hp
    exact Ideal.subset_span ⟨d, hd, hp⟩

lemma homogenizeAll_isHomogeneous {K : Type} [Field K] {n : ℕ}
    (p : Polynomials K n) (d : ℕ) (hd : p.totalDegree ≤ d) :
    (homogenizeAll d p).IsHomogeneous d := by
  classical
  apply MvPolynomial.IsHomogeneous.sum
  intro e he
  apply MvPolynomial.isHomogeneous_monomial
  rw [map_add, Finsupp.degree_single, Finsupp.degree_mapDomain, Finsupp.degree_eq_sum,
    ← finsupp_nat_sum_eq]
  exact Nat.sub_add_cancel ((MvPolynomial.le_totalDegree he).trans hd)

lemma eval_homogenize_chart {K : Type} [Field K] {n : ℕ}
    (p : Polynomials K n) (d : ℕ) (hd : p.totalDegree ≤ d) (x : Affine K n) :
    eval (Fin.cons 1 x) (homogenizeAll d p) = eval x p := by
  have hh := eval_homogenize_scaled (RingHom.id K) p d hd 1 x
  have he : (Fin.cons (α := fun _ : Fin (n + 1) => K) (1 : K) x) = (fun i : Fin (n + 1) => Fin.cases (1 : K) (fun j : Fin n => x j) i) := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i <;> simp
  rw [he]
  simpa using hh

end APSCounting893.Main
end Component_5

section Component_6

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
open MvPolynomial
namespace APSCounting893.Main

lemma evaluation_substitution {K : Type} [Field K] {n m : ℕ}
    (F : PolynomialMap K n m) (p : Polynomials K m) (x : Affine K n) :
    eval x (eval₂Hom MvPolynomial.C F p) = eval (evaluate F x) p := by
  have heq : (eval x).comp (eval₂Hom MvPolynomial.C F) = eval (evaluate F x) := by
    apply MvPolynomial.ringHom_ext
    · intro c; simp
    · intro i; simp [evaluate]
  exact RingHom.congr_fun heq p

lemma image_vanishingIdeal_eq_kernel {K : Type} [Field K] [Infinite K] {n m : ℕ}
    (F : PolynomialMap K n m) :
    vanishingIdeal K (Set.range (evaluate F)) = RingHom.ker (eval₂Hom MvPolynomial.C F) := by
  ext p
  constructor
  · intro hp
    rw [RingHom.mem_ker]
    apply MvPolynomial.funext
    intro x
    rw [evaluation_substitution]
    simpa only [map_zero, aeval_def, Algebra.algebraMap_self, eval₂_id] using
      hp (evaluate F x) (Set.mem_range_self x)
  · intro hp y hy
    obtain ⟨x, rfl⟩ := hy
    rw [RingHom.mem_ker] at hp
    rw [aeval_def, Algebra.algebraMap_self, eval₂_id, ← evaluation_substitution, hp, map_zero]

lemma hasAPS_iff_annihilator {n m : ℕ} (F : PolynomialMap ℂ n m) :
    hasAPS F ↔ ∀ p ∈ annihilator F, eval (0 : Affine ℂ m) p = 0 := by
  unfold hasAPS imageClosure RSCapacity.zClosure
  rw [image_vanishingIdeal_eq_kernel]
  rfl

lemma isAlgSet_zeroLocus {K : Type} [Field K] {n : ℕ}
    (I : Ideal (Polynomials K n)) : RSCapacity.IsAlgSet (zeroLocus K I) := by
  refine ⟨I, ?_⟩
  ext x
  simp only [mem_zeroLocus_iff, RSCapacity.zeroSet, Set.mem_setOf_eq,
    aeval_def, Algebra.algebraMap_self, eval₂_id, SetLike.mem_coe]

lemma isAlgSet_eq_zeroLocus {K : Type} [Field K] {n : ℕ}
    {X : Set (Affine K n)} (hX : RSCapacity.IsAlgSet X) :
    X = zeroLocus K (vanishingIdeal K X) := by
  apply Set.Subset.antisymm (zeroLocus_vanishingIdeal_le X)
  obtain ⟨S, rfl⟩ := hX
  intro x hx p hp
  have hv : p ∈ vanishingIdeal K (RSCapacity.zeroSet S) := by
    intro y hy
    simpa only [aeval_def, Algebra.algebraMap_self, eval₂_id] using hy p hp
  simpa only [aeval_def, Algebra.algebraMap_self, eval₂_id] using hx p hv

lemma irreducibleAffine_ideal_prime {K : Type} [Field K] {n : ℕ}
    {X : Set (Affine K n)} (hX : IrreducibleAffine X) :
    (vanishingIdeal K X).IsPrime := by
  refine ⟨?_, ?_⟩
  · intro htop
    obtain ⟨x, hx⟩ := hX.1
    have hone : (1 : Polynomials K n) ∈ vanishingIdeal K X := by rw [htop]; trivial
    have := hone x hx
    simpa using this
  · intro p q hpq
    let A := RSCapacity.zeroSet ({p} : Set (Polynomials K n))
    let B := RSCapacity.zeroSet ({q} : Set (Polynomials K n))
    have hAB : X ⊆ A ∪ B := by
      intro x hx
      have hprod : eval x p * eval x q = 0 := by
        simpa only [map_mul, aeval_def, Algebra.algebraMap_self, eval₂_id] using hpq x hx
      rcases mul_eq_zero.mp hprod with hp | hq
      · left; simpa [A, RSCapacity.zeroSet] using hp
      · right; simpa [B, RSCapacity.zeroSet] using hq
    rcases hX.2.2 A B ⟨{p}, rfl⟩ ⟨{q}, rfl⟩ hAB with hA | hB
    · left
      intro x hx
      simpa only [aeval_def, Algebra.algebraMap_self, eval₂_id] using (hA hx) p (Set.mem_singleton p)
    · right
      intro x hx
      simpa only [aeval_def, Algebra.algebraMap_self, eval₂_id] using (hB hx) q (Set.mem_singleton q)

lemma prime_ideal_irreducibleAffine {K : Type} [Field K] {n : ℕ}
    {X : Set (Affine K n)} (hne : X.Nonempty) (hclosed : RSCapacity.IsAlgSet X)
    (hprime : (vanishingIdeal K X).IsPrime) : IrreducibleAffine X := by
  classical
  refine ⟨hne, hclosed, ?_⟩
  intro A B hA hB hAB
  by_cases hXA : X ⊆ A
  · exact Or.inl hXA
  by_cases hXB : X ⊆ B
  · exact Or.inr hXB
  obtain ⟨x, hx, hxA⟩ := Set.not_subset.mp hXA
  obtain ⟨y, hy, hyB⟩ := Set.not_subset.mp hXB
  rw [isAlgSet_eq_zeroLocus hA] at hxA
  rw [isAlgSet_eq_zeroLocus hB] at hyB
  simp only [mem_zeroLocus_iff, not_forall, exists_prop] at hxA hyB
  obtain ⟨p, hpA, hpx⟩ := hxA
  obtain ⟨q, hqB, hqy⟩ := hyB
  have hpq : p * q ∈ vanishingIdeal K X := by
    intro z hz
    rcases hAB hz with hzA | hzB
    · simp only [map_mul, hpA z hzA, zero_mul]
    · simp only [map_mul, hqB z hzB, mul_zero]
  rcases hprime.mem_or_mem hpq with hpX | hqX
  · exact (hpx (hpX x hx)).elim
  · exact (hqy (hqX y hy)).elim

lemma vanishingIdeal_zClosure {K : Type} [Field K] {n : ℕ} (X : Set (Affine K n)) :
    vanishingIdeal K (RSCapacity.zClosure X) = vanishingIdeal K X := by
  apply le_antisymm
  · exact vanishingIdeal_anti_mono (zeroLocus_vanishingIdeal_le X)
  · intro p hp x hx
    exact hx p hp

lemma irreducibleAffine_imageClosure {K : Type} [Field K] [Infinite K] {n m : ℕ}
    (F : PolynomialMap K n m) : IrreducibleAffine (imageClosure F) := by
  apply prime_ideal_irreducibleAffine
  · exact ⟨evaluate F 0, zeroLocus_vanishingIdeal_le _ (Set.mem_range_self 0)⟩
  · exact isAlgSet_zeroLocus _
  · unfold imageClosure
    rw [vanishingIdeal_zClosure, image_vanishingIdeal_eq_kernel]
    exact RingHom.ker_isPrime _

noncomputable def coordinatePullback {K : Type} [Field K] {n m : ℕ}
    (X : Set (Affine K n)) (F : PolynomialMap K n m) :
    Polynomials K m →+* CoordinateRing X :=
  (Ideal.Quotient.mk (vanishingIdeal K X)).comp (eval₂Hom MvPolynomial.C F)

noncomputable def coordinatePullbackAlgebra {K : Type} [Field K] {n m : ℕ}
    (X : Set (Affine K n)) (F : PolynomialMap K n m) :
    Algebra (Polynomials K m) (CoordinateRing X) := (coordinatePullback X F).toAlgebra

lemma finiteMorphism_module_finite {K : Type} [Field K] {n m : ℕ}
    (X : Set (Affine K n)) (F : PolynomialMap K n m) (hfinite : FiniteMorphism X F) :
    letI : Algebra (Polynomials K m) (CoordinateRing X) := coordinatePullbackAlgebra X F
    Module.Finite (Polynomials K m) (CoordinateRing X) := by
  classical
  letI : Algebra (Polynomials K m) (CoordinateRing X) := coordinatePullbackAlgebra X F
  have halg : algebraMap (Polynomials K m) (CoordinateRing X) = coordinatePullback X F := rfl
  obtain ⟨s, generators, hgen⟩ := hfinite
  let g : Fin s → CoordinateRing X := fun i => Ideal.Quotient.mk _ (generators i)
  rw [Module.finite_def, Submodule.fg_def]
  refine ⟨Set.range g, Set.finite_range g, ?_⟩
  rw [Submodule.eq_top_iff']
  intro b
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective b
  obtain ⟨coefficients, hcoeff⟩ := hgen p
  have hz : p - ∑ i : Fin s, (eval₂Hom MvPolynomial.C F (coefficients i)) * generators i ∈
      vanishingIdeal K X := by
    intro x hx
    simp only [aeval_def, Algebra.algebraMap_self, eval₂_id, map_sub, map_sum, map_mul,
      evaluation_substitution, sub_eq_zero]
    exact hcoeff x hx
  have heq : Ideal.Quotient.mk (vanishingIdeal K X) p =
      ∑ i : Fin s, coefficients i • g i := by
    apply sub_eq_zero.mp
    have h := (Ideal.Quotient.eq_zero_iff_mem).mpr hz
    simpa only [map_sub, map_sum, map_mul, Algebra.smul_def,
      halg, coordinatePullback, RingHom.comp_apply, g] using h
  rw [heq]
  apply Submodule.sum_mem
  intro i _
  exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self i))

lemma coordinatePullback_injective_of_dominant {K : Type} [Field K] [Infinite K] {n m : ℕ}
    (X : Set (Affine K n)) (F : PolynomialMap K n m)
    (hdom : RSCapacity.zClosure (evaluate F '' X) = Set.univ) :
    Function.Injective (coordinatePullback X F) := by
  rw [RingHom.injective_iff_ker_eq_bot]
  apply le_antisymm ?_ bot_le
  intro p hp
  have hz : eval₂Hom MvPolynomial.C F p ∈ vanishingIdeal K X :=
    Ideal.Quotient.eq_zero_iff_mem.mp hp
  have hpI : p ∈ vanishingIdeal K (evaluate F '' X) := by
    rintro y ⟨x, hx, rfl⟩
    simpa only [aeval_def, Algebra.algebraMap_self, eval₂_id, evaluation_substitution] using hz x hx
  rw [Ideal.mem_bot]
  apply MvPolynomial.funext
  intro y
  have hy : y ∈ RSCapacity.zClosure (evaluate F '' X) := by rw [hdom]; trivial
  simpa only [aeval_def, Algebra.algebraMap_self, eval₂_id, map_zero] using hy p hpI

noncomputable def hahnValuationRing : ValuationSubring PuiseuxAmbient :=
  (AddValuation.toValuation (HahnSeries.addVal ℚ ℂ)).valuationSubring

lemma constant_in_hahnValuationRing (c : ℂ) : HahnSeries.C c ∈ hahnValuationRing := by
  change 0 ≤ (HahnSeries.single (0 : ℚ) c).orderTop
  exact HahnSeries.orderTop_single_le

lemma positive_series_relation {m : ℕ} (p : Polynomials ℂ m)
    (y : Affine PuiseuxAmbient m) (hy : ∀ i, 0 < (y i).orderTop)
    (hrel : MvPolynomial.eval₂ HahnSeries.C y p = 0) :
    eval (0 : Affine ℂ m) p = 0 := by
  classical
  let V := hahnValuationRing
  let c0 : ℂ →+* V :=
    { toFun := fun c => ⟨HahnSeries.C c, constant_in_hahnValuationRing c⟩
      map_zero' := Subtype.ext (HahnSeries.C.map_zero)
      map_one' := Subtype.ext (HahnSeries.C.map_one)
      map_add' := fun a b => Subtype.ext (HahnSeries.C.map_add a b)
      map_mul' := fun a b => Subtype.ext (HahnSeries.C.map_mul a b) }
  let z : Fin m → V := fun i => ⟨y i, le_of_lt (hy i)⟩
  have hz : MvPolynomial.eval₂ c0 z p = 0 := by
    apply Subtype.val_injective
    change V.subtype (MvPolynomial.eval₂ c0 z p) = 0
    rw [MvPolynomial.hom_eval₂]
    exact hrel
  let res := IsLocalRing.residue V
  have hzi (i : Fin m) : res (z i) = 0 := by
    apply (IsLocalRing.residue_eq_zero_iff _).mpr
    apply (Valuation.mem_maximalIdeal_iff (v := AddValuation.toValuation (HahnSeries.addVal ℚ ℂ))).mpr
    exact hy i
  let phi : ℂ →+* IsLocalRing.ResidueField V := res.comp c0
  have heq : MvPolynomial.eval₂ phi (fun _ : Fin m => 0) p = 0 := by
    have h := congrArg res hz
    rw [MvPolynomial.hom_eval₂] at h
    simpa only [hzi, map_zero] using h
  apply phi.injective
  rw [map_zero]
  have hmap : phi (eval (0 : Affine ℂ m) p) = MvPolynomial.eval₂ phi (fun _ : Fin m => 0) p := by
    simpa only [RingHom.comp_id, Pi.zero_apply, map_zero, eval₂_id] using
      (MvPolynomial.hom_eval₂ p (RingHom.id ℂ) phi (0 : Affine ℂ m))
  exact hmap.trans heq

lemma approximateVanishing_implies_hasAPS {n m : ℕ} (F : PolynomialMap ℂ n m)
    (hF : (approximateVanishing F).Nonempty) : hasAPS F := by
  rw [hasAPS_iff_annihilator]
  obtain ⟨x, hx⟩ := hF
  intro p hp
  apply positive_series_relation p (fun j => MvPolynomial.eval₂ HahnSeries.C x (F j)) hx.2
  have heq : (MvPolynomial.eval₂Hom HahnSeries.C x).comp (MvPolynomial.eval₂Hom MvPolynomial.C F) =
      MvPolynomial.eval₂Hom HahnSeries.C (fun j => MvPolynomial.eval₂ HahnSeries.C x (F j)) := by
    apply MvPolynomial.ringHom_ext
    · intro c; simp
    · intro j; simp
  have hp0 : MvPolynomial.eval₂Hom MvPolynomial.C F p = 0 := hp
  have h := RingHom.congr_fun heq p
  rw [RingHom.comp_apply, hp0, map_zero] at h
  exact h.symm

end APSCounting893.Main
end Component_6

section Component_7
set_option autoImplicit false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency.types false
open MvPolynomial
namespace APSCounting893.Main

noncomputable def scaledChart {K : Type} [Field K] {n : ℕ} (Y : Set (Affine K n)) : Set (Affine K (n+1)) :=
  {z | ∃ a : K, ∃ y ∈ Y, z = fun j => a * (Fin.cons 1 y : Fin (n+1) → K) j}

noncomputable def projectiveCone {K : Type} [Field K] {n : ℕ} (Y : Set (Affine K n)) : Set (Affine K (n+1)) :=
  zeroLocus K (chartHomogeneousIdeal Y)

lemma chartHomogeneousIdeal_eq_scaledChart_vanishing {K : Type} [Field K] [Infinite K] {n : ℕ}
    (Y : Set (Affine K n)) : chartHomogeneousIdeal Y = vanishingIdeal K (scaledChart Y) := by
  classical
  apply le_antisymm
  · apply Ideal.span_le.mpr
    rintro p ⟨d,hd,hp⟩ z ⟨a,y,hy,rfl⟩
    have hh := homogeneous_eval₂_scaled p d hd (RingHom.id K) a (Fin.cons 1 y)
    simpa only [MvPolynomial.eval₂_id,hp y hy,mul_zero,aeval_def,Algebra.algebraMap_self] using hh
  · intro p hp
    rw [← MvPolynomial.sum_homogeneousComponent p]
    apply Ideal.sum_mem
    intro d hd
    apply Ideal.subset_span
    refine ⟨d,homogeneousComponent_isHomogeneous d p,?_⟩
    intro y hy
    apply eval_homogeneousComponent_zero_of_scaled_zero p (Fin.cons 1 y)
    intro a
    exact hp _ ⟨a,y,hy,rfl⟩

lemma projectiveCone_eq_closure_scaledChart {K : Type} [Field K] [Infinite K] {n : ℕ}
    (Y : Set (Affine K n)) : projectiveCone Y = RSCapacity.zClosure (scaledChart Y) := by
  rw [projectiveCone,chartHomogeneousIdeal_eq_scaledChart_vanishing]
  rfl

lemma projectiveCone_chart_iff {K : Type} [Field K] {n : ℕ}
    (Y : Set (Affine K n)) (hY : RSCapacity.IsAlgSet Y) (y : Affine K n) :
    Fin.cons 1 y ∈ projectiveCone Y ↔ y ∈ Y := by
  constructor
  · intro hy
    rw [isAlgSet_eq_zeroLocus hY]
    intro p hp
    have hm : homogenizeAll p.totalDegree p ∈ chartHomogeneousIdeal Y := by
      apply Ideal.subset_span
      refine ⟨p.totalDegree,homogenizeAll_isHomogeneous p p.totalDegree le_rfl,?_⟩
      intro x hx
      rw [eval_homogenize_chart p p.totalDegree le_rfl]
      exact hp x hx
    have hh := hy _ hm
    simp only [aeval_def,Algebra.algebraMap_self,eval₂_id] at hh ⊢
    rwa [eval_homogenize_chart p p.totalDegree le_rfl] at hh
  · intro hy p hp
    exact chartHomogeneousIdeal_le_vanishing Y hp _ ⟨y,hy,rfl⟩

lemma scaledChart_subset_projectiveCone {K : Type} [Field K] [Infinite K] {n : ℕ}
    (Y : Set (Affine K n)) : scaledChart Y ⊆ projectiveCone Y := by
  rw [projectiveCone_eq_closure_scaledChart]
  exact zeroLocus_vanishingIdeal_le _

lemma projectiveCone_scale {K : Type} [Field K] [Infinite K] {n : ℕ}
    (Y : Set (Affine K n)) (z : Affine K (n+1)) (hz : z ∈ projectiveCone Y) (a : K) :
    (fun j => a*z j) ∈ projectiveCone Y := by
  have hle : chartHomogeneousIdeal Y ≤ RingHom.ker (eval (fun j => a*z j)) := by
    apply Ideal.span_le.mpr
    rintro p ⟨d,hd,hp⟩
    have hm : p ∈ chartHomogeneousIdeal Y := Ideal.subset_span ⟨d,hd,hp⟩
    have hh := homogeneous_eval₂_scaled p d hd (RingHom.id K) a z
    change eval (fun j => a*z j) p = 0
    have hz' : eval z p = 0 := by
      simpa only [aeval_def,Algebra.algebraMap_self,eval₂_id] using hz p hm
    simpa only [MvPolynomial.eval₂_id,hz',mul_zero] using hh
  intro p hp
  exact hle hp

end APSCounting893.Main
end Component_7

section Component_8
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
open MvPolynomial
namespace APSCounting893.Main

noncomputable def composePolynomialMap {K : Type} [Field K] {n m r : ℕ}
    (F : PolynomialMap K n m) (G : PolynomialMap K m r) : PolynomialMap K n r :=
  fun j => MvPolynomial.eval₂Hom MvPolynomial.C F (G j)

lemma evaluate_composePolynomialMap {K : Type} [Field K] {n m r : ℕ}
    (F : PolynomialMap K n m) (G : PolynomialMap K m r) (x : Affine K n) :
    evaluate (composePolynomialMap F G) x = evaluate G (evaluate F x) := by
  funext j
  exact evaluation_substitution F (G j) x

end APSCounting893.Main
end Component_8

section Component_9
set_option autoImplicit false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency.types false
open MvPolynomial
namespace APSCounting893.Main

noncomputable def conePolynomialMap {K : Type} [Field K] {n m : ℕ}
    (F : PolynomialMap K n m) : PolynomialMap K (n+1) (m+1) :=
  Fin.cons (MvPolynomial.X 0) (fun i => MvPolynomial.X 0 * MvPolynomial.rename Fin.succ (F i))

lemma conePolynomialMap_eval {K : Type} [Field K] {n m : ℕ}
    (F : PolynomialMap K n m) (a : K) (x : Affine K n) :
    evaluate (conePolynomialMap F) (Fin.cons a x) = fun j => a * (Fin.cons 1 (evaluate F x) : Fin (m+1) → K) j := by
  funext j
  refine Fin.cases ?_ (fun j => ?_) j
  · simp [evaluate,conePolynomialMap]
  · simp [evaluate,conePolynomialMap,MvPolynomial.eval_rename,Function.comp_def]

lemma scaledChart_range_eq_conePolynomialMap_range {K : Type} [Field K] {n m : ℕ}
    (F : PolynomialMap K n m) : scaledChart (Set.range (evaluate F)) = Set.range (evaluate (conePolynomialMap F)) := by
  ext z
  constructor
  · rintro ⟨a,y,⟨x,rfl⟩,rfl⟩
    exact ⟨Fin.cons a x,conePolynomialMap_eval F a x⟩
  · rintro ⟨x,rfl⟩
    refine ⟨x 0,evaluate F (fun i => x i.succ),Set.mem_range_self _,?_⟩
    have hx : Fin.cons (x 0) (fun i => x i.succ) = x := by
      funext i
      refine Fin.cases ?_ (fun j => ?_) i <;> simp
    rw [← conePolynomialMap_eval,hx]

lemma scaledChart_closure_vanishing {K : Type} [Field K] {n m : ℕ}
    (F : PolynomialMap K n m) :
    vanishingIdeal K (scaledChart (imageClosure F)) = vanishingIdeal K (scaledChart (Set.range (evaluate F))) := by
  apply le_antisymm
  · apply vanishingIdeal_anti_mono
    rintro z ⟨a,y,hy,rfl⟩
    exact ⟨a,y,zeroLocus_vanishingIdeal_le _ hy,rfl⟩
  · intro p hp z
    rintro ⟨a,y,hy,rfl⟩
    let P : PolynomialMap K m (m+1) := Fin.cons (MvPolynomial.C a)
      (fun j => MvPolynomial.C a * MvPolynomial.X j)
    have hP (y : Affine K m) : evaluate P y = fun j => a*(Fin.cons 1 y : Fin (m+1) → K) j := by
      funext j
      refine Fin.cases ?_ (fun j => ?_) j <;> simp [P,evaluate]
    have hvan : MvPolynomial.aeval P p ∈ vanishingIdeal K (Set.range (evaluate F)) := by
      intro y hy
      have hh := hp _ (show (fun j => a*(Fin.cons 1 y : Fin (m+1) → K) j) ∈ scaledChart (Set.range (evaluate F)) from ⟨a,y,hy,rfl⟩)
      rw [← hP] at hh
      exact (evaluation_substitution P p y).trans hh
    have hh := hy _ hvan
    rw [← hP]
    exact (evaluation_substitution P p y).symm.trans hh

lemma projectiveCone_imageClosure {K : Type} [Field K] [Infinite K] {n m : ℕ}
    (F : PolynomialMap K n m) : projectiveCone (imageClosure F) = imageClosure (conePolynomialMap F) := by
  rw [projectiveCone,chartHomogeneousIdeal_eq_scaledChart_vanishing,scaledChart_closure_vanishing,
    scaledChart_range_eq_conePolynomialMap_range]
  rfl

lemma projectiveCone_image_irreducible {K : Type} [Field K] [Infinite K] {n m : ℕ}
    (F : PolynomialMap K n m) : IrreducibleAffine (projectiveCone (imageClosure F)) := by
  rw [projectiveCone_imageClosure]
  exact irreducibleAffine_imageClosure _

end APSCounting893.Main
end Component_9

section Component_10
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
open MvPolynomial
namespace APSCounting893.Main

lemma imageClosure_vanishingIdeal_eq_kernel {K : Type} [Field K] [Infinite K] {n m : ℕ}
    (F : PolynomialMap K n m) :
    vanishingIdeal K (imageClosure F) = RingHom.ker (MvPolynomial.aeval F).toRingHom := by
  rw [imageClosure,vanishingIdeal_zClosure,image_vanishingIdeal_eq_kernel]
  rfl

noncomputable def imageCoordinateAlgebraMap {K : Type} [Field K] [Infinite K] {n m : ℕ}
    (F : PolynomialMap K n m) : CoordinateRing (imageClosure F) →ₐ[K] MvPolynomial (Fin n) K :=
  Ideal.Quotient.liftₐ _ (MvPolynomial.aeval F) (fun p hp => by
    rw [imageClosure_vanishingIdeal_eq_kernel] at hp
    exact hp)

lemma imageCoordinateAlgebraMap_mk {K : Type} [Field K] [Infinite K] {n m : ℕ}
    (F : PolynomialMap K n m) (p : Polynomials K m) :
    imageCoordinateAlgebraMap F (Ideal.Quotient.mk (vanishingIdeal K (imageClosure F)) p) =
      MvPolynomial.aeval F p := rfl

lemma imageCoordinateAlgebraMap_injective {K : Type} [Field K] [Infinite K] {n m : ℕ}
    (F : PolynomialMap K n m) : Function.Injective (imageCoordinateAlgebraMap F) := by
  apply (injective_iff_map_eq_zero (imageCoordinateAlgebraMap F).toRingHom).mpr
  intro x hx
  obtain ⟨p,rfl⟩ := Ideal.Quotient.mk_surjective x
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  rw [imageClosure_vanishingIdeal_eq_kernel]
  change MvPolynomial.aeval F p = 0
  change imageCoordinateAlgebraMap F (Ideal.Quotient.mk _ p) = 0 at hx
  rw [imageCoordinateAlgebraMap_mk] at hx
  exact hx

lemma imageCoordinateAlgebraMap_coordinate {K : Type} [Field K] [Infinite K] {n m : ℕ}
    (F : PolynomialMap K n m) (j : Fin m) :
    imageCoordinateAlgebraMap F (coordinate (imageClosure F) j) = F j := by
  change imageCoordinateAlgebraMap F (Ideal.Quotient.mk _ (MvPolynomial.X j)) = F j
  rw [imageCoordinateAlgebraMap_mk,MvPolynomial.aeval_X]

end APSCounting893.Main
end Component_10

section Component_11
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 100000
set_option maxSynthPendingDepth 5
set_option backward.isDefEq.respectTransparency.types false
open MvPolynomial
namespace APSCounting893.Main

lemma prime_quotient_dimension_lower_of_independent {m r : ℕ}
    (P : Ideal (MvPolynomial (Fin (m+1)) ℂ)) [P.IsPrime]
    (v : Fin r → MvPolynomial (Fin (m+1)) ℂ ⧸ P) (hv : AlgebraicIndependent ℂ v) :
    ((r : ℕ∞) : WithBot ℕ∞) ≤ ringKrullDim (MvPolynomial (Fin (m+1)) ℂ ⧸ P) := by
  classical
  let A := MvPolynomial (Fin (m+1)) ℂ ⧸ P
  let L := FractionRing A
  letI : Algebra.EssFiniteType A L := Algebra.EssFiniteType.of_isLocalization L (nonZeroDivisors A)
  letI : Algebra.EssFiniteType ℂ L := Algebra.EssFiniteType.comp ℂ A L
  let f : A →ₐ[ℂ] L := IsScalarTower.toAlgHom ℂ A L
  have hfield := hv.map' (f := f) (IsFractionRing.injective A L)
  have hcard := hfield.cardinalMk_le_trdeg
  have hfinite := trdeg_lt_aleph0 ℂ L
  have hnat := Cardinal.toNat_le_toNat hcard hfinite
  have hn : r ≤ (Algebra.trdeg ℂ L).toNat := by simpa using hnat
  rw [OAI.PiExponent.FormalInterpolation.mvPolynomial_quotient_dimension_eq_fraction_field_trdeg_toNat P]
  exact_mod_cast hn

end APSCounting893.Main
end Component_11

section Component_12
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 100000
set_option maxSynthPendingDepth 5
set_option backward.isDefEq.respectTransparency.types false
open MvPolynomial
namespace APSCounting893.Main

lemma prime_quotient_dimension_mono {m n : ℕ}
    (P : Ideal (MvPolynomial (Fin (m+1)) ℂ)) [P.IsPrime]
    (Q : Ideal (MvPolynomial (Fin (n+1)) ℂ)) [Q.IsPrime]
    (f : (MvPolynomial (Fin (m+1)) ℂ ⧸ P) →ₐ[ℂ] (MvPolynomial (Fin (n+1)) ℂ ⧸ Q))
    (hf : Function.Injective f) :
    ringKrullDim (MvPolynomial (Fin (m+1)) ℂ ⧸ P) ≤ ringKrullDim (MvPolynomial (Fin (n+1)) ℂ ⧸ Q) := by
  classical
  let A := MvPolynomial (Fin (m+1)) ℂ ⧸ P
  let B := MvPolynomial (Fin (n+1)) ℂ ⧸ Q
  let L := FractionRing A
  let M := FractionRing B
  let g : A →ₐ[ℂ] M := (IsScalarTower.toAlgHom ℂ B M).comp f
  have hg : Function.Injective g := (IsFractionRing.injective B M).comp hf
  let h : L →ₐ[ℂ] M := IsFractionRing.liftAlgHom hg
  have hh := trdeg_le_of_injective h h.injective
  letI : Algebra.EssFiniteType B M := Algebra.EssFiniteType.of_isLocalization M (nonZeroDivisors B)
  letI : Algebra.EssFiniteType ℂ M := Algebra.EssFiniteType.comp ℂ B M
  have hnat := Cardinal.toNat_le_toNat hh (trdeg_lt_aleph0 ℂ M)
  rw [OAI.PiExponent.FormalInterpolation.mvPolynomial_quotient_dimension_eq_fraction_field_trdeg_toNat P,
    OAI.PiExponent.FormalInterpolation.mvPolynomial_quotient_dimension_eq_fraction_field_trdeg_toNat Q]
  exact_mod_cast hnat

end APSCounting893.Main
end Component_12

section Component_13
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
open MvPolynomial
namespace APSCounting893.Main

lemma aeval_composePolynomialMap {K : Type} [Field K] {n m t : ℕ}
    (F : PolynomialMap K n m) (P : PolynomialMap K m t) (p : Polynomials K t) :
    MvPolynomial.aeval F (MvPolynomial.aeval P p) = MvPolynomial.aeval (composePolynomialMap F P) p := by
  have hh : composePolynomialMap F P = fun i => MvPolynomial.aeval F (P i) := by
    funext i
    simp only [composePolynomialMap,aeval_def,MvPolynomial.algebraMap_eq]
    rfl
  rw [hh]
  exact MvPolynomial.comp_aeval_apply P (MvPolynomial.aeval F) p

noncomputable def polynomialImageCoordinateMap {K : Type} [Field K] [Infinite K] {n m t : ℕ}
    (F : PolynomialMap K n m) (P : PolynomialMap K m t) :
    CoordinateRing (imageClosure (composePolynomialMap F P)) →ₐ[K] CoordinateRing (imageClosure F) :=
  Ideal.Quotient.liftₐ _ ((Ideal.Quotient.mkₐ K _).comp (MvPolynomial.aeval P)) (by
    intro p hp
    change Ideal.Quotient.mk (vanishingIdeal K (imageClosure F)) (MvPolynomial.aeval P p) = 0
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    rw [imageClosure_vanishingIdeal_eq_kernel]
    change MvPolynomial.aeval F (MvPolynomial.aeval P p) = 0
    rw [aeval_composePolynomialMap]
    rw [imageClosure_vanishingIdeal_eq_kernel] at hp
    exact hp)

lemma polynomialImageCoordinateMap_injective {K : Type} [Field K] [Infinite K] {n m t : ℕ}
    (F : PolynomialMap K n m) (P : PolynomialMap K m t) :
    Function.Injective (polynomialImageCoordinateMap F P) := by
  apply (injective_iff_map_eq_zero (polynomialImageCoordinateMap F P).toRingHom).mpr
  intro x hx
  obtain ⟨p,rfl⟩ := Ideal.Quotient.mk_surjective x
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  rw [imageClosure_vanishingIdeal_eq_kernel]
  change MvPolynomial.aeval (composePolynomialMap F P) p = 0
  rw [← aeval_composePolynomialMap]
  have hh : Ideal.Quotient.mk (vanishingIdeal K (imageClosure F)) (MvPolynomial.aeval P p) = 0 := hx
  have hm := Ideal.Quotient.eq_zero_iff_mem.mp hh
  rw [imageClosure_vanishingIdeal_eq_kernel] at hm
  exact hm

lemma image_dimension_compose_le {n m t : ℕ}
    (F : PolynomialMap ℂ n (m+1)) (P : PolynomialMap ℂ (m+1) (t+1)) :
    RSCapacity.algDim (imageClosure (composePolynomialMap F P)) ≤ RSCapacity.algDim (imageClosure F) := by
  let I := vanishingIdeal ℂ (imageClosure (composePolynomialMap F P))
  let J := vanishingIdeal ℂ (imageClosure F)
  letI : I.IsPrime := irreducibleAffine_ideal_prime (irreducibleAffine_imageClosure _)
  letI : J.IsPrime := irreducibleAffine_ideal_prime (irreducibleAffine_imageClosure _)
  exact prime_quotient_dimension_mono I J (polynomialImageCoordinateMap F P) (polynomialImageCoordinateMap_injective F P)

lemma polynomialImage_maps_closure {K : Type} [Field K] {n m t : ℕ}
    (F : PolynomialMap K n m) (P : PolynomialMap K m t) :
    evaluate P '' imageClosure F ⊆ imageClosure (composePolynomialMap F P) := by
  rintro y ⟨x,hx,rfl⟩ p hp
  have hvan : MvPolynomial.aeval P p ∈ vanishingIdeal K (Set.range (evaluate F)) := by
    intro z hz
    obtain ⟨u,rfl⟩ := hz
    have hh := hp (evaluate (composePolynomialMap F P) u) (Set.mem_range_self u)
    rw [evaluate_composePolynomialMap] at hh
    exact (evaluation_substitution P p (evaluate F u)).trans hh
  have hh := hx (MvPolynomial.aeval P p) hvan
  exact (evaluation_substitution P p x).symm.trans hh

end APSCounting893.Main
end Component_13

section Component_14
set_option autoImplicit false
set_option maxHeartbeats 500000
set_option backward.isDefEq.respectTransparency.types false
open MvPolynomial
namespace APSCounting893.Main

lemma cone_output_nonzero_of_origin_excluded {K : Type} [Field K] [Infinite K] {m : ℕ}
    (Y : Set (Affine K m)) (hY : RSCapacity.IsAlgSet Y) (h0 : (0 : Affine K m) ∉ Y)
    (z : Affine K (m+1)) (hz : z ∈ projectiveCone Y) (hne : z ≠ 0) :
    (fun j : Fin m => z j.succ) ≠ 0 := by
  intro hout
  have hz0 : z 0 ≠ 0 := by
    intro hz0
    apply hne
    funext j
    refine Fin.cases ?_ (fun j => ?_) j
    · exact hz0
    · exact congrFun hout j
  have hscaled := projectiveCone_scale Y z hz (z 0)⁻¹
  have hpoint : (fun j => (z 0)⁻¹*z j) = (Fin.cons 1 (0 : Affine K m) : Affine K (m+1)) := by
    funext j
    refine Fin.cases ?_ (fun j => ?_) j
    · simp [hz0]
    · simp [congrFun hout j]
  rw [hpoint] at hscaled
  exact h0 ((projectiveCone_chart_iff Y hY 0).mp hscaled)

end APSCounting893.Main
end Component_14

section Component_15
set_option autoImplicit false
set_option maxHeartbeats 500000
set_option backward.isDefEq.respectTransparency.types false
open MvPolynomial
namespace APSCounting893.Main

noncomputable def outputConePolynomialMap {K : Type} [Field K] {n m : ℕ}
    (F : PolynomialMap K n m) : PolynomialMap K (n+1) m :=
  fun i => MvPolynomial.X 0 * MvPolynomial.rename Fin.succ (F i)

noncomputable def coneOutputCoordinates {K : Type} [Field K] (m : ℕ) : PolynomialMap K (m+1) m :=
  fun i => MvPolynomial.X i.succ

lemma coneOutputCoordinates_evaluate {K : Type} [Field K] {m : ℕ} (z : Affine K (m+1)) :
    evaluate (coneOutputCoordinates m) z = fun i => z i.succ := by
  funext i
  simp [evaluate,coneOutputCoordinates]

lemma outputConePolynomialMap_eq_compose {K : Type} [Field K] {n m : ℕ}
    (F : PolynomialMap K n m) : composePolynomialMap (conePolynomialMap F) (coneOutputCoordinates m) =
      outputConePolynomialMap F := by
  funext i
  simp [composePolynomialMap,coneOutputCoordinates,conePolynomialMap,outputConePolynomialMap]

lemma outputConePolynomialMap_eval {K : Type} [Field K] {n m : ℕ}
    (F : PolynomialMap K n m) (a : K) (x : Affine K n) :
    evaluate (outputConePolynomialMap F) (Fin.cons a x) = fun j => a*evaluate F x j := by
  funext i
  simp [outputConePolynomialMap,evaluate,MvPolynomial.eval_rename,Function.comp_def]

lemma cone_output_mem_outputConeClosure {K : Type} [Field K] [Infinite K] {n m : ℕ}
    (F : PolynomialMap K n m) (z : Affine K (m+1)) (hz : z ∈ projectiveCone (imageClosure F)) :
    (fun i => z i.succ) ∈ imageClosure (outputConePolynomialMap F) := by
  rw [projectiveCone_imageClosure] at hz
  have hh := polynomialImage_maps_closure (conePolynomialMap F) (coneOutputCoordinates m)
    ⟨z,hz,rfl⟩
  rw [outputConePolynomialMap_eq_compose,coneOutputCoordinates_evaluate] at hh
  exact hh

lemma outputConeClosure_coordinate_nonzero {K : Type} [Field K] [Infinite K] {n m : ℕ}
    (F : PolynomialMap K n m) (j : Fin m) (hF : F j ≠ 0) :
    ∃ y ∈ imageClosure (outputConePolynomialMap F), y j ≠ 0 := by
  have hex : ∃ x : Affine K n, eval x (F j) ≠ 0 := by
    by_contra h
    push Not at h
    apply hF
    apply MvPolynomial.funext
    intro x
    simpa only [map_zero] using h x
  obtain ⟨x,hx⟩ := hex
  refine ⟨evaluate F x,?_,hx⟩
  apply zeroLocus_vanishingIdeal_le _
  refine ⟨Fin.cons 1 x,?_⟩
  simpa only [one_mul] using outputConePolynomialMap_eval F 1 x

end APSCounting893.Main
end Component_15

section Component_16
set_option autoImplicit false
set_option maxHeartbeats 500000
open MvPolynomial
namespace APSCounting893.Main

noncomputable def incidenceMatrixAt {K : Type} [Field K] {m r : ℕ}
    (j : Fin m) (z : Fin m → K) (B : Fin r × Fin m → K) : Fin r × Fin m → K :=
  fun a => z j * B a - (∑ t : Fin m, z t * B (a.1,t)) * (if a.2=j then 1 else 0)

lemma incidenceMatrixAt_annihilates {K : Type} [Field K] {m r : ℕ}
    (j : Fin m) (z : Fin m → K) (B : Fin r × Fin m → K) (i : Fin r) :
    ∑ l : Fin m, incidenceMatrixAt j z B (i,l) * z l = 0 := by
  classical
  simp only [incidenceMatrixAt,sub_mul,Finset.sum_sub_distrib,mul_assoc,← Finset.mul_sum,
    ite_mul,one_mul,zero_mul]
  rw [Finset.sum_ite_eq']
  simp only [Finset.mem_univ,ite_true]
  have hh : (∑ x : Fin m, B (i,x)*z x) = ∑ x : Fin m, z x*B (i,x) := by
    apply Finset.sum_congr rfl
    intro x hx
    exact mul_comm _ _
  rw [hh,mul_comm,sub_self]

lemma incidenceMatrixAt_recover {K : Type} [Field K] {m r : ℕ}
    (j : Fin m) (z : Fin m → K) (hj : z j ≠ 0) (A : Fin r × Fin m → K)
    (hA : ∀ i, ∑ l : Fin m, A (i,l)*z l=0) :
    incidenceMatrixAt j z (fun a => A a / z j) = A := by
  classical
  have hsum (i : Fin r) : (∑ t : Fin m, z t*(A (i,t)/z j)) = 0 := by
    simp only [← mul_div_assoc,← Finset.sum_div]
    have hh : (∑ t : Fin m, z t*A (i,t)) = ∑ t : Fin m, A (i,t)*z t := by
      apply Finset.sum_congr rfl
      intro t ht
      exact mul_comm _ _
    rw [hh,hA,zero_div]
  funext a
  simp only [incidenceMatrixAt,hsum,zero_mul,sub_zero]
  field_simp

noncomputable def incidencePointPolynomials {K : Type} [Field K] {m r : ℕ}
    (j : Fin m) (B : Fin r × Fin m → K) : Fin r × Fin m → MvPolynomial (Fin m) K :=
  fun a => MvPolynomial.C (B a) * MvPolynomial.X j -
    (∑ t : Fin m, MvPolynomial.C (B (a.1,t))*MvPolynomial.X t) * (if a.2=j then 1 else 0)

lemma incidencePointPolynomials_eval {K : Type} [Field K] {m r : ℕ}
    (j : Fin m) (B : Fin r × Fin m → K) (z : Fin m → K) :
    (fun a => eval z (incidencePointPolynomials j B a)) = incidenceMatrixAt j z B := by
  classical
  funext a
  by_cases ha : a.2=j <;> simp [incidencePointPolynomials,incidenceMatrixAt,ha,mul_comm]

end APSCounting893.Main
end Component_16

section Component_17
set_option autoImplicit false
set_option maxHeartbeats 400000
open MvPolynomial
namespace APSCounting893.Main

lemma vanishes_on_irreducible_of_vanishes_off_hyperplane {K : Type} [Field K] {m : ℕ}
    (Y : Set (Affine K m)) (hY : IrreducibleAffine Y) (j : Fin m)
    (hj : ∃ z ∈ Y, z j ≠ 0) (p : Polynomials K m)
    (hp : ∀ z ∈ Y, z j ≠ 0 → eval z p = 0) : p ∈ vanishingIdeal K Y := by
  have hprime := irreducibleAffine_ideal_prime hY
  have hX : (MvPolynomial.X j : Polynomials K m) ∉ vanishingIdeal K Y := by
    intro hh
    obtain ⟨z,hz,hzj⟩ := hj
    apply hzj
    simpa using hh z hz
  have hprod : MvPolynomial.X j*p ∈ vanishingIdeal K Y := by
    intro z hz
    simp only [MvPolynomial.aeval_def,Algebra.algebraMap_self,MvPolynomial.eval₂_id,map_mul,MvPolynomial.eval_X]
    by_cases hh : z j=0
    · rw [hh,zero_mul]
    · rw [hp z hz hh,mul_zero]
  exact (hprime.mem_or_mem hprod).resolve_left hX

end APSCounting893.Main
end Component_17

section Component_18
set_option autoImplicit false
set_option maxHeartbeats 500000
set_option backward.isDefEq.respectTransparency.types false
open MvPolynomial
namespace APSCounting893.Main

lemma eval_incidencePointSubstitution {K : Type} [Field K] {m r : ℕ}
    (q : MvPolynomial (Fin r × Fin m) K) (j : Fin m) (B : Fin r × Fin m → K) (z : Fin m → K) :
    eval z (MvPolynomial.aeval (incidencePointPolynomials j B) q) = eval (incidenceMatrixAt j z B) q := by
  have hh := MvPolynomial.comp_aeval_apply (incidencePointPolynomials j B) (MvPolynomial.aeval (R := K) z) q
  have hf : (fun a => MvPolynomial.aeval (R := K) z (incidencePointPolynomials j B a)) = incidenceMatrixAt j z B := by
    simpa only [MvPolynomial.aeval_def,Algebra.algebraMap_self,MvPolynomial.eval₂_id] using incidencePointPolynomials_eval j B z
  rw [hf] at hh
  simpa only [MvPolynomial.aeval_def,Algebra.algebraMap_self,MvPolynomial.eval₂_id] using hh

lemma incidence_relation_all_pivots {K : Type} [Field K] {m r : ℕ}
    (Y : Set (Affine K m)) (hY : IrreducibleAffine Y) (j : Fin m)
    (hj : ∃ z ∈ Y, z j ≠ 0) (q : MvPolynomial (Fin r × Fin m) K)
    (hq : ∀ z ∈ Y, ∀ B : Fin r × Fin m → K, eval (incidenceMatrixAt j z B) q = 0) :
    ∀ k : Fin m, ∀ z ∈ Y, ∀ B : Fin r × Fin m → K, eval (incidenceMatrixAt k z B) q = 0 := by
  classical
  intro k z hz B
  let p := MvPolynomial.aeval (incidencePointPolynomials k B) q
  have hp : p ∈ vanishingIdeal K Y := by
    apply vanishes_on_irreducible_of_vanishes_off_hyperplane Y hY j hj
    intro x hx hxj
    rw [show p = MvPolynomial.aeval (incidencePointPolynomials k B) q from rfl,eval_incidencePointSubstitution]
    let A := incidenceMatrixAt k x B
    have hA (i : Fin r) : ∑ l : Fin m, A (i,l)*x l=0 := incidenceMatrixAt_annihilates k x B i
    have hh := hq x hx (fun a => A a / x j)
    rw [incidenceMatrixAt_recover j x hxj A hA] at hh
    exact hh
  have hh := hp z hz
  simp only [MvPolynomial.aeval_def,Algebra.algebraMap_self,MvPolynomial.eval₂_id] at hh
  change eval z (MvPolynomial.aeval (incidencePointPolynomials k B) q) = 0 at hh
  rwa [eval_incidencePointSubstitution] at hh

lemma incidence_relation_vanishes_on_common_zero {K : Type} [Field K] {m r : ℕ}
    (Y : Set (Affine K m)) (hY : IrreducibleAffine Y) (j : Fin m)
    (hj : ∃ z ∈ Y, z j ≠ 0) (q : MvPolynomial (Fin r × Fin m) K)
    (hq : ∀ z ∈ Y, ∀ B : Fin r × Fin m → K, eval (incidenceMatrixAt j z B) q = 0)
    (z : Fin m → K) (hz : z ∈ Y) (hne : z ≠ 0) (A : Fin r × Fin m → K)
    (hA : ∀ i, ∑ l : Fin m, A (i,l)*z l=0) : eval A q=0 := by
  classical
  have hex : ∃ k, z k ≠ 0 := by
    by_contra h
    push Not at h
    apply hne
    funext k
    exact h k
  obtain ⟨k,hk⟩ := hex
  have hh := incidence_relation_all_pivots Y hY j hj q hq k z hz (fun a => A a / z k)
  rwa [incidenceMatrixAt_recover k z hk A hA] at hh

end APSCounting893.Main
end Component_18

section Component_19
set_option autoImplicit false
set_option maxHeartbeats 400000
open MvPolynomial
namespace APSCounting893.Main

lemma homogeneousComponent_mul_homogeneous {K σ : Type} [CommRing K]
    (p q : MvPolynomial σ K) (d n : ℕ) (hp : p.IsHomogeneous d) (hd : d ≤ n) :
    homogeneousComponent n (p*q) = p * homogeneousComponent (n-d) q := by
  classical
  induction q using MvPolynomial.induction_on' with
  | monomial e c =>
    rw [homogeneousComponent_of_mem (hp.mul (MvPolynomial.isHomogeneous_monomial c (rfl : e.degree = e.degree))),
      homogeneousComponent_of_mem (MvPolynomial.isHomogeneous_monomial c (rfl : e.degree = e.degree))]
    by_cases h : n=d+e.degree
    · have hh : n-d=e.degree := by omega
      simp [h,hh]
    · have hh : n-d≠e.degree := by omega
      simp [h,hh]
  | add q₁ q₂ h₁ h₂ => simp only [mul_add,map_add,h₁,h₂]

end APSCounting893.Main
end Component_19

section Component_20
set_option autoImplicit false
set_option maxHeartbeats 400000
attribute [local instance] MvPolynomial.gradedAlgebra
open MvPolynomial
namespace APSCounting893.Main

lemma homogeneous_power_linear_relation {K σ τ : Type} [Field K] [Fintype τ]
    (I : Ideal (MvPolynomial σ K))
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule σ K))
    (ell : τ → MvPolynomial σ K) (hell : ∀ i, (ell i).IsHomogeneous 1)
    (j : σ) (N : ℕ) (hN : 0 < N)
    (hmem : MvPolynomial.X j ^ N ∈ I ⊔ Ideal.span (Set.range ell)) :
    ∃ h : τ → MvPolynomial σ K, (∀ i, (h i).totalDegree < N) ∧
      MvPolynomial.X j ^ N - ∑ i, ell i * h i ∈ I := by
  classical
  obtain ⟨p,hp,q,hq,heq⟩ := Submodule.mem_sup.mp hmem
  obtain ⟨c,hc⟩ := Ideal.mem_span_range_iff_exists_fun.mp hq
  refine ⟨fun i => homogeneousComponent (N-1) (c i),?_,?_⟩
  · intro i
    change (homogeneousComponent (N-1) (c i)).totalDegree < N
    have hh := (homogeneousComponent_isHomogeneous (N-1) (c i)).totalDegree_le
    omega
  · have hh := congrArg (homogeneousComponent N) heq
    have hX : (MvPolynomial.X j ^ N : MvPolynomial σ K).IsHomogeneous N := by
      simpa using (MvPolynomial.isHomogeneous_X K j).pow N
    rw [map_add,homogeneousComponent_eq_self hX,← hc,map_sum] at hh
    have hm (i : τ) : homogeneousComponent N (c i * ell i) = ell i * homogeneousComponent (N-1) (c i) := by
      rw [mul_comm]
      exact homogeneousComponent_mul_homogeneous _ _ 1 N (hell i) hN
    simp only [hm] at hh
    have hp' := MvPolynomial.homogeneousComponent_mem_of_mem hI hp N
    rw [← hh]
    simpa only [add_sub_cancel_right] using hp'

end APSCounting893.Main
end Component_20

section Component_21
set_option autoImplicit false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency.types false
open MvPolynomial
namespace APSCounting893.Main

lemma map_polynomial_mem_of_monomials {K S R σ : Type} [Field K] [CommRing S] [CommRing R]
    [Algebra K S] [Algebra K R] [Algebra S R] [IsScalarTower K S R]
    (f : MvPolynomial σ K →ₐ[K] R) (M : Submodule S R) (p : MvPolynomial σ K)
    (hp : ∀ e ∈ p.support, f (MvPolynomial.monomial e 1) ∈ M) : f p ∈ M := by
  classical
  rw [MvPolynomial.as_sum p,map_sum]
  apply M.sum_mem
  intro e he
  have hh := M.smul_mem (algebraMap K S (p.coeff e)) (hp e he)
  rw [Algebra.smul_def,← IsScalarTower.algebraMap_apply K S R,← f.commutes,← map_mul] at hh
  simpa only [MvPolynomial.algebraMap_eq,MvPolynomial.C_mul_monomial,mul_one] using hh

lemma submodule_eq_top_of_degree_lowering_relations {K S R σ τ : Type}
    [Field K] [CommRing S] [CommRing R] [Fintype σ] [Fintype τ]
    [Algebra K S] [Algebra K R] [Algebra S R] [IsScalarTower K S R]
    (f : MvPolynomial σ K →ₐ[K] R) (hf : Function.Surjective f)
    (N : σ → ℕ) (hN : ∀ j, 0 < N j)
    (a : τ → S) (h : σ → τ → MvPolynomial σ K)
    (hdegree : ∀ j i, (h j i).totalDegree < N j)
    (hrelation : ∀ j, f (MvPolynomial.X j ^ N j) = ∑ i, a i • f (h j i))
    (M : Submodule S R)
    (hlow : ∀ e : σ →₀ ℕ, (∀ j, e j < N j) → f (MvPolynomial.monomial e 1) ∈ M) : M = ⊤ := by
  classical
  have hall (t : ℕ) : ∀ e : σ →₀ ℕ, e.degree = t → f (MvPolynomial.monomial e 1) ∈ M := by
    induction t using Nat.strong_induction_on with
    | h t ih =>
      intro e het
      by_cases he : ∀ j, e j < N j
      · exact hlow e he
      · push_neg at he
        obtain ⟨j,hj⟩ := he
        have hle : Finsupp.single j (N j) ≤ e := by
          intro k
          by_cases hk : k=j
          · subst k; simpa using hj
          · simp [Finsupp.single_apply,hk]
        let e' := e - Finsupp.single j (N j)
        have heq : Finsupp.single j (N j) + e' = e := add_tsub_cancel_of_le hle
        have hdeg : N j + e'.degree = t := by
          have hh := congrArg Finsupp.degree heq
          simpa only [map_add,Finsupp.degree_single,het] using hh
        have hsmall (p : MvPolynomial σ K) (hp : p.totalDegree < t) : f p ∈ M := by
          apply map_polynomial_mem_of_monomials f M p
          intro b hb
          apply ih b.degree ((MvPolynomial.le_totalDegree hb).trans_lt hp) b rfl
        have hprod (i : τ) : f (h j i * MvPolynomial.monomial e' 1) ∈ M := by
          apply hsmall
          have hh := (MvPolynomial.totalDegree_mul (h j i) (MvPolynomial.monomial e' 1)).trans
            (Nat.add_le_add_left (MvPolynomial.totalDegree_monomial_le e' (1 : K)) (h j i).totalDegree)
          change (h j i * MvPolynomial.monomial e' 1).totalDegree ≤ (h j i).totalDegree + e'.degree at hh
          have hhi := hdegree j i
          omega
        have hmon : MvPolynomial.monomial e (1 : K) = MvPolynomial.X j ^ N j * MvPolynomial.monomial e' 1 := by
          rw [MvPolynomial.X_pow_eq_monomial,MvPolynomial.monomial_mul,mul_one,heq]
        rw [hmon,map_mul,hrelation,Finset.sum_mul]
        apply M.sum_mem
        intro i hi
        have hh := M.smul_mem (a i) (hprod i)
        simpa only [map_mul,smul_mul_assoc] using hh
  apply top_le_iff.mp
  intro x hx
  obtain ⟨p,rfl⟩ := hf x
  exact map_polynomial_mem_of_monomials f M p (fun e he => hall e.degree e rfl)

end APSCounting893.Main
end Component_21

section Component_22
set_option autoImplicit false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency.types false
open MvPolynomial
namespace APSCounting893.Main

lemma finite_module_of_degree_lowering_relations {K S R σ τ : Type}
    [Field K] [CommRing S] [CommRing R] [Fintype σ] [Fintype τ]
    [Algebra K S] [Algebra K R] [Algebra S R] [IsScalarTower K S R]
    (f : MvPolynomial σ K →ₐ[K] R) (hf : Function.Surjective f)
    (N : σ → ℕ) (hN : ∀ j, 0 < N j)
    (a : τ → S) (h : σ → τ → MvPolynomial σ K)
    (hdegree : ∀ j i, (h j i).totalDegree < N j)
    (hrelation : ∀ j, f (MvPolynomial.X j ^ N j) = ∑ i, a i • f (h j i)) :
    Module.Finite S R := by
  classical
  let V := (j : σ) → Fin (N j)
  let g : V → R := fun v => f (MvPolynomial.monomial (Finsupp.equivFunOnFinite.symm (fun j => (v j).val)) 1)
  let E := Finset.univ.image g
  let M : Submodule S R := Submodule.span S (E : Set R)
  have hlow (e : σ →₀ ℕ) (he : ∀ j, e j < N j) : f (MvPolynomial.monomial e 1) ∈ M := by
    apply Submodule.subset_span
    apply Finset.mem_image.mpr
    refine ⟨fun j => ⟨e j,he j⟩,Finset.mem_univ _,?_⟩
    change f (MvPolynomial.monomial (Finsupp.equivFunOnFinite.symm (fun j => e j)) 1) = _
    simp
  have hM : M = ⊤ := submodule_eq_top_of_degree_lowering_relations f hf N hN a h hdegree hrelation M hlow
  exact Module.Finite.of_fg_top ⟨E,hM⟩

end APSCounting893.Main
end Component_22

section Component_23
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option synthInstance.maxHeartbeats 400000
set_option maxSynthPendingDepth 5
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] MvPolynomial.gradedAlgebra
open MvPolynomial
namespace APSCounting893.Main

lemma coordinate_power_mem_of_zeroLocus_subset_zero {K σ : Type} [Field K] [IsAlgClosed K] [Fintype σ]
    (J : Ideal (MvPolynomial σ K)) (hJ : zeroLocus K J ⊆ {0}) (j : σ) :
    ∃ N : ℕ, 0 < N ∧ MvPolynomial.X j ^ N ∈ J := by
  have hx : MvPolynomial.X j ∈ vanishingIdeal K (zeroLocus K J) := by
    intro x hx
    have hz : x=0 := Set.mem_singleton_iff.mp (hJ hx)
    subst x
    simp
  rw [MvPolynomial.vanishingIdeal_zeroLocus_eq_radical] at hx
  obtain ⟨N,hN⟩ := Ideal.mem_radical_iff.mp hx
  refine ⟨N+1,by omega,?_⟩
  rw [pow_succ']
  exact J.mul_mem_left _ hN

end APSCounting893.Main
end Component_23

section Component_24

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] MvPolynomial.gradedAlgebra
open MvPolynomial
namespace APSCounting893.Main

noncomputable def chartDehomogenize {K : Type} [Field K] {n : ℕ} :
    Polynomials K (n + 1) →ₐ[K] Polynomials K n :=
  MvPolynomial.aeval (Fin.cons 1 (fun i : Fin n => MvPolynomial.X i))

lemma chartDehomogenize_degree {K : Type} [Field K] {n : ℕ}
    (p : Polynomials K (n + 1)) :
    (chartDehomogenize p).totalDegree ≤ p.totalDegree := by
  have h := totalDegree_eval₂_bounded (RingHom.id K)
    (Fin.cons 1 (fun i : Fin n => MvPolynomial.X i)) 1 (fun i => ?_) p
  · simpa [chartDehomogenize, MvPolynomial.aeval_def] using h
  · refine Fin.cases ?_ (fun j => ?_) i <;> simp

lemma eval_chartDehomogenize {K : Type} [Field K] {n : ℕ}
    (p : Polynomials K (n + 1)) (x : Affine K n) :
    eval x (chartDehomogenize p) = eval (Fin.cons 1 x) p := by
  apply MvPolynomial.induction_on p
  · intro c; simp [chartDehomogenize]
  · intro p q hp hq; simpa only [map_add] using congrArg₂ (· + ·) hp hq
  · intro p i hp
    simp only [map_mul, hp]
    congr 1
    refine Fin.cases ?_ (fun j => ?_) i <;> simp [chartDehomogenize]

noncomputable def homogeneousChartEvaluation {K : Type} [Field K] {n : ℕ}
    (X : Set (Affine K n)) (d : ℕ) :
    homogeneousSubmodule (Fin (n + 1)) K d →ₗ[K] (X → K) where
  toFun p := fun x => eval (Fin.cons 1 x.val) p.val
  map_add' p q := by funext x; exact map_add (eval (Fin.cons 1 x.val)) p.val q.val
  map_smul' c p := by funext x; simp [MvPolynomial.smul_eq_C_mul]

lemma homogeneousChartEvaluation_range {K : Type} [Field K] {n : ℕ}
    (X : Set (Affine K n)) (d : ℕ) :
    LinearMap.range (homogeneousChartEvaluation X d) = affineFilteredPiece X d := by
  ext f
  rw [LinearMap.mem_range, mem_affineFilteredPiece]
  constructor
  · rintro ⟨p, rfl⟩
    refine ⟨chartDehomogenize p.val,
      (chartDehomogenize_degree p.val).trans p.property.totalDegree_le, ?_⟩
    funext x
    exact (eval_chartDehomogenize p.val x.val).symm
  · rintro ⟨p, hp, rfl⟩
    refine ⟨⟨homogenizeAll d p, homogenizeAll_isHomogeneous p d hp⟩, ?_⟩
    funext x
    exact eval_homogenize_chart p d hp x.val

noncomputable def homogeneousChartQuotient {K : Type} [Field K] {n : ℕ}
    (X : Set (Affine K n)) (d : ℕ) :
    homogeneousSubmodule (Fin (n + 1)) K d →ₗ[K]
      (Polynomials K (n + 1) ⧸ chartHomogeneousIdeal X) :=
  (Ideal.Quotient.mkₐ K (chartHomogeneousIdeal X)).toLinearMap.comp
    (homogeneousSubmodule (Fin (n + 1)) K d).subtype

lemma homogeneousChart_kernels {K : Type} [Field K] {n : ℕ}
    (X : Set (Affine K n)) (d : ℕ) :
    LinearMap.ker (homogeneousChartQuotient X d) =
      LinearMap.ker (homogeneousChartEvaluation X d) := by
  ext p
  rw [LinearMap.mem_ker, LinearMap.mem_ker]
  change (Ideal.Quotient.mk (chartHomogeneousIdeal X) p.val = 0) ↔ _
  rw [Ideal.Quotient.eq_zero_iff_mem,
    homogeneous_mem_chartIdeal_iff X p.val d p.property]
  constructor
  · intro h; funext x; exact h x.val x.property
  · intro h x hx; exact congrFun h ⟨x, hx⟩

lemma chartQuotientPiece_finrank {K : Type} [Field K] {n : ℕ}
    (X : Set (Affine K n)) (d : ℕ) :
    Module.finrank K (LinearMap.range (homogeneousChartQuotient X d)) =
      affineHilbertFunction X d := by
  rw [← (homogeneousChartQuotient X d).quotKerEquivRange.finrank_eq,
    homogeneousChart_kernels,
    (homogeneousChartEvaluation X d).quotKerEquivRange.finrank_eq,
    homogeneousChartEvaluation_range]
  rfl

end APSCounting893.Main
end Component_24

section Component_25
set_option autoImplicit false
set_option maxHeartbeats 400000
open MvPolynomial
namespace APSCounting893.Main

lemma chartDehomogenize_rename_succ {K : Type} [Field K] {n : ℕ} (p : Polynomials K n) :
    chartDehomogenize (MvPolynomial.rename Fin.succ p) = p := by
  unfold chartDehomogenize
  rw [MvPolynomial.aeval_rename]
  have hh : (Fin.cons (1 : Polynomials K n) (fun i : Fin n => MvPolynomial.X i)) ∘ Fin.succ = fun i => (MvPolynomial.X i : Polynomials K n) := by
    funext i
    simp
  rw [hh,MvPolynomial.aeval_X_left_apply]

lemma chartDehomogenize_mem_vanishing {K : Type} [Field K] {n : ℕ}
    (Y : Set (Affine K n)) (p : Polynomials K (n+1)) (hp : p ∈ chartHomogeneousIdeal Y) :
    chartDehomogenize p ∈ vanishingIdeal K Y := by
  intro y hy
  have hh := chartHomogeneousIdeal_le_vanishing Y hp (Fin.cons 1 y) ⟨y,hy,rfl⟩
  simp only [MvPolynomial.aeval_def,Algebra.algebraMap_self,MvPolynomial.eval₂_id] at hh ⊢
  rw [eval_chartDehomogenize]
  exact hh

end APSCounting893.Main
end Component_25

section Component_26

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open MvPolynomial
namespace APSCounting893.Main

lemma zeroLocus_prime_nonempty {K : Type} [Field K] [IsAlgClosed K] {n : ℕ}
    (I : Ideal (Polynomials K n)) (hI : I.IsPrime) : (zeroLocus K I).Nonempty := by
  obtain ⟨M, hM, hIM⟩ := Ideal.exists_le_maximal I hI.ne_top
  obtain ⟨x, hMx⟩ := MvPolynomial.eq_vanishingIdeal_singleton_of_isMaximal K hM
  refine ⟨x, ?_⟩
  intro p hp
  have hpM := hIM hp
  rw [hMx] at hpM
  exact hpM x (Set.mem_singleton x)

lemma irreducibleAffine_zeroLocus_prime {K : Type} [Field K] [IsAlgClosed K] {n : ℕ}
    (I : Ideal (Polynomials K n)) (hI : I.IsPrime) : IrreducibleAffine (zeroLocus K I) := by
  letI : I.IsPrime := hI
  apply prime_ideal_irreducibleAffine (zeroLocus_prime_nonempty I hI) (isAlgSet_zeroLocus I)
  rw [MvPolynomial.IsPrime.vanishingIdeal_zeroLocus]
  exact hI

lemma affineComponent_ideal_minimal {K : Type} [Field K] [IsAlgClosed K] {n : ℕ}
    {C W : Set (Affine K n)} (hC : RSCapacity.IsAlgSet C) (hW : AffineComponent C W) :
    (vanishingIdeal K C).IsMinimalPrime (vanishingIdeal K W) := by
  refine ⟨⟨irreducibleAffine_ideal_prime hW.1, vanishingIdeal_anti_mono hW.2.1⟩, ?_⟩
  intro Q hQ hQW
  letI : Q.IsPrime := hQ.1
  have hWQ : W ⊆ zeroLocus K Q := by
    rw [isAlgSet_eq_zeroLocus hW.1.2.1]
    exact zeroLocus_anti_mono hQW
  have hQC : zeroLocus K Q ⊆ C := by
    rw [isAlgSet_eq_zeroLocus hC]
    exact zeroLocus_anti_mono hQ.2
  have heq := hW.2.2 (zeroLocus K Q) (irreducibleAffine_zeroLocus_prime Q hQ.1) hWQ hQC
  rw [← heq, MvPolynomial.IsPrime.vanishingIdeal_zeroLocus]

lemma affineComponent_of_minimal {K : Type} [Field K] [IsAlgClosed K] {n : ℕ}
    {C : Set (Affine K n)} (hC : RSCapacity.IsAlgSet C)
    (Q : Ideal (Polynomials K n)) (hQ : (vanishingIdeal K C).IsMinimalPrime Q) :
    AffineComponent C (zeroLocus K Q) := by
  letI : Q.IsPrime := hQ.isPrime
  refine ⟨irreducibleAffine_zeroLocus_prime Q hQ.isPrime, ?_, ?_⟩
  · rw [isAlgSet_eq_zeroLocus hC]
    exact zeroLocus_anti_mono hQ.le
  · intro W hW hQW hWC
    have hIWQ : vanishingIdeal K W ≤ Q := by
      rw [← MvPolynomial.IsPrime.vanishingIdeal_zeroLocus (K := K) Q]
      exact vanishingIdeal_anti_mono hQW
    have hQI : Q ≤ vanishingIdeal K W := hQ.2
      ⟨irreducibleAffine_ideal_prime hW, vanishingIdeal_anti_mono hWC⟩ hIWQ
    rw [isAlgSet_eq_zeroLocus hW.2.1, hIWQ.antisymm hQI]

lemma exists_affineComponent_mem {K : Type} [Field K] [IsAlgClosed K] {n : ℕ}
    {C : Set (Affine K n)} (hC : RSCapacity.IsAlgSet C) {x : Affine K n} (hx : x ∈ C) :
    ∃ W, AffineComponent C W ∧ x ∈ W := by
  have hI : vanishingIdeal K C ≤ vanishingIdeal K ({x} : Set (Affine K n)) :=
    vanishingIdeal_anti_mono (Set.singleton_subset_iff.mpr hx)
  obtain ⟨Q, hQ, hQx⟩ := Ideal.exists_minimalPrimes_le hI
  exact ⟨zeroLocus K Q, affineComponent_of_minimal hC Q hQ,
    fun p hp => hQx hp x (Set.mem_singleton x)⟩

lemma isAlgSet_inter {K : Type} [Field K] {n : ℕ} {A B : Set (Affine K n)}
    (hA : RSCapacity.IsAlgSet A) (hB : RSCapacity.IsAlgSet B) : RSCapacity.IsAlgSet (A ∩ B) := by
  obtain ⟨S, rfl⟩ := hA
  obtain ⟨T, rfl⟩ := hB
  refine ⟨S ∪ T, ?_⟩
  ext x
  simp only [RSCapacity.zeroSet, Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_union]
  aesop

lemma isAlgSet_preimage_evaluate {K : Type} [Field K] {n m : ℕ}
    (F : PolynomialMap K n m) {A : Set (Affine K m)} (hA : RSCapacity.IsAlgSet A) :
    RSCapacity.IsAlgSet (evaluate F ⁻¹' A) := by
  obtain ⟨S, rfl⟩ := hA
  refine ⟨(eval₂Hom MvPolynomial.C F) '' S, ?_⟩
  ext x
  simp only [Set.mem_preimage, RSCapacity.zeroSet, Set.mem_setOf_eq, Set.forall_mem_image, evaluation_substitution]

lemma isAlgSet_affineLine {K : Type} [Field K] {d : ℕ}
    (base direction : Affine K d) (hdir : direction ≠ 0) : RSCapacity.IsAlgSet (affineLine base direction) := by
  classical
  obtain ⟨i, hi⟩ : ∃ i, direction i ≠ 0 := by
    by_contra h
    push Not at h
    exact hdir (funext h)
  let p : Fin d → Polynomials K d := fun j =>
    MvPolynomial.C (direction i) * (MvPolynomial.X j - MvPolynomial.C (base j)) -
      MvPolynomial.C (direction j) * (MvPolynomial.X i - MvPolynomial.C (base i))
  refine ⟨Set.range p, ?_⟩
  apply Set.Subset.antisymm
  · rintro x ⟨t, rfl⟩ q ⟨j, rfl⟩
    simp only [p, map_sub, map_mul, eval_C, eval_X, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  · intro x hx
    have hj (j : Fin d) : direction i * (x j - base j) - direction j * (x i - base i) = 0 := by
      simpa [p] using hx (p j) (Set.mem_range_self j)
    refine ⟨(x i - base i) / direction i, ?_⟩
    funext j
    have he : x j - base j = direction j * (x i - base i) / direction i :=
      (eq_div_iff hi).mpr (by simpa only [mul_comm] using sub_eq_zero.mp (hj j))
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    linear_combination -he

lemma irreducibleAffine_affineLine {K : Type} [Field K] [Infinite K] {d : ℕ}
    (base direction : Affine K d) (hdir : direction ≠ 0) : IrreducibleAffine (affineLine base direction) := by
  let F : PolynomialMap K 1 d := fun j => MvPolynomial.C (base j) +
    MvPolynomial.C (direction j) * MvPolynomial.X 0
  have hrange : Set.range (evaluate F) = affineLine base direction := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      refine ⟨x 0, ?_⟩
      funext j
      simp [evaluate, F, mul_comm]
    · rintro ⟨t, rfl⟩
      refine ⟨fun _ => t, ?_⟩
      funext j
      simp [evaluate, F, mul_comm]
  have hcl : imageClosure F = affineLine base direction := by
    unfold imageClosure RSCapacity.zClosure
    rw [hrange, ← isAlgSet_eq_zeroLocus (isAlgSet_affineLine base direction hdir)]
  exact hcl ▸ irreducibleAffine_imageClosure F

lemma finiteMorphism_restrict {K : Type} [Field K] {n m : ℕ}
    {X W : Set (Affine K n)} (F : PolynomialMap K n m) (hfinite : FiniteMorphism X F)
    (hWX : W ⊆ X) : FiniteMorphism W F := by
  obtain ⟨s, g, hg⟩ := hfinite
  refine ⟨s, g, ?_⟩
  intro p
  obtain ⟨c, hc⟩ := hg p
  exact ⟨c, fun x hx => hc x (hWX hx)⟩

lemma finiteMorphism_image {K : Type} [Field K] [IsAlgClosed K] {n m : ℕ}
    (W : Set (Affine K n)) (hclosed : RSCapacity.IsAlgSet W)
    (F : PolynomialMap K n m) (hfinite : FiniteMorphism W F) :
    evaluate F '' W = zeroLocus K (RingHom.ker (coordinatePullback W F)) := by
  classical
  letI : Algebra (Polynomials K m) (CoordinateRing W) := coordinatePullbackAlgebra W F
  letI : Module.Finite (Polynomials K m) (CoordinateRing W) := finiteMorphism_module_finite W F hfinite
  have halg : algebraMap (Polynomials K m) (CoordinateRing W) = coordinatePullback W F := rfl
  apply Set.Subset.antisymm
  · rintro y ⟨x, hx, rfl⟩ p hp
    have hpI : eval₂Hom MvPolynomial.C F p ∈ vanishingIdeal K W :=
      Ideal.Quotient.eq_zero_iff_mem.mp hp
    simpa only [aeval_def, Algebra.algebraMap_self, eval₂_id, evaluation_substitution] using hpI x hx
  · intro y hy
    let P := vanishingIdeal K ({y} : Set (Affine K m))
    have hker : RingHom.ker (algebraMap (Polynomials K m) (CoordinateRing W)) ≤ P := by
      intro p hp
      rw [halg] at hp
      exact (MvPolynomial.mem_vanishingIdeal_singleton_iff y p).mpr (hy p hp)
    obtain ⟨Q, hQmax, hQ⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral
      (S := CoordinateRing W) P hker
    letI : Q.IsMaximal := hQmax
    let N : Ideal (Polynomials K n) := Q.comap (Ideal.Quotient.mk (vanishingIdeal K W))
    have hNmax : N.IsMaximal := Ideal.comap_isMaximal_of_surjective _ Ideal.Quotient.mk_surjective
    obtain ⟨x, hNx⟩ := MvPolynomial.eq_vanishingIdeal_singleton_of_isMaximal K hNmax
    have hxW : x ∈ W := by
      rw [isAlgSet_eq_zeroLocus hclosed]
      intro p hp
      have hpN : p ∈ N := by
        change Ideal.Quotient.mk (vanishingIdeal K W) p ∈ Q
        rw [Ideal.Quotient.eq_zero_iff_mem.mpr hp]
        exact Q.zero_mem
      rw [hNx] at hpN
      exact hpN x (Set.mem_singleton x)
    refine ⟨x, hxW, ?_⟩
    funext j
    have hpP : MvPolynomial.X j - MvPolynomial.C (y j) ∈ P := by
      rw [MvPolynomial.mem_vanishingIdeal_singleton_iff]
      simp
    rw [← hQ] at hpP
    have hpN : eval₂Hom MvPolynomial.C F (MvPolynomial.X j - MvPolynomial.C (y j)) ∈ N := hpP
    rw [hNx] at hpN
    have hpval := hpN x (Set.mem_singleton x)
    simp only [aeval_def, Algebra.algebraMap_self, eval₂_id, evaluation_substitution,
      map_sub, eval_X, eval_C, sub_eq_zero] at hpval
    exact hpval

lemma finite_dominant_component_surjective {K : Type} [Field K] [IsAlgClosed K] {n m : ℕ}
    (X : Set (Affine K n)) (hX : IrreducibleAffine X)
    (F : PolynomialMap K n m) (hfinite : FiniteMorphism X F)
    (hdom : RSCapacity.zClosure (evaluate F '' X) = Set.univ)
    (L : Set (Affine K m)) (hL : IrreducibleAffine L)
    (W : Set (Affine K n)) (hW : AffineComponent {x | x ∈ X ∧ evaluate F x ∈ L} W) :
    evaluate F '' W = L := by
  classical
  letI : (vanishingIdeal K X).IsPrime := irreducibleAffine_ideal_prime hX
  letI : (vanishingIdeal K W).IsPrime := irreducibleAffine_ideal_prime hW.1
  letI : Algebra (Polynomials K m) (CoordinateRing X) := coordinatePullbackAlgebra X F
  letI : Module.Finite (Polynomials K m) (CoordinateRing X) := finiteMorphism_module_finite X F hfinite
  have halg : algebraMap (Polynomials K m) (CoordinateRing X) = coordinatePullback X F := rfl
  letI : FaithfulSMul (Polynomials K m) (CoordinateRing X) :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr (coordinatePullback_injective_of_dominant X F hdom)
  have hWX : W ⊆ X := fun x hx => (hW.2.1 hx).1
  let psi : CoordinateRing X →+* CoordinateRing W :=
    Ideal.Quotient.factor (vanishingIdeal_anti_mono hWX)
  let Q : Ideal (CoordinateRing X) := RingHom.ker psi
  letI : Q.IsPrime := RingHom.ker_isPrime psi
  have hraw : Q.comap (Ideal.Quotient.mk (vanishingIdeal K X)) = vanishingIdeal K W := by
    ext p
    simp [Q, psi, Ideal.mem_comap, RingHom.mem_ker, Ideal.Quotient.factor_mk,
      Ideal.Quotient.eq_zero_iff_mem]
  let P : Ideal (Polynomials K m) := vanishingIdeal K L
  letI : P.IsPrime := irreducibleAffine_ideal_prime hL
  have hP : P ≤ Q.under (Polynomials K m) := by
    intro p hp
    change (coordinatePullback X F) p ∈ Q
    have hs : eval₂Hom MvPolynomial.C F p ∈ vanishingIdeal K W := by
      intro x hx
      simpa only [aeval_def, Algebra.algebraMap_self, eval₂_id, evaluation_substitution] using
        hp (evaluate F x) (hW.2.1 hx).2
    rw [← hraw] at hs
    exact hs
  let q : Ideal (Polynomials K m) := Q.under (Polynomials K m)
  letI : Q.LiesOver q := ⟨rfl⟩
  obtain ⟨Q0, hQ0Q, hQ0prime, hQ0over⟩ :=
    Ideal.exists_ideal_le_liesOver_of_le (p := P) (q := q) Q hP
  letI : Q0.IsPrime := hQ0prime
  letI : Q0.LiesOver P := hQ0over
  have hQ0base : Q0.comap (coordinatePullback X F) = P := (Q0.over_def P).symm
  let J : Ideal (Polynomials K n) := Q0.comap (Ideal.Quotient.mk (vanishingIdeal K X))
  letI : J.IsPrime := Ideal.comap_isPrime _ Q0
  have hJW : J ≤ vanishingIdeal K W := (Ideal.comap_mono hQ0Q).trans_eq hraw
  have hWJ : W ⊆ zeroLocus K J := by
    rw [isAlgSet_eq_zeroLocus hW.1.2.1]
    exact zeroLocus_anti_mono hJW
  have hJC : zeroLocus K J ⊆ {x | x ∈ X ∧ evaluate F x ∈ L} := by
    intro x hx
    constructor
    · rw [isAlgSet_eq_zeroLocus hX.2.1]
      intro p hp
      have hpJ : p ∈ J := by
        change Ideal.Quotient.mk (vanishingIdeal K X) p ∈ Q0
        rw [Ideal.Quotient.eq_zero_iff_mem.mpr hp]
        exact Q0.zero_mem
      exact hx p hpJ
    · rw [isAlgSet_eq_zeroLocus hL.2.1]
      intro p hp
      have hp0 : (coordinatePullback X F) p ∈ Q0 := by
        change p ∈ Q0.comap (coordinatePullback X F)
        rw [hQ0base]
        exact hp
      have hpJ : eval₂Hom MvPolynomial.C F p ∈ J := hp0
      simpa only [aeval_def, Algebra.algebraMap_self, eval₂_id, evaluation_substitution] using hx _ hpJ
  have hWeq := hW.2.2 (zeroLocus K J) (irreducibleAffine_zeroLocus_prime J inferInstance) hWJ hJC
  have hIW : vanishingIdeal K W = J := by
    rw [← hWeq, MvPolynomial.IsPrime.vanishingIdeal_zeroLocus]
  have hker : RingHom.ker (coordinatePullback W F) = P := by
    ext p
    rw [RingHom.mem_ker]
    change Ideal.Quotient.mk (vanishingIdeal K W) (eval₂Hom MvPolynomial.C F p) = 0 ↔ p ∈ P
    rw [Ideal.Quotient.eq_zero_iff_mem, hIW]
    change p ∈ Q0.comap (coordinatePullback X F) ↔ p ∈ P
    rw [hQ0base]
  rw [finiteMorphism_image W hW.1.2.1 F (finiteMorphism_restrict F hfinite hWX), hker]
  exact (isAlgSet_eq_zeroLocus hL.2.1).symm

end APSCounting893.Main

end Component_26

section Component_27

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open MvPolynomial
namespace APSCounting893.Main

lemma top_homogeneousComponent_ne_zero {K : Type} [Field K] {n : ℕ}
    (p : Polynomials K n) (hp : p ≠ 0) : homogeneousComponent p.totalDegree p ≠ 0 := by
  classical
  obtain ⟨e, he, hmax⟩ := Finset.exists_mem_eq_sup p.support (support_nonempty.mpr hp)
    (fun e => e.sum (fun _ a => a))
  have hd : e.degree = p.totalDegree := by simpa [Finsupp.degree, Finsupp.sum, totalDegree] using hmax.symm
  intro h
  have hc := congrArg (MvPolynomial.coeff e) h
  rw [coeff_homogeneousComponent, if_pos hd, coeff_zero] at hc
  exact (mem_support_iff.mp he) hc

lemma homogeneous_eval_scale {K : Type} [Field K] {n D : ℕ}
    (p : Polynomials K n) (hp : p.IsHomogeneous D) (a : K) (x : Affine K n) :
    eval (fun i => a * x i) p = a ^ D * eval x p := by
  classical
  rw [eval_eq', eval_eq', Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro e he
  have hd : ∑ i : Fin n, e i = D := by
    have hs : (∑ i ∈ e.support, e i) = ∑ i : Fin n, e i := by
      exact e.sum_fintype (fun _ b => b) (fun _ => rfl)
    exact hs.symm.trans (hp.degree_eq_sum_deg_support he).symm
  simp only [mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, hd]
  ring

noncomputable def normalizationParameter {K : Type} [Field K] {n : ℕ}
    (p : Polynomials K (n + 1)) : Polynomials K n :=
  eval₂Hom MvPolynomial.C (Fin.lastCases 1 MvPolynomial.X) (homogeneousComponent p.totalDegree p)

lemma normalizationParameter_ne_zero {K : Type} [Field K] [Infinite K] {n : ℕ}
    (p : Polynomials K (n + 1)) (hp : p ≠ 0) : normalizationParameter p ≠ 0 := by
  classical
  let H := homogeneousComponent p.totalDegree p
  have hH : H ≠ 0 := top_homogeneousComponent_ne_zero p hp
  have hprod : H * MvPolynomial.X (Fin.last n) ≠ 0 := mul_ne_zero hH (X_ne_zero _)
  obtain ⟨w, hw⟩ : ∃ w : Affine K (n + 1), eval w (H * MvPolynomial.X (Fin.last n)) ≠ 0 := by
    by_contra h
    push Not at h
    apply hprod
    apply MvPolynomial.funext
    intro w
    simpa only [map_zero] using h w
  rw [map_mul, eval_X] at hw
  have hwH := left_ne_zero_of_mul hw
  have hwl := right_ne_zero_of_mul hw
  let c : Affine K n := fun i => w i.castSucc / w (Fin.last n)
  have hv : evaluate (Fin.lastCases (1 : Polynomials K n) MvPolynomial.X) c =
      fun i => (w (Fin.last n))⁻¹ * w i := by
    funext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp [evaluate, hwl]
    · simp [evaluate, c, div_eq_mul_inv, mul_comm]
  have hval : eval c (normalizationParameter p) ≠ 0 := by
    unfold normalizationParameter
    rw [evaluation_substitution, hv, homogeneous_eval_scale _ (homogeneousComponent_isHomogeneous _ _)]
    exact mul_ne_zero (pow_ne_zero _ (inv_ne_zero hwl)) hwH
  intro h
  exact hval (by rw [h, map_zero])

lemma coeff_prod_sum_of_natDegree_le {A ι : Type} [CommRing A]
    (s : Finset ι) (f : ι → Polynomial A) (d : ι → ℕ)
    (hd : ∀ i ∈ s, (f i).natDegree ≤ d i) :
    (∏ i ∈ s, f i).coeff (∑ i ∈ s, d i) = ∏ i ∈ s, (f i).coeff (d i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.sum_insert hi, Finset.prod_insert hi,
      Polynomial.coeff_mul_add_eq_of_natDegree_le (hd i (Finset.mem_insert_self _ _))]
    · rw [ih (fun j hj => hd j (Finset.mem_insert_of_mem hj))]
    · exact (Polynomial.natDegree_prod_le s f).trans (Finset.sum_le_sum (fun j hj => hd j (Finset.mem_insert_of_mem hj)))

lemma natDegree_eval₂_of_linear {K A : Type} [CommRing K] [CommRing A] {N : ℕ}
    (f : K →+* A) (g : Fin N → Polynomial A) (hg : ∀ i, (g i).natDegree ≤ 1)
    (p : Polynomials K N) :
    (eval₂Hom (Polynomial.C.comp f) g p).natDegree ≤ p.totalDegree := by
  classical
  conv_lhs => rw [p.as_sum]
  rw [map_sum]
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro e he
  rw [eval₂Hom_monomial, Finsupp.prod_pow]
  apply Polynomial.natDegree_mul_le.trans
  simp only [RingHom.comp_apply, Polynomial.natDegree_C, zero_add]
  apply (Polynomial.natDegree_prod_le _ _).trans
  apply le_trans (Finset.sum_le_sum (fun i _ =>
    Polynomial.natDegree_pow_le.trans (Nat.mul_le_mul_left _ (hg i))))
  have he' : e.degree ≤ p.totalDegree := by
    simpa [Finsupp.degree_apply, Finsupp.sum] using (le_totalDegree he)
  simpa only [mul_one, ← Finsupp.degree_eq_sum] using he' 

lemma coeff_eval₂_monomial_of_linear {K A : Type} [CommRing K] [CommRing A] {N D : ℕ}
    (f : K →+* A) (g : Fin N → Polynomial A) (hg : ∀ i, (g i).natDegree ≤ 1)
    (e : Fin N →₀ ℕ) (c : K) (he : e.degree ≤ D) :
    (eval₂Hom (Polynomial.C.comp f) g (MvPolynomial.monomial e c)).coeff D =
      if e.degree = D then f c * ∏ i : Fin N, (g i).coeff 1 ^ e i else 0 := by
  classical
  rw [eval₂Hom_monomial, Finsupp.prod_pow]
  simp only [RingHom.comp_apply, Polynomial.coeff_C_mul]
  have hbound : (∏ i : Fin N, g i ^ e i).natDegree ≤ e.degree := by
    apply (Polynomial.natDegree_prod_le _ _).trans
    apply le_trans (Finset.sum_le_sum (fun i _ =>
      Polynomial.natDegree_pow_le.trans (Nat.mul_le_mul_left _ (hg i))))
    simp [Finsupp.degree_eq_sum]
  split_ifs with heq
  · have hcoeff := coeff_prod_sum_of_natDegree_le Finset.univ (fun i : Fin N => g i ^ e i)
      (fun i => e i) (fun i _ => Polynomial.natDegree_pow_le.trans (by simpa using Nat.mul_le_mul_left (e i) (hg i)))
    have hpows (i : Fin N) : (g i ^ e i).coeff (e i) = (g i).coeff 1 ^ e i := by
      simpa using (Polynomial.coeff_pow_of_natDegree_le (m := e i) (hg i))
    rw [← heq, Finsupp.degree_eq_sum, hcoeff]
    simp only [hpows]
  · have hlt : (∏ i : Fin N, g i ^ e i).natDegree < D := hbound.trans_lt (lt_of_le_of_ne he heq)
    rw [Polynomial.coeff_eq_zero_of_natDegree_lt hlt, mul_zero]

lemma coeff_eval₂_linear_top {K A : Type} [CommRing K] [CommRing A] {N D : ℕ}
    (f : K →+* A) (g : Fin N → Polynomial A) (hg : ∀ i, (g i).natDegree ≤ 1)
    (p : Polynomials K N) (hp : p.totalDegree ≤ D) :
    (eval₂Hom (Polynomial.C.comp f) g p).coeff D =
      eval₂Hom f (fun i => (g i).coeff 1) (homogeneousComponent D p) := by
  classical
  conv_lhs => rw [p.as_sum]
  rw [map_sum, Polynomial.finsetSum_coeff, homogeneousComponent_apply, map_sum, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro e he
  have hd0 : e.degree ≤ p.totalDegree := by
    simpa [Finsupp.degree_apply, Finsupp.sum] using le_totalDegree he
  have hd : e.degree ≤ D := hd0.trans hp
  rw [coeff_eval₂_monomial_of_linear f g hg e _ hd]
  split_ifs
  · rw [eval₂Hom_monomial, Finsupp.prod_pow]
  · rfl

noncomputable def normalizationLinearForms {K : Type} [Field K] {n : ℕ}
    (c : Affine K n) : Fin (n + 1) → Polynomial (Polynomials K n) :=
  Fin.lastCases Polynomial.X (fun i => Polynomial.C (MvPolynomial.X i) +
    Polynomial.C (MvPolynomial.C (c i)) * Polynomial.X)

lemma normalizationLinearForms_degree {K : Type} [Field K] {n : ℕ}
    (c : Affine K n) (i : Fin (n + 1)) : (normalizationLinearForms c i).natDegree ≤ 1 := by
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp [normalizationLinearForms]
  · simp only [normalizationLinearForms, Fin.lastCases_castSucc]
    apply (Polynomial.natDegree_add_le _ _).trans
    apply max_le (by simp)
    exact Polynomial.natDegree_mul_le.trans (by simp)

noncomputable def normalizationShear {K : Type} [Field K] {n : ℕ}
    (c : Affine K n) (p : Polynomials K (n + 1)) : Polynomial (Polynomials K n) :=
  eval₂Hom (Polynomial.C.comp MvPolynomial.C) (normalizationLinearForms c) p

lemma normalizationShear_top_coeff {K : Type} [Field K] {n : ℕ}
    (c : Affine K n) (p : Polynomials K (n + 1)) :
    (normalizationShear c p).coeff p.totalDegree = MvPolynomial.C (eval c (normalizationParameter p)) := by
  rw [normalizationShear, coeff_eval₂_linear_top MvPolynomial.C _ (normalizationLinearForms_degree c) _ le_rfl]
  have heq : eval₂Hom MvPolynomial.C (fun i => (normalizationLinearForms c i).coeff 1) =
      MvPolynomial.C.comp (eval (Fin.lastCases 1 c)) := by
    apply MvPolynomial.ringHom_ext
    · intro a; simp
    · intro i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simp [normalizationLinearForms]
      · simp [normalizationLinearForms]
  rw [heq, RingHom.comp_apply]
  have hv : evaluate (Fin.lastCases (1 : Polynomials K n) MvPolynomial.X) c = Fin.lastCases 1 c := by
    funext i
    refine Fin.lastCases ?_ (fun j => ?_) i <;> simp [evaluate]
  rw [normalizationParameter, evaluation_substitution, hv]

lemma normalizationShear_unit_leadingCoeff {K : Type} [Field K] {n : ℕ}
    (c : Affine K n) (p : Polynomials K (n + 1))
    (hc : eval c (normalizationParameter p) ≠ 0) :
    IsUnit (normalizationShear c p).leadingCoeff := by
  have hcoef : (normalizationShear c p).coeff p.totalDegree ≠ 0 := by
    rw [normalizationShear_top_coeff]
    simpa only [map_zero] using (MvPolynomial.C_injective (Fin n) K).ne hc
  have hdegree : (normalizationShear c p).natDegree = p.totalDegree :=
    Polynomial.natDegree_eq_of_le_of_coeff_ne_zero
      (natDegree_eval₂_of_linear MvPolynomial.C _ (normalizationLinearForms_degree c) p) hcoef
  rw [Polynomial.leadingCoeff, hdegree, normalizationShear_top_coeff]
  exact (isUnit_iff_ne_zero.mpr hc).map MvPolynomial.C

lemma normalizationShear_eval {n : ℕ} (Y : Set (Affine ℂ (n + 1)))
    (c : Affine ℂ n) (p : Polynomials ℂ (n + 1)) :
    (normalizationShear c p).eval₂ (coordinatePullback Y (normalizationPolynomials c))
      (coordinate Y (Fin.last n)) = Ideal.Quotient.mk (vanishingIdeal ℂ Y) p := by
  let phi := Polynomial.eval₂RingHom (coordinatePullback Y (normalizationPolynomials c))
    (coordinate Y (Fin.last n))
  have heq : phi.comp (eval₂Hom (Polynomial.C.comp MvPolynomial.C) (normalizationLinearForms c)) =
      Ideal.Quotient.mk (vanishingIdeal ℂ Y) := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp [phi, coordinatePullback]
    · intro i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simp [phi, normalizationLinearForms, coordinate]
      · simp [phi, normalizationLinearForms, coordinatePullback, normalizationPolynomials, coordinate]
  exact RingHom.congr_fun heq p

lemma normalization_last_integral {n : ℕ} (Y : Set (Affine ℂ (n + 1)))
    (c : Affine ℂ n) (p : Polynomials ℂ (n + 1)) (hp : p ∈ vanishingIdeal ℂ Y)
    (hc : eval c (normalizationParameter p) ≠ 0) :
    letI : Algebra (Polynomials ℂ n) (CoordinateRing Y) := coordinatePullbackAlgebra Y (normalizationPolynomials c)
    IsIntegral (Polynomials ℂ n) (coordinate Y (Fin.last n)) := by
  classical
  letI : Algebra (Polynomials ℂ n) (CoordinateRing Y) := coordinatePullbackAlgebra Y (normalizationPolynomials c)
  let q := normalizationShear c p
  have hu : IsUnit q.leadingCoeff := normalizationShear_unit_leadingCoeff c p hc
  have hzero : q.eval₂ (coordinatePullback Y (normalizationPolynomials c))
      (coordinate Y (Fin.last n)) = 0 :=
    (normalizationShear_eval Y c p).trans (Ideal.Quotient.eq_zero_iff_mem.mpr hp)
  refine ⟨hu.unit⁻¹.val • q, Polynomial.monic_of_isUnit_leadingCoeff_inv_smul hu, ?_⟩
  change Polynomial.eval₂ (coordinatePullback Y (normalizationPolynomials c))
    (coordinate Y (Fin.last n)) (hu.unit⁻¹.val • q) = 0
  rw [Polynomial.eval₂_smul, hzero, mul_zero]

lemma normalization_adjoin_last_eq_top {n : ℕ} (Y : Set (Affine ℂ (n + 1))) (c : Affine ℂ n) :
    letI : Algebra (Polynomials ℂ n) (CoordinateRing Y) := coordinatePullbackAlgebra Y (normalizationPolynomials c)
    Algebra.adjoin (Polynomials ℂ n) ({coordinate Y (Fin.last n)} : Set (CoordinateRing Y)) = ⊤ := by
  classical
  letI : Algebra (Polynomials ℂ n) (CoordinateRing Y) := coordinatePullbackAlgebra Y (normalizationPolynomials c)
  have halg : algebraMap (Polynomials ℂ n) (CoordinateRing Y) = coordinatePullback Y (normalizationPolynomials c) := rfl
  let S := Algebra.adjoin (Polynomials ℂ n) ({coordinate Y (Fin.last n)} : Set (CoordinateRing Y))
  have hz : coordinate Y (Fin.last n) ∈ S := Algebra.subset_adjoin (Set.mem_singleton _)
  have hvar (i : Fin (n + 1)) : coordinate Y i ∈ S := by
    refine Fin.lastCases hz (fun j => ?_) i
    have h := S.add_mem (S.algebraMap_mem (MvPolynomial.X j))
      (S.mul_mem (S.algebraMap_mem (MvPolynomial.C (c j))) hz)
    simpa [halg, coordinatePullback, coordinate, normalizationPolynomials] using h
  apply top_unique
  intro b hb
  clear hb
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective b
  induction p using MvPolynomial.induction_on with
  | C a =>
    simpa [halg, coordinatePullback] using S.algebraMap_mem (MvPolynomial.C a)
  | add p q hp hq => simpa only [map_add] using S.add_mem hp hq
  | mul_X p i hp => simpa only [map_mul, coordinate, S] using S.mul_mem hp (hvar i)

lemma normalization_module_finite {n : ℕ} (Y : Set (Affine ℂ (n + 1)))
    (c : Affine ℂ n) (p : Polynomials ℂ (n + 1)) (hp : p ∈ vanishingIdeal ℂ Y)
    (hc : eval c (normalizationParameter p) ≠ 0) :
    letI : Algebra (Polynomials ℂ n) (CoordinateRing Y) := coordinatePullbackAlgebra Y (normalizationPolynomials c)
    Module.Finite (Polynomials ℂ n) (CoordinateRing Y) := by
  classical
  letI : Algebra (Polynomials ℂ n) (CoordinateRing Y) := coordinatePullbackAlgebra Y (normalizationPolynomials c)
  let S := Algebra.adjoin (Polynomials ℂ n) ({coordinate Y (Fin.last n)} : Set (CoordinateRing Y))
  letI : Module.Finite (Polynomials ℂ n) S :=
    Algebra.finite_adjoin_simple_of_isIntegral (normalization_last_integral Y c p hp hc)
  apply Module.Finite.of_surjective S.val.toLinearMap
  intro b
  have hS : S = ⊤ := normalization_adjoin_last_eq_top Y c
  have hb : b ∈ S := by rw [hS]; trivial
  exact ⟨⟨b, hb⟩, rfl⟩

lemma module_finite_finiteMorphism {K : Type} [Field K] {n m : ℕ}
    (Y : Set (Affine K n)) (F : PolynomialMap K n m) :
    letI : Algebra (Polynomials K m) (CoordinateRing Y) := coordinatePullbackAlgebra Y F
    Module.Finite (Polynomials K m) (CoordinateRing Y) → FiniteMorphism Y F := by
  classical
  letI : Algebra (Polynomials K m) (CoordinateRing Y) := coordinatePullbackAlgebra Y F
  intro hfinite
  letI := hfinite
  have halg : algebraMap (Polynomials K m) (CoordinateRing Y) = coordinatePullback Y F := rfl
  obtain ⟨s, g, hgen⟩ := Module.Finite.exists_fin (R := Polynomials K m) (M := CoordinateRing Y)
  choose representatives hrep using fun i => Ideal.Quotient.mk_surjective (g i)
  refine ⟨s, representatives, ?_⟩
  intro p
  have hp : Ideal.Quotient.mk (vanishingIdeal K Y) p ∈ Submodule.span (Polynomials K m) (Set.range g) := by
    rw [hgen]; trivial
  obtain ⟨coefficients, hcoeff⟩ := (Submodule.mem_span_range_iff_exists_fun (Polynomials K m)).mp hp
  refine ⟨coefficients, ?_⟩
  have hz : p - ∑ i : Fin s, eval₂Hom MvPolynomial.C F (coefficients i) * representatives i ∈
      vanishingIdeal K Y := by
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    rw [map_sub, map_sum]
    apply sub_eq_zero.mpr
    have h := hcoeff.symm
    simpa only [Algebra.smul_def, halg, coordinatePullback, RingHom.comp_apply, map_mul, hrep] using h
  intro x hx
  simpa only [aeval_def, Algebra.algebraMap_self, eval₂_id, map_sub, map_sum, map_mul,
    evaluation_substitution, sub_eq_zero] using hz x hx

lemma coordinatePullback_injective_of_finite_dimension {K : Type} [Field K] {a n : ℕ}
    (Y : Set (Affine K a)) (F : PolynomialMap K a n)
    (hdim : RSCapacity.algDim Y = ((n : ℕ∞) : WithBot ℕ∞))
    (hfinite : letI : Algebra (Polynomials K n) (CoordinateRing Y) := coordinatePullbackAlgebra Y F
      Module.Finite (Polynomials K n) (CoordinateRing Y)) :
    Function.Injective (coordinatePullback Y F) := by
  classical
  letI : Algebra (Polynomials K n) (CoordinateRing Y) := coordinatePullbackAlgebra Y F
  letI : Module.Finite (Polynomials K n) (CoordinateRing Y) := hfinite
  let f : Polynomials K n →+* CoordinateRing Y := algebraMap (Polynomials K n) (CoordinateRing Y)
  have hf : f.IsIntegral := Algebra.IsIntegral.isIntegral
  have hdimBound := ringKrullDim_le_of_ringHom_isIntegral f.kerLift hf.kerLift
  have hdimBase : ringKrullDim (Polynomials K n) = ((n : ℕ∞) : WithBot ℕ∞) := by simp [Polynomials]
  change ringKrullDim (CoordinateRing Y) = ((n : ℕ∞) : WithBot ℕ∞) at hdim
  rw [RingHom.injective_iff_ker_eq_bot]
  by_contra hker
  obtain ⟨r, hr, hrne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hker
  have hquot := ringKrullDim_succ_le_of_surjective (Ideal.Quotient.mk (RingHom.ker f))
    Ideal.Quotient.mk_surjective (mem_nonZeroDivisors_iff_ne_zero.mpr hrne)
    (Ideal.Quotient.eq_zero_iff_mem.mpr hr)
  have hbad := (add_le_add hdimBound le_rfl).trans hquot
  rw [hdim, hdimBase] at hbad
  have hn : n + 1 ≤ n := by exact_mod_cast hbad
  omega

lemma vanishingIdeal_ne_bot_of_codimension_one {K : Type} [Field K] {n : ℕ}
    (Y : Set (Affine K (n + 1)))
    (hdim : RSCapacity.algDim Y = ((n : ℕ∞) : WithBot ℕ∞)) : vanishingIdeal K Y ≠ ⊥ := by
  intro h
  change ringKrullDim (Polynomials K (n + 1) ⧸ vanishingIdeal K Y) = ((n : ℕ∞) : WithBot ℕ∞) at hdim
  rw [h, ringKrullDim_eq_of_ringEquiv (RingEquiv.quotientBot _)] at hdim
  have hn : n + 1 = n := by exact_mod_cast (by simpa [Polynomials] using hdim :
    (((n + 1 : ℕ) : ℕ∞) : WithBot ℕ∞) = ((n : ℕ∞) : WithBot ℕ∞))
  omega

lemma module_finite_coordinatesIntegral {K : Type} [Field K] {a n : ℕ}
    (Y : Set (Affine K a)) (hY : IrreducibleAffine Y) (F : PolynomialMap K a n)
    (hfinite : letI : Algebra (Polynomials K n) (CoordinateRing Y) := coordinatePullbackAlgebra Y F
      Module.Finite (Polynomials K n) (CoordinateRing Y)) : CoordinatesIntegral Y F := by
  classical
  letI : (vanishingIdeal K Y).IsPrime := irreducibleAffine_ideal_prime hY
  letI : Algebra (Polynomials K n) (CoordinateRing Y) := coordinatePullbackAlgebra Y F
  letI : Module.Finite (Polynomials K n) (CoordinateRing Y) := hfinite
  have halg : algebraMap (Polynomials K n) (CoordinateRing Y) = coordinatePullback Y F := rfl
  intro j
  obtain ⟨p, hp, hroot⟩ := Algebra.IsIntegral.isIntegral (R := Polynomials K n) (coordinate Y j)
  have hd : 0 < p.natDegree := by
    by_contra h
    have hp1 := Polynomial.eq_one_of_monic_natDegree_zero hp (Nat.eq_zero_of_not_pos h)
    simpa [hp1] using hroot
  refine ⟨p.natDegree, hd, fun i => p.coeff i.val, ?_⟩
  intro x hx
  let ex : CoordinateRing Y →+* K := Ideal.Quotient.lift (vanishingIdeal K Y)
    (MvPolynomial.eval x) (fun q hq => by
      simpa only [aeval_def, Algebra.algebraMap_self, eval₂_id] using hq x hx)
  have hcomp : ex.comp (algebraMap (Polynomials K n) (CoordinateRing Y)) = eval (evaluate F x) := by
    apply MvPolynomial.ringHom_ext
    · intro c; simp [ex, halg, coordinatePullback]
    · intro i; simp [ex, halg, coordinatePullback, evaluate]
  have hz : ex (coordinate Y j) = x j := by simp [ex, coordinate]
  have hpoint : Polynomial.eval₂ (eval (evaluate F x)) (x j) p = 0 := by
    have h := congrArg ex hroot
    rw [Polynomial.hom_eval₂, hcomp, hz, map_zero] at h
    exact h
  rw [Polynomial.eval₂_eq_sum_range, Finset.sum_range_succ, hp.coeff_natDegree, map_one, one_mul] at hpoint
  rw [← Fin.sum_univ_eq_sum_range] at hpoint
  simpa only [add_comm] using hpoint

end APSCounting893.Main

open APSCounting893.Main
end Component_27

section Component_28
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option synthInstance.maxHeartbeats 400000
set_option maxSynthPendingDepth 5
set_option backward.isDefEq.respectTransparency.types false
open MvPolynomial
namespace APSCounting893.Main

lemma finiteMorphism_of_projective_avoidance {K : Type} [Field K] [IsAlgClosed K] {n r : ℕ}
    (Y : Set (Affine K n)) (P : PolynomialMap K n r)
    (hP : ∀ i, (P i).IsHomogeneous 1)
    (hzero : zeroLocus K (chartHomogeneousIdeal Y ⊔ Ideal.span (Set.range (fun i => MvPolynomial.rename Fin.succ (P i)))) ⊆ {0}) :
    FiniteMorphism Y P := by
  classical
  let I := chartHomogeneousIdeal Y
  let ell : Fin r → Polynomials K (n+1) := fun i => MvPolynomial.rename Fin.succ (P i)
  let S := Polynomials K r
  let R := CoordinateRing Y
  letI : Algebra S R := coordinatePullbackAlgebra Y P
  let phi : S →ₐ[K] R := (Ideal.Quotient.mkₐ K (vanishingIdeal K Y)).comp (MvPolynomial.aeval P)
  have hmap : algebraMap S R = phi.toRingHom := by
    ext x <;> rfl
  letI : IsScalarTower K S R := IsScalarTower.of_algebraMap_eq (fun c => by
    rw [hmap]
    exact (phi.commutes c).symm)
  have hpowers (j : Fin n) := coordinate_power_mem_of_zeroLocus_subset_zero
    (I ⊔ Ideal.span (Set.range ell)) hzero j.succ
  choose N hN hpow using hpowers
  have hrels (j : Fin n) := homogeneous_power_linear_relation I (chartHomogeneousIdeal_isHomogeneous Y) ell
    (fun i => (hP i).rename_isHomogeneous) j.succ (N j) (hN j) (hpow j)
  choose h hdegree hrelation using hrels
  have hfinite : Module.Finite S R := by
    apply finite_module_of_degree_lowering_relations (Ideal.Quotient.mkₐ K (vanishingIdeal K Y))
      Ideal.Quotient.mk_surjective N hN (fun i => MvPolynomial.X i)
      (fun j i => chartDehomogenize (h j i))
    · intro j i
      exact (chartDehomogenize_degree (h j i)).trans_lt (hdegree j i)
    · intro j
      have hmem := chartDehomogenize_mem_vanishing Y _ (hrelation j)
      have hh := Ideal.Quotient.eq_zero_iff_mem.mpr hmem
      rw [map_sub,map_pow,map_sum] at hh
      have hx : chartDehomogenize (MvPolynomial.X j.succ : Polynomials K (n+1)) = MvPolynomial.X j := by
        simp [chartDehomogenize]
      rw [hx,map_sub,map_pow,map_sum,sub_eq_zero] at hh
      change Ideal.Quotient.mk (vanishingIdeal K Y) (MvPolynomial.X j ^ N j) = _
      rw [map_pow,hh]
      apply Finset.sum_congr rfl
      intro i hi
      rw [map_mul,map_mul,Algebra.smul_def]
      change _ = phi (MvPolynomial.X i) * _
      congr 1
      rw [show ell i = MvPolynomial.rename Fin.succ (P i) from rfl,chartDehomogenize_rename_succ]
      change Ideal.Quotient.mk _ (P i) = Ideal.Quotient.mk _ (MvPolynomial.aeval P (MvPolynomial.X i))
      rw [MvPolynomial.aeval_X]
  exact module_finite_finiteMorphism Y P hfinite

end APSCounting893.Main
end Component_28

section Component_29
set_option autoImplicit false
set_option maxHeartbeats 600000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
open MvPolynomial
namespace APSCounting893.Main

lemma coordinatePullback_image_kernel {K : Type} [Field K] [Infinite K] {n m t : ℕ}
    (F : PolynomialMap K n m) (P : PolynomialMap K m t) :
    RingHom.ker (coordinatePullback (imageClosure F) P) =
      vanishingIdeal K (imageClosure (composePolynomialMap F P)) := by
  rw [imageClosure_vanishingIdeal_eq_kernel (composePolynomialMap F P)]
  ext p
  change Ideal.Quotient.mk (vanishingIdeal K (imageClosure F)) (MvPolynomial.eval₂Hom MvPolynomial.C P p) = 0 ↔ _
  rw [Ideal.Quotient.eq_zero_iff_mem,imageClosure_vanishingIdeal_eq_kernel]
  change MvPolynomial.aeval F (MvPolynomial.aeval P p) = 0 ↔ MvPolynomial.aeval (composePolynomialMap F P) p = 0
  rw [aeval_composePolynomialMap]

lemma imageClosure_compose_eq_image_of_finite {K : Type} [Field K] [IsAlgClosed K] {n m t : ℕ}
    (F : PolynomialMap K n m) (P : PolynomialMap K m t)
    (hfinite : FiniteMorphism (imageClosure F) P) :
    imageClosure (composePolynomialMap F P) = evaluate P '' imageClosure F := by
  rw [finiteMorphism_image _ (irreducibleAffine_imageClosure F).2.1 P hfinite,
    coordinatePullback_image_kernel]
  exact (isAlgSet_eq_zeroLocus (irreducibleAffine_imageClosure _).2.1)

lemma image_dimension_compose_eq_of_finite {n m t : ℕ}
    (F : PolynomialMap ℂ n (m+1)) (P : PolynomialMap ℂ (m+1) (t+1))
    (hfinite : FiniteMorphism (imageClosure F) P) :
    RSCapacity.algDim (imageClosure (composePolynomialMap F P)) = RSCapacity.algDim (imageClosure F) := by
  apply le_antisymm (image_dimension_compose_le F P)
  letI : Algebra (Polynomials ℂ (t+1)) (CoordinateRing (imageClosure F)) := coordinatePullbackAlgebra (imageClosure F) P
  letI : Module.Finite (Polynomials ℂ (t+1)) (CoordinateRing (imageClosure F)) := finiteMorphism_module_finite _ P hfinite
  let f := coordinatePullback (imageClosure F) P
  have hf : f.IsIntegral := by
    change (algebraMap (Polynomials ℂ (t+1)) (CoordinateRing (imageClosure F))).IsIntegral
    exact Algebra.IsIntegral.isIntegral
  have hbound := ringKrullDim_le_of_ringHom_isIntegral f.kerLift hf.kerLift
  rw [show RingHom.ker f = vanishingIdeal ℂ (imageClosure (composePolynomialMap F P)) from coordinatePullback_image_kernel F P] at hbound
  exact hbound

end APSCounting893.Main
end Component_29

section Component_30
set_option autoImplicit false
open MvPolynomial
namespace APSCounting893.Main

noncomputable def outputProjection {K : Type} [Field K] {m r : ℕ}
    (A : Fin (r+1) × Fin m → K) : PolynomialMap K m (r+1) :=
  fun i => ∑ j, MvPolynomial.C (A (i,j)) * MvPolynomial.X j

lemma outputProjection_composite {K : Type} [Field K] {n m r : ℕ}
    (F : PolynomialMap K n m) (A : Fin (r+1) × Fin m → K) (i : Fin (r+1)) :
    composePolynomialMap F (outputProjection A) i = ∑ j, MvPolynomial.C (A (i,j)) * F j := by
  classical
  simp [composePolynomialMap,outputProjection]


end APSCounting893.Main
end Component_30

section Component_31
set_option autoImplicit false
set_option maxHeartbeats 600000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
open MvPolynomial
namespace APSCounting893.Main

lemma outputProjection_homogeneous {K : Type} [Field K] {m r : ℕ}
    (A : Fin (r+1) × Fin m → K) (i : Fin (r+1)) : (outputProjection A i).IsHomogeneous 1 := by
  classical
  apply MvPolynomial.IsHomogeneous.sum
  intro j hj
  simpa only [zero_add] using (MvPolynomial.isHomogeneous_C (Fin m) (A (i,j))).mul (MvPolynomial.isHomogeneous_X K j)

lemma projective_avoidance_projection_success {n m r : ℕ} (F : PolynomialMap ℂ n (m+1))
    (A : Fin (r+1) × Fin (m+1) → ℂ)
    (hzero : zeroLocus ℂ (chartHomogeneousIdeal (imageClosure F) ⊔ Ideal.span (Set.range
      (fun i => MvPolynomial.rename Fin.succ (outputProjection A i)))) ⊆ {0}) :
    RSCapacity.algDim (imageClosure (composePolynomialMap F (outputProjection A))) =
        RSCapacity.algDim (imageClosure F) ∧
      ¬ hasAPS F ∧ ¬ hasAPS (composePolynomialMap F (outputProjection A)) := by
  have hfinite := finiteMorphism_of_projective_avoidance (imageClosure F) (outputProjection A)
    (outputProjection_homogeneous A) hzero
  have hdim := image_dimension_compose_eq_of_finite F (outputProjection A) hfinite
  have hpreimage : ∀ y ∈ imageClosure F, evaluate (outputProjection A) y ≠ 0 := by
    intro y hy hz
    have hcone : Fin.cons 1 y ∈ projectiveCone (imageClosure F) :=
      (projectiveCone_chart_iff _ (irreducibleAffine_imageClosure F).2.1 y).mpr hy
    have hmem : Fin.cons 1 y ∈ zeroLocus ℂ (chartHomogeneousIdeal (imageClosure F) ⊔
        Ideal.span (Set.range (fun i => MvPolynomial.rename Fin.succ (outputProjection A i)))) := by
      have hle : chartHomogeneousIdeal (imageClosure F) ⊔
          Ideal.span (Set.range (fun i => MvPolynomial.rename Fin.succ (outputProjection A i))) ≤
          vanishingIdeal ℂ {Fin.cons 1 y} := by
        apply sup_le
        · intro p hp z hz'
          have hz'' : z = Fin.cons 1 y := Set.mem_singleton_iff.mp hz'
          subst z
          exact hcone p hp
        · apply Ideal.span_le.mpr
          rintro p ⟨i,rfl⟩ z hz'
          have hz'' : z = Fin.cons 1 y := Set.mem_singleton_iff.mp hz'
          subst z
          have hh : eval y (outputProjection A i) = 0 := congrFun hz i
          simp only [MvPolynomial.aeval_def,Algebra.algebraMap_self,MvPolynomial.eval₂_id,MvPolynomial.eval_rename]
          have hf : (Fin.cons (1 : ℂ) y) ∘ Fin.succ = y := by funext j; simp
          rw [hf]
          exact hh
      intro p hp
      exact hle hp _ (Set.mem_singleton _)
    have hz' := hzero hmem
    change (Fin.cons (1 : ℂ) y : Affine ℂ (m+2)) = 0 at hz'
    have hh := congrFun hz' 0
    simpa using hh
  have hnotG : ¬ hasAPS (composePolynomialMap F (outputProjection A)) := by
    rw [hasAPS,imageClosure_compose_eq_image_of_finite F (outputProjection A) hfinite]
    rintro ⟨y,hy,hy0⟩
    exact hpreimage y hy hy0
  refine ⟨hdim,?_,hnotG⟩
  intro hF
  have hz : evaluate (outputProjection A) (0 : Affine ℂ (m+1)) = 0 := by
    funext i
    simp [evaluate,outputProjection]
  exact hpreimage 0 hF hz

end APSCounting893.Main
end Component_31

section Component_32
set_option autoImplicit false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency.types false
open MvPolynomial
namespace APSCounting893.Main

lemma cone_avoidance_of_incidence_relation {n m r : ℕ} (F : PolynomialMap ℂ n (m+1))
    (h0 : ¬ hasAPS F) (j : Fin (m+1)) (hF : F j ≠ 0)
    (q : MvPolynomial (Fin (r+1) × Fin (m+1)) ℂ)
    (hq : ∀ z ∈ imageClosure (outputConePolynomialMap F), ∀ B : Fin (r+1) × Fin (m+1) → ℂ,
      eval (incidenceMatrixAt j z B) q = 0)
    (A : Fin (r+1) × Fin (m+1) → ℂ) (hA : eval A q ≠ 0) :
    zeroLocus ℂ (chartHomogeneousIdeal (imageClosure F) ⊔ Ideal.span (Set.range
      (fun i => MvPolynomial.rename Fin.succ (outputProjection A i)))) ⊆ {0} := by
  classical
  let I := chartHomogeneousIdeal (imageClosure F)
  let J := Ideal.span (Set.range (fun i => MvPolynomial.rename Fin.succ (outputProjection A i)))
  intro z hz
  change z=0
  by_contra hne
  have hcone : z ∈ projectiveCone (imageClosure F) := by
    intro p hp
    exact hz p ((show I ≤ I ⊔ J from le_sup_left) hp)
  have hout := cone_output_nonzero_of_origin_excluded (imageClosure F)
    (irreducibleAffine_imageClosure F).2.1 h0 z hcone hne
  have hmem := cone_output_mem_outputConeClosure F z hcone
  have hmat (i : Fin (r+1)) : ∑ l : Fin (m+1), A (i,l)*z l.succ=0 := by
    have hi : MvPolynomial.rename Fin.succ (outputProjection A i) ∈
        chartHomogeneousIdeal (imageClosure F) ⊔ Ideal.span (Set.range
          (fun i => MvPolynomial.rename Fin.succ (outputProjection A i))) :=
      (show J ≤ I ⊔ J from le_sup_right) (Ideal.subset_span (Set.mem_range_self i))
    have hh := hz _ hi
    simpa [MvPolynomial.aeval_def,Algebra.algebraMap_self,MvPolynomial.eval₂_id,
      MvPolynomial.eval_rename,outputProjection] using hh
  exact hA (incidence_relation_vanishes_on_common_zero (imageClosure (outputConePolynomialMap F))
    (irreducibleAffine_imageClosure _) j (outputConeClosure_coordinate_nonzero F j hF) q hq
    (fun i => z i.succ) hmem hout A hmat)

lemma projection_success_of_incidence_relation {n m r : ℕ} (F : PolynomialMap ℂ n (m+1))
    (hdim : RSCapacity.algDim (imageClosure F) = ((r : ℕ∞) : WithBot ℕ∞))
    (h0 : ¬ hasAPS F) (j : Fin (m+1)) (hF : F j ≠ 0)
    (q : MvPolynomial (Fin (r+1) × Fin (m+1)) ℂ)
    (hq : ∀ z ∈ imageClosure (outputConePolynomialMap F), ∀ B : Fin (r+1) × Fin (m+1) → ℂ,
      eval (incidenceMatrixAt j z B) q = 0)
    (A : Fin (r+1) × Fin (m+1) → ℂ) (hA : eval A q ≠ 0) :
    RSCapacity.algDim (imageClosure (composePolynomialMap F (outputProjection A))) = ((r : ℕ∞) : WithBot ℕ∞) ∧
      (hasAPS F ↔ hasAPS (composePolynomialMap F (outputProjection A))) := by
  obtain ⟨hd,hnotF,hnotG⟩ := projective_avoidance_projection_success F A
    (cone_avoidance_of_incidence_relation F h0 j hF q hq A hA)
  exact ⟨hd.trans hdim,iff_of_false hnotF hnotG⟩

end APSCounting893.Main
end Component_32

section Component_33
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 100000
set_option backward.isDefEq.respectTransparency.types false
open MvPolynomial
namespace APSCounting893.Main

lemma exists_independent_image_coordinates {n m r : ℕ} (F : PolynomialMap ℂ n (m+1))
    (hdim : RSCapacity.algDim (imageClosure F) = ((r : ℕ∞) : WithBot ℕ∞)) :
    ∃ g : Fin r → Fin (m+1), Function.Injective g ∧ AlgebraicIndependent ℂ (F ∘ g) := by
  classical
  let S := MvPolynomial (Fin (m+1)) ℂ
  let R := MvPolynomial (Fin n) ℂ
  let P : Ideal S := RingHom.ker (MvPolynomial.aeval F).toRingHom
  letI : P.IsPrime := RingHom.ker_isPrime _
  obtain ⟨s,hind,hcard⟩ := OAI.PiExponent.FormalInterpolation.mvPolynomial_exists_coordinate_transcendence_basis P
  have hDim := OAI.PiExponent.FormalInterpolation.mvPolynomial_quotient_dimension_eq_fraction_field_trdeg_toNat P
  have hP : vanishingIdeal ℂ (imageClosure F) = P := by
    rw [imageClosure,vanishingIdeal_zClosure,image_vanishingIdeal_eq_kernel]
    rfl
  change ringKrullDim (S ⧸ vanishingIdeal ℂ (imageClosure F)) = ((r : ℕ∞) : WithBot ℕ∞) at hdim
  rw [hP] at hdim
  have htr : (Algebra.trdeg ℂ (FractionRing (S ⧸ P))).toNat = r := by
    exact_mod_cast hDim.symm.trans hdim
  have hsr : s.card = r := hcard.trans htr
  let f₀ : (S ⧸ P) →ₐ[ℂ] FractionRing (S ⧸ P) := IsScalarTower.toAlgHom ℂ (S ⧸ P) _
  have he (i : s) : f₀ (Ideal.Quotient.mk P (MvPolynomial.X i.1)) =
      algebraMap S (FractionRing (S ⧸ P)) (MvPolynomial.X i.1) := by
    dsimp only [f₀]
    rw [IsScalarTower.toAlgHom_apply,IsScalarTower.algebraMap_apply S (S ⧸ P) (FractionRing (S ⧸ P))]
    rfl
  have hquot : AlgebraicIndependent ℂ (fun i : s => Ideal.Quotient.mk P (MvPolynomial.X i.1)) := by
    apply AlgebraicIndependent.of_comp f₀
    have hef : (f₀ ∘ (fun i : s => Ideal.Quotient.mk P (MvPolynomial.X i.1))) =
        fun i : s => algebraMap S (FractionRing (S ⧸ P)) (MvPolynomial.X i.1) := funext he
    rw [hef]
    exact hind
  let f : (S ⧸ P) →ₐ[ℂ] R := Ideal.Quotient.liftₐ P (MvPolynomial.aeval F) (fun p hp => hp)
  have hfapp (p : S) : f (Ideal.Quotient.mk P p) = MvPolynomial.aeval F p := rfl
  have hf : Function.Injective f := by
    apply (injective_iff_map_eq_zero f.toRingHom).mpr
    intro x hx
    obtain ⟨p,rfl⟩ := Ideal.Quotient.mk_surjective x
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    change MvPolynomial.aeval F p = 0
    change f (Ideal.Quotient.mk P p) = 0 at hx
    rw [hfapp] at hx
    exact hx
  have hindF : AlgebraicIndependent ℂ (fun i : s => F i.1) := by
    have hh := hquot.map' hf
    have hefun : (f ∘ (fun i : s => Ideal.Quotient.mk P (MvPolynomial.X i.1))) =
        fun i : s => F i.1 := by
      funext i
      change f (Ideal.Quotient.mk P (MvPolynomial.X i.1)) = F i.1
      rw [hfapp,MvPolynomial.aeval_X]
    rw [hefun] at hh
    exact hh
  let e : Fin r ≃ s := Fintype.equivOfCardEq (by simpa only [Fintype.card_fin,Fintype.card_coe] using hsr.symm)
  refine ⟨fun i => (e i).1,Subtype.val_injective.comp e.injective,?_⟩
  exact hindF.comp e e.injective

end APSCounting893.Main
end Component_33

section Component_34
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
open MvPolynomial
namespace APSCounting893.Main

lemma image_dimension_lower_of_independent_coordinates {n m r : ℕ}
    (F : PolynomialMap ℂ n (m+1)) (g : Fin r → Fin (m+1))
    (hF : AlgebraicIndependent ℂ (F ∘ g)) :
    ((r : ℕ∞) : WithBot ℕ∞) ≤ RSCapacity.algDim (imageClosure F) := by
  classical
  let P := vanishingIdeal ℂ (imageClosure F)
  letI : P.IsPrime := irreducibleAffine_ideal_prime (irreducibleAffine_imageClosure F)
  have hcoord : AlgebraicIndependent ℂ (fun i => coordinate (imageClosure F) (g i)) := by
    apply AlgebraicIndependent.of_comp (imageCoordinateAlgebraMap F)
    have he : (imageCoordinateAlgebraMap F ∘ (fun i => coordinate (imageClosure F) (g i))) = F ∘ g := by
      funext i
      exact imageCoordinateAlgebraMap_coordinate F (g i)
    rw [he]
    exact hF
  exact prime_quotient_dimension_lower_of_independent P _ hcoord

end APSCounting893.Main
end Component_34

section Component_35
set_option autoImplicit false
set_option maxHeartbeats 400000
open MvPolynomial
namespace APSCounting893.Main

lemma totalDegree_determinant_le_row_bound {R σ ι : Type} [CommRing R] [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι (MvPolynomial σ R)) (d : ι → ℕ)
    (hd : ∀ i j, (M i j).totalDegree ≤ d i) :
    M.det.totalDegree ≤ ∑ i, d i := by
  classical
  rw [Matrix.det_apply']
  apply MvPolynomial.totalDegree_finsetSum_le
  intro s hs
  have hcast : ((Equiv.Perm.sign s : MvPolynomial σ R)).totalDegree = 0 := by
    rcases Int.units_eq_one_or (Equiv.Perm.sign s) with hh | hh <;> rw [hh] <;> simp
  apply (MvPolynomial.totalDegree_mul _ _).trans
  rw [hcast,zero_add]
  apply (MvPolynomial.totalDegree_finsetProd _ _).trans
  calc
    (∑ i, (M (s i) i).totalDegree) ≤ ∑ i, d (s i) := Finset.sum_le_sum (fun i hi => hd _ _)
    _ = ∑ i, d i := Equiv.sum_comp s d

end APSCounting893.Main
end Component_35

section Component_36
set_option autoImplicit false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency.types false
open MvPolynomial Matrix
namespace APSCounting893.Main

noncomputable def outputRankMatrix {K : Type} [Field K] {n m r : ℕ}
    (F : PolynomialMap K n m) (j : Fin r → Fin n) (x : Fin n → K) :
    Matrix (Fin r) (Fin r) (MvPolynomial (Fin (r+1) × Fin m) K) :=
  fun i a => ∑ b : Fin m, MvPolynomial.C (eval x (pderiv (j a) (F b))) * MvPolynomial.X (i.castSucc,b)

lemma outputRankMatrix_degree {K : Type} [Field K] {n m r : ℕ}
    (F : PolynomialMap K n m) (j : Fin r → Fin n) (x : Fin n → K) :
    (outputRankMatrix F j x).det.totalDegree ≤ r := by
  classical
  have hh := totalDegree_determinant_le_row_bound (outputRankMatrix F j x) (fun _ => 1) (by
    intro i a
    apply MvPolynomial.totalDegree_finsetSum_le
    intro b hb
    exact (MvPolynomial.totalDegree_mul _ _).trans (by simp))
  simpa using hh

lemma outputRankMatrix_eval {K : Type} [Field K] {n m r : ℕ}
    (F : PolynomialMap K n m) (j : Fin r → Fin n) (x : Fin n → K)
    (A : Fin (r+1) × Fin m → K) :
    (outputRankMatrix F j x).map (eval A) = Matrix.of (fun i a =>
      eval x (pderiv (j a) (composePolynomialMap F (outputProjection A) i.castSucc))) := by
  classical
  ext i a
  rw [Matrix.map_apply,Matrix.of_apply,outputProjection_composite]
  simp [outputRankMatrix,map_sum,MvPolynomial.pderiv_mul,mul_comm]

lemma output_rank_certificate {n m r : ℕ} (F : PolynomialMap ℂ n (m+1))
    (hdim : RSCapacity.algDim (imageClosure F) = ((r : ℕ∞) : WithBot ℕ∞)) :
    ∃ q : MvPolynomial (Fin (r+1) × Fin (m+1)) ℂ, q ≠ 0 ∧ q.totalDegree ≤ r ∧
      ∀ A : Fin (r+1) × Fin (m+1) → ℂ, eval A q ≠ 0 →
        RSCapacity.algDim (imageClosure (composePolynomialMap F (outputProjection A))) = ((r : ℕ∞) : WithBot ℕ∞) := by
  classical
  obtain ⟨g,hg,hInd⟩ := exists_independent_image_coordinates F hdim
  obtain ⟨j,hj,hminor⟩ := (jacobian_independence_criterion (F ∘ g)).mp hInd
  obtain ⟨x,hx⟩ : ∃ x : Fin n → ℂ, eval x (Matrix.of (fun i a => pderiv (j a) (F (g i)))).det ≠ 0 := by
    by_contra h
    push Not at h
    apply hminor
    apply MvPolynomial.funext
    intro x
    simpa only [map_zero,Function.comp_def] using h x
  let A₀ : Fin (r+1) × Fin (m+1) → ℂ := fun b =>
    if h : b.1.val < r then if b.2 = g ⟨b.1.val,h⟩ then 1 else 0 else 0
  have hA₀ (i : Fin r) (b : Fin (m+1)) : A₀ (i.castSucc,b) = if b=g i then 1 else 0 := by simp [A₀,i.isLt]
  let q := (outputRankMatrix F j x).det
  have hnonzero : q ≠ 0 := by
    intro hz
    have he := congrArg (eval A₀) hz
    rw [map_zero,RingHom.map_det] at he
    have hm : (outputRankMatrix F j x).map (eval A₀) = Matrix.of (fun i a => eval x (pderiv (j a) (F (g i)))) := by
      ext i a
      simp [outputRankMatrix,hA₀,mul_ite]
    change ((outputRankMatrix F j x).map (eval A₀)).det = 0 at he
    rw [hm] at he
    apply hx
    rw [RingHom.map_det]
    exact he
  refine ⟨q,hnonzero,outputRankMatrix_degree F j x,?_⟩
  intro A hq
  apply le_antisymm ((image_dimension_compose_le F (outputProjection A)).trans_eq hdim)
  have hdet : (Matrix.of (fun i a => pderiv (j a)
      (composePolynomialMap F (outputProjection A) i.castSucc))).det ≠ 0 := by
    intro hz
    apply hq
    change eval A (outputRankMatrix F j x).det = 0
    rw [RingHom.map_det]
    change ((outputRankMatrix F j x).map (eval A)).det = 0
    rw [outputRankMatrix_eval]
    have hh := congrArg (eval x) hz
    rw [map_zero,RingHom.map_det] at hh
    exact hh
  have hind := (jacobian_independence_criterion (fun i : Fin r => composePolynomialMap F (outputProjection A) i.castSucc)).mpr ⟨j,hj,hdet⟩
  have hlo := image_dimension_lower_of_independent_coordinates (composePolynomialMap F (outputProjection A)) Fin.castSucc hind
  exact hlo

lemma hasAPS_outputProjection {n m r : ℕ}
    (F : PolynomialMap ℂ n m) (A : Fin (r+1) × Fin m → ℂ) (hF : hasAPS F) :
    hasAPS (composePolynomialMap F (outputProjection A)) := by
  have hzero : evaluate (outputProjection A) 0 = 0 := by
    funext i
    simp [evaluate,outputProjection]
  have hh := polynomialImage_maps_closure F (outputProjection A) ⟨0,hF,rfl⟩
  rwa [hzero] at hh

end APSCounting893.Main
end Component_36

section Component_37
set_option autoImplicit false
set_option maxHeartbeats 400000
open MvPolynomial
namespace APSCounting893.Main

lemma output_projection_certificate_of_hasAPS {n m r : ℕ} (F : PolynomialMap ℂ n (m+1))
    (hdim : RSCapacity.algDim (imageClosure F) = ((r : ℕ∞) : WithBot ℕ∞)) (hF : hasAPS F) :
    ∃ p : MvPolynomial (Fin (r+1) × Fin (m+1)) ℂ,
      p ≠ 0 ∧ p.totalDegree ≤ (r+1)*(inputDegree F)^r ∧
      ∀ A : Fin (r+1) × Fin (m+1) → ℚ,
        eval (fun a => (A a : ℂ)) p ≠ 0 →
        RSCapacity.algDim (imageClosure
          (fun i : Fin (r+1) => ∑ j : Fin (m+1), MvPolynomial.C (A (i,j) : ℂ) * F j)) = ((r : ℕ∞) : WithBot ℕ∞) ∧
        (hasAPS F ↔ hasAPS (fun i : Fin (r+1) => ∑ j : Fin (m+1), MvPolynomial.C (A (i,j) : ℂ) * F j)) := by
  classical
  obtain ⟨q,hq,hdeg,hgood⟩ := output_rank_certificate F hdim
  have hbound : r ≤ (r+1)*(inputDegree F)^r := by
    have hh : 1 ≤ (inputDegree F)^r := one_le_pow₀ (le_max_left _ _)
    nlinarith
  refine ⟨q,hq,hdeg.trans hbound,?_⟩
  intro A hA
  have hd := hgood (fun a => (A a : ℂ)) hA
  have hAPS := hasAPS_outputProjection F (fun a => (A a : ℂ)) hF
  have hmap : composePolynomialMap F (outputProjection (fun a => (A a : ℂ))) =
      fun i : Fin (r+1) => ∑ j : Fin (m+1), MvPolynomial.C (A (i,j) : ℂ)*F j := by
    funext i
    exact outputProjection_composite F _ i
  rw [hmap] at hd hAPS
  exact ⟨hd,iff_of_true hF hAPS⟩

end APSCounting893.Main
end Component_37

section Component_38
set_option autoImplicit false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency.types false
open MvPolynomial
namespace APSCounting893.Main

lemma output_projection_certificate_from_incidence
    {n m r : ℕ} (F : PolynomialMap ℂ n m)
    (hrpos : 0 < r) (hrm : r < m)
    (hdim : RSCapacity.algDim (imageClosure F) = ((r : ℕ∞) : WithBot ℕ∞)) :
    ∃ p : MvPolynomial (Fin (r+1) × Fin m) ℂ,
      p ≠ 0 ∧ p.totalDegree ≤ (r+1)*(inputDegree F)^r ∧
      ∀ A : Fin (r+1) × Fin m → ℚ,
        eval (fun a => (A a : ℂ)) p ≠ 0 →
        RSCapacity.algDim (imageClosure
          (fun i : Fin (r+1) => ∑ j : Fin m, MvPolynomial.C (A (i,j) : ℂ) * F j)) = ((r : ℕ∞) : WithBot ℕ∞) ∧
        (hasAPS F ↔ hasAPS (fun i : Fin (r+1) => ∑ j : Fin m, MvPolynomial.C (A (i,j) : ℂ) * F j)) := by
  classical
  obtain ⟨m,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show m ≠ 0 by omega)
  by_cases h0 : hasAPS F
  · exact output_projection_certificate_of_hasAPS F hdim h0
  · have hex : ∃ j : Fin (m+1), F j ≠ 0 := by
      by_contra h
      push Not at h
      apply h0
      have hz : evaluate F (0 : Affine ℂ n) = 0 := by
        funext i
        simp [evaluate,h i]
      rw [hasAPS,← hz]
      exact zeroLocus_vanishingIdeal_le _ (Set.mem_range_self _)
    obtain ⟨j,hj⟩ := hex
    obtain ⟨q,hq,hdeg,hrelation⟩ := projective_incidence_relation_degree_bound F hrpos hrm hdim h0 j hj
    change ∀ z ∈ imageClosure (outputConePolynomialMap F), ∀ B : Fin (r+1) × Fin (m+1) → ℂ,
      eval (incidenceMatrixAt j z B) q=0 at hrelation
    refine ⟨q,hq,hdeg,?_⟩
    intro A hA
    have hh := projection_success_of_incidence_relation F hdim h0 j hj q hrelation (fun a => (A a : ℂ)) hA
    have hmap : composePolynomialMap F (outputProjection (fun a => (A a : ℂ))) =
        fun i : Fin (r+1) => ∑ j : Fin (m+1), MvPolynomial.C (A (i,j) : ℂ)*F j := by
      funext i
      exact outputProjection_composite F _ i
    rwa [hmap] at hh

end APSCounting893.Main
end Component_38

open APSCounting893.Main
open MvPolynomial
theorem solution
    {n m r : ℕ} (F : APSCounting893.Main.PolynomialMap ℂ n m)
    (hrpos : 0 < r) (hrm : r < m)
    (hdim : RSCapacity.algDim (APSCounting893.Main.imageClosure F) = ((r : ℕ∞) : WithBot ℕ∞)) :
    ∃ p : MvPolynomial (Fin (r+1) × Fin m) ℂ,
      p ≠ 0 ∧ p.totalDegree ≤ (r+1)*(APSCounting893.Main.inputDegree F)^r ∧
      ∀ A : Fin (r+1) × Fin m → ℚ,
        eval (fun a => (A a : ℂ)) p ≠ 0 →
        RSCapacity.algDim (APSCounting893.Main.imageClosure
          (fun i : Fin (r+1) => ∑ j : Fin m, MvPolynomial.C (A (i,j) : ℂ) * F j)) = ((r : ℕ∞) : WithBot ℕ∞) ∧
        (APSCounting893.Main.hasAPS F ↔ APSCounting893.Main.hasAPS
          (fun i : Fin (r+1) => ∑ j : Fin m, MvPolynomial.C (A (i,j) : ℂ) * F j)) := by
  exact output_projection_certificate_from_incidence F hrpos hrm hdim

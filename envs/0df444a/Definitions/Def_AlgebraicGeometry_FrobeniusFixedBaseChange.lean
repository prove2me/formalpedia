-- Prove2me | Definitions.Def_AlgebraicGeometry_FrobeniusFixedBaseChange
-- name    : AlgebraicGeometry_FrobeniusFixedBaseChange
-- status  : Definition
-- author  : @tomasz
-- created : 2026-11-26T09:17:24.276699+00:00
-- url     : https://prove2.me/theorems/400f5047-8a92-44e1-82d9-10bb1a50e4e3
-- title:
--   Frobenius-fixed classes under scalar extension
-- statement:
--   A scalar extension on a finite-dimensional module induces a bijection on fixed points of compatible Frobenius-semilinear maps over an algebraically closed field.
-- source:
--   Stacks Project, Lemma 59.63.6, https://stacks.math.columbia.edu/tag/0A3P.

import Mathlib.Algebra.CharP.Lemmas
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.FieldTheory.IsSepClosed
import Mathlib.LinearAlgebra.Basis.Basic
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.RingTheory.Jacobson.Ring
import Mathlib.RingTheory.TensorProduct.IsBaseChangeFree
import Mathlib.RingTheory.TensorProduct.Maps
import Mathlib.RingTheory.TensorProduct.Nontrivial
import Mathlib.Tactic.Abel

noncomputable section

section

section

set_option autoImplicit false

open scoped TensorProduct

namespace PhilipponTensorProductOverAlgClosed

section

variable {k B : Type*} [Field k] [CommRing B] [Algebra k B]

private theorem repr_map_left {I A D : Type*}
    [CommRing A] [CommRing D] [Algebra k A] [Algebra k D]
    (b : Module.Basis I k B) (f : A →ₐ[k] D) (x : A ⊗[k] B) (i : I) :
    (b.baseChange D).repr (Algebra.TensorProduct.map f (AlgHom.id k B) x) i =
      f ((b.baseChange A).repr x i) := by
  induction x with
  | zero => simp
  | tmul a y =>
    simp only [Algebra.TensorProduct.map_tmul, AlgHom.id_apply, Module.Basis.baseChange_repr_tmul,
      Algebra.smul_def, map_mul, AlgHom.commutes]
  | add x y hx hy => simp only [map_add, Finsupp.add_apply, hx, hy]

/-- A nonzero finite-type algebra over an algebraically closed field has a rational point. -/
theorem exists_specialization [IsAlgClosed k] (D : Type*) [CommRing D] [Nontrivial D]
    [Algebra k D] [Algebra.FiniteType k D] : Nonempty (D →ₐ[k] k) := by
  obtain ⟨m, hm, _⟩ := Ideal.exists_le_maximal (⊥ : Ideal D) bot_ne_top
  let : m.IsMaximal := hm
  let : Field (D ⧸ m) := Ideal.Quotient.field m
  let : Module.Finite k (D ⧸ m) := finite_of_finite_type_of_isJacobsonRing k (D ⧸ m)
  let e := AlgEquiv.ofBijective (Algebra.ofId k (D ⧸ m))
    IsAlgClosed.algebraMap_bijective_of_isIntegral
  exact ⟨e.symm.toAlgHom.comp (Ideal.Quotient.mkₐ k m)⟩

/-- Over an algebraically closed field, the tensor product of a field extension
with any domain algebra is a domain. -/
theorem isDomain_tensorProduct [IsAlgClosed k] [IsDomain B]
    (A : Type*) [Field A] [Algebra k A] : IsDomain (A ⊗[k] B) := by
  classical
  have hn := Algebra.TensorProduct.nontrivial_of_algebraMap_injective_of_isDomain k A B
    (RingHom.injective _) (RingHom.injective _)
  refine (isDomain_iff_noZeroDivisors_and_nontrivial _).mpr ⟨⟨?_⟩, hn⟩
  intro x y hxy
  by_contra h
  push Not at h
  let I := Module.Free.ChooseBasisIndex k B
  let b : Module.Basis I k B := Module.Free.chooseBasis k B
  let fx := (b.baseChange A).repr x
  let fy := (b.baseChange A).repr y
  have nonzero_index {z : A ⊗[k] B} (hz : z ≠ 0) :
      ∃ i : I, (b.baseChange A).repr z i ≠ 0 := by
    by_contra h'
    push Not at h'
    apply hz ((b.baseChange A).repr.injective ?_)
    ext i
    simpa only [map_zero, Finsupp.zero_apply] using h' i
  obtain ⟨i, hi⟩ := nonzero_index h.1
  obtain ⟨j, hj⟩ := nonzero_index h.2
  let s : Finset A := (fx.support.image fx ∪ fy.support.image fy) ∪ {(fx i)⁻¹, (fy j)⁻¹}
  let R := Algebra.adjoin k (s : Set A)
  let : Algebra.FiniteType k R := Algebra.FiniteType.adjoin_of_finite s.finite_toSet
  have hmem (g : I →₀ A) (hg : g.support.image g ⊆ s) (a : I) : g a ∈ R := by
    by_cases ha : a ∈ g.support
    · exact Algebra.subset_adjoin (hg (Finset.mem_image.mpr ⟨a, ha, rfl⟩))
    · simpa only [Finsupp.notMem_support_iff.mp ha] using R.zero_mem
  have hxs : fx.support.image fx ⊆ s := Finset.Subset.trans Finset.subset_union_left Finset.subset_union_left
  have hys : fy.support.image fy ⊆ s := Finset.Subset.trans Finset.subset_union_right Finset.subset_union_left
  let liftCoeffs (g : I →₀ A) (hg : g.support.image g ⊆ s) : I →₀ R :=
    Finsupp.onFinset g.support (fun a => ⟨g a, hmem g hg a⟩)
      (fun a ha => Finsupp.mem_support_iff.mpr fun ha' => ha (Subtype.ext ha'))
  let X := (b.baseChange R).repr.symm (liftCoeffs fx hxs)
  let Y := (b.baseChange R).repr.symm (liftCoeffs fy hys)
  have hX : (b.baseChange R).repr X = liftCoeffs fx hxs := (b.baseChange R).repr.apply_symm_apply _
  have hY : (b.baseChange R).repr Y = liftCoeffs fy hys := (b.baseChange R).repr.apply_symm_apply _
  let ι := Algebra.TensorProduct.map R.val (AlgHom.id k B)
  have he (z : R ⊗[k] B) (a : I) :
      (b.baseChange A).repr (ι z) a = ((b.baseChange R).repr z a : A) :=
    repr_map_left b R.val z a
  have hι : Function.Injective ι := by
    intro u v huv
    apply (b.baseChange R).repr.injective
    ext a
    exact (he u a).symm.trans ((congrArg (fun z => (b.baseChange A).repr z a) huv).trans (he v a))
  have hx : ι X = x := by
    apply (b.baseChange A).repr.injective
    ext a
    rw [he, hX]
    rfl
  have hy : ι Y = y := by
    apply (b.baseChange A).repr.injective
    ext a
    rw [he, hY]
    rfl
  have hXY : X * Y = 0 := hι (by rw [map_mul, map_zero, hx, hy, hxy])
  obtain ⟨τ⟩ := exists_specialization (k := k) R
  let ψ := Algebra.TensorProduct.map τ (AlgHom.id k B)
  have unit_specializes (a : R) (ha : (a : A) ≠ 0) (ha' : (a : A)⁻¹ ∈ R) : τ a ≠ 0 := by
    let inv : R := ⟨(a : A)⁻¹, ha'⟩
    have e : a * inv = 1 := Subtype.ext (mul_inv_cancel₀ ha)
    have hu : IsUnit a := isUnit_iff_exists_inv.mpr ⟨inv, e⟩
    exact (hu.map τ).ne_zero
  have specialize_nonzero (g : I →₀ A) (hg : g.support.image g ⊆ s)
      (z : R ⊗[k] B) (hz : (b.baseChange R).repr z = liftCoeffs g hg)
      (a : I) (ha : g a ≠ 0) (ha' : (g a)⁻¹ ∈ R) : ψ z ≠ 0 := by
    intro hzero
    have e := repr_map_left b τ z a
    rw [show Algebra.TensorProduct.map τ (AlgHom.id k B) z = 0 from hzero,
      map_zero, Finsupp.zero_apply, hz] at e
    exact unit_specializes _ ha ha' e.symm
  have hxi : (fx i)⁻¹ ∈ R :=
    Algebra.subset_adjoin (Finset.mem_union_right _ (Finset.mem_insert_self _ _))
  have hyj : (fy j)⁻¹ ∈ R :=
    Algebra.subset_adjoin (Finset.mem_union_right _ (Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton_self _))))
  let e := Algebra.TensorProduct.lid k B
  have hzero : e (ψ X) * e (ψ Y) = 0 := by
    rw [← map_mul, ← map_mul, hXY, map_zero, map_zero]
  exact mul_ne_zero
    (fun hzero => specialize_nonzero fx hxs X hX i hi hxi (e.injective (hzero.trans (map_zero e).symm)))
    (fun hzero => specialize_nonzero fy hys Y hY j hj hyj (e.injective (hzero.trans (map_zero e).symm)))
    hzero

end

end PhilipponTensorProductOverAlgClosed

end

section

set_option autoImplicit false

open MvPolynomial
open PhilipponTensorProductOverAlgClosed (exists_specialization)

namespace PhilipponFinitePolynomialSolutions

variable {k E ι : Type*} [Field k] [IsAlgClosed k] [Field E] [Algebra k E] [Finite ι]

/-- If a polynomial system has finitely many solutions over an algebraically
closed field, every solution over a field extension is defined over that field. -/
theorem exists_solution_over_base (eqs : Set (MvPolynomial ι k))
    [Finite {x : ι → k // ∀ p ∈ eqs, aeval x p = 0}]
    (y : ι → E) (hy : ∀ p ∈ eqs, aeval y p = 0) :
    ∃ x : ι → k, (∀ p ∈ eqs, aeval x p = 0) ∧ (algebraMap k E) ∘ x = y := by
  classical
  let S := {x : ι → k // ∀ p ∈ eqs, aeval x p = 0}
  have descend (i : ι) : ∃ a : k, algebraMap k E a = y i := by
    by_contra! hi
    let diff (x : S) := y i - algebraMap k E (x.val i)
    let D := Algebra.adjoin k (Set.range y ∪ Set.range (fun x : S => (diff x)⁻¹))
    let : Algebra.FiniteType k D :=
      Algebra.FiniteType.adjoin_of_finite ((Set.finite_range y).union (Set.finite_range _))
    let z (j : ι) : D := ⟨y j, Algebra.subset_adjoin (Or.inl ⟨j, rfl⟩)⟩
    obtain ⟨τ⟩ := exists_specialization (k := k) D
    have hz (p : MvPolynomial ι k) (hp : p ∈ eqs) : aeval z p = 0 := by
      apply Subtype.val_injective
      change D.val (aeval z p) = 0
      exact (comp_aeval_apply (f := z) D.val p).trans (hy p hp)
    have hτ (p : MvPolynomial ι k) (hp : p ∈ eqs) : aeval (τ ∘ z) p = 0 := by
      calc
        _ = τ (aeval z p) := (comp_aeval_apply (f := z) τ p).symm
        _ = 0 := by rw [hz p hp, map_zero]
    let x : S := ⟨τ ∘ z, hτ⟩
    let r : D := z i - algebraMap k D (x.val i)
    let inv : D := ⟨(diff x)⁻¹, Algebra.subset_adjoin (Or.inr ⟨x, rfl⟩)⟩
    have hr : r * inv = 1 := Subtype.ext (mul_inv_cancel₀ (sub_ne_zero.mpr (Ne.symm (hi _))))
    have hr₀ : τ r = 0 := by
      change τ (z i - algebraMap k D (τ (z i))) = 0
      rw [map_sub, AlgHom.commutes, Algebra.algebraMap_self, RingHom.id_apply, sub_self]
    have hu : IsUnit r := isUnit_iff_exists_inv.mpr ⟨inv, hr⟩
    exact (hu.map τ).ne_zero hr₀
  choose x hx using descend
  have he : (algebraMap k E) ∘ x = y := funext hx
  refine ⟨x, ?_, he⟩
  intro p hp
  apply (algebraMap k E).injective
  rw [map_zero]
  calc
    _ = aeval ((algebraMap k E) ∘ x) p := comp_aeval_apply (f := x) (Algebra.ofId k E) p
    _ = 0 := by rw [he, hy p hp]

end PhilipponFinitePolynomialSolutions

end

section

set_option autoImplicit false
set_option linter.style.haveILetI false

open scoped BigOperators
open Polynomial

namespace PhilipponArtinSchreierLinear

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
variable {p : ℕ} [CharP K p] [FiniteDimensional K V]
variable (F : V →+ V) (hF : ∀ a : K, ∀ v : V, F (a • v) = a ^ p • F v)

private theorem derivative_pow_char (P : K[X]) : (P ^ p).derivative = 0 := by
  rw [derivative_pow]
  simp

private theorem derivative_ne_zero_of_neg_one {P : K[X]} (h : P.derivative = -1) :
    P.derivative ≠ 0 := by
  rw [h]
  simp

include hF in
/-- The fixed vectors form a finite set, even over an imperfect field. -/
theorem finite_fixed : Finite {v : V // F v = v} := by
  classical
  let S : Set V := {v | F v = v}
  obtain ⟨b, hb, hspan, hind⟩ := Submodule.exists_fun_fin_finrank_span_eq K S
  have hrepr (x : S) : ∃ a : _ → K, ∑ i, a i • b i = x.val := by
    apply (Submodule.mem_span_range_iff_exists_fun (R := K)).mp
    rw [hspan]
    exact Submodule.subset_span x.property
  choose a ha using hrepr
  let Q : K[X] := X ^ p - X
  have hQ : Q.derivative = -1 := by
    simp only [Q, derivative_sub, derivative_pow_char, derivative_X, zero_sub]
  letI : Finite {r : K // Q.IsRoot r} :=
    (finite_setOfPred_isRoot fun he =>
      derivative_ne_zero_of_neg_one hQ (by simp [he])).to_subtype
  have hscalar (x : S) (i) : (a x i) ^ p = a x i := by
    refine hind.eq_coords_of_eq (f := fun j => (a x j) ^ p) (g := a x) ?_ i
    calc
      (∑ j, (a x j) ^ p • b j) = F (∑ j, a x j • b j) := by
        simp only [map_sum, hF]
        exact Finset.sum_congr rfl (fun j _ => by rw [show F (b j) = b j from hb j])
      _ = x.val := (congrArg F (ha x)).trans x.property
      _ = ∑ j, a x j • b j := (ha x).symm
  let encode (x : S) (i : _) : {r : K // Q.IsRoot r} :=
    ⟨a x i, by simpa [Q, IsRoot, sub_eq_zero] using hscalar x i⟩
  refine Finite.of_injective encode ?_
  intro x y hxy
  have h : a x = a y := by
    funext i
    exact congrArg Subtype.val (congrFun hxy i)
  exact Subtype.ext ((ha x).symm.trans (h ▸ ha y))

private theorem exists_iterate_relation (v : ℕ → V) :
    ∃ n : ℕ, v (n + 1) ∈ Submodule.span K (Set.range fun i : Fin (n + 1) => v i) ∨
      v 0 = 0 := by
  classical
  let bad (n : ℕ) := ¬ LinearIndependent K (fun i : Fin (n + 1) => v i)
  have hbad : ∃ n, bad n := by
    refine ⟨Module.finrank K V, fun h => ?_⟩
    have hle := h.fintype_card_le_finrank
    simp only [Fintype.card_fin] at hle
    exact Nat.not_succ_le_self _ hle
  generalize hk : Nat.find hbad = k
  have hd : bad k := hk ▸ Nat.find_spec hbad
  cases k with
  | zero =>
    refine ⟨0, Or.inr ?_⟩
    by_contra h
    apply hd
    rw [Fintype.linearIndependent_iff]
    intro g hg i
    have hz : g 0 • v 0 = 0 := by simpa using hg
    simpa [Fin.fin_one_eq_zero i] using (smul_eq_zero.mp hz).resolve_right h
  | succ n =>
    refine ⟨n, Or.inl ?_⟩
    by_contra h
    apply hd
    apply linearIndependent_finSucc'.mpr
    refine ⟨?_, h⟩
    change LinearIndependent K (fun i : Fin (n + 1) => v i)
    by_contra hin
    have hle := Nat.find_min' hbad hin
    rw [hk] at hle
    exact Nat.not_succ_le_self _ hle

private noncomputable def coefficientPolynomial (p : ℕ) (c : ℕ → K) : ℕ → K[X]
  | 0 => C (c 0) * X ^ p - 1
  | i + 1 => coefficientPolynomial p c i ^ p + C (c (i + 1)) * X ^ p

private theorem coefficientPolynomial_derivative (c : ℕ → K) (n : ℕ) :
    (coefficientPolynomial p c n).derivative = 0 := by
  cases n <;>
    simp [coefficientPolynomial, derivative_pow_char, derivative_mul, derivative_C]

omit [CharP K p] [FiniteDimensional K V] in
private theorem sum_coefficientPolynomial_balance (v : ℕ → V) (c : ℕ → K)
    (t : K) (n : ℕ) :
    let a := fun i : ℕ => (coefficientPolynomial p c i).eval t
    (∑ i ∈ Finset.range (n + 1), (a i) ^ p • v (i + 1)) -
        (∑ i ∈ Finset.range (n + 1), a i • v i) =
      (a n) ^ p • v (n + 1) - t ^ p • (∑ i ∈ Finset.range (n + 1), c i • v i) + v 0 := by
  intro a
  have h₀ : a 0 = c 0 * t ^ p - 1 := by simp [a, coefficientPolynomial]
  have hs (i : ℕ) : a (i + 1) = (a i) ^ p + c (i + 1) * t ^ p := by
    simp [a, coefficientPolynomial]
  induction n with
  | zero =>
    simp only [Nat.zero_add, Finset.sum_range_one]
    have hab : a 0 • v 0 = (t ^ p * c 0) • v 0 - v 0 := by
      rw [h₀, sub_smul, one_smul, mul_comm (c 0)]
    rw [hab, smul_smul]
    abel
  | succ n ih =>
    simp only [Finset.sum_range_succ _ (n + 1)]
    rw [show (∑ i ∈ Finset.range (n + 1), a i ^ p • v (i + 1)) +
          a (n + 1) ^ p • v (n + 2) -
        ((∑ i ∈ Finset.range (n + 1), a i • v i) + a (n + 1) • v (n + 1)) =
        ((∑ i ∈ Finset.range (n + 1), a i ^ p • v (i + 1)) -
          (∑ i ∈ Finset.range (n + 1), a i • v i)) +
          a (n + 1) ^ p • v (n + 2) - a (n + 1) • v (n + 1) by abel]
    rw [ih, smul_add, hs n, add_smul, smul_smul, mul_comm (c (n + 1))]
    abel

include hF in
/-- In finite dimension, (F-1) is onto over a separably closed field.
A finite span of iterates of the target reduces the equation to one separable polynomial. -/
theorem surjective_sub_id [IsSepClosed K] : Function.Surjective (fun v : V => F v - v) := by
  classical
  intro w
  let v (i : ℕ) : V := F^[i] w
  have v_zero : v 0 = w := rfl
  have hv (i : ℕ) : F (v i) = v (i + 1) := (Function.iterate_succ_apply' _ _ _).symm
  obtain ⟨n, hn | hzero⟩ := exists_iterate_relation (K := K) v
  · obtain ⟨b, hb⟩ := (Submodule.mem_span_range_iff_exists_fun (R := K)).mp hn
    let c (i : ℕ) : K := if hi : i < n + 1 then b ⟨i, hi⟩ else 0
    have hc : (∑ i ∈ Finset.range (n + 1), c i • v i) = v (n + 1) := by
      rw [← Fin.sum_univ_eq_sum_range]
      refine (Finset.sum_congr rfl (fun i _ => ?_)).trans hb
      simp only [c, dif_pos i.isLt]
    let P : K[X] := coefficientPolynomial p c n - X
    have hP : P.derivative = -1 := by
      simp only [P, derivative_sub, coefficientPolynomial_derivative, derivative_X, zero_sub]
    have hdeg : P.degree ≠ 0 := by
      intro hd
      have he := eq_C_of_degree_le_zero hd.le
      exact derivative_ne_zero_of_neg_one hP (by rw [he, derivative_C])
    have hsep : P.Separable := by
      rw [separable_def']
      exact ⟨0, -1, by simp [hP]⟩
    obtain ⟨t, ht⟩ := IsSepClosed.exists_root P hdeg hsep
    let a (i : ℕ) : K := (coefficientPolynomial p c i).eval t
    have ha : a n = t := by simpa [P, a, IsRoot, sub_eq_zero] using ht
    refine ⟨∑ i ∈ Finset.range (n + 1), a i • v i, ?_⟩
    simp only [map_sum, hF, hv]
    have hbal := sum_coefficientPolynomial_balance (p := p) v c t n
    change (∑ i ∈ Finset.range (n + 1), a i ^ p • v (i + 1)) -
      (∑ i ∈ Finset.range (n + 1), a i • v i) =
      a n ^ p • v (n + 1) - t ^ p • (∑ i ∈ Finset.range (n + 1), c i • v i) + v 0 at hbal
    simpa only [ha, hc, sub_self, zero_add, v_zero] using hbal
  · exact ⟨0, by simpa [v_zero] using hzero.symm⟩

end PhilipponArtinSchreierLinear

end

section

set_option autoImplicit false

open MvPolynomial

namespace PhilipponArtinSchreierFieldExtension

universe u v

variable {k E : Type u} {ι : Type v} [Field k] [Field E] [Algebra k E] [Fintype ι]
variable (p : ℕ) [Fact p.Prime] [CharP k p]

/-- Apply Frobenius coordinatewise and then multiply by the given matrix. -/
def frobeniusMatrix (A : ι → ι → k) : (ι → k) →+ (ι → k) where
  toFun x i := ∑ j, A i j * (x j) ^ p
  map_zero' := by
    funext i
    simp [zero_pow (Fact.out : p.Prime).ne_zero]
  map_add' x y := by
    funext i
    simp only [Pi.add_apply, add_pow_char, mul_add, Finset.sum_add_distrib]

private theorem frobeniusMatrix_smul (A : ι → ι → k) (a : k) (x : ι → k) :
    frobeniusMatrix p A (a • x) = a ^ p • frobeniusMatrix p A x := by
  funext i
  change (∑ j, A i j * (a * x j) ^ p) = a ^ p * (∑ j, A i j * (x j) ^ p)
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl (fun j _ => by rw [mul_pow, mul_left_comm])

/-- Extending an algebraically closed field does not add fixed vectors
for a Frobenius-semilinear matrix. -/
theorem exists_fixed_vector_over_base [IsAlgClosed k] (A : ι → ι → k) (y : ι → E)
    (hy : ∀ i, (∑ j, algebraMap k E (A i j) * (y j) ^ p) = y i) :
    ∃ x : ι → k, frobeniusMatrix p A x = x ∧ (algebraMap k E) ∘ x = y := by
  let Q (i : ι) : MvPolynomial ι k := (∑ j, C (A i j) * X j ^ p) - X i
  have evalQ {B : Type u} [CommRing B] [Algebra k B] (x : ι → B) (i : ι) :
      aeval x (Q i) = (∑ j, algebraMap k B (A i j) * (x j) ^ p) - x i := by
    simp only [Q, map_sub, map_sum, map_mul, map_pow, aeval_C, aeval_X]
  have fixed (x : ι → k) (hx : ∀ q ∈ Set.range Q, aeval x q = 0) :
      frobeniusMatrix p A x = x := by
    funext i
    change (∑ j, A i j * (x j) ^ p) = x i
    exact sub_eq_zero.mp (by simpa only [evalQ, Algebra.algebraMap_self, RingHom.id_apply]
      using (hx (Q i) ⟨i, rfl⟩))
  let : Finite {x : ι → k // ∀ q ∈ Set.range Q, aeval x q = 0} := by
    let : Finite {x : ι → k // frobeniusMatrix p A x = x} :=
      PhilipponArtinSchreierLinear.finite_fixed (frobeniusMatrix p A) (frobeniusMatrix_smul p A)
    let encode (x : {x : ι → k // ∀ q ∈ Set.range Q, aeval x q = 0}) :
        {x : ι → k // frobeniusMatrix p A x = x} := ⟨x.val, fixed x.val x.property⟩
    apply Finite.of_injective encode
    intro x z h
    have he : (encode x).val = (encode z).val := congrArg Subtype.val h
    exact Subtype.ext he
  have hy' : ∀ q ∈ Set.range Q, aeval y q = 0 := by
    rintro q ⟨i, rfl⟩
    rw [evalQ, hy i, sub_self]
  obtain ⟨x, hx, he⟩ :=
    PhilipponFinitePolynomialSolutions.exists_solution_over_base (Set.range Q) y hy'
  exact ⟨x, fixed x hx, he⟩

/-- The subgroup of vectors fixed by a Frobenius-semilinear endomorphism. -/
def fixedSubgroup (A : ι → ι → k) : AddSubgroup (ι → k) :=
  (frobeniusMatrix p A - AddMonoidHom.id (ι → k)).ker

theorem mem_fixedSubgroup_iff (A : ι → ι → k) (x : ι → k) :
    x ∈ fixedSubgroup p A ↔ frobeniusMatrix p A x = x := by
  change frobeniusMatrix p A x - x = 0 ↔ _
  exact sub_eq_zero

/-- Scalar extension induces an additive equivalence on Frobenius-fixed vectors. -/
noncomputable def fixedSubgroupEquiv [IsAlgClosed k] [CharP E p] (A : ι → ι → k) :
    fixedSubgroup p A ≃+ fixedSubgroup p (fun i j => algebraMap k E (A i j)) := by
  let a : (ι → k) →+ (ι → E) :=
    { toFun := fun x i => algebraMap k E (x i)
      map_zero' := funext (fun i => map_zero (algebraMap k E))
      map_add' := fun x y => funext (fun i => map_add (algebraMap k E) (x i) (y i)) }
  let B (i j : ι) := algebraMap k E (A i j)
  let f := (a.comp (fixedSubgroup p A).subtype).codRestrict (fixedSubgroup p B) (fun x => by
    apply (mem_fixedSubgroup_iff p B _).mpr
    have hx := (mem_fixedSubgroup_iff p A x.val).mp x.property
    funext i
    change (∑ j, algebraMap k E (A i j) * (algebraMap k E (x.val j)) ^ p) =
      algebraMap k E (x.val i)
    have hi := congrFun hx i
    change (∑ j, A i j * (x.val j) ^ p) = x.val i at hi
    simpa only [map_sum, map_mul, map_pow] using
      congrArg (algebraMap k E) hi)
  refine AddEquiv.ofBijective f ⟨?_, ?_⟩
  · intro x y h
    apply Subtype.ext
    funext i
    have hval : (f x).val = (f y).val := congrArg Subtype.val h
    exact (algebraMap k E).injective (congrFun hval i)
  · intro y
    have hy := (mem_fixedSubgroup_iff p B y.val).mp y.property
    obtain ⟨x, hx, he⟩ := exists_fixed_vector_over_base p A y.val (congrFun hy)
    exact ⟨⟨x, (mem_fixedSubgroup_iff p A x).mpr hx⟩, Subtype.ext he⟩

omit [Fact p.Prime] in
private theorem repr_frobenius {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (b : Module.Basis ι K V) (F : V →+ V) (hF : ∀ (a : K) (v : V),
      F (a • v) = a ^ p • F v) (v : V) (i : ι) :
    b.repr (F v) i = ∑ j, b.repr (F (b j)) i * (b.repr v j) ^ p := by
  calc
    b.repr (F v) i = b.repr (F (∑ j, b.repr v j • b j)) i := by rw [b.sum_repr]
    _ = _ := by simp only [map_sum, hF, LinearEquiv.map_smul, Finsupp.finsetSum_apply,
      Finsupp.smul_apply, smul_eq_mul, mul_comm]

/-- A comparison that extends coordinates in compatible bases induces a
bijection on the fixed points of Frobenius-semilinear maps. -/
theorem bijective_on_fixed_of_basis [IsAlgClosed k] {V W : Type u}
    [AddCommGroup V] [Module k V] [AddCommGroup W] [Module E W]
    (b : Module.Basis ι k V) (c : Module.Basis ι E W) (t : V →+ W)
    (F : V →+ V) (G : W →+ W)
    (hF : ∀ (a : k) (v : V), F (a • v) = a ^ p • F v)
    (hG : ∀ (a : E) (w : W), G (a • w) = a ^ p • G w)
    (ht : ∀ v i, c.repr (t v) i = algebraMap k E (b.repr v i))
    (hcomm : ∀ v, t (F v) = G (t v)) :
    Function.Bijective (fun v : {v // F v = v} =>
      (⟨t v.val, by rw [← hcomm, v.property]⟩ : {w // G w = w})) := by
  classical
  have hb (j : ι) : t (b j) = c j := by
    apply c.repr.injective
    ext i
    simp only [ht, b.repr_self_apply, c.repr_self_apply]
    split <;> simp_all
  let A (i j : ι) := b.repr (F (b j)) i
  have hA (i j : ι) : c.repr (G (c j)) i = algebraMap k E (A i j) := by
    rw [← hb, ← hcomm, ht]
  constructor
  · intro v z hvz
    apply Subtype.ext
    apply b.repr.injective
    ext i
    apply (algebraMap k E).injective
    simpa only [← ht] using congrArg (fun w : {w // G w = w} => c.repr w.val i) hvz
  · intro w
    have hw (i : ι) : ∑ j, algebraMap k E (A i j) * (c.repr w.val j) ^ p = c.repr w.val i := by
      simpa only [w.property, hA] using (repr_frobenius p c G hG w.val i).symm
    obtain ⟨x, hx, hxt⟩ := exists_fixed_vector_over_base p A (c.repr w.val) hw
    let v := b.equivFun.symm x
    have hv (i : ι) : b.repr v i = x i := by
      simpa only [Module.Basis.equivFun_apply] using congrFun (b.equivFun.apply_symm_apply x) i
    have hfix : F v = v := by
      apply b.repr.injective
      ext i
      rw [repr_frobenius p b F hF, hv]
      simpa only [hv, frobeniusMatrix, AddMonoidHom.coe_mk, ZeroHom.coe_mk, A] using congrFun hx i
    refine ⟨⟨v, hfix⟩, Subtype.ext ?_⟩
    apply c.repr.injective
    ext i
    rw [ht, hv]
    exact congrFun hxt i

/-- Scalar extension on a finite-dimensional module induces a bijection on
the fixed points of compatible Frobenius-semilinear endomorphisms. -/
theorem bijOn_fixed_of_isBaseChange [IsAlgClosed k] {V W : Type u}
    [AddCommGroup V] [Module k V] [Module.Finite k V]
    [AddCommGroup W] [Module k W] [Module E W] [IsScalarTower k E W]
    (t : V →ₗ[k] W) (ht : IsBaseChange E t)
    (F : V →+ V) (G : W →+ W)
    (hF : ∀ (a : k) (v : V), F (a • v) = a ^ p • F v)
    (hG : ∀ (a : E) (w : W), G (a • w) = a ^ p • G w)
    (hcomm : ∀ v, t (F v) = G (t v)) :
    Set.BijOn t {v | F v = v} {w | G w = w} := by
  classical
  let b := Module.finBasis k V
  have h := bijective_on_fixed_of_basis p b (ht.basis b) t.toAddMonoidHom F G hF hG
    (ht.basis_repr_comp_apply b) hcomm
  refine ⟨fun x hx => (hcomm x).symm.trans (congrArg t hx), ?_, ?_⟩
  · intro x hx y hy hxy
    exact congrArg Subtype.val (h.injective (a₁ := ⟨x, hx⟩) (a₂ := ⟨y, hy⟩)
      (Subtype.ext hxy))
  · intro y hy
    obtain ⟨x, hx⟩ := h.surjective ⟨y, hy⟩
    exact ⟨x.val, x.property, congrArg Subtype.val hx⟩

end PhilipponArtinSchreierFieldExtension

end

end



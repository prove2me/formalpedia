-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.exists_finite_surjective_projectiveLinePower_cover
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-11-24T03:05:06.350346+00:00
-- url     : https://prove2.me/submissions/1d9948d5-552e-4378-9136-a951c2e64b54

import Definitions.Def_AlgebraicGeometry_ProjSpace
import Definitions.Def_AlgebraicGeometry_ProjectiveLineTower
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.OfFn
import Mathlib.AlgebraicGeometry.AlgClosed.Basic
import Mathlib.AlgebraicGeometry.ZariskisMainTheorem
import Mathlib.Data.Fintype.Pi
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.Tactic.FieldSimp

noncomputable section

section

section

set_option autoImplicit false


namespace PhilipponProjectiveProductCoefficients

open Polynomial

variable {K : Type*} [CommRing K] {n : ℕ}

/-- The binary form obtained by multiplying the given linear factors,
written in the affine indeterminate so its coefficients index a point
of projective `n`-space. -/
def factorProduct (x y : Fin n → K) : K[X] :=
  ∏ i, (C (x i) * X + C (y i))

lemma factorProduct_map {A : Type*} [CommRing A] (f : K →+* A) (x y : Fin n → K) :
    (factorProduct x y).map f = factorProduct (f ∘ x) (f ∘ y) := by
  simp [factorProduct, Polynomial.map_prod]

/-- Rescaling the pairs of homogeneous coordinates scales every
coefficient of the product by the same product of scalars. -/
theorem factorProduct_scale (a x y : Fin n → K) :
    factorProduct (fun i => a i * x i) (fun i => a i * y i) =
      C (∏ i, a i) * factorProduct x y := by
  unfold factorProduct
  calc
    _ = ∏ i, C (a i) * (C (x i) * X + C (y i)) := by
      apply Finset.prod_congr rfl
      intro i _
      simp only [map_mul, mul_add, mul_assoc]
    _ = _ := by rw [Finset.prod_mul_distrib, map_prod]

theorem natDegree_factorProduct_le (x y : Fin n → K) :
    (factorProduct x y).natDegree ≤ n := by
  classical
  unfold factorProduct
  apply (natDegree_prod_le _ _).trans
  calc
    _ ≤ ∑ _i : Fin n, (1 : ℕ) := by
      apply Finset.sum_le_sum
      intro i _
      apply (natDegree_add_le _ _).trans
      apply max_le
      · exact (natDegree_mul_le).trans (by
          simpa only [natDegree_C, zero_add] using (natDegree_X_le (R := K)))
      · simp
    _ = n := by simp

/-- The product coefficients do not vanish simultaneously when each
factor represents a projective point over a field. -/
theorem exists_nonzero_coefficient [IsDomain K] (x y : Fin n → K)
    (h : ∀ i, x i ≠ 0 ∨ y i ≠ 0) :
    ∃ j : Fin (n + 1), (factorProduct x y).coeff j.val ≠ 0 := by
  have hFactor (i : Fin n) : C (x i) * X + C (y i) ≠ 0 := by
    intro hz
    have hx : x i = 0 := by
      simpa using congrArg (fun p : K[X] => p.coeff 1) hz
    have hy : y i = 0 := by
      simpa using congrArg (fun p : K[X] => p.coeff 0) hz
    exact (h i).elim (fun h => h hx) (fun h => h hy)
  have hn : factorProduct x y ≠ 0 := by
    unfold factorProduct
    exact Finset.prod_ne_zero_iff.mpr fun i _ => hFactor i
  refine ⟨⟨(factorProduct x y).natDegree, Nat.lt_succ_of_le (natDegree_factorProduct_le x y)⟩, ?_⟩
  exact leadingCoeff_ne_zero.mpr hn

/-- Unimodular linear factors have a unimodular product coefficient vector. -/
theorem span_coeff_factorProduct_eq_top (x y : Fin n → K)
    (h : ∀ i, Ideal.span ({x i, y i} : Set K) = ⊤) :
    Ideal.span (Set.range (fun j : Fin (n + 1) => (factorProduct x y).coeff j.val)) = ⊤ := by
  by_contra hproper
  obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal _ hproper
  let : M.IsMaximal := hM
  let f := Ideal.Quotient.mk M
  have hpair (i : Fin n) : (f ∘ x) i ≠ 0 ∨ (f ∘ y) i ≠ 0 := by
    by_contra! hz
    have hMi : Ideal.span ({x i, y i} : Set K) ≤ M := by
      apply Ideal.span_le.mpr
      intro a ha
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha
      rcases ha with rfl | rfl
      · exact Ideal.Quotient.eq_zero_iff_mem.mp hz.1
      · exact Ideal.Quotient.eq_zero_iff_mem.mp hz.2
    exact hM.ne_top (top_le_iff.mp (h i ▸ hMi))
  obtain ⟨j, hj⟩ := exists_nonzero_coefficient (f ∘ x) (f ∘ y) hpair
  apply hj
  rw [← factorProduct_map f, coeff_map]
  exact Ideal.Quotient.eq_zero_iff_mem.mpr
    (hle (Ideal.subset_span ⟨j, rfl⟩))

/-- Proportional coordinate vectors in the prescribed degree bound
give proportional polynomials. -/
lemma eq_C_mul_of_coeff_eq {m : ℕ} {p q : K[X]} {a : K}
    (hp : p.natDegree ≤ m) (hq : q.natDegree ≤ m)
    (h : ∀ j : Fin (m + 1), p.coeff j.val = a * q.coeff j.val) : p = C a * q := by
  ext j
  rw [coeff_C_mul]
  by_cases hj : j ≤ m
  · exact h ⟨j, Nat.lt_succ_of_le hj⟩
  · have hz := Nat.lt_of_not_ge hj
    rw [coeff_eq_zero_of_natDegree_lt (hp.trans_lt hz),
      coeff_eq_zero_of_natDegree_lt (hq.trans_lt hz), mul_zero]

/-- The coefficient vector of the product of the linear forms in a tuple. -/
def coefficients (c : Fin n → Fin 2 → K) (j : Fin (n + 1)) : K :=
  (factorProduct (fun i => c i 0) (fun i => c i 1)).coeff j.val

lemma coefficients_map {A : Type*} [CommRing A] (f : K →+* A) (c : Fin n → Fin 2 → K) :
    f ∘ coefficients c = coefficients (fun i => f ∘ c i) := by
  funext j
  simp only [coefficients, Function.comp_apply, ← coeff_map, factorProduct_map]
  rfl

lemma coefficients_scale (u : Fin n → Kˣ) (c : Fin n → Fin 2 → K) :
    coefficients (fun i j => ↑(u i) * c i j) = fun k => ↑(∏ i, u i) * coefficients c k := by
  funext k
  rw [coefficients, factorProduct_scale, coeff_C_mul, Units.coe_prod]
  rfl

lemma span_coefficients_eq_top (c : Fin n → Fin 2 → K) (a : Fin n → Fin 2)
    (h : ∀ i, IsUnit (c i (a i))) : Ideal.span (Set.range (coefficients c)) = ⊤ := by
  apply span_coeff_factorProduct_eq_top
  intro i
  apply Ideal.eq_top_of_isUnit_mem _ _ (h i)
  apply Ideal.subset_span
  have casesFin (j : Fin 2) : j = 0 ∨ j = 1 := by fin_cases j <;> decide
  have hi := casesFin (a i)
  rcases hi with hi | hi <;> simp [hi]

lemma exists_unit_coefficient {L : Type*} [Field L] (c : Fin n → Fin 2 → L) (a : Fin n → Fin 2)
    (h : ∀ i, IsUnit (c i (a i))) : ∃ k, IsUnit (coefficients c k) := by
  have hn (i : Fin n) : c i 0 ≠ 0 ∨ c i 1 ≠ 0 := by
    have hh : ∀ j : Fin 2, j = 0 ∨ j = 1 := by intro j; fin_cases j <;> decide
    rcases hh (a i) with he | he
    · exact Or.inl (he ▸ (h i).ne_zero)
    · exact Or.inr (he ▸ (h i).ne_zero)
  obtain ⟨k, hk⟩ := exists_nonzero_coefficient (fun i => c i 0) (fun i => c i 1) hn
  exact ⟨k, isUnit_iff_ne_zero.mpr hk⟩

/-- A polynomial of degree at most `n` over an algebraically closed field
is a scalar times a product of `n` projective linear factors. Constant
factors provide the factors at infinity. -/
theorem exists_factorProduct {L : Type*} [Field L] [IsAlgClosed L] {m : ℕ}
    (p : L[X]) (hp : p.natDegree ≤ m) :
    ∃ x y : Fin m → L, (∀ i, x i ≠ 0 ∨ y i ≠ 0) ∧
      p = C p.leadingCoeff * factorProduct x y := by
  classical
  let roots := p.roots.toList
  have hs := IsAlgClosed.splits p
  have hLen : roots.length = p.natDegree := by
    rw [show roots.length = p.roots.card from Multiset.length_toList _]
    exact hs.natDegree_eq_card_roots.symm
  let k := m - roots.length
  have hk : roots.length + k = m := Nat.add_sub_of_le (hLen.symm ▸ hp)
  let e : Fin m ≃ Fin roots.length ⊕ Fin k := (finCongr hk.symm).trans finSumFinEquiv.symm
  let pair : Fin roots.length ⊕ Fin k → L × L :=
    Sum.elim (fun i => (1, -roots[i.val])) (fun _ => (0, 1))
  let x (i : Fin m) := (pair (e i)).1
  let y (i : Fin m) := (pair (e i)).2
  refine ⟨x, y, ?_, ?_⟩
  · intro i
    dsimp only [x, y]
    cases e i <;> simp [pair]
  calc
    p = C p.leadingCoeff * (p.roots.map (X - C ·)).prod := hs.eq_prod_roots
    _ = C p.leadingCoeff * factorProduct x y := by
      congr 1
      let g (z : Fin roots.length ⊕ Fin k) : L[X] := C (pair z).1 * X + C (pair z).2
      change _ = ∏ i, g (e i)
      rw [Equiv.prod_comp e g, Fintype.prod_sum_type]
      simp only [g, pair, Sum.elim_inl, Sum.elim_inr, C_1, one_mul, map_zero, zero_mul, zero_add,
        Finset.prod_const_one, mul_one, C_neg, ← sub_eq_add_neg]
      rw [← Fin.prod_ofFn, List.ofFn_getElem_eq_map roots (X - C ·), ← Multiset.prod_coe,
        ← Multiset.map_coe]
      rw [show (roots : Multiset L) = p.roots from Multiset.coe_toList _]

/-- A projective linear factor is represented by its root, with
`none` denoting the point at infinity. -/
def normalizedRoot {L : Type*} [Field L] (x y : L) : Option L := by
  classical
  exact if x = 0 then none else some (-y / x)

theorem normalizedRoot_scale {L : Type*} [Field L] {a : L} (ha : a ≠ 0) (x y : L) :
    normalizedRoot (a * x) (a * y) = normalizedRoot x y := by
  classical
  by_cases hx : x = 0
  · simp [normalizedRoot, hx]
  · simp only [normalizedRoot, if_neg hx, if_neg (mul_ne_zero ha hx), neg_mul_eq_mul_neg,
      mul_div_mul_left _ _ ha]

/-- The ordered projective linear factorizations of a fixed nonzero
form, normalized up to scaling the factors, form a finite set. -/
theorem finite_normalized_factorizations {L : Type*} [Field L] {m : ℕ} (p : L[X]) (hp : p ≠ 0) :
    {z : Fin m → Option L | ∃ (x y : Fin m → L) (a : L),
      p = C a * factorProduct x y ∧ z = fun i => normalizedRoot (x i) (y i)}.Finite := by
  classical
  let choices : Set (Option L) := {none} ∪ Option.some '' (p.roots.toFinset : Set L)
  have hChoices : choices.Finite := (Set.finite_singleton _).union (p.roots.toFinset.finite_toSet.image _)
  refine (Set.Finite.pi' (t := fun _ : Fin m => choices) fun _ => hChoices).subset ?_
  rintro z ⟨x, y, a, h, rfl⟩ i
  by_cases hx : x i = 0
  · have hm : (none : Option L) ∈ choices := Or.inl rfl
    simpa only [normalizedRoot, hx, if_true] using hm
  · let b := -y i / x i
    have hFactor : (factorProduct x y).eval b = 0 := by
      rw [factorProduct, eval_prod]
      apply Finset.prod_eq_zero (Finset.mem_univ i)
      simp only [eval_add, eval_mul, eval_C, eval_X]
      have he : x i * b = -y i := by
        dsimp [b]
        field_simp
      rw [he, neg_add_cancel]
    have hb : p.IsRoot b := by
      change p.eval b = 0
      rw [h, eval_mul, hFactor, mul_zero]
    have hm : (some b : Option L) ∈ choices :=
      Or.inr ⟨b, Multiset.mem_toFinset.mpr ((Polynomial.mem_roots hp).mpr hb), rfl⟩
    simpa only [normalizedRoot, if_neg hx] using hm

end PhilipponProjectiveProductCoefficients

end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory HomogeneousLocalization TopologicalSpace


namespace PhilipponProjectiveTupleChart

universe u
attribute [local instance] MvPolynomial.gradedAlgebra

variable {R A : Type u} [CommRing R] [CommRing A] {n : ℕ}

abbrev grading (R : Type u) [CommRing R] (n : ℕ) :=
  MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R

abbrev chartRing (R : Type u) [CommRing R] (n : ℕ) (i : Fin (n + 1)) :=
  Away (grading R n) (MvPolynomial.X i)

/-- Evaluate degree-zero fractions wherever the chosen denominator is invertible. -/
def evaluate (ρ : R →+* A) (c : Fin (n + 1) → A)
    (g : MvPolynomial (Fin (n + 1)) R) (hg : IsUnit (MvPolynomial.eval₂Hom ρ c g)) :
    Away (grading R n) g →+* A :=
  (Localization.awayLift (MvPolynomial.eval₂Hom ρ c) g hg).comp
    (algebraMap (Away (grading R n) g) (Localization.Away g))

lemma evaluate_mk (ρ : R →+* A) (c : Fin (n + 1) → A)
    {g : MvPolynomial (Fin (n + 1)) R} {d : ℕ} (hg : g ∈ grading R n d)
    {u : Aˣ} (hu : MvPolynomial.eval₂Hom ρ c g = (u : A))
    (m : ℕ) (p : MvPolynomial (Fin (n + 1)) R) (hp : p ∈ grading R n (m • d)) :
    evaluate ρ c g (hu ▸ u.isUnit) (Away.mk (grading R n) hg m p hp) =
      MvPolynomial.eval₂Hom ρ c p * (↑u⁻¹ : A) ^ m := by
  have hi : MvPolynomial.eval₂Hom ρ c g * (↑u⁻¹ : A) = 1 := by
    rw [hu, Units.mul_inv]
  change Localization.awayLift (MvPolynomial.eval₂Hom ρ c) g (hu ▸ u.isUnit)
    (Away.mk (grading R n) hg m p hp).val = _
  rw [Away.val_mk, Localization.awayLift_mk _ _ _ _ hi]

def chartEval (ρ : R →+* A) (c : Fin (n + 1) → A) (i : Fin (n + 1))
    (hi : IsUnit (c i)) : chartRing R n i →+* A :=
  evaluate ρ c (MvPolynomial.X i) (by simpa only [MvPolynomial.eval₂Hom_X'] using hi)

lemma chartEval_coeff (ρ : R →+* A) (c : Fin (n + 1) → A) (i : Fin (n + 1))
    (hi : IsUnit (c i)) (r : R) : chartEval ρ c i hi (algebraMap R _ r) = ρ r := by
  change Localization.awayLift (MvPolynomial.eval₂Hom ρ c) (MvPolynomial.X i)
    (by simpa only [MvPolynomial.eval₂Hom_X'] using hi)
    ((algebraMap R (chartRing R n i) r).val) = _
  rw [ProjSpace.val_algebraMap, IsLocalization.Away.lift_eq, MvPolynomial.eval₂Hom_C]

lemma chartEval_ratio (ρ : R →+* A) (c : Fin (n + 1) → A) (i j : Fin (n + 1))
    (u : Aˣ) (hu : c i = (u : A)) :
    chartEval ρ c i (hu ▸ u.isUnit) (ProjSpace.ratio R n i j) = c j * ↑u⁻¹ := by
  have hX : MvPolynomial.eval₂Hom ρ c (MvPolynomial.X i) = (u : A) := by simpa using hu
  rw [ProjSpace.ratio, chartEval, evaluate_mk ρ c _ hX]
  simp

/-- The values on the base ring and coordinate ratios determine a chart evaluation. -/
lemma chart_ring_ext (i : Fin (n + 1)) {f g : chartRing R n i →+* A}
    (hR : ∀ r, f (algebraMap R _ r) = g (algebraMap R _ r))
    (hratio : ∀ j, f (ProjSpace.ratio R n i j) = g (ProjSpace.ratio R n i j)) : f = g := by
  let : Algebra R A := (f.comp (algebraMap R (chartRing R n i))).toAlgebra
  let F : chartRing R n i →ₐ[R] A := ⟨f, fun _ => rfl⟩
  let G : chartRing R n i →ₐ[R] A := ⟨g, fun r => (hR r).symm⟩
  have he : F = G := AlgHom.ext_of_adjoin_eq_top (ProjSpace.adjoin_range_ratio R n i) (by
    rintro _ ⟨j, rfl⟩
    exact hratio j)
  exact congrArg AlgHom.toRingHom he

def point (ρ : R →+* A) (c : Fin (n + 1) → A) (i : Fin (n + 1)) (hi : IsUnit (c i)) :
    Spec (.of A) ⟶ Proj (grading R n) :=
  Spec.map (CommRingCat.ofHom (chartEval ρ c i hi)) ≫
    Proj.awayι (grading R n) (MvPolynomial.X i) (ProjSpace.X_mem_one R n i) one_pos

lemma point_over (ρ : R →+* A) (c : Fin (n + 1) → A) (i : Fin (n + 1))
    (hi : IsUnit (c i)) : point ρ c i hi ≫ ProjSpace.π R n = Spec.map (CommRingCat.ofHom ρ) := by
  rw [point, Category.assoc, ProjSpace.awayι_comp_π, ← Spec.map_comp]
  apply congrArg Spec.map
  apply CommRingCat.hom_ext
  exact RingHom.ext (chartEval_coeff ρ c i hi)

lemma point_preimage_basicOpen (ρ : R →+* A) (c : Fin (n + 1) → A) (i j : Fin (n + 1))
    (hi : IsUnit (c i)) :
    point ρ c i hi ⁻¹ᵁ Proj.basicOpen (grading R n) (MvPolynomial.X j) =
      PrimeSpectrum.basicOpen (c j) := by
  rw [point, Scheme.Hom.comp_preimage, Proj.awayι_preimage_basicOpen
    (grading R n) (ProjSpace.X_mem_one R n i) one_pos (ProjSpace.X_mem_one R n j) one_pos]
  have he : Away.isLocalizationElem (ProjSpace.X_mem_one R n i) (ProjSpace.X_mem_one R n j) =
      ProjSpace.ratio R n i j := by
    apply HomogeneousLocalization.val_injective
    simp [Away.isLocalizationElem, ProjSpace.ratio, Away.val_mk]
  rw [he]
  ext x
  change chartEval ρ c i hi (ProjSpace.ratio R n i j) ∉ x.asIdeal ↔ c j ∉ x.asIdeal
  rw [chartEval_ratio ρ c i j hi.unit hi.unit_spec.symm]
  exact not_congr (x.asIdeal.mul_unit_mem_iff_mem (hi.unit⁻¹).isUnit)

private lemma evaluate_mul_comp_awayMap (ρ : R →+* A) (c : Fin (n + 1) → A)
    (i j : Fin (n + 1)) (u v : Aˣ) (hu : c i = ↑u) (hv : c j = ↑v)
    (g : MvPolynomial (Fin (n + 1)) R) (hg : g = MvPolynomial.X i * MvPolynomial.X j)
    (hunit : MvPolynomial.eval₂Hom ρ c g = ↑(u * v)) :
    (evaluate ρ c g (hunit ▸ (u * v).isUnit)).comp
      (awayMap (grading R n) (ProjSpace.X_mem_one R n j) hg) =
    chartEval ρ c i (hu ▸ u.isUnit) := by
  apply chart_ring_ext i
  · intro r
    change evaluate ρ c g (hunit ▸ (u * v).isUnit)
      (awayMap (grading R n) (ProjSpace.X_mem_one R n j) hg
        (fromZeroRingHom (grading R n) _ ((ProjSpace.grad0Equiv R n) r))) = _
    rw [awayMap_fromZeroRingHom, chartEval_coeff]
    change Localization.awayLift (MvPolynomial.eval₂Hom ρ c) g (hunit ▸ (u * v).isUnit)
      (algebraMap (MvPolynomial (Fin (n + 1)) R) _ (MvPolynomial.C r)) = _
    rw [IsLocalization.Away.lift_eq, MvPolynomial.eval₂Hom_C]
  · intro k
    change evaluate ρ c g (hunit ▸ (u * v).isUnit)
      (awayMap (grading R n) (ProjSpace.X_mem_one R n j) hg (ProjSpace.ratio R n i k)) = _
    rw [chartEval_ratio ρ c i k u hu, ProjSpace.ratio, awayMap_mk, evaluate_mk ρ c _ hunit]
    simp only [pow_one, map_mul, MvPolynomial.eval₂Hom_X', hv, mul_inv_rev, Units.val_mul]
    calc
      (c k * ↑v) * (↑v⁻¹ * ↑u⁻¹) = (c k * ↑u⁻¹) * (↑v * ↑v⁻¹) := by ac_rfl
      _ = _ := by rw [Units.mul_inv, mul_one]

/-- The projective point computed from a tuple is independent of its unit pivot. -/
lemma point_eq_of_unit_pivots (ρ : R →+* A) (c : Fin (n + 1) → A)
    (i j : Fin (n + 1)) (hi : IsUnit (c i)) (hj : IsUnit (c j)) :
    point ρ c i hi = point ρ c j hj := by
  let g : MvPolynomial (Fin (n + 1)) R := MvPolynomial.X i * MvPolynomial.X j
  have hg : g = MvPolynomial.X j * MvPolynomial.X i := mul_comm _ _
  let u := hi.unit
  let v := hj.unit
  have hu : c i = ↑u := hi.unit_spec.symm
  have hv : c j = ↑v := hj.unit_spec.symm
  have hunit : MvPolynomial.eval₂Hom ρ c g = ↑(u * v) := by
    simp only [g, map_mul, MvPolynomial.eval₂Hom_X', hu, hv, Units.val_mul]
  have hunit' : MvPolynomial.eval₂Hom ρ c g = ↑(v * u) := by rw [mul_comm v u, hunit]
  rw [point, point, ← evaluate_mul_comp_awayMap ρ c i j u v hu hv g rfl hunit,
    ← evaluate_mul_comp_awayMap ρ c j i v u hv hu g hg hunit',
    CommRingCat.ofHom_comp, CommRingCat.ofHom_comp, Spec.map_comp, Spec.map_comp,
    Category.assoc, Category.assoc, Proj.SpecMap_awayMap_awayι, Proj.SpecMap_awayMap_awayι]

lemma point_naturality {B : Type u} [CommRing B] (ρ : R →+* A) (f : A →+* B)
    (c : Fin (n + 1) → A) (i : Fin (n + 1)) (hi : IsUnit (c i)) :
    Spec.map (CommRingCat.ofHom f) ≫ point ρ c i hi =
      point (f.comp ρ) (f ∘ c) i (hi.map f) := by
  let u := hi.unit
  have hu : c i = ↑u := hi.unit_spec.symm
  let v := Units.map (f : A →* B) u
  have hv : (f ∘ c) i = ↑v := congrArg f hu
  have h : f.comp (chartEval ρ c i hi) = chartEval (f.comp ρ) (f ∘ c) i (hi.map f) := by
    apply chart_ring_ext i
    · intro r
      change f (chartEval ρ c i hi (algebraMap R _ r)) = _
      rw [chartEval_coeff, chartEval_coeff]
      rfl
    · intro j
      change f (chartEval ρ c i hi (ProjSpace.ratio R n i j)) = _
      rw [chartEval_ratio ρ c i j u hu, chartEval_ratio (f.comp ρ) (f ∘ c) i j v hv, map_mul]
      rfl
  rw [point, point, ← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, h]

lemma point_scale (ρ : R →+* A) (c : Fin (n + 1) → A) (a : Aˣ)
    (i : Fin (n + 1)) (hi : IsUnit (c i)) :
    point ρ (fun j => ↑a * c j) i (a.isUnit.mul hi) = point ρ c i hi := by
  let u := hi.unit
  have hu : c i = ↑u := hi.unit_spec.symm
  have huv : (fun j => (a : A) * c j) i = ↑(a * u) := by
    change (a : A) * c i = ↑(a * u)
    rw [hu, Units.val_mul]
  have h : chartEval ρ (fun j => ↑a * c j) i (a.isUnit.mul hi) = chartEval ρ c i hi := by
    apply chart_ring_ext i
    · intro r
      rw [chartEval_coeff, chartEval_coeff]
    · intro j
      rw [chartEval_ratio ρ _ i j (a * u) huv, chartEval_ratio ρ c i j u hu]
      simp only [mul_inv_rev, Units.val_mul]
      calc
        (↑a * c j) * (↑u⁻¹ * ↑a⁻¹) = (c j * ↑u⁻¹) * (↑a * ↑a⁻¹) := by ac_rfl
        _ = _ := by rw [Units.mul_inv, mul_one]
  rw [point, point, h]

lemma exists_scale_of_chartEval_eq (ρ : R →+* A) (c d : Fin (n + 1) → A)
    (i : Fin (n + 1)) (hi : IsUnit (c i)) (hd : IsUnit (d i))
    (he : chartEval ρ c i hi = chartEval ρ d i hd) :
    ∃ a : Aˣ, c = fun k => ↑a * d k := by
  let u := hi.unit
  let v := hd.unit
  refine ⟨u * v⁻¹, funext fun k => ?_⟩
  have hr := RingHom.congr_fun he (ProjSpace.ratio R n i k)
  rw [chartEval_ratio ρ c i k u hi.unit_spec.symm,
    chartEval_ratio ρ d i k v hd.unit_spec.symm] at hr
  calc
    c k = (c k * ↑u⁻¹) * ↑u := by rw [mul_assoc, Units.inv_mul, mul_one]
    _ = (d k * ↑v⁻¹) * ↑u := by rw [hr]
    _ = ↑(u * v⁻¹) * d k := by rw [Units.val_mul]; ac_rfl

/-- Over a field, equal projective points have proportional coordinate tuples. -/
lemma exists_unit_scale_of_point_eq {K : Type u} [Field K] (ρ : R →+* K)
    (c d : Fin (n + 1) → K) (i j : Fin (n + 1)) (hi : IsUnit (c i)) (hj : IsUnit (d j))
    (h : point ρ c i hi = point ρ d j hj) :
    ∃ a : Kˣ, c = fun k => ↑a * d k := by
  have hopen := congrArg
    (fun f : Spec (.of K) ⟶ Proj (grading R n) =>
      f ⁻¹ᵁ Proj.basicOpen (grading R n) (MvPolynomial.X i)) h
  rw [point_preimage_basicOpen, point_preimage_basicOpen] at hopen
  have hd : IsUnit (d i) := isUnit_iff_ne_zero.mpr (by
    intro hz
    have hm : (default : PrimeSpectrum K) ∈ PrimeSpectrum.basicOpen (c i) :=
      fun hh => (default : PrimeSpectrum K).isPrime.ne_top
        (Ideal.eq_top_of_isUnit_mem _ hh hi)
    rw [hopen, hz] at hm
    exact hm (Ideal.zero_mem _))
  have hp := h.trans (point_eq_of_unit_pivots ρ d j i hj hd)
  let inc := Proj.awayι (grading R n) (MvPolynomial.X i) (ProjSpace.X_mem_one R n i) one_pos
  change Spec.map (CommRingCat.ofHom (chartEval ρ c i hi)) ≫ inc =
    Spec.map (CommRingCat.ofHom (chartEval ρ d i hd)) ≫ inc at hp
  have : IsOpenImmersion inc := by dsimp [inc]; infer_instance
  have he := Spec.map_injective ((cancel_mono inc).mp hp)
  exact exists_scale_of_chartEval_eq ρ c d i hi hd (congrArg CommRingCat.Hom.hom he)

/-- Any field-valued point over the base has a coordinate tuple with a unit pivot. -/
lemma exists_point {K : Type u} [Field K] (ρ : R →+* K)
    (s : Spec (.of K) ⟶ Proj (grading R n))
    (hs : s ≫ ProjSpace.π R n = Spec.map (CommRingCat.ofHom ρ)) :
    ∃ (i : Fin (n + 1)) (c : Fin (n + 1) → K) (hc : IsUnit (c i)), point ρ c i hc = s := by
  have hcover : s default ∈ (⨆ i : Fin (n + 1),
      Proj.basicOpen (grading R n) (MvPolynomial.X i) : (Proj (grading R n)).Opens) := by
    rw [Proj.iSup_basicOpen_eq_top _ _ (ProjSpace.irrelevant_le_span_X R n)]
    trivial
  obtain ⟨i, hi⟩ := Opens.mem_iSup.mp hcover
  let chart := Proj.awayι (grading R n) (MvPolynomial.X i) (ProjSpace.X_mem_one R n i) one_pos
  have hrange : Set.range s ⊆ Set.range chart := by
    rintro _ ⟨x, rfl⟩
    have hx : x = default := Subsingleton.elim _ _
    rw [hx]
    change s default ∈ chart.opensRange
    rwa [Proj.opensRange_awayι]
  let lift := IsOpenImmersion.lift chart s hrange
  have hfac : lift ≫ chart = s := IsOpenImmersion.lift_fac _ _ _
  let φ := Spec.preimage lift
  let c (j : Fin (n + 1)) := φ.hom (ProjSpace.ratio R n i j)
  have hc : c i = 1 := by simp [c, ProjSpace.ratio_self]
  refine ⟨i, c, hc ▸ isUnit_one, ?_⟩
  have hring : φ.hom = chartEval ρ c i (hc ▸ isUnit_one) := by
    apply chart_ring_ext i
    · intro r
      have hbase := congrArg (fun f => f ≫ ProjSpace.π R n) hfac
      rw [Category.assoc, hs] at hbase
      change lift ≫ (chart ≫ ProjSpace.π R n) = _ at hbase
      rw [show chart ≫ ProjSpace.π R n = _ from ProjSpace.awayι_comp_π R n i,
        ← Spec.map_preimage lift, ← Spec.map_comp] at hbase
      have he := Spec.map_injective hbase
      rw [chartEval_coeff]
      exact RingHom.congr_fun (congrArg CommRingCat.Hom.hom he) r
    · intro j
      rw [chartEval_ratio ρ c i j 1 hc]
      simp [c]
  change Spec.map (CommRingCat.ofHom (chartEval ρ c i (hc ▸ isUnit_one))) ≫ chart = s
  have he : CommRingCat.ofHom (chartEval ρ c i (hc ▸ isUnit_one)) = φ := CommRingCat.hom_ext hring.symm
  rw [he, Spec.map_preimage lift, hfac]

end PhilipponProjectiveTupleChart

end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace


namespace PhilipponProjectiveTupleOnScheme

universe u v
attribute [local instance] MvPolynomial.gradedAlgebra
open PhilipponProjectiveTupleChart (grading chartRing chartEval chartEval_coeff chartEval_ratio chart_ring_ext)

variable {R : Type u} [CommRing R] {X : Scheme.{u}} {n : ℕ}

def baseRing (s : X ⟶ Spec (.of R)) : R →+* Γ(X, ⊤) :=
  ((Scheme.ΓSpecIso (.of R)).inv ≫ s.appTop).hom

lemma toSpecΓ_baseRing (s : X ⟶ Spec (.of R)) :
    X.toSpecΓ ≫ Spec.map (CommRingCat.ofHom (baseRing s)) = s := by
  change X.toSpecΓ ≫ Spec.map ((Scheme.ΓSpecIso (.of R)).inv ≫ s.appTop) = s
  rw [Spec.map_comp, ← Category.assoc, ← Scheme.toSpecΓ_naturality, Category.assoc,
    toSpecΓ_SpecMap_ΓSpecIso_inv, Category.comp_id]

lemma baseRing_comp_specMap {A : Type u} [CommRing A] (g : X ⟶ Spec (.of A)) (φ : R →+* A) :
    baseRing (g ≫ Spec.map (CommRingCat.ofHom φ)) = (baseRing g).comp φ := by
  unfold baseRing
  rw [Scheme.Hom.comp_appTop, ← Scheme.ΓSpecIso_inv_naturality_assoc]
  rfl

lemma baseRing_toSpecΓ (X : Scheme.{u}) :
    baseRing X.toSpecΓ = RingHom.id Γ(X, ⊤) := by
  unfold baseRing
  rw [Scheme.toSpecΓ_appTop, Iso.inv_hom_id]
  rfl

def point (s : X ⟶ Spec (.of R)) (c : Fin (n + 1) → Γ(X, ⊤))
    (i : Fin (n + 1)) (hi : IsUnit (c i)) : X ⟶ Proj (grading R n) :=
  X.toSpecΓ ≫ PhilipponProjectiveTupleChart.point (baseRing s) c i hi

lemma point_over (s : X ⟶ Spec (.of R)) (c : Fin (n + 1) → Γ(X, ⊤))
    (i : Fin (n + 1)) (hi : IsUnit (c i)) : point s c i hi ≫ ProjSpace.π R n = s := by
  rw [point, Category.assoc, PhilipponProjectiveTupleChart.point_over, toSpecΓ_baseRing]

lemma point_naturality {Y : Scheme.{u}} (f : Y ⟶ X) (s : X ⟶ Spec (.of R))
    (c : Fin (n + 1) → Γ(X, ⊤)) (i : Fin (n + 1)) (hi : IsUnit (c i)) :
    f ≫ point s c i hi = point (f ≫ s) (f.appTop.hom ∘ c) i (hi.map f.appTop.hom) := by
  rw [point, point, ← Category.assoc, Scheme.toSpecΓ_naturality, Category.assoc,
    ← show CommRingCat.ofHom f.appTop.hom = f.appTop from rfl,
    PhilipponProjectiveTupleChart.point_naturality]
  have h : f.appTop.hom.comp (baseRing s) = baseRing (f ≫ s) := by
    unfold baseRing
    rw [Scheme.Hom.comp_appTop, ← Category.assoc]
    rfl
  rw [h]
  simp only [CommRingCat.hom_ofHom]

lemma point_eq_of_scale (s : X ⟶ Spec (.of R)) (c d : Fin (n + 1) → Γ(X, ⊤))
    (i j : Fin (n + 1)) (hi : IsUnit (c i)) (hj : IsUnit (d j))
    (a : Γ(X, ⊤)ˣ) (h : c = fun k => ↑a * d k) : point s c i hi = point s d j hj := by
  subst c
  have hdi : IsUnit (d i) := isUnit_of_mul_isUnit_right hi
  rw [point, point, PhilipponProjectiveTupleChart.point_scale (baseRing s) d a i hdi,
    PhilipponProjectiveTupleChart.point_eq_of_unit_pivots (baseRing s) d i j hdi hj]

lemma point_preimage_basicOpen (s : X ⟶ Spec (.of R)) (c : Fin (n + 1) → Γ(X, ⊤))
    (i j : Fin (n + 1)) (hi : IsUnit (c i)) :
    point s c i hi ⁻¹ᵁ Proj.basicOpen (grading R n) (MvPolynomial.X j) = X.basicOpen (c j) := by
  rw [point, Scheme.Hom.comp_preimage, PhilipponProjectiveTupleChart.point_preimage_basicOpen,
    Scheme.toSpecΓ_preimage_basicOpen]

lemma point_Spec {A : Type u} [CommRing A] (ρ : R →+* A) (c : Fin (n + 1) → A)
    (i : Fin (n + 1)) (hi : IsUnit (c i)) :
    point (Spec.map (CommRingCat.ofHom ρ)) ((Scheme.ΓSpecIso (.of A)).inv.hom ∘ c) i
      (hi.map (Scheme.ΓSpecIso (.of A)).inv.hom) = PhilipponProjectiveTupleChart.point ρ c i hi := by
  let f := (Scheme.ΓSpecIso (.of A)).inv.hom
  have hb : baseRing (Spec.map (CommRingCat.ofHom ρ)) = f.comp ρ := by
    have he := baseRing_comp_specMap (𝟙 (Spec (.of A))) ρ
    rw [Category.id_comp] at he
    rw [he, baseRing, Scheme.Hom.id_appTop, Category.comp_id]
  rw [point, hb, ← PhilipponProjectiveTupleChart.point_naturality, ← Category.assoc]
  change ((Spec (.of A)).toSpecΓ ≫ Spec.map (Scheme.ΓSpecIso (.of A)).inv) ≫ _ = _
  rw [toSpecΓ_SpecMap_ΓSpecIso_inv, Category.id_comp]

/-- Invertibility of a pulled-back section can be checked on the image of the map. -/
lemma isUnit_appTop_of_mem_basicOpen {Y : Scheme.{u}} (g : X ⟶ Y) (r : Γ(Y, ⊤))
    (h : ∀ x : X, g x ∈ Y.basicOpen r) : IsUnit (g.appTop r) := by
  apply X.toRingedSpace.isUnit_of_isUnit_germ ⊤ (g.appTop r)
  intro x hx
  apply (Scheme.mem_basicOpen X (g.appTop r) x hx).mp
  rw [← Scheme.preimage_basicOpen_top]
  exact h x

/-- Equal maps to projective space induce proportional tuples wherever
both tuples have invertible coordinates. -/
lemma exists_unit_scale_of_point_eq (s : X ⟶ Spec (.of R)) (c d : Fin (n + 1) → Γ(X, ⊤))
    (i j : Fin (n + 1)) (hi : IsUnit (c i)) (hj : IsUnit (d j))
    (h : point s c i hi = point s d j hj) : ∃ a : Γ(X, ⊤)ˣ, c = fun k => ↑a * d k := by
  have hopen := congrArg
    (fun f : X ⟶ Proj (grading R n) => f ⁻¹ᵁ Proj.basicOpen (grading R n) (MvPolynomial.X i)) h
  rw [point_preimage_basicOpen, point_preimage_basicOpen, X.basicOpen_of_isUnit hi] at hopen
  have hd : IsUnit (d i) := by
    apply X.toRingedSpace.isUnit_of_isUnit_germ ⊤ (d i)
    intro x hx
    exact (Scheme.mem_basicOpen X (d i) x hx).mp (hopen ▸ hx)
  have hp : point s c i hi = point s d i hd := by
    rw [h, point, point, PhilipponProjectiveTupleChart.point_eq_of_unit_pivots (baseRing s) d j i hj hd]
  let inc := Proj.awayι (grading R n) (MvPolynomial.X i) (ProjSpace.X_mem_one R n i) one_pos
  have : IsOpenImmersion inc := by dsimp [inc]; infer_instance
  change X.toSpecΓ ≫ Spec.map (CommRingCat.ofHom (chartEval (baseRing s) c i hi)) ≫ inc =
    X.toSpecΓ ≫ Spec.map (CommRingCat.ofHom (chartEval (baseRing s) d i hd)) ≫ inc at hp
  rw [← Category.assoc, ← Category.assoc] at hp
  have he := congrArg (baseRing (R := chartRing R n i)) ((cancel_mono inc).mp hp)
  simp only [baseRing_comp_specMap, baseRing_toSpecΓ, RingHom.id_comp] at he
  exact PhilipponProjectiveTupleChart.exists_scale_of_chartEval_eq (baseRing s) c d i hi hd he

/-- A morphism with image in a standard chart has a tuple of global coordinates. -/
lemma exists_point_of_range_subset (s : X ⟶ Spec (.of R)) (p : X ⟶ Proj (grading R n))
    (hs : p ≫ ProjSpace.π R n = s) (i : Fin (n + 1))
    (hi : ∀ x : X, p x ∈ Proj.basicOpen (grading R n) (MvPolynomial.X i)) :
    ∃ (c : Fin (n + 1) → Γ(X, ⊤)) (hc : c i = 1), point s c i (hc ▸ isUnit_one) = p := by
  let chart := Proj.awayι (grading R n) (MvPolynomial.X i) (ProjSpace.X_mem_one R n i) one_pos
  have hrange : Set.range p ⊆ Set.range chart := by
    rintro _ ⟨x, rfl⟩
    change p x ∈ chart.opensRange
    rw [Proj.opensRange_awayι]
    exact hi x
  let g := IsOpenImmersion.lift chart p hrange
  have hg : g ≫ chart = p := IsOpenImmersion.lift_fac _ _ _
  let φ := baseRing g
  let c (j : Fin (n + 1)) := φ (ProjSpace.ratio R n i j)
  have hc : c i = 1 := by simp [c, ProjSpace.ratio_self]
  refine ⟨c, hc, ?_⟩
  have he : chartEval (baseRing s) c i (hc ▸ isUnit_one) = φ := by
    apply chart_ring_ext i
    · intro r
      rw [chartEval_coeff]
      have hb : s = g ≫ Spec.map (CommRingCat.ofHom (algebraMap R (chartRing R n i))) := by
        rw [← hs, ← hg, Category.assoc]
        exact congrArg (fun f => g ≫ f) (ProjSpace.awayι_comp_π R n i)
      rw [hb, baseRing_comp_specMap]
      rfl
    · intro j
      rw [chartEval_ratio (baseRing s) c i j 1 hc]
      simp [c]
  change X.toSpecΓ ≫ Spec.map (CommRingCat.ofHom (chartEval (baseRing s) c i (hc ▸ isUnit_one))) ≫
    chart = p
  rw [he, ← Category.assoc, toSpecΓ_baseRing, hg]

/-- Coordinate tuples on a cover define a projective morphism when their
restrictions are related by an invertible scalar on every overlap. -/
theorem exists_glued_point (s : X ⟶ Spec (.of R)) (U : X.OpenCover.{v})
    (c : ∀ b : U.I₀, Fin (n + 1) → Γ(U.X b, ⊤)) (i : U.I₀ → Fin (n + 1))
    (hi : ∀ b, IsUnit (c b (i b)))
    (hs : ∀ a b, ∃ u : Γ(pullback (U.f a) (U.f b), ⊤)ˣ,
      (pullback.fst (U.f a) (U.f b)).appTop.hom ∘ c a =
        fun k => ↑u * (pullback.snd (U.f a) (U.f b)).appTop (c b k)) :
    ∃ g : X ⟶ Proj (grading R n), g ≫ ProjSpace.π R n = s ∧
      ∀ b, U.f b ≫ g = point (U.f b ≫ s) (c b) (i b) (hi b) := by
  let localMap (b : U.I₀) := point (U.f b ≫ s) (c b) (i b) (hi b)
  have hCompat (a b : U.I₀) : pullback.fst (U.f a) (U.f b) ≫ localMap a =
      pullback.snd (U.f a) (U.f b) ≫ localMap b := by
    obtain ⟨u, hu⟩ := hs a b
    dsimp only [localMap]
    rw [point_naturality, point_naturality, ← Category.assoc, ← Category.assoc, pullback.condition]
    exact point_eq_of_scale _ _ _ _ _ _ _ u hu
  let g := U.glueMorphisms localMap hCompat
  have hlocal : ∀ b, U.f b ≫ g = localMap b := U.ι_glueMorphisms _ _
  refine ⟨g, U.hom_ext _ _ (fun b => ?_), hlocal⟩
  rw [← Category.assoc, hlocal]
  exact point_over _ _ _ _

end PhilipponProjectiveTupleOnScheme

end

section

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace


namespace PhilipponProjectiveLineMultiplication

universe u
attribute [local instance] MvPolynomial.gradedAlgebra

open PhilipponProjectiveProductCoefficients (coefficients coefficients_map coefficients_scale span_coefficients_eq_top)
open PhilipponProjectiveTupleChart (grading)
open PhilipponProjectiveTupleOnScheme

variable {R : Type u} [CommRing R] {X : Scheme.{u}} {m : ℕ}

private abbrev Line := Proj (grading R 1)

private def standardOpen (i : Fin 2) : (Line (R := R)).Opens :=
  Proj.basicOpen (grading R 1) (MvPolynomial.X i)

private def commonOpen (p : Fin m → (X ⟶ Line (R := R))) (b : Fin m → Fin 2) : X.Opens :=
  ⨅ i, p i ⁻¹ᵁ standardOpen (R := R) (b i)

private lemma exists_mem_commonOpen (p : Fin m → (X ⟶ Line (R := R))) (x : X) :
    ∃ b, x ∈ commonOpen p b := by
  have h (i : Fin m) : ∃ j, p i x ∈ standardOpen (R := R) j := by
    apply Opens.mem_iSup.mp
    change p i x ∈ (⨆ j : Fin 2, Proj.basicOpen (grading R 1) (MvPolynomial.X j) : (Line (R := R)).Opens)
    rw [Proj.iSup_basicOpen_eq_top _ _ (ProjSpace.irrelevant_le_span_X R 1)]
    trivial
  choose b hb using h
  refine ⟨b, ?_⟩
  change x ∈ (↑(⨅ i, p i ⁻¹ᵁ standardOpen (R := R) (b i) : X.Opens) : Set X)
  rw [Opens.coe_iInf, Set.mem_iInter]
  exact hb

/-- Refine the common standard charts of the linear factors by the
basic opens of the product coefficients. -/
private lemma exists_product_cover (s : X ⟶ Spec (.of R))
    (p : Fin m → (X ⟶ Line (R := R))) (hp : ∀ i, p i ≫ ProjSpace.π R 1 = s) :
    ∃ (U : X.OpenCover.{0}) (c : ∀ b : U.I₀, Fin m → Fin 2 → Γ(U.X b, ⊤))
      (a : U.I₀ → Fin m → Fin 2) (k : U.I₀ → Fin (m + 1))
      (hc : ∀ b i, IsUnit (c b i (a b i))),
      (∀ b i, point (U.f b ≫ s) (c b i) (a b i) (hc b i) = U.f b ≫ p i) ∧
      ∀ b, IsUnit (coefficients (c b) (k b)) := by
  let V := commonOpen p
  have hFrame (b : Fin m → Fin 2) (i : Fin m) :
      ∃ (c : Fin 2 → Γ((V b : Scheme), ⊤)) (hc : c (b i) = 1),
        point ((V b).ι ≫ s) c (b i) (hc ▸ isUnit_one) = (V b).ι ≫ p i := by
    apply exists_point_of_range_subset _ _ (by rw [Category.assoc, hp])
    intro x
    exact (iInf_le (fun j => p j ⁻¹ᵁ standardOpen (R := R) (b j)) i) x.2
  choose c hc hfactor using hFrame
  let W (b : Fin m → Fin 2) (k : Fin (m + 1)) :=
    (V b : Scheme).basicOpen (coefficients (c b) k)
  have hW (b : Fin m → Fin 2) (x : (V b : Scheme)) : ∃ k, x ∈ W b k := by
    have he := iSup_basicOpen_of_span_eq_top (X := (V b : Scheme)) ⊤
      (Set.range (coefficients (c b)))
      (span_coefficients_eq_top (c b) b (fun i => hc b i ▸ isUnit_one))
    have hx : x ∈ (⨆ a ∈ Set.range (coefficients (c b)), (V b : Scheme).basicOpen a :
        (V b : Scheme).Opens) := by
      rw [he]
      trivial
    rw [Opens.mem_iSup] at hx
    obtain ⟨_, hx⟩ := hx
    rw [Opens.mem_iSup] at hx
    obtain ⟨⟨k, rfl⟩, hk⟩ := hx
    exact ⟨k, hk⟩
  let U : X.OpenCover.{0} := {
    I₀ := (Fin m → Fin 2) × Fin (m + 1)
    X := fun b => W b.1 b.2
    f := fun b => (W b.1 b.2).ι ≫ (V b.1).ι
    mem₀ := by
      rw [Scheme.presieve₀_mem_precoverage_iff]
      refine ⟨fun x => ?_, fun b => inferInstance⟩
      obtain ⟨b, hb⟩ := exists_mem_commonOpen p x
      obtain ⟨k, hk⟩ := hW b ⟨x, hb⟩
      exact ⟨(b, k), ⟨⟨x, hb⟩, hk⟩, rfl⟩ }
  let c' (b : U.I₀) (i : Fin m) := (W b.1 b.2).ι.appTop.hom ∘ c b.1 i
  have hc' (b : U.I₀) (i : Fin m) : IsUnit (c' b i (b.1 i)) :=
    (hc b.1 i ▸ isUnit_one : IsUnit (c b.1 i (b.1 i))).map (W b.1 b.2).ι.appTop.hom
  refine ⟨U, c', Prod.fst, Prod.snd, hc', ?_, ?_⟩
  · intro b i
    have h := congrArg (fun f => (W b.1 b.2).ι ≫ f) (hfactor b.1 i)
    rw [point_naturality, ← Category.assoc, ← Category.assoc] at h
    exact h
  · intro b
    change IsUnit (coefficients (fun i => (W b.1 b.2).ι.appTop.hom ∘ c b.1 i) b.2)
    rw [← coefficients_map]
    exact isUnit_appTop_of_mem_basicOpen (W b.1 b.2).ι _ (fun x => x.2)

private lemma exists_scale_of_products (s : X ⟶ Spec (.of R))
    (c d : Fin m → Fin 2 → Γ(X, ⊤)) (a b : Fin m → Fin 2)
    (hc : ∀ i, IsUnit (c i (a i))) (hd : ∀ i, IsUnit (d i (b i)))
    (he : ∀ i, point s (c i) (a i) (hc i) = point s (d i) (b i) (hd i)) :
    ∃ u : Γ(X, ⊤)ˣ, coefficients c = fun k => ↑u * coefficients d k := by
  choose u hu using fun i => exists_unit_scale_of_point_eq s (c i) (d i) (a i) (b i) (hc i) (hd i) (he i)
  refine ⟨∏ i, u i, ?_⟩
  have h : c = fun i j => ↑(u i) * d i j := funext hu
  rw [h, coefficients_scale]

/-- Multiplication on families of lines is global, and on every test
scheme where the factors and product have unit pivots it is computed by convolution. -/
theorem exists_multiplication (s : X ⟶ Spec (.of R))
    (p : Fin m → (X ⟶ Line (R := R))) (hp : ∀ i, p i ≫ ProjSpace.π R 1 = s) :
    ∃ g : X ⟶ Proj (grading R m), g ≫ ProjSpace.π R m = s ∧
      ∀ {T : Scheme.{u}} (t : T ⟶ X) (c : Fin m → Fin 2 → Γ(T, ⊤)) (a : Fin m → Fin 2)
        (hc : ∀ i, IsUnit (c i (a i)))
        (_ : ∀ i, point (t ≫ s) (c i) (a i) (hc i) = t ≫ p i)
        (k : Fin (m + 1)) (hk : IsUnit (coefficients c k)),
        t ≫ g = point (t ≫ s) (coefficients c) k hk := by
  obtain ⟨U, c, a, k, hc, hfactor, hk⟩ := exists_product_cover s p hp
  have hCompat (b d : U.I₀) : ∃ u : Γ(pullback (U.f b) (U.f d), ⊤)ˣ,
      (pullback.fst (U.f b) (U.f d)).appTop.hom ∘ coefficients (c b) =
        fun j => ↑u * (pullback.snd (U.f b) (U.f d)).appTop (coefficients (c d) j) := by
    let l := pullback.fst (U.f b) (U.f d)
    let r := pullback.snd (U.f b) (U.f d)
    have hbase : l ≫ U.f b ≫ s = r ≫ U.f d ≫ s := pullback.condition_assoc s
    rw [coefficients_map]
    change ∃ u : Γ(pullback (U.f b) (U.f d), ⊤)ˣ, _ =
      fun j => ↑u * (r.appTop.hom ∘ coefficients (c d)) j
    rw [coefficients_map]
    apply exists_scale_of_products (r ≫ U.f d ≫ s) _ _ (a b) (a d)
        (fun i => (hc b i).map l.appTop.hom) (fun i => (hc d i).map r.appTop.hom)
    intro i
    have hl := congrArg (fun g => l ≫ g) (hfactor b i)
    have hr := congrArg (fun g => r ≫ g) (hfactor d i)
    rw [point_naturality, hbase] at hl
    rw [point_naturality] at hr
    exact hl.trans ((pullback.condition_assoc (p i)).trans hr.symm)
  obtain ⟨g, hg, hlocal⟩ := exists_glued_point s U (fun b => coefficients (c b)) k hk hCompat
  refine ⟨g, hg, ?_⟩
  intro T t d b hd hFactors j hj
  let V : T.OpenCover.{0} := U.pullback₁ t
  refine V.hom_ext _ _ (fun i => ?_)
  let l := pullback.fst t (U.f i)
  let r := pullback.snd t (U.f i)
  change l ≫ t ≫ g = l ≫ point (t ≫ s) (coefficients d) j hj
  have hbase : l ≫ t ≫ s = r ≫ U.f i ≫ s := pullback.condition_assoc s
  have hprod : l ≫ t ≫ g = r ≫ U.f i ≫ g := pullback.condition_assoc g
  rw [hprod, hlocal, point_naturality, point_naturality, hbase]
  have hscale := exists_scale_of_products (r ≫ U.f i ≫ s)
    (fun q => r.appTop.hom ∘ c i q) (fun q => l.appTop.hom ∘ d q) (a i) b
    (fun q => (hc i q).map r.appTop.hom) (fun q => (hd q).map l.appTop.hom) (by
      intro q
      have hr := congrArg (fun g => r ≫ g) (hfactor i q)
      have hl := congrArg (fun g => l ≫ g) (hFactors q)
      rw [point_naturality] at hr
      rw [point_naturality, hbase] at hl
      exact hr.trans ((pullback.condition_assoc (p q)).symm.trans hl.symm))
  obtain ⟨u, hu⟩ := hscale
  have hScale : (r.appTop.hom ∘ coefficients (c i)) =
      fun k => ↑u * (l.appTop.hom ∘ coefficients d) k := by
    rw [coefficients_map, coefficients_map, hu]
  exact point_eq_of_scale _ _ _ _ _ _ _ u hScale

/-- The formula for multiplication on field-valued points. -/
def Multiplies (s : X ⟶ Spec (.of R)) (p : Fin m → (X ⟶ Line (R := R)))
    (g : X ⟶ Proj (grading R m)) : Prop :=
  ∀ {K : Type u} [Field K] (ρ : R →+* K) (t : Spec (.of K) ⟶ X)
    (_ : t ≫ s = Spec.map (CommRingCat.ofHom ρ))
    (c : Fin m → Fin 2 → K) (a : Fin m → Fin 2) (hc : ∀ i, IsUnit (c i (a i)))
    (_ : ∀ i, PhilipponProjectiveTupleChart.point ρ (c i) (a i) (hc i) = t ≫ p i)
    (k : Fin (m + 1)) (hk : IsUnit (coefficients c k)),
    t ≫ g = PhilipponProjectiveTupleChart.point ρ (coefficients c) k hk

theorem exists_multiplication_on_fields (s : X ⟶ Spec (.of R))
    (p : Fin m → (X ⟶ Line (R := R))) (hp : ∀ i, p i ≫ ProjSpace.π R 1 = s) :
    ∃ g : X ⟶ Proj (grading R m), g ≫ ProjSpace.π R m = s ∧ Multiplies s p g := by
  obtain ⟨g, hg, hm⟩ := exists_multiplication s p hp
  refine ⟨g, hg, ?_⟩
  intro K _ ρ t ht c a hc hfactor k hk
  let f := (Scheme.ΓSpecIso (.of K)).inv.hom
  let c' (i : Fin m) := f ∘ c i
  have hc' (i : Fin m) : IsUnit (c' i (a i)) := (hc i).map f
  have hfactor' (i : Fin m) : point (t ≫ s) (c' i) (a i) (hc' i) = t ≫ p i := by
    rw [ht]
    exact (point_Spec ρ (c i) (a i) (hc i)).trans (hfactor i)
  have he : coefficients c' = f ∘ coefficients c := (coefficients_map f c).symm
  have hk' : IsUnit (coefficients c' k) := he.symm ▸ hk.map f
  rw [hm t c' a hc' hfactor' k hk', ht]
  have compare (q : Fin (m + 1) → Γ(Spec (.of K), ⊤)) (h : q = f ∘ coefficients c)
      (hu : IsUnit (q k)) : point (Spec.map (CommRingCat.ofHom ρ)) q k hu =
        PhilipponProjectiveTupleChart.point ρ (coefficients c) k hk := by
    subst q
    exact point_Spec ρ (coefficients c) k hk
  exact compare _ he hk'

end PhilipponProjectiveLineMultiplication

end

section

set_option autoImplicit false
set_option maxHeartbeats 500000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory Polynomial


namespace PhilipponProjectiveLineFactorizationPoints

universe u

open PhilipponProjectiveProductCoefficients
open PhilipponProjectiveTupleChart (point point_scale point_eq_of_unit_pivots)

variable {R K : Type u} [CommRing R] [Field K]

private lemma point_eq_of_scale (ρ : R →+* K) {n : ℕ} (c d : Fin (n + 1) → K)
    (i j : Fin (n + 1)) (hi : IsUnit (c i)) (hj : IsUnit (d j))
    (a : Kˣ) (h : c = fun k => ↑a * d k) : point ρ c i hi = point ρ d j hj := by
  subst c
  have hd : IsUnit (d i) := isUnit_of_mul_isUnit_right hi
  exact (point_scale ρ d a i hd).trans (point_eq_of_unit_pivots ρ d i j hd hj)

private lemma finTwo (j : Fin 2) : j = 0 ∨ j = 1 := by fin_cases j <;> decide

private def rootCoordinates : Option K → Fin 2 → K
  | none => ![0, 1]
  | some z => ![1, -z]

private def rootPivot : Option K → Fin 2
  | none => 1
  | some _ => 0

private lemma root_unit (z : Option K) : IsUnit (rootCoordinates z (rootPivot z)) := by
  cases z <;> exact isUnit_one

private lemma point_eq_root (ρ : R →+* K) (c : Fin 2 → K) (i : Fin 2) (hi : IsUnit (c i)) :
    point ρ c i hi = point ρ (rootCoordinates (normalizedRoot (c 0) (c 1)))
      (rootPivot (normalizedRoot (c 0) (c 1))) (root_unit _) := by
  classical
  by_cases h : c 0 = 0
  · have hu : IsUnit (c 1) := by
      rcases finTwo i with rfl | rfl
      · exact False.elim (hi.ne_zero h)
      · exact hi
    simp only [normalizedRoot, if_pos h]
    apply point_eq_of_scale ρ _ _ _ _ _ _ hu.unit
    funext j
    rcases finTwo j with rfl | rfl
    · simp [rootCoordinates, h]
    · simp [rootCoordinates]
  · let a := Units.mk0 (c 0) h
    simp only [normalizedRoot, if_neg h]
    apply point_eq_of_scale ρ _ _ _ _ _ _ a
    funext j
    rcases finTwo j with rfl | rfl
    · simp [a, rootCoordinates]
    · change c 1 = c 0 * -(-c 1 / c 0)
      rw [neg_div, neg_neg, mul_comm (c 0), div_mul_cancel₀ _ h]

/-- Normalizing the root retains precisely the information in the represented point. -/
lemma point_eq_of_normalizedRoot_eq (ρ : R →+* K) (c d : Fin 2 → K)
    (i j : Fin 2) (hi : IsUnit (c i)) (hj : IsUnit (d j))
    (h : normalizedRoot (c 0) (c 1) = normalizedRoot (d 0) (d 1)) :
    point ρ c i hi = point ρ d j hj := by
  rw [point_eq_root ρ c i hi, point_eq_root ρ d j hj, h]

def coefficientPolynomial {m : ℕ} (c : Fin (m + 1) → K) : K[X] := by
  classical
  exact ofFn (m + 1) c

lemma coefficientPolynomial_coeff {m : ℕ} (c : Fin (m + 1) → K) (i : Fin (m + 1)) :
    (coefficientPolynomial c).coeff i.val = c i := by
  classical
  exact ofFn_coeff_eq_val_of_lt c i.isLt

lemma natDegree_coefficientPolynomial_le {m : ℕ} (c : Fin (m + 1) → K) :
    (coefficientPolynomial c).natDegree ≤ m := by
  classical
  exact Nat.le_of_lt_succ (ofFn_natDegree_lt (Nat.succ_pos _) c)

lemma coefficientPolynomial_ne_zero {m : ℕ} (c : Fin (m + 1) → K) (i : Fin (m + 1))
    (hi : IsUnit (c i)) : coefficientPolynomial c ≠ 0 := by
  intro h
  have hz := congrArg (fun p : K[X] => p.coeff i.val) h
  rw [coefficientPolynomial_coeff, coeff_zero] at hz
  exact hi.ne_zero hz

/-- Every point of projective space over an algebraically closed field
is represented by the product of a tuple of linear forms. -/
theorem exists_factorization [IsAlgClosed K] (ρ : R →+* K) {m : ℕ} (c : Fin (m + 1) → K)
    (i : Fin (m + 1)) (hi : IsUnit (c i)) :
    ∃ (d : Fin m → Fin 2 → K) (a : Fin m → Fin 2) (_ : ∀ j, IsUnit (d j (a j)))
      (h : IsUnit (coefficients d i)), point ρ (coefficients d) i h = point ρ c i hi := by
  classical
  let p := coefficientPolynomial c
  obtain ⟨x, y, huv, hp⟩ := exists_factorProduct p (natDegree_coefficientPolynomial_le c)
  let d (j : Fin m) : Fin 2 → K := ![x j, y j]
  have hunit : p.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr (coefficientPolynomial_ne_zero c i hi)
  let a := Units.mk0 p.leadingCoeff hunit
  have he : c = fun j => ↑a * coefficients d j := by
    funext j
    have hb := congrArg (fun q : K[X] => q.coeff j.val) hp
    rw [show p.coeff j.val = c j from coefficientPolynomial_coeff c j, coeff_C_mul] at hb
    exact hb
  have h : IsUnit (coefficients d i) :=
    isUnit_of_mul_isUnit_right ((congrFun he i) ▸ hi)
  refine ⟨d, fun j => if x j = 0 then 1 else 0, ?_, h, ?_⟩
  · intro j
    by_cases hz : x j = 0
    · have hy := (huv j).resolve_left (not_ne_iff.mpr hz)
      simpa [d, hz] using isUnit_iff_ne_zero.mpr hy
    · simpa [d, hz] using isUnit_iff_ne_zero.mpr hz
  · exact (point_eq_of_scale ρ c (coefficients d) i i hi h a he).symm

end PhilipponProjectiveLineFactorizationPoints

end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits


namespace PhilipponProjectiveLineTowerCoordinates

universe u
attribute [local instance] MvPolynomial.gradedAlgebra
open PhilipponEtaleProjectiveLineTower (linePower)

abbrev Line (R : Type u) [CommRing R] := Proj (MvPolynomial.homogeneousSubmodule (Fin 2) R)

variable {R : Type u} [CommRing R] {S : Scheme.{u}} (v : S ⟶ Spec (.of R))

/-- The projection to the specified factor of the projective-line tower. -/
def projection : (n : ℕ) → Fin (n + 1) → ((linePower v n).left ⟶ Line R)
  | 0, _ => pullback.snd v (ProjSpace.π R 1)
  | n + 1, i => Fin.lastCases
      (pullback.snd ((linePower v n).hom ≫ v) (ProjSpace.π R 1))
      (fun j => pullback.fst ((linePower v n).hom ≫ v) (ProjSpace.π R 1) ≫ projection n j) i

lemma projection_over (n : ℕ) (i : Fin (n + 1)) :
    projection v n i ≫ ProjSpace.π R 1 = (linePower v n).hom ≫ v := by
  induction n with
  | zero => exact pullback.condition.symm
  | succ n ih =>
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simp only [projection, Fin.lastCases_last]
        change pullback.snd _ _ ≫ ProjSpace.π R 1 =
          (pullback.fst _ _ ≫ (linePower v n).hom) ≫ v
        rw [Category.assoc, pullback.condition]
      · simp only [projection, Fin.lastCases_castSucc, Category.assoc, ih]
        rfl

/-- A map to the tower is uniquely determined by its base map and its factor maps. -/
theorem existsUnique_lift {T : Scheme.{u}} (a : T ⟶ S) (n : ℕ)
    (f : Fin (n + 1) → (T ⟶ Line R)) (hf : ∀ i, f i ≫ ProjSpace.π R 1 = a ≫ v) :
    ∃! p : T ⟶ (linePower v n).left,
      p ≫ (linePower v n).hom = a ∧ ∀ i, p ≫ projection v n i = f i := by
  induction n with
  | zero =>
      have h : a ≫ v = f 0 ≫ ProjSpace.π R 1 := (hf 0).symm
      refine ⟨pullback.lift a (f 0) h, ⟨pullback.lift_fst _ _ _, ?_⟩, ?_⟩
      · intro i
        have hi : i = 0 := Fin.eq_zero i
        subst i
        exact pullback.lift_snd _ _ _
      · intro p hp
        apply pullback.hom_ext
        · exact hp.1.trans (pullback.lift_fst _ _ _).symm
        · exact (hp.2 0).trans (pullback.lift_snd _ _ _).symm
  | succ n ih =>
      let B := linePower v n
      obtain ⟨b, hb, hb_unique⟩ := ih (fun j => f j.castSucc) (fun j => hf j.castSucc)
      let g := f (Fin.last (n + 1))
      have h : b ≫ (B.hom ≫ v) = g ≫ ProjSpace.π R 1 := by
        rw [← Category.assoc, hb.1, hf]
      let p := pullback.lift b g h
      have hp : ∀ i, p ≫ projection v (n + 1) i = f i := by
        intro i
        refine Fin.lastCases ?_ (fun j => ?_) i
        · simpa only [projection, Fin.lastCases_last] using pullback.lift_snd b g h
        · simp only [projection, Fin.lastCases_castSucc]
          change p ≫ pullback.fst (B.hom ≫ v) (ProjSpace.π R 1) ≫ projection v n j = f j.castSucc
          rw [← Category.assoc, pullback.lift_fst]
          exact hb.2 j
      refine ⟨p, ⟨?_, hp⟩, ?_⟩
      · change p ≫ pullback.fst _ _ ≫ B.hom = a
        rw [← Category.assoc, pullback.lift_fst, hb.1]
      · intro q hq
        have he : q ≫ pullback.fst (B.hom ≫ v) (ProjSpace.π R 1) = b := by
          apply hb_unique
          refine ⟨hq.1, fun j => ?_⟩
          simpa only [projection, Fin.lastCases_castSucc, Category.assoc] using hq.2 j.castSucc
        apply pullback.hom_ext
        · exact he.trans (pullback.lift_fst _ _ _).symm
        · change q ≫ pullback.snd (B.hom ≫ v) (ProjSpace.π R 1) =
            p ≫ pullback.snd (B.hom ≫ v) (ProjSpace.π R 1)
          rw [pullback.lift_snd]
          simpa only [projection, Fin.lastCases_last] using hq.2 (Fin.last (n + 1))

instance isProper_hom (n : ℕ) : IsProper (linePower v n).hom := by
  induction n with
  | zero =>
      change IsProper (pullback.fst v (ProjSpace.π R 1))
      infer_instance
  | succ n ih =>
      change IsProper (pullback.fst ((linePower v n).hom ≫ v) (ProjSpace.π R 1) ≫
        (linePower v n).hom)
      infer_instance

end PhilipponProjectiveLineTowerCoordinates

end

section

set_option autoImplicit false
set_option maxHeartbeats 500000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits


namespace PhilipponFiniteGeometricFibers

universe u

private lemma finite_of_finite_sections {K : Type u} [Field K] [IsAlgClosed K]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of K)) [LocallyOfFiniteType f]
    (h : Finite {p : Spec (.of K) ⟶ X // p ≫ f = 𝟙 _}) : Finite X := by
  let : Finite (closedPoints X) := Finite.of_injective (pointEquivClosedPoint f).symm
    (pointEquivClosedPoint f).symm.injective
  have he : (closedPoints X : Set X) = ⋃ z : closedPoints X, ({z.1} : Set X) := by
    ext x
    simp only [Set.mem_iUnion, Set.mem_singleton_iff]
    exact ⟨fun hx => ⟨⟨x, hx⟩, rfl⟩, fun ⟨z, hz⟩ => hz ▸ z.2⟩
  have hc : IsClosed (closedPoints X) := he ▸ isClosed_iUnion_of_finite (fun z => z.2)
  have : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace f
  have ht : (closedPoints X : Set X) = Set.univ := by
    rw [← hc.closure_eq]
    simpa using JacobsonSpace.closure_inter_closedPoints_eq_closure
      (isOpen_univ.isLocallyClosed : IsLocallyClosed (Set.univ : Set X))
  exact Finite.of_injective (fun x : X => (⟨x, ht ▸ Set.mem_univ x⟩ : closedPoints X))
    (fun _ _ e => congrArg Subtype.val e)

/-- A proper morphism with finitely many lifts of each algebraically
closed field-valued point is finite. -/
theorem isFinite_of_finite_geometric_lifts {X Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f]
    (h : ∀ {K : Type u} [Field K] [IsAlgClosed K] (y : Spec (.of K) ⟶ Y),
      Finite {p : Spec (.of K) ⟶ X // p ≫ f = y}) : IsFinite f := by
  have : LocallyQuasiFinite f := LocallyQuasiFinite.of_finite_preimage_singleton f fun y => by
    let k := Y.residueField y
    let K := AlgebraicClosure k
    let a : Spec (.of K) ⟶ Spec k := Spec.map (CommRingCat.ofHom (algebraMap k K))
    let e := Y.fromSpecResidueField y
    have : Surjective a := ⟨fun z => ⟨default, Subsingleton.elim _ z⟩⟩
    let F := f.fiberToSpecResidueField y
    have : LocallyOfFiniteType F := by
      change LocallyOfFiniteType (pullback.snd f e)
      infer_instance
    let Z := pullback F a
    let r : Z ⟶ f.fiber y := pullback.fst F a
    let t : Z ⟶ Spec (.of K) := pullback.snd F a
    have : LocallyOfFiniteType t := by dsimp only [t]; infer_instance
    have hfin : Finite Z := by
      apply finite_of_finite_sections t
      have : Finite {p : Spec (.of K) ⟶ X // p ≫ f = a ≫ e} := h (a ≫ e)
      let v : {p : Spec (.of K) ⟶ Z // p ≫ t = 𝟙 _} →
          {p : Spec (.of K) ⟶ X // p ≫ f = a ≫ e} := fun p =>
        ⟨p.1 ≫ r ≫ f.fiberι y, by
          have he : f.fiberι y ≫ f = F ≫ e := pullback.condition
          rw [Category.assoc, Category.assoc, he, ← Category.assoc r F,
            pullback.condition, Category.assoc, ← Category.assoc p.1 t, p.2, Category.id_comp]⟩
      apply Finite.of_injective v
      intro p q hv
      apply Subtype.ext
      apply pullback.hom_ext
      · apply (cancel_mono (f.fiberι y)).mp
        simpa only [Category.assoc] using congrArg Subtype.val hv
      · exact p.2.trans q.2.symm
    have : Surjective r := by dsimp only [r]; infer_instance
    have : Finite (f.fiber y) := Finite.of_surjective r r.surjective
    rw [← f.range_fiberι y]
    exact Set.finite_range _
  exact IsFinite.of_isProper_of_locallyQuasiFinite f

/-- Lifting every algebraically closed field-valued point implies surjectivity. -/
theorem surjective_of_geometric_lifts {X Y : Scheme.{u}} (f : X ⟶ Y)
    (h : ∀ {K : Type u} [Field K] [IsAlgClosed K] (y : Spec (.of K) ⟶ Y),
      ∃ p : Spec (.of K) ⟶ X, p ≫ f = y) : Surjective f := by
  constructor
  intro y
  let k := Y.residueField y
  let K := AlgebraicClosure k
  let a : Spec (.of K) ⟶ Spec k := Spec.map (CommRingCat.ofHom (algebraMap k K))
  obtain ⟨p, hp⟩ := h (a ≫ Y.fromSpecResidueField y)
  refine ⟨p default, ?_⟩
  change (p ≫ f) default = y
  rw [hp, Scheme.Hom.comp_apply, Scheme.fromSpecResidueField_apply]

end PhilipponFiniteGeometricFibers

end

section

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Polynomial


namespace PhilipponProjectiveLineCover

universe u
attribute [local instance] MvPolynomial.gradedAlgebra

open PhilipponEtaleProjectiveLineTower (linePower)
open PhilipponProjectiveLineTowerCoordinates (projection projection_over existsUnique_lift)
open PhilipponProjectiveLineMultiplication (Multiplies exists_multiplication_on_fields)
open PhilipponProjectiveProductCoefficients
open PhilipponProjectiveLineFactorizationPoints
open PhilipponProjectiveTupleChart (grading point point_over exists_point exists_unit_scale_of_point_eq)
open PhilipponFiniteGeometricFibers

variable {R : Type u} [CommRing R] {n : ℕ}

private abbrev tower (R : Type u) [CommRing R] (n : ℕ) := linePower (𝟙 (Spec (.of R))) n

private lemma proj_over (i : Fin (n + 1)) :
    projection (𝟙 (Spec (.of R))) n i ≫ ProjSpace.π R 1 = (tower R n).hom := by
  simpa only [Category.comp_id] using projection_over (𝟙 (Spec (.of R))) n i

private lemma all_geometric_points_lift {K : Type u} [Field K] [IsAlgClosed K]
    (g : (tower R n).left ⟶ Proj (grading R (n + 1)))
    (hm : Multiplies (tower R n).hom (projection (𝟙 (Spec (.of R))) n) g)
    (y : Spec (.of K) ⟶ Proj (grading R (n + 1))) : ∃ t, t ≫ g = y := by
  let σ := y ≫ ProjSpace.π R (n + 1)
  let ρ := (Spec.preimage σ).hom
  have hσ : σ = Spec.map (CommRingCat.ofHom ρ) := (Spec.map_preimage σ).symm
  obtain ⟨i, c, hi, hy⟩ := exists_point ρ y hσ
  obtain ⟨d, a, ha, hk, hFactor⟩ := exists_factorization ρ c i hi
  let q (j : Fin (n + 1)) := point ρ (d j) (a j) (ha j)
  have hq (j : Fin (n + 1)) : q j ≫ ProjSpace.π R 1 = σ ≫ 𝟙 _ := by
    rw [Category.comp_id, hσ]
    exact point_over _ _ _ _
  obtain ⟨t, ht, _⟩ := existsUnique_lift (𝟙 (Spec (.of R))) σ n q hq
  refine ⟨t, ?_⟩
  exact (hm ρ t (ht.1.trans hσ) d a ha (fun j => (ht.2 j).symm) i hk).trans (hFactor.trans hy)

private lemma geometric_lifts_finite {K : Type u} [Field K]
    (g : (tower R n).left ⟶ Proj (grading R (n + 1)))
    (hg : g ≫ ProjSpace.π R (n + 1) = (tower R n).hom)
    (hm : Multiplies (tower R n).hom (projection (𝟙 (Spec (.of R))) n) g)
    (y : Spec (.of K) ⟶ Proj (grading R (n + 1))) :
    Finite {t : Spec (.of K) ⟶ (tower R n).left // t ≫ g = y} := by
  let T := {t : Spec (.of K) ⟶ (tower R n).left // t ≫ g = y}
  let σ := y ≫ ProjSpace.π R (n + 1)
  let ρ := (Spec.preimage σ).hom
  have hσ : σ = Spec.map (CommRingCat.ofHom ρ) := (Spec.map_preimage σ).symm
  have ht (t : T) : t.1 ≫ (tower R n).hom = σ := by
    rw [← hg, ← Category.assoc, t.2]
  obtain ⟨i, e, he, hy⟩ := exists_point ρ y hσ
  let Q := coefficientPolynomial e
  let S : Set (Fin (n + 1) → Option K) := {z | ∃ (x y : Fin (n + 1) → K) (a : K),
    Q = C a * factorProduct x y ∧ z = fun i => normalizedRoot (x i) (y i)}
  have hSf : S.Finite := finite_normalized_factorizations Q (coefficientPolynomial_ne_zero e i he)
  let : Finite S := Set.finite_coe_iff.mpr hSf
  have hRep (t : T) (j : Fin (n + 1)) :
      ∃ (a : Fin 2) (d : Fin 2 → K) (hd : IsUnit (d a)),
        point ρ d a hd = t.1 ≫ projection (𝟙 (Spec (.of R))) n j := by
    apply exists_point
    rw [Category.assoc, proj_over, ht, hσ]
  choose a c hc hcoords using hRep
  let w (t : T) (j : Fin (n + 1)) := normalizedRoot (c t j 0) (c t j 1)
  have hw (t : T) : w t ∈ S := by
    obtain ⟨k, hk⟩ := exists_unit_coefficient (c t) (a t) (hc t)
    have hprod := hm ρ t.1 ((ht t).trans hσ) (c t) (a t) (hc t) (hcoords t) k hk
    have hv := exists_unit_scale_of_point_eq ρ e (coefficients (c t)) i k he hk
      (hy.trans (t.2.symm.trans hprod))
    obtain ⟨u, hu⟩ := hv
    refine ⟨fun j => c t j 0, fun j => c t j 1, ↑u, ?_, rfl⟩
    apply eq_C_mul_of_coeff_eq (natDegree_coefficientPolynomial_le e) (natDegree_factorProduct_le _ _)
    intro j
    rw [show Q.coeff j.val = e j from coefficientPolynomial_coeff e j]
    exact congrFun hu j
  apply Finite.of_injective (fun t : T => (⟨w t, hw t⟩ : S))
  intro t t' h
  have hProj (j : Fin (n + 1)) :
      t.1 ≫ projection (𝟙 (Spec (.of R))) n j = t'.1 ≫ projection (𝟙 (Spec (.of R))) n j := by
    exact (hcoords t j).symm.trans <|
      (point_eq_of_normalizedRoot_eq ρ _ _ _ _ (hc t j) (hc t' j)
        (congrFun (congrArg Subtype.val h) j)).trans (hcoords t' j)
  obtain ⟨z, _, huniq⟩ := existsUnique_lift (𝟙 (Spec (.of R))) σ n
    (fun j => t.1 ≫ projection (𝟙 (Spec (.of R))) n j) (by
      intro j
      rw [Category.assoc, proj_over, ht, Category.comp_id])
  apply Subtype.ext
  exact (huniq t.1 ⟨ht t, fun _ => rfl⟩).trans
    (huniq t'.1 ⟨ht t', fun j => (hProj j).symm⟩).symm

/-- Multiplication gives a finite surjection from the product of projective lines. -/
theorem exists_finite_cover (R : Type u) [CommRing R] (n : ℕ) :
    ∃ g : (tower R n).left ⟶ Proj (grading R (n + 1)),
      IsFinite g ∧ Surjective g ∧ g ≫ ProjSpace.π R (n + 1) = (tower R n).hom := by
  obtain ⟨g, hg, hm⟩ := exists_multiplication_on_fields (tower R n).hom
    (projection (𝟙 (Spec (.of R))) n) (fun _ => proj_over _)
  have : IsProper (g ≫ ProjSpace.π R (n + 1)) := by rw [hg]; infer_instance
  have : IsProper g := IsProper.of_comp g (ProjSpace.π R (n + 1))
  exact ⟨g, isFinite_of_finite_geometric_lifts g (geometric_lifts_finite g hg hm),
    surjective_of_geometric_lifts g (all_geometric_points_lift g hm), hg⟩

end PhilipponProjectiveLineCover

end

section

open PhilipponEtaleProjectiveLineTower (linePower)
attribute [local instance] MvPolynomial.gradedAlgebra

set_option autoImplicit false
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u

theorem solution
    (R : Type u) [CommRing R] (n : ℕ) :
    ∃ k : (linePower (𝟙 (Spec (.of R))) n).left ⟶
        Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1 + 1)) R),
      IsFinite k ∧ Surjective k ∧ k ≫ ProjSpace.π R (n + 1) = (linePower (𝟙 (Spec (.of R))) n).hom := by
  exact PhilipponProjectiveLineCover.exists_finite_cover R n

end

end

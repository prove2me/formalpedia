-- Prove2me | solution 1 for Algebra.exists_monic_irreducible_map_algebraicClosure_hypersurfaceModel_of_forall_isSeparable
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/27a0c18d-b5be-5b90-baf4-6d92475dc4b2

import Mathlib
import Theorems.Thm_Algebra_exists_ne_zero_algebraicIndependent_forall_isIntegral_pow_smul_of_finiteType
import Theorems.Thm_Polynomial_irreducible_map_map_algebraicClosure_of_separable_of_forall_isSeparable_mem_range
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Algebra_exists_monic_irreducible_map_algebraicClosure_hypersurfaceModel_of_forall_isSeparable

set_option autoImplicit false

universe u v w

open Polynomial
open scoped IntermediateField

namespace P2mHypModel

section SepPow

variable {F E : Type*} [Field F] [Field E] [Algebra F E]

theorem exists_isSeparable_pow (q : ℕ) [ExpChar F q] {t : E} (ht : IsIntegral F t) :
    ∃ n : ℕ, IsSeparable F (t ^ q ^ n) := by
  obtain ⟨g, hgsep, n, hg⟩ := (minpoly.irreducible ht).hasSeparableContraction q
  refine ⟨n, ?_⟩
  have h0 : Polynomial.aeval (t ^ q ^ n) g = 0 := by
    rw [← Polynomial.expand_aeval (q ^ n), hg, minpoly.aeval]
  have hne : g ≠ 0 := hgsep.ne_zero
  exact (hgsep.of_dvd (minpoly.dvd F _ h0))

theorem isSeparable_pow_add (q : ℕ) [ExpChar F q] {t : E} {n : ℕ} (h : IsSeparable F (t ^ q ^ n)) (m : ℕ) :
    IsSeparable F (t ^ q ^ (n + m)) := by
  have : t ^ q ^ (n + m) = (t ^ q ^ n) ^ q ^ m := by rw [← pow_mul, ← pow_add]
  rw [this]
  haveI := (IntermediateField.isSeparable_adjoin_simple_iff_isSeparable F E).2 h
  exact IntermediateField.isSeparable_of_mem_isSeparable F E
    (pow_mem (IntermediateField.mem_adjoin_simple_self F (t ^ q ^ n)) (q ^ m))

end SepPow

section FracRange

variable {k R L K : Type*} [Field k] [CommRing R] [IsDomain R] [Field L] [Field K]
  [Algebra k R] [Algebra R L] [Algebra k L] [IsScalarTower k R L]
  [Algebra R K] [IsFractionRing R K] [Algebra K L] [IsScalarTower R K L]

theorem coe_adjoin_range_eq_range :
    (IntermediateField.adjoin k (Set.range (algebraMap R L)) : Set L) = Set.range (algebraMap K L) := by
  apply le_antisymm
  ·
    let S : IntermediateField k L := (algebraMap K L).fieldRange.toIntermediateField (by
      intro a
      refine ⟨algebraMap R K (algebraMap k R a), ?_⟩
      rw [← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply])
    have h : IntermediateField.adjoin k (Set.range (algebraMap R L)) ≤ S := by
      rw [IntermediateField.adjoin_le_iff]
      rintro _ ⟨r, rfl⟩
      exact ⟨algebraMap R K r, (IsScalarTower.algebraMap_apply R K L r).symm⟩
    intro x hx
    exact h hx
  · rintro _ ⟨x, rfl⟩
    obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := R) x
    rw [map_div₀, ← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]
    exact div_mem (IntermediateField.subset_adjoin k _ ⟨a, rfl⟩) (IntermediateField.subset_adjoin k _ ⟨b, rfl⟩)

theorem forall_isSeparable_mem_range
    (hgi : ∀ θ : L, IsSeparable (IntermediateField.adjoin k (Set.range (algebraMap R L))) θ →
      θ ∈ IntermediateField.adjoin k (Set.range (algebraMap R L))) :
    ∀ θ : L, IsSeparable K θ → θ ∈ (algebraMap K L).range := by
  have hset := coe_adjoin_range_eq_range (k := k) (R := R) (L := L) (K := K)

  let K' := IntermediateField.adjoin k (Set.range (algebraMap R L))
  have hmemK' : ∀ x : K, algebraMap K L x ∈ K' := by
    intro x
    change algebraMap K L x ∈ (K' : Set L)
    rw [hset]
    exact ⟨x, rfl⟩
  let f : K →+* K' := (algebraMap K L).codRestrict K' hmemK'
  have hfbij : Function.Bijective f := by
    refine ⟨fun a b hab => (algebraMap K L).injective (congrArg Subtype.val hab), ?_⟩
    rintro ⟨y, hy⟩
    have hy' : y ∈ (K' : Set L) := hy
    rw [hset] at hy'
    obtain ⟨x, rfl⟩ := hy'
    exact ⟨x, rfl⟩
  let e : K ≃+* K' := RingEquiv.ofBijective f hfbij
  have he : (algebraMap K' L).comp (e : K →+* K') = (RingEquiv.refl L : L →+* L).comp (algebraMap K L) := by
    ext x; rfl
  intro θ hθ
  have h1 : IsSeparable K' ((RingEquiv.refl L) θ) := IsSeparable.of_equiv_equiv e (RingEquiv.refl L) he hθ
  have h2 : θ ∈ K' := hgi θ h1
  have h3 : θ ∈ (K' : Set L) := h2
  rw [hset] at h3
  exact h3

end FracRange

section Denom

theorem exists_ne_zero_map_eq_C_mul {R K : Type*} [CommRing R] [IsDomain R] [Field K] [Algebra R K]
    [IsFractionRing R K] {d : ℕ} (p : MvPolynomial (Fin d) K) :
    ∃ ρ : R, ρ ≠ 0 ∧ ∃ p₀ : MvPolynomial (Fin d) R,
      MvPolynomial.map (algebraMap R K) p₀ = MvPolynomial.C (algebraMap R K ρ) * p := by
  classical
  letI : Algebra (MvPolynomial (Fin d) R) (MvPolynomial (Fin d) K) := MvPolynomial.algebraMvPolynomial
  haveI hloc := MvPolynomial.isLocalization (σ := Fin d) (nonZeroDivisors R) K
  obtain ⟨⟨p₀, s⟩, hps⟩ := IsLocalization.surj ((nonZeroDivisors R).map (MvPolynomial.C : R →+* MvPolynomial (Fin d) R)) p
  obtain ⟨ρ, hρ, hρs⟩ := (Submonoid.mem_map).mp s.2
  refine ⟨ρ, nonZeroDivisors.ne_zero hρ, p₀, ?_⟩
  have hps' : p * MvPolynomial.map (algebraMap R K) (s : MvPolynomial (Fin d) R) =
      MvPolynomial.map (algebraMap R K) p₀ := hps
  rw [← hps', ← hρs, MvPolynomial.map_C, mul_comm]

end Denom

section Main

variable (k : Type u) [Field k] {R : Type v} {C : Type w} [CommRing R] [IsDomain R] [Algebra k R]
    [Algebra.FiniteType k R] [CommRing C] [IsDomain C] [Algebra k C] [Algebra R C]
    [IsScalarTower k R C] [Algebra.FiniteType R C] [FaithfulSMul R C]

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 16000000 in
set_option synthInstance.maxHeartbeats 1600000 in
theorem main
    (hgi : ∀ θ : FractionRing C,
      IsSeparable (IntermediateField.adjoin k (Set.range (algebraMap R (FractionRing C)))) θ →
      θ ∈ IntermediateField.adjoin k (Set.range (algebraMap R (FractionRing C)))) :
    ∃ r : R, r ≠ 0 ∧ ∃ (d : ℕ) (z : Fin d → C) (w : C) (F : Polynomial (MvPolynomial (Fin d) R))
      (g : MvPolynomial (Fin d) R),
      AlgebraicIndependent R z ∧ F.Monic ∧
      F.eval₂ (MvPolynomial.aeval z : MvPolynomial (Fin d) R →ₐ[R] C).toRingHom w = 0 ∧
      Irreducible (F.map (MvPolynomial.map (algebraMap R (AlgebraicClosure (FractionRing R))))) ∧
      g ≠ 0 ∧
      (∀ c : C, ∃ m M : ℕ, 0 < M ∧
        ((MvPolynomial.aeval z g) ^ m * c) ^ M ∈ Algebra.adjoin R (insert w (Set.range z))) ∧
      (∀ c : C, ∃ n : ℕ, IsIntegral (Algebra.adjoin R (Set.range z)) (r ^ n • c)) := by
  classical

  let K := FractionRing R
  let L := FractionRing C
  letI : Algebra K L := FractionRing.liftAlgebra R L
  haveI : IsScalarTower R K L := FractionRing.isScalarTower_liftAlgebra R L
  haveI : IsScalarTower k R L := IsScalarTower.of_algebraMap_eq (fun a => by
    rw [IsScalarTower.algebraMap_apply k C L, IsScalarTower.algebraMap_apply k R C,
      ← IsScalarTower.algebraMap_apply R C L])
  have hCL : Function.Injective (algebraMap C L) := IsFractionRing.injective C L
  have hRK : Function.Injective (algebraMap R K) := IsFractionRing.injective R K
  have hsc : ∀ θ : L, IsSeparable K θ → θ ∈ (algebraMap K L).range :=
    forall_isSeparable_mem_range (k := k) (R := R) (L := L) (K := K) hgi

  obtain ⟨r, hr, d, z, hz, hint⟩ :=
    Algebra.exists_ne_zero_algebraicIndependent_forall_isIntegral_pow_smul_of_finiteType (R := R) (C := C)

  let x : Fin d → L := fun i => algebraMap C L (z i)
  have hxR : AlgebraicIndependent R x := by
    change Function.Injective (MvPolynomial.aeval x)
    have : (MvPolynomial.aeval x : MvPolynomial (Fin d) R →ₐ[R] L) =
        (IsScalarTower.toAlgHom R C L).comp (MvPolynomial.aeval z) := by
      rw [MvPolynomial.comp_aeval]; rfl
    rw [this, AlgHom.coe_comp]
    exact hCL.comp hz
  haveI : Algebra.IsAlgebraic R K := IsLocalization.isAlgebraic (R := R) (S := K) (nonZeroDivisors R)
  have hx : AlgebraicIndependent K x := hxR.extendScalars K

  let φ : MvPolynomial (Fin d) K →+* L := (MvPolynomial.aeval x : MvPolynomial (Fin d) K →ₐ[K] L).toRingHom
  have hφinj : Function.Injective φ := hx
  have hφmap : ∀ q : MvPolynomial (Fin d) R,
      φ (MvPolynomial.map (algebraMap R K) q) = algebraMap C L (MvPolynomial.aeval z q) := by
    intro q
    change MvPolynomial.aeval x (MvPolynomial.map (algebraMap R K) q) = _
    rw [MvPolynomial.aeval_map_algebraMap]
    change MvPolynomial.aeval (fun i => (IsScalarTower.toAlgHom R C L) (z i)) q = _
    rw [← MvPolynomial.comp_aeval_apply]
    rfl
  have hφC : ∀ a : K, φ (MvPolynomial.C a) = algebraMap K L a := fun a =>
    (MvPolynomial.aeval x : MvPolynomial (Fin d) K →ₐ[K] L).commutes a
  letI algPL : Algebra (MvPolynomial (Fin d) K) L := φ.toAlgebra
  haveI : IsScalarTower K (MvPolynomial (Fin d) K) L := IsScalarTower.of_algebraMap_eq (fun a => (hφC a).symm)
  let ψ₀ : FractionRing (MvPolynomial (Fin d) K) →+* L := IsFractionRing.lift hφinj
  letI algML : Algebra (FractionRing (MvPolynomial (Fin d) K)) L := ψ₀.toAlgebra
  have hψ₀ : ∀ p, ψ₀ (algebraMap (MvPolynomial (Fin d) K) _ p) = φ p := fun p => IsFractionRing.lift_algebraMap hφinj p
  haveI : IsScalarTower (MvPolynomial (Fin d) K) (FractionRing (MvPolynomial (Fin d) K)) L :=
    IsScalarTower.of_algebraMap_eq (fun p => (hψ₀ p).symm)
  haveI : IsScalarTower K (FractionRing (MvPolynomial (Fin d) K)) L := IsScalarTower.of_algebraMap_eq (fun a => by
    rw [IsScalarTower.algebraMap_apply K (MvPolynomial (Fin d) K) (FractionRing (MvPolynomial (Fin d) K)),
      ← IsScalarTower.algebraMap_apply (MvPolynomial (Fin d) K)]
    exact (hφC a).symm)

  have hrL : algebraMap R L r ≠ 0 := (map_ne_zero_iff _ (hCL.comp (FaithfulSMul.algebraMap_injective R C) :
    Function.Injective ((algebraMap C L).comp (algebraMap R C)))).mpr hr
  have hRL : ∀ ρ : R, algebraMap R L ρ = φ (MvPolynomial.C (algebraMap R K ρ)) := by
    intro ρ; rw [hφC, ← IsScalarTower.algebraMap_apply]

  have hrangeA : ∀ a ∈ Algebra.adjoin R (Set.range z), algebraMap C L a ∈ φ.range := by
    intro a ha
    induction ha using Algebra.adjoin_induction with
    | mem c hc =>
      obtain ⟨i, rfl⟩ := hc
      exact ⟨MvPolynomial.X i, by simp [φ, x]⟩
    | algebraMap ρ =>
      exact ⟨MvPolynomial.C (algebraMap R K ρ), by rw [← hRL, IsScalarTower.algebraMap_apply R C L]⟩
    | add a b _ _ ha hb => rw [map_add]; exact add_mem ha hb
    | mul a b _ _ ha hb => rw [map_mul]; exact mul_mem ha hb
  have hintC : ∀ c : C, IsIntegral (MvPolynomial (Fin d) K) (algebraMap C L c) := by
    intro c
    obtain ⟨n₀, P₁, hP₁m, hP₁⟩ := hint c
    let P₂ : Polynomial L := P₁.map ((algebraMap C L).comp (algebraMap (Algebra.adjoin R (Set.range z)) C))
    have hP₂m : P₂.Monic := hP₁m.map _
    have hP₂ : P₂.eval (algebraMap C L (r ^ n₀ • c)) = 0 := by
      rw [Polynomial.eval_map, ← Polynomial.hom_eval₂, hP₁, map_zero]
    have hlift : P₂ ∈ Polynomial.lifts φ := by
      rw [Polynomial.lifts_iff_coeff_lifts]
      intro t
      rw [Polynomial.coeff_map, RingHom.comp_apply]
      obtain ⟨s, hs⟩ := hrangeA _ (P₁.coeff t).2
      exact ⟨s, hs⟩
    obtain ⟨Q, hQ, -, hQm⟩ := Polynomial.lifts_and_degree_eq_and_monic hlift hP₂m
    have hint1 : IsIntegral (MvPolynomial (Fin d) K) (algebraMap C L (r ^ n₀ • c)) := by
      refine ⟨Q, hQm, ?_⟩
      change Polynomial.eval₂ φ _ Q = 0
      rw [Polynomial.eval₂_eq_eval_map, hQ]
      exact hP₂
    have heq : algebraMap C L c =
        algebraMap (MvPolynomial (Fin d) K) L (MvPolynomial.C ((algebraMap R K r)⁻¹ ^ n₀)) *
          algebraMap C L (r ^ n₀ • c) := by
      change _ = φ _ * _
      rw [Algebra.smul_def, map_mul, map_pow, ← IsScalarTower.algebraMap_apply R C L, hRL, ← map_pow, ← mul_assoc,
        ← map_mul, ← MvPolynomial.C_mul, map_pow, ← mul_pow,
        inv_mul_cancel₀ ((map_ne_zero_iff _ hRK).mpr hr), one_pow, MvPolynomial.C_1, map_one, one_mul]
    rw [heq]
    exact isIntegral_algebraMap.mul hint1
  have hintM : ∀ c : C, IsIntegral (FractionRing (MvPolynomial (Fin d) K)) (algebraMap C L c) := fun c =>
    (hintC c).tower_top

  obtain ⟨q, hq⟩ := ExpChar.exists K
  haveI hqK : ExpChar K q := hq
  haveI hqM : ExpChar (FractionRing (MvPolynomial (Fin d) K)) q :=
    expChar_of_injective_algebraMap (algebraMap K _).injective q
  haveI hqL : ExpChar L q := expChar_of_injective_algebraMap (algebraMap K L).injective q
  haveI hqC : ExpChar C q := by
    exact (algebraMap C L).expChar hCL q
  obtain ⟨s, hs⟩ := Algebra.FiniteType.out (R := R) (A := C)
  have hex : ∀ c : C, ∃ n : ℕ, IsSeparable (FractionRing (MvPolynomial (Fin d) K)) (algebraMap C L c ^ q ^ n) :=
    fun c => exists_isSeparable_pow q (hintM c)
  choose nsep hnsep using hex
  obtain ⟨e, he⟩ : ∃ e : ℕ, ∀ c ∈ s, nsep c ≤ e := ⟨s.sup nsep, fun c hc => Finset.le_sup hc⟩
  have hsepgen : ∀ c ∈ s, IsSeparable (FractionRing (MvPolynomial (Fin d) K)) (algebraMap C L c ^ q ^ e) := by
    intro c hc
    obtain ⟨m, hm⟩ := Nat.exists_eq_add_of_le (he c hc)
    rw [hm]
    exact isSeparable_pow_add q (hnsep c) m

  let T : Set L := (fun c : C => algebraMap C L c ^ q ^ e) '' (s : Set C)
  let L₁ : IntermediateField (FractionRing (MvPolynomial (Fin d) K)) L := IntermediateField.adjoin _ T
  have hTint : ∀ t ∈ T, IsIntegral (FractionRing (MvPolynomial (Fin d) K)) t := by
    rintro _ ⟨c, -, rfl⟩; exact (hintM c).pow _
  haveI hL₁sep : Algebra.IsSeparable (FractionRing (MvPolynomial (Fin d) K)) L₁ :=
    (IntermediateField.isSeparable_adjoin_iff_isSeparable _ L).2 (by rintro _ ⟨c, hc, rfl⟩; exact hsepgen c hc)
  haveI hL₁fin : FiniteDimensional (FractionRing (MvPolynomial (Fin d) K)) L₁ :=
    IntermediateField.finiteDimensional_adjoin hTint
  have hML : ∀ p : MvPolynomial (Fin d) K,
      algebraMap (FractionRing (MvPolynomial (Fin d) K)) L (algebraMap _ _ p) = φ p := hψ₀
  have hmemL₁ : ∀ c : C, algebraMap C L c ^ q ^ e ∈ L₁ := by
    let S₁ : Subalgebra R C :=
      { carrier := {c | algebraMap C L c ^ q ^ e ∈ L₁}
        mul_mem' := fun {a b} ha hb => by
          change algebraMap C L (a * b) ^ q ^ e ∈ L₁
          rw [map_mul, mul_pow]; exact mul_mem ha hb
        add_mem' := fun {a b} ha hb => by
          change algebraMap C L (a + b) ^ q ^ e ∈ L₁
          rw [map_add, add_pow_expChar_pow]; exact add_mem ha hb
        algebraMap_mem' := fun ρ => by
          change algebraMap C L (algebraMap R C ρ) ^ q ^ e ∈ L₁
          rw [← IsScalarTower.algebraMap_apply R C L, hRL, ← hML]
          exact pow_mem (IntermediateField.algebraMap_mem L₁ _) _ }
    have hsS : Algebra.adjoin R (s : Set C) ≤ S₁ := Algebra.adjoin_le (fun c hc =>
      show algebraMap C L c ^ q ^ e ∈ L₁ from IntermediateField.subset_adjoin _ _ ⟨c, hc, rfl⟩)
    intro c
    exact hsS (by rw [hs]; exact Algebra.mem_top)

  obtain ⟨α, hα⟩ := Field.exists_primitive_element (FractionRing (MvPolynomial (Fin d) K)) L₁
  have hL₁α : (FractionRing (MvPolynomial (Fin d) K))⟮(α : L)⟯ = L₁ := by
    rw [← IntermediateField.lift_adjoin_simple, hα, IntermediateField.lift_top]

  have hden : ∀ t ∈ Algebra.adjoin (FractionRing (MvPolynomial (Fin d) K)) T,
      ∃ m : FractionRing (MvPolynomial (Fin d) K), m ≠ 0 ∧
        algebraMap _ L m ∈ (algebraMap C L).range ∧ algebraMap _ L m * t ∈ (algebraMap C L).range := by
    intro t ht
    induction ht using Algebra.adjoin_induction with
    | mem t ht =>
      obtain ⟨c, -, rfl⟩ := ht
      exact ⟨1, one_ne_zero, ⟨1, by rw [map_one, map_one]⟩, ⟨c ^ q ^ e, by rw [map_one, one_mul, map_pow]⟩⟩
    | algebraMap μ =>
      obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := MvPolynomial (Fin d) K) μ
      obtain ⟨ρa, hρa, a₀, ha₀⟩ := exists_ne_zero_map_eq_C_mul (R := R) (K := K) a
      obtain ⟨ρb, hρb, b₀, hb₀⟩ := exists_ne_zero_map_eq_C_mul (R := R) (K := K) b
      have hb' : b ≠ 0 := nonZeroDivisors.ne_zero hb
      refine ⟨algebraMap _ _ (MvPolynomial.C (algebraMap R K ρb) * b * MvPolynomial.C (algebraMap R K ρa)), ?_, ?_, ?_⟩
      · rw [map_ne_zero_iff _ (IsFractionRing.injective (MvPolynomial (Fin d) K) _)]
        exact mul_ne_zero (mul_ne_zero ((map_ne_zero_iff _ (MvPolynomial.C_injective _ _)).mpr
          ((map_ne_zero_iff _ hRK).mpr hρb)) hb') ((map_ne_zero_iff _ (MvPolynomial.C_injective _ _)).mpr
          ((map_ne_zero_iff _ hRK).mpr hρa))
      · refine ⟨MvPolynomial.aeval z b₀ * algebraMap R C ρa, ?_⟩
        rw [hML, ← hb₀, map_mul, map_mul, hφmap, ← hRL, IsScalarTower.algebraMap_apply R C L]
      · refine ⟨algebraMap R C ρb * MvPolynomial.aeval z a₀, ?_⟩
        have hbM : algebraMap (MvPolynomial (Fin d) K) (FractionRing (MvPolynomial (Fin d) K)) b ≠ 0 :=
          (map_ne_zero_iff _ (IsFractionRing.injective (MvPolynomial (Fin d) K) _)).mpr hb'
        have h1 : algebraMap (MvPolynomial (Fin d) K) (FractionRing (MvPolynomial (Fin d) K))
              (MvPolynomial.C (algebraMap R K ρb) * b * MvPolynomial.C (algebraMap R K ρa)) *
            (algebraMap _ _ a / algebraMap _ _ b) =
            algebraMap (MvPolynomial (Fin d) K) (FractionRing (MvPolynomial (Fin d) K))
              (MvPolynomial.C (algebraMap R K ρb) * (MvPolynomial.C (algebraMap R K ρa) * a)) := by
          rw [map_mul, map_mul, map_mul, map_mul, div_eq_mul_inv]
          have hring : ∀ X Y Z Bi B' : FractionRing (MvPolynomial (Fin d) K),
              X * B' * Y * (Z * Bi) = X * (Y * Z) * (B' * Bi) := by intros; ring
          rw [hring, mul_inv_cancel₀ hbM, mul_one]
        symm
        rw [← map_mul, h1, hML, ← ha₀, map_mul, hφmap, ← hRL, IsScalarTower.algebraMap_apply R C L, ← map_mul]
    | add a b _ _ ha hb =>
      obtain ⟨m₁, hm₁, ⟨c₁, hc₁⟩, ⟨d₁, hd₁⟩⟩ := ha
      obtain ⟨m₂, hm₂, ⟨c₂, hc₂⟩, ⟨d₂, hd₂⟩⟩ := hb
      refine ⟨m₁ * m₂, mul_ne_zero hm₁ hm₂, ⟨c₁ * c₂, by rw [map_mul, map_mul, hc₁, hc₂]⟩,
        ⟨c₂ * d₁ + c₁ * d₂, ?_⟩⟩
      rw [map_add (algebraMap C L), map_mul (algebraMap C L), map_mul (algebraMap C L), hc₁, hc₂, hd₁, hd₂, map_mul]
      ring
    | mul a b _ _ ha hb =>
      obtain ⟨m₁, hm₁, ⟨c₁, hc₁⟩, ⟨d₁, hd₁⟩⟩ := ha
      obtain ⟨m₂, hm₂, ⟨c₂, hc₂⟩, ⟨d₂, hd₂⟩⟩ := hb
      refine ⟨m₁ * m₂, mul_ne_zero hm₁ hm₂, ⟨c₁ * c₂, by rw [map_mul, map_mul, hc₁, hc₂]⟩, ⟨d₁ * d₂, ?_⟩⟩
      rw [map_mul (algebraMap C L), hd₁, hd₂, map_mul]
      ring

  have hadj_mul : ∀ (m : FractionRing (MvPolynomial (Fin d) K)) (_ : m ≠ 0) (t : L),
      (FractionRing (MvPolynomial (Fin d) K))⟮algebraMap _ L m * t⟯ = (FractionRing (MvPolynomial (Fin d) K))⟮t⟯ := by
    intro m hm t
    apply le_antisymm
    · rw [IntermediateField.adjoin_simple_le_iff]
      exact mul_mem (IntermediateField.algebraMap_mem _ m) (IntermediateField.mem_adjoin_simple_self _ t)
    · rw [IntermediateField.adjoin_simple_le_iff]
      have h1 : algebraMap _ L m * t ∈ (FractionRing (MvPolynomial (Fin d) K))⟮algebraMap _ L m * t⟯ :=
        IntermediateField.mem_adjoin_simple_self _ _
      have h2 : algebraMap _ L m⁻¹ * (algebraMap _ L m * t) ∈ (FractionRing (MvPolynomial (Fin d) K))⟮algebraMap _ L m * t⟯ :=
        mul_mem (IntermediateField.algebraMap_mem _ _) h1
      rwa [← mul_assoc, ← map_mul, inv_mul_cancel₀ hm, map_one, one_mul] at h2
  have hα₀ : (α : L) ∈ Algebra.adjoin (FractionRing (MvPolynomial (Fin d) K)) T := by
    have h1 : (α : L) ∈ L₁ := α.2
    rwa [← IntermediateField.mem_toSubalgebra,
      IntermediateField.adjoin_toSubalgebra_of_isAlgebraic (fun t ht => (hTint t ht).isAlgebraic)] at h1
  obtain ⟨m, hm0, -, ⟨w₀, hw₀⟩⟩ := hden _ hα₀
  have hyL₁ : (FractionRing (MvPolynomial (Fin d) K))⟮algebraMap C L w₀⟯ = L₁ := by
    rw [hw₀, hadj_mul m hm0, hL₁α]

  let F₀ : Polynomial (MvPolynomial (Fin d) K) := minpoly (MvPolynomial (Fin d) K) (algebraMap C L w₀)
  have hF₀m : F₀.Monic := minpoly.monic (hintC w₀)
  have hF₀y : F₀.eval₂ φ (algebraMap C L w₀) = 0 := by
    have := minpoly.aeval (MvPolynomial (Fin d) K) (algebraMap C L w₀)
    rwa [Polynomial.aeval_def] at this
  have hcoef : ∀ j : ℕ, ∃ ρ : R, ρ ≠ 0 ∧ ∃ p₀ : MvPolynomial (Fin d) R,
      MvPolynomial.map (algebraMap R K) p₀ = MvPolynomial.C (algebraMap R K ρ) * F₀.coeff j := fun j =>
    exists_ne_zero_map_eq_C_mul (R := R) (K := K) (F₀.coeff j)
  choose ρj hρj p₀j hp₀j using hcoef
  let ρ : R := ∏ j ∈ Finset.range F₀.natDegree, ρj j
  have hρ : ρ ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun j _ => hρj j)
  let F₁ : Polynomial (MvPolynomial (Fin d) K) := F₀.scaleRoots (MvPolynomial.C (algebraMap R K ρ))
  have hF₁m : F₁.Monic := (Polynomial.monic_scaleRoots_iff _).mpr hF₀m
  have hF₁lifts : F₁ ∈ Polynomial.lifts (MvPolynomial.map (algebraMap R K) :
      MvPolynomial (Fin d) R →+* MvPolynomial (Fin d) K) := by
    rw [Polynomial.lifts_iff_coeff_lifts]
    intro j
    change F₁.coeff j ∈ Set.range (MvPolynomial.map (algebraMap R K))
    rw [Polynomial.coeff_scaleRoots]
    rcases lt_trichotomy j F₀.natDegree with hj | hj | hj
    ·
      obtain ⟨t, ht⟩ : ∃ t, F₀.natDegree - j = t + 1 := ⟨F₀.natDegree - j - 1, by omega⟩
      have hdvd : ρj j ∣ ρ := Finset.dvd_prod_of_mem _ (Finset.mem_range.mpr hj)
      obtain ⟨σ, hσ⟩ := hdvd
      refine ⟨p₀j j * MvPolynomial.C σ * MvPolynomial.C ρ ^ t, ?_⟩
      rw [map_mul, map_mul, map_pow, MvPolynomial.map_C, MvPolynomial.map_C, hp₀j, ht, pow_succ, hσ, map_mul,
        MvPolynomial.C_mul]
      ring
    · refine ⟨1, ?_⟩
      rw [map_one, hj, Nat.sub_self, pow_zero, mul_one]
      exact (hF₀m.coeff_natDegree).symm
    · refine ⟨0, ?_⟩
      rw [map_zero, Polynomial.coeff_eq_zero_of_natDegree_lt hj, zero_mul]
  obtain ⟨F, hFmap, -, hFm⟩ := Polynomial.lifts_and_degree_eq_and_monic hF₁lifts hF₁m

  let w : C := ρ • w₀
  have hw : algebraMap C L w = φ (MvPolynomial.C (algebraMap R K ρ)) * algebraMap C L w₀ := by
    change algebraMap C L (ρ • w₀) = _
    rw [Algebra.smul_def, map_mul, ← IsScalarTower.algebraMap_apply, hRL]
  have hF₁y : F₁.eval₂ φ (algebraMap C L w) = 0 := by
    rw [hw]; exact Polynomial.scaleRoots_eval₂_eq_zero φ hF₀y
  have hφcomp : φ.comp (MvPolynomial.map (algebraMap R K)) =
      (algebraMap C L).comp (MvPolynomial.aeval z : MvPolynomial (Fin d) R →ₐ[R] C).toRingHom :=
    RingHom.ext fun q => hφmap q
  have hFroot : F.eval₂ (MvPolynomial.aeval z : MvPolynomial (Fin d) R →ₐ[R] C).toRingHom w = 0 := by
    apply hCL
    rw [Polynomial.hom_eval₂, ← hφcomp, ← Polynomial.eval₂_map, hFmap, hF₁y, map_zero]

  have hwL₁ : (FractionRing (MvPolynomial (Fin d) K))⟮algebraMap C L w⟯ = L₁ := by
    rw [hw, ← hML, hadj_mul _ ((map_ne_zero_iff _ (IsFractionRing.injective (MvPolynomial (Fin d) K) _)).mpr
      ((map_ne_zero_iff _ (MvPolynomial.C_injective _ _)).mpr ((map_ne_zero_iff _ hRK).mpr hρ))) _, hyL₁]
  haveI : IsGCDMonoid (MvPolynomial (Fin d) K) := ⟨UniqueFactorizationMonoid.toGCDMonoid _⟩
  haveI : IsIntegrallyClosed (MvPolynomial (Fin d) K) := GCDMonoid.toIsIntegrallyClosed
  have hdeg : (minpoly (FractionRing (MvPolynomial (Fin d) K)) (algebraMap C L w)).natDegree =
      (F₁.map (algebraMap (MvPolynomial (Fin d) K) (FractionRing (MvPolynomial (Fin d) K)))).natDegree := by
    rw [Polynomial.natDegree_map_eq_of_injective (IsFractionRing.injective (MvPolynomial (Fin d) K) _),
      Polynomial.natDegree_scaleRoots, ← IntermediateField.adjoin.finrank (hintM w), hwL₁, ← hyL₁,
      IntermediateField.adjoin.finrank (hintM w₀),
      minpoly.isIntegrallyClosed_eq_field_fractions' (FractionRing (MvPolynomial (Fin d) K)) (hintC w₀),
      Polynomial.natDegree_map_eq_of_injective (IsFractionRing.injective (MvPolynomial (Fin d) K) _)]
  have hmineq : minpoly (FractionRing (MvPolynomial (Fin d) K)) (algebraMap C L w) =
      F₁.map (algebraMap (MvPolynomial (Fin d) K) (FractionRing (MvPolynomial (Fin d) K))) := by
    symm
    apply Polynomial.eq_of_monic_of_dvd_of_natDegree_le (minpoly.monic (hintM w)) (hF₁m.map _)
    · apply minpoly.dvd
      rw [Polynomial.aeval_map_algebraMap, Polynomial.aeval_def]
      exact hF₁y
    · exact hdeg.ge
  have hF₁irr : Irreducible (F₁.map (algebraMap (MvPolynomial (Fin d) K) (FractionRing (MvPolynomial (Fin d) K)))) := by
    rw [← hmineq]; exact minpoly.irreducible (hintM w)
  have hF₁sep : (F₁.map (algebraMap (MvPolynomial (Fin d) K) (FractionRing (MvPolynomial (Fin d) K)))).Separable := by
    rw [← hmineq]
    exact IntermediateField.isSeparable_of_mem_isSeparable _ L (L := L₁)
      (by rw [← hwL₁]; exact IntermediateField.mem_adjoin_simple_self _ _)

  have hF₁abs := Polynomial.irreducible_map_map_algebraicClosure_of_separable_of_forall_isSeparable_mem_range
    hsc x hx (algebraMap C L w) F₁ hF₁m hF₁irr hF₁sep hF₁y
  have hFabs : Irreducible (F.map (MvPolynomial.map (algebraMap R (AlgebraicClosure (FractionRing R))))) := by
    have : MvPolynomial.map (algebraMap R (AlgebraicClosure (FractionRing R))) =
        (MvPolynomial.map (algebraMap K (AlgebraicClosure K))).comp
          (MvPolynomial.map (σ := Fin d) (algebraMap R K)) := by
      apply RingHom.ext; intro q
      rw [RingHom.comp_apply, MvPolynomial.map_map, ← IsScalarTower.algebraMap_eq]
    rw [this, ← Polynomial.map_map, hFmap]
    exact hF₁abs

  have hwsep : IsSeparable (FractionRing (MvPolynomial (Fin d) K)) (algebraMap C L w) :=
    IntermediateField.isSeparable_of_mem_isSeparable _ L (L := L₁)
      (by rw [← hwL₁]; exact IntermediateField.mem_adjoin_simple_self _ _)
  haveI : Algebra.IsSeparable (FractionRing (MvPolynomial (Fin d) K)) (FractionRing (MvPolynomial (Fin d) K))⟮algebraMap C L w⟯ :=
    (IntermediateField.isSeparable_adjoin_simple_iff_isSeparable _ L).2 hwsep
  haveI : FiniteDimensional (FractionRing (MvPolynomial (Fin d) K)) (FractionRing (MvPolynomial (Fin d) K))⟮algebraMap C L w⟯ :=
    IntermediateField.adjoin.finiteDimensional (hintM w)
  haveI : IsScalarTower (MvPolynomial (Fin d) K) (FractionRing (MvPolynomial (Fin d) K)) (FractionRing (MvPolynomial (Fin d) K))⟮algebraMap C L w⟯ :=
    IsScalarTower.of_algebraMap_eq (fun p => Subtype.ext (IsScalarTower.algebraMap_apply _ _ L p))
  haveI : IsScalarTower (MvPolynomial (Fin d) K) (FractionRing (MvPolynomial (Fin d) K))⟮algebraMap C L w⟯ L := IsScalarTower.of_algebraMap_eq (fun p => rfl)
  have hintKy : ∀ t : (FractionRing (MvPolynomial (Fin d) K))⟮algebraMap C L w⟯, IsIntegral (MvPolynomial (Fin d) K) (t : L) → IsIntegral (MvPolynomial (Fin d) K) t := by
    intro t ht
    exact (isIntegral_algHom_iff (IsScalarTower.toAlgHom (MvPolynomial (Fin d) K) (FractionRing (MvPolynomial (Fin d) K))⟮algebraMap C L w⟯ L) Subtype.val_injective).mp ht
  obtain ⟨B, hBgen⟩ : ∃ B : PowerBasis (FractionRing (MvPolynomial (Fin d) K)) (FractionRing (MvPolynomial (Fin d) K))⟮algebraMap C L w⟯, (B.gen : L) = algebraMap C L w :=
    ⟨IntermediateField.adjoin.powerBasis (hintM w), by
      rw [IntermediateField.adjoin.powerBasis_gen, IntermediateField.AdjoinSimple.coe_gen]⟩
  have hBint : IsIntegral (MvPolynomial (Fin d) K) B.gen := hintKy _ (by rw [hBgen]; exact hintC w)
  obtain ⟨Δ, hΔdef⟩ : ∃ Δ : FractionRing (MvPolynomial (Fin d) K), Algebra.discr _ B.basis = Δ := ⟨_, rfl⟩
  have hΔ0 : Δ ≠ 0 := by rw [← hΔdef]; exact Algebra.discr_not_zero_of_basis _ B.basis
  have hΔ : ∀ c : C, algebraMap _ L Δ * algebraMap C L c ^ q ^ e ∈
      Algebra.adjoin (MvPolynomial (Fin d) K) {algebraMap C L w} := by
    intro c
    have hmem : algebraMap C L c ^ q ^ e ∈ (FractionRing (MvPolynomial (Fin d) K))⟮algebraMap C L w⟯ := by
      rw [hwL₁]; exact hmemL₁ c
    have hzint : IsIntegral (MvPolynomial (Fin d) K) (⟨_, hmem⟩ : (FractionRing (MvPolynomial (Fin d) K))⟮algebraMap C L w⟯) := hintKy _ ((hintC c).pow _)
    have h1 := Algebra.discr_mul_isIntegral_mem_adjoin (K := FractionRing (MvPolynomial (Fin d) K)) hBint hzint
    rw [hΔdef] at h1
    have h2 : ((IsScalarTower.toAlgHom (MvPolynomial (Fin d) K) (FractionRing (MvPolynomial (Fin d) K))⟮algebraMap C L w⟯ L) (Δ • (⟨_, hmem⟩ : (FractionRing (MvPolynomial (Fin d) K))⟮algebraMap C L w⟯))) ∈
        (Algebra.adjoin (MvPolynomial (Fin d) K) {B.gen}).map (IsScalarTower.toAlgHom (MvPolynomial (Fin d) K) (FractionRing (MvPolynomial (Fin d) K))⟮algebraMap C L w⟯ L) :=
      Subalgebra.mem_map.mpr ⟨_, h1, rfl⟩
    rw [AlgHom.map_adjoin, Set.image_singleton] at h2
    have h3 : (IsScalarTower.toAlgHom (MvPolynomial (Fin d) K) (FractionRing (MvPolynomial (Fin d) K))⟮algebraMap C L w⟯ L) B.gen = algebraMap C L w := hBgen
    rw [h3] at h2
    have h4 : (IsScalarTower.toAlgHom (MvPolynomial (Fin d) K) (FractionRing (MvPolynomial (Fin d) K))⟮algebraMap C L w⟯ L) (Δ • (⟨_, hmem⟩ : (FractionRing (MvPolynomial (Fin d) K))⟮algebraMap C L w⟯)) =
        algebraMap _ L Δ * algebraMap C L c ^ q ^ e := by
      change ((Δ • (⟨_, hmem⟩ : (FractionRing (MvPolynomial (Fin d) K))⟮algebraMap C L w⟯) : (FractionRing (MvPolynomial (Fin d) K))⟮algebraMap C L w⟯) : L) = _
      rw [IntermediateField.coe_smul, Algebra.smul_def]
    rwa [h4] at h2

  have hden2 : ∀ t ∈ Algebra.adjoin (MvPolynomial (Fin d) K) {algebraMap C L w},
      ∃ σ : R, σ ≠ 0 ∧ algebraMap R L σ * t ∈ (algebraMap C L) '' (Algebra.adjoin R (insert w (Set.range z))) := by
    have hzH : ∀ p₀ : MvPolynomial (Fin d) R, MvPolynomial.aeval z p₀ ∈ Algebra.adjoin R (insert w (Set.range z)) := by
      intro p₀
      have : MvPolynomial.aeval z p₀ ∈ Algebra.adjoin R (Set.range z) := by
        rw [Algebra.adjoin_range_eq_range_aeval]; exact ⟨p₀, rfl⟩
      exact Algebra.adjoin_mono (Set.subset_insert _ _) this
    intro t ht
    induction ht using Algebra.adjoin_induction with
    | mem t ht =>
      rw [Set.mem_singleton_iff] at ht
      subst ht
      exact ⟨1, one_ne_zero, ⟨w, Algebra.subset_adjoin (Set.mem_insert _ _), by rw [map_one, one_mul]⟩⟩
    | algebraMap p =>
      obtain ⟨σ, hσ, p₀, hp₀⟩ := exists_ne_zero_map_eq_C_mul (R := R) (K := K) p
      refine ⟨σ, hσ, ⟨MvPolynomial.aeval z p₀, hzH p₀, ?_⟩⟩
      rw [← hφmap, hp₀, map_mul, ← hRL]; rfl
    | add a b _ _ ha hb =>
      obtain ⟨σ₁, hσ₁, ⟨h₁, hh₁, e₁⟩⟩ := ha
      obtain ⟨σ₂, hσ₂, ⟨h₂, hh₂, e₂⟩⟩ := hb
      refine ⟨σ₁ * σ₂, mul_ne_zero hσ₁ hσ₂, ⟨algebraMap R C σ₂ * h₁ + algebraMap R C σ₁ * h₂,
        add_mem (mul_mem (Subalgebra.algebraMap_mem _ _) hh₁) (mul_mem (Subalgebra.algebraMap_mem _ _) hh₂), ?_⟩⟩
      rw [map_add, map_mul, map_mul, e₁, e₂, ← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply,
        map_mul]
      ring
    | mul a b _ _ ha hb =>
      obtain ⟨σ₁, hσ₁, ⟨h₁, hh₁, e₁⟩⟩ := ha
      obtain ⟨σ₂, hσ₂, ⟨h₂, hh₂, e₂⟩⟩ := hb
      refine ⟨σ₁ * σ₂, mul_ne_zero hσ₁ hσ₂, ⟨h₁ * h₂, mul_mem hh₁ hh₂, ?_⟩⟩
      rw [map_mul, e₁, e₂, map_mul]
      ring

  obtain ⟨aΔ, bΔ, hbΔ, hΔab⟩ := IsFractionRing.div_surjective (A := MvPolynomial (Fin d) K) Δ
  have haΔ : aΔ ≠ 0 := by
    intro h; apply hΔ0; rw [← hΔab, h, map_zero, zero_div]
  have hΔ' : ∀ c : C, φ aΔ * algebraMap C L c ^ q ^ e ∈ Algebra.adjoin (MvPolynomial (Fin d) K) {algebraMap C L w} := by
    intro c
    have hbΔ' : algebraMap (MvPolynomial (Fin d) K) (FractionRing (MvPolynomial (Fin d) K)) bΔ ≠ 0 :=
      (map_ne_zero_iff _ (IsFractionRing.injective (MvPolynomial (Fin d) K) _)).mpr (nonZeroDivisors.ne_zero hbΔ)
    have h1 : φ aΔ = φ bΔ * algebraMap _ L Δ := by
      rw [← hML, ← hML, ← map_mul, ← hΔab, mul_div_cancel₀ _ hbΔ']
    rw [h1, mul_assoc]
    exact mul_mem (Subalgebra.algebraMap_mem _ bΔ) (hΔ c)
  obtain ⟨ρa, hρa, a₀, ha₀⟩ := exists_ne_zero_map_eq_C_mul (R := R) (K := K) aΔ
  have ha₀0 : a₀ ≠ 0 := by
    intro h
    rw [h, map_zero, eq_comm, mul_eq_zero] at ha₀
    rcases ha₀ with h' | h'
    · exact ((map_ne_zero_iff _ (MvPolynomial.C_injective _ _)).mpr ((map_ne_zero_iff _ hRK).mpr hρa)) h'
    · exact haΔ h'
  have hσc : ∀ c : C, ∃ σ : R, σ ≠ 0 ∧
      algebraMap R C σ * (MvPolynomial.aeval z a₀ * c ^ q ^ e) ∈ Algebra.adjoin R (insert w (Set.range z)) := by
    intro c
    obtain ⟨σ, hσ, ⟨h, hh, he⟩⟩ := hden2 _ (hΔ' c)
    refine ⟨σ, hσ, ?_⟩
    have : algebraMap R C σ * (MvPolynomial.aeval z a₀ * c ^ q ^ e) = algebraMap R C ρa * h := by
      apply hCL
      rw [map_mul, map_mul, map_mul, ← hφmap, ha₀, map_mul, he, ← IsScalarTower.algebraMap_apply,
        ← IsScalarTower.algebraMap_apply, ← hRL, map_pow]
      ring
    rw [this]
    exact mul_mem (Subalgebra.algebraMap_mem _ _) hh
  choose σc hσc0 hσc using hσc
  let g : MvPolynomial (Fin d) R := MvPolynomial.C (∏ c ∈ s, σc c) * a₀
  have hg0 : g ≠ 0 := mul_ne_zero ((map_ne_zero_iff _ (MvPolynomial.C_injective _ _)).mpr
    (Finset.prod_ne_zero_iff.mpr fun c _ => hσc0 c)) ha₀0
  have hgH : MvPolynomial.aeval z g ∈ Algebra.adjoin R (insert w (Set.range z)) := by
    have : MvPolynomial.aeval z g ∈ Algebra.adjoin R (Set.range z) := by
      rw [Algebra.adjoin_range_eq_range_aeval]; exact ⟨g, rfl⟩
    exact Algebra.adjoin_mono (Set.subset_insert _ _) this
  have hggen : ∀ c ∈ s, MvPolynomial.aeval z g * c ^ q ^ e ∈ Algebra.adjoin R (insert w (Set.range z)) := by
    intro c hc
    obtain ⟨τ, hτ⟩ : σc c ∣ ∏ c ∈ s, σc c := Finset.dvd_prod_of_mem _ hc
    have : MvPolynomial.aeval z g * c ^ q ^ e =
        algebraMap R C τ * (algebraMap R C (σc c) * (MvPolynomial.aeval z a₀ * c ^ q ^ e)) := by
      change MvPolynomial.aeval z (MvPolynomial.C _ * a₀) * _ = _
      rw [map_mul, MvPolynomial.algHom_C, hτ, map_mul]; ring
    rw [this]
    exact mul_mem (Subalgebra.algebraMap_mem _ _) (hσc c)

  have hpos : 0 < q ^ e := Nat.pos_of_ne_zero (pow_ne_zero _ (expChar_pos K q).ne')
  have hrad : ∀ c : C, ∃ m M : ℕ, 0 < M ∧
      ((MvPolynomial.aeval z g) ^ m * c) ^ M ∈ Algebra.adjoin R (insert w (Set.range z)) := by
    let S₂ : Subalgebra R C :=
      { carrier := {c | ∃ m : ℕ, ((MvPolynomial.aeval z g) ^ m * c) ^ q ^ e ∈ Algebra.adjoin R (insert w (Set.range z))}
        mul_mem' := fun {a b} ha hb => by
          obtain ⟨m₁, h₁⟩ := ha
          obtain ⟨m₂, h₂⟩ := hb
          refine ⟨m₁ + m₂, ?_⟩
          have : ((MvPolynomial.aeval z g) ^ (m₁ + m₂) * (a * b)) ^ q ^ e =
              ((MvPolynomial.aeval z g) ^ m₁ * a) ^ q ^ e * ((MvPolynomial.aeval z g) ^ m₂ * b) ^ q ^ e := by
            rw [← mul_pow]; ring
          rw [this]; exact mul_mem h₁ h₂
        add_mem' := fun {a b} ha hb => by
          obtain ⟨m₁, h₁⟩ := ha
          obtain ⟨m₂, h₂⟩ := hb
          refine ⟨m₁ + m₂, ?_⟩
          have : ((MvPolynomial.aeval z g) ^ (m₁ + m₂) * (a + b)) ^ q ^ e =
              ((MvPolynomial.aeval z g) ^ m₂) ^ q ^ e * ((MvPolynomial.aeval z g) ^ m₁ * a) ^ q ^ e +
              ((MvPolynomial.aeval z g) ^ m₁) ^ q ^ e * ((MvPolynomial.aeval z g) ^ m₂ * b) ^ q ^ e := by
            rw [mul_add, add_pow_expChar_pow, ← mul_pow, ← mul_pow]; ring
          rw [this]
          exact add_mem (mul_mem (pow_mem (pow_mem hgH _) _) h₁) (mul_mem (pow_mem (pow_mem hgH _) _) h₂)
        algebraMap_mem' := fun ρ' => ⟨0, by
          rw [pow_zero, one_mul]; exact pow_mem (Subalgebra.algebraMap_mem _ _) _⟩ }
    have hsS : Algebra.adjoin R (s : Set C) ≤ S₂ := Algebra.adjoin_le (fun c hc => ⟨1, by
      obtain ⟨t, ht⟩ : ∃ t, q ^ e = t + 1 := ⟨q ^ e - 1, by omega⟩
      have : ((MvPolynomial.aeval z g) ^ 1 * c) ^ q ^ e =
          (MvPolynomial.aeval z g) ^ t * (MvPolynomial.aeval z g * c ^ q ^ e) := by
        rw [pow_one, mul_pow, ht, pow_succ]; ring
      rw [this]
      exact mul_mem (pow_mem hgH _) (hggen c hc)⟩)
    intro c
    obtain ⟨m, hm⟩ := hsS (show c ∈ Algebra.adjoin R (s : Set C) by rw [hs]; exact Algebra.mem_top)
    exact ⟨m, q ^ e, hpos, hm⟩
  exact ⟨r, hr, d, z, w, F, g, hz, hFm, hFroot, hFabs, hg0, hrad, hint⟩

end Main

end P2mHypModel

theorem solution
    (k : Type u) [Field k] {R : Type v} {C : Type w} [CommRing R] [IsDomain R] [Algebra k R]
    [Algebra.FiniteType k R] [CommRing C] [IsDomain C] [Algebra k C] [Algebra R C]
    [IsScalarTower k R C] [Algebra.FiniteType R C] [FaithfulSMul R C]
    (hgi : ∀ θ : FractionRing C,
      IsSeparable (IntermediateField.adjoin k (Set.range (algebraMap R (FractionRing C)))) θ →
      θ ∈ IntermediateField.adjoin k (Set.range (algebraMap R (FractionRing C)))) :
    ∃ r : R, r ≠ 0 ∧ ∃ (d : ℕ) (z : Fin d → C) (w : C) (F : Polynomial (MvPolynomial (Fin d) R))
      (g : MvPolynomial (Fin d) R),
      AlgebraicIndependent R z ∧ F.Monic ∧
      F.eval₂ (MvPolynomial.aeval z : MvPolynomial (Fin d) R →ₐ[R] C).toRingHom w = 0 ∧
      Irreducible (F.map (MvPolynomial.map (algebraMap R (AlgebraicClosure (FractionRing R))))) ∧
      g ≠ 0 ∧
      (∀ c : C, ∃ m M : ℕ, 0 < M ∧
        ((MvPolynomial.aeval z g) ^ m * c) ^ M ∈ Algebra.adjoin R (insert w (Set.range z))) ∧
      (∀ c : C, ∃ n : ℕ, IsIntegral (Algebra.adjoin R (Set.range z)) (r ^ n • c)) :=
  P2mHypModel.main k hgi

end S_Algebra_exists_monic_irreducible_map_algebraicClosure_hypersurfaceModel_of_forall_isSeparable
end P2MW
export P2MW.S_Algebra_exists_monic_irreducible_map_algebraicClosure_hypersurfaceModel_of_forall_isSeparable (solution)

-- Prove2me | solution 1 for AlgebraicCurve.RegularProlongation.exists_smoothPointStalk_baseChange_layer
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/fd733a1c-1f93-5bf4-baf9-ed31d0e88ddf

import Mathlib
import Definitions.Def_AlgebraicCurve_ResidueDiscs
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_StandardAnnulus
import Theorems.Thm_HenselianLocalRing_existsUnique_section_and_ker_eq_span_of_formallySmooth_of_formallyUnramified
import Theorems.Thm_IsRegularLocalRing_uniqueFactorizationMonoid_of_ringKrullDim_le_two
import Theorems.Thm_ValuationSubring_toSubring_eq_integralClosure_and_finite_and_isDiscreteValuationRing_of_henselian
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_RegularProlongation_exists_smoothPointStalk_baseChange_layer

set_option autoImplicit false

set_option autoImplicit false

open IsLocalRing

namespace L1BhEis

variable {A₁ A₂ : Type*} [CommRing A₁] [IsDomain A₁] [IsDiscreteValuationRing A₁]
  [CommRing A₂] [IsDomain A₂] [IsDiscreteValuationRing A₂]

theorem dvd_of_not_isUnit {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {ϖ : R} (hϖ : Irreducible ϖ) {x : R} (hx : ¬ IsUnit x) : ϖ ∣ x := by
  have hmem : x ∈ maximalIdeal R := (IsLocalRing.mem_maximalIdeal x).mpr hx
  rw [(IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).mp hϖ, Ideal.mem_span_singleton] at hmem
  exact hmem

theorem forall_dvd_of_sum_eq_zero
    (ι : A₁ →+* A₂) (ϖ₁ : A₁) (ϖ₂ : A₂) (hϖ₂ : Irreducible ϖ₂)
    (e : ℕ) (u : A₂ˣ) (he : ι ϖ₁ = (u : A₂) * ϖ₂ ^ e) (hϖ₁ : Irreducible ϖ₁)
    (a : Fin e → A₁) (ha : ∑ j, ι (a j) * ϖ₂ ^ (j : ℕ) = 0) : ∀ j, ϖ₁ ∣ a j := by
  classical
  by_contra hnot
  push Not at hnot

  have hne : (Finset.univ.filter fun j : Fin e => IsUnit (a j)).Nonempty := by
    obtain ⟨j, hj⟩ := hnot
    exact ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, by
      by_contra hu; exact hj (dvd_of_not_isUnit hϖ₁ hu)⟩⟩
  set j₀ := (Finset.univ.filter fun j : Fin e => IsUnit (a j)).min' hne with hj₀
  have hj₀u : IsUnit (a j₀) := (Finset.mem_filter.mp (Finset.min'_mem _ hne)).2
  have hlt : ∀ j : Fin e, j < j₀ → ¬ IsUnit (a j) := by
    intro j hj hu
    have hmem : j ∈ Finset.univ.filter (fun j : Fin e => IsUnit (a j)) :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, hu⟩
    have := Finset.min'_le _ j hmem
    rw [← hj₀] at this
    exact absurd hj (not_lt.mpr this)

  have hdiv : ∀ j : Fin e, j ≠ j₀ → ϖ₂ ^ ((j₀ : ℕ) + 1) ∣ ι (a j) * ϖ₂ ^ (j : ℕ) := by
    intro j hj
    rcases lt_or_gt_of_ne hj with h | h
    ·
      obtain ⟨b, hb⟩ := dvd_of_not_isUnit hϖ₁ (hlt j h)
      have h1 : ϖ₂ ^ e ∣ ι (a j) := by
        rw [hb, map_mul, he]
        exact Dvd.dvd.mul_right (Dvd.intro_left _ rfl) _
      have h2 : (j₀ : ℕ) + 1 ≤ e := by have := j₀.2; omega
      exact (pow_dvd_pow ϖ₂ h2).trans (h1.mul_right _)
    ·
      have h2 : (j₀ : ℕ) + 1 ≤ (j : ℕ) := by
        have : (j₀ : ℕ) < (j : ℕ) := h
        omega
      exact Dvd.dvd.mul_left (pow_dvd_pow ϖ₂ h2) _

  have hsum : ι (a j₀) * ϖ₂ ^ (j₀ : ℕ) = -∑ j ∈ Finset.univ.erase j₀, ι (a j) * ϖ₂ ^ (j : ℕ) := by
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ j₀)] at ha
    linear_combination ha
  have hdvd : ϖ₂ ^ ((j₀ : ℕ) + 1) ∣ ι (a j₀) * ϖ₂ ^ (j₀ : ℕ) := by
    rw [hsum]
    exact (Finset.dvd_sum fun j hj => hdiv j (Finset.ne_of_mem_erase hj)).neg_right
  have hdvd' : ϖ₂ ∣ ι (a j₀) := by
    rw [pow_succ, mul_comm (ϖ₂ ^ (j₀ : ℕ))] at hdvd
    exact (mul_dvd_mul_iff_right (pow_ne_zero _ hϖ₂.ne_zero)).mp hdvd
  have : ¬ IsUnit (ι (a j₀)) := fun hu => hϖ₂.not_isUnit (isUnit_of_dvd_unit hdvd' hu)
  exact this (hj₀u.map ι)

theorem forall_pow_dvd_of_sum_eq_zero
    (ι : A₁ →+* A₂) (hι : Function.Injective ι) (ϖ₁ : A₁) (hϖ₁ : Irreducible ϖ₁) (ϖ₂ : A₂) (hϖ₂ : Irreducible ϖ₂)
    (e : ℕ) (u : A₂ˣ) (he : ι ϖ₁ = (u : A₂) * ϖ₂ ^ e) :
    ∀ (n : ℕ) (a : Fin e → A₁), ∑ j, ι (a j) * ϖ₂ ^ (j : ℕ) = 0 → ∀ j, ϖ₁ ^ n ∣ a j := by
  classical
  intro n
  induction n with
  | zero => intro a _ j; exact ⟨a j, by rw [pow_zero, one_mul]⟩
  | succ n ih =>
    intro a ha j
    have hall := forall_dvd_of_sum_eq_zero ι ϖ₁ ϖ₂ hϖ₂ e u he hϖ₁ a ha
    choose b hb using hall

    have hb0 : ∑ j, ι (b j) * ϖ₂ ^ (j : ℕ) = 0 := by
      have hι0 : ι ϖ₁ ≠ 0 := fun h => hϖ₁.ne_zero (hι (by rw [h, map_zero]))
      apply mul_left_cancel₀ hι0
      rw [mul_zero, Finset.mul_sum, ← ha]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [hb j, map_mul]; ring
    obtain ⟨c, hc⟩ := ih b hb0 j
    exact ⟨c, by rw [hb j, hc, pow_succ]; ring⟩

theorem forall_eq_zero_of_sum_mul_pow_eq_zero
    (ι : A₁ →+* A₂) (hι : Function.Injective ι) (ϖ₁ : A₁) (hϖ₁ : Irreducible ϖ₁) (ϖ₂ : A₂) (hϖ₂ : Irreducible ϖ₂)
    (e : ℕ) (u : A₂ˣ) (he : ι ϖ₁ = (u : A₂) * ϖ₂ ^ e)
    (a : Fin e → A₁) (ha : ∑ j, ι (a j) * ϖ₂ ^ (j : ℕ) = 0) : ∀ j, a j = 0 := by
  intro j
  by_contra hj
  obtain ⟨m, v, hm⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hj hϖ₁
  obtain ⟨c, hc⟩ := forall_pow_dvd_of_sum_eq_zero ι hι ϖ₁ hϖ₁ ϖ₂ hϖ₂ e u he (m + 1) a ha j

  apply hϖ₁.not_isUnit
  have h1 : (v : A₁) * ϖ₁ ^ m = ϖ₁ ^ m * (ϖ₁ * c) := by rw [← hm, hc, pow_succ]; ring
  have h2 : (v : A₁) = ϖ₁ * c := by
    rw [mul_comm] at h1
    exact mul_left_cancel₀ (pow_ne_zero _ hϖ₁.ne_zero) h1
  exact isUnit_of_mul_isUnit_left (h2 ▸ Units.isUnit v)

end L1BhEis

set_option autoImplicit false

open IsLocalRing

namespace L1BhEis

theorem exists_coords_of_finite
    {A₁ A₂ : Type*} [CommRing A₁] [IsDomain A₁] [IsDiscreteValuationRing A₁]
    [CommRing A₂] [IsDomain A₂] [IsDiscreteValuationRing A₂] [Algebra A₁ A₂] [Module.Finite A₁ A₂]
    (ϖ₁ : A₁) (hϖ₁ : Irreducible ϖ₁) (ϖ₂ : A₂)
    (e : ℕ) (u : A₂ˣ) (he : algebraMap A₁ A₂ ϖ₁ = (u : A₂) * ϖ₂ ^ e)
    (hres : ∀ a : A₂, ∃ c : A₁, ϖ₂ ∣ a - algebraMap A₁ A₂ c) :
    ∀ a : A₂, ∃ c : Fin e → A₁, a = ∑ j, algebraMap A₁ A₂ (c j) * ϖ₂ ^ (j : ℕ) := by
  classical
  set M : Submodule A₁ A₂ := Submodule.span A₁ (Set.range fun j : Fin e => ϖ₂ ^ (j : ℕ)) with hM

  have step : ∀ k : ℕ, k ≤ e → ∀ a : A₂, ∃ m ∈ M, ∃ a' : A₂, a = m + ϖ₂ ^ k * a' := by
    intro k
    induction k with
    | zero => intro _ a; exact ⟨0, M.zero_mem, a, by rw [pow_zero, one_mul, zero_add]⟩
    | succ k ih =>
      intro hk a
      obtain ⟨m, hm, a', ha⟩ := ih (Nat.le_of_succ_le hk) a
      obtain ⟨c, b, hb⟩ := hres a'

      have ha' : a' = algebraMap A₁ A₂ c + ϖ₂ * b := by linear_combination hb
      refine ⟨m + algebraMap A₁ A₂ c * ϖ₂ ^ k, M.add_mem hm ?_, b, ?_⟩
      · have hk' : k < e := Nat.lt_of_succ_le hk
        have : algebraMap A₁ A₂ c * ϖ₂ ^ k = c • (ϖ₂ ^ ((⟨k, hk'⟩ : Fin e) : ℕ)) := by
          rw [Algebra.smul_def]
        rw [this]
        exact M.smul_mem c (Submodule.subset_span ⟨⟨k, hk'⟩, rfl⟩)
      · rw [ha, ha', pow_succ]; ring

  have hle : (⊤ : Submodule A₁ A₂) ≤ M ⊔ (Ideal.span {ϖ₁} : Ideal A₁) • (⊤ : Submodule A₁ A₂) := by
    intro a _
    obtain ⟨m, hm, a', ha⟩ := step e le_rfl a
    rw [ha]
    refine Submodule.add_mem_sup hm ?_
    have hrew : ϖ₂ ^ e * a' = ϖ₁ • (((u⁻¹ : A₂ˣ) : A₂) * a') := by
      rw [Algebra.smul_def, he]
      calc ϖ₂ ^ e * a' = ((u : A₂) * ((u⁻¹ : A₂ˣ) : A₂)) * ϖ₂ ^ e * a' := by rw [Units.mul_inv, one_mul]
        _ = (u : A₂) * ϖ₂ ^ e * (((u⁻¹ : A₂ˣ) : A₂) * a') := by ring
    rw [hrew]
    exact Submodule.smul_mem_smul (Ideal.mem_span_singleton_self ϖ₁) Submodule.mem_top

  have hjac : (Ideal.span {ϖ₁} : Ideal A₁) ≤ (⊥ : Ideal A₁).jacobson := by
    rw [IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top, Ideal.span_le]
    intro x hx
    rw [Set.mem_singleton_iff.mp hx]
    exact (IsLocalRing.mem_maximalIdeal _).mpr hϖ₁.not_isUnit
  have htop : (⊤ : Submodule A₁ A₂) ≤ M :=
    Submodule.le_of_le_smul_of_le_jacobson_bot Module.Finite.fg_top hjac hle
  intro a
  have ha : a ∈ M := htop Submodule.mem_top
  rw [hM, Submodule.mem_span_range_iff_exists_fun] at ha
  obtain ⟨c, hc⟩ := ha
  refine ⟨c, ?_⟩
  rw [← hc]
  exact Finset.sum_congr rfl fun j _ => Algebra.smul_def _ _

end L1BhEis

set_option autoImplicit false

open IsLocalRing

namespace L1BhEis

set_option maxHeartbeats 6400000 in
set_option synthInstance.maxHeartbeats 800000 in
theorem exists_eisenstein {k₀ L : Type} [Field k₀] [Field L] [Algebra k₀ L] [CharZero L]
    (A : ValuationSubring L) (K₁ K₂ : IntermediateField k₀ L) (hK : K₁ ≤ K₂)
    (hKfin₂ : FiniteDimensional k₀ ↥K₂)
    (A₁ : ValuationSubring ↥K₁) (hA₁ : ∀ x : ↥K₁, x ∈ A₁ ↔ (x : L) ∈ A)
    (A₂ : ValuationSubring ↥K₂) (hA₂ : ∀ x : ↥K₂, x ∈ A₂ ↔ (x : L) ∈ A)
    (hκ₁ : Function.Surjective (fun a : ↥A₁ => IsLocalRing.residue ↥A ⟨((a : ↥K₁) : L), (hA₁ a).mp a.2⟩))
    (hdvr₁ : IsDiscreteValuationRing ↥A₁) (hdvr₂ : IsDiscreteValuationRing ↥A₂)
    (hhens₁ : HenselianLocalRing ↥A₁)
    (ϖ₂ : ↥A₂) (hϖ₂ : maximalIdeal ↥A₂ = Ideal.span {ϖ₂}) (hϖ₂0 : ϖ₂ ≠ 0)
    (hA₁₂ : ∀ a : ↥A₁, (IntermediateField.inclusion hK (a : ↥K₁)) ∈ A₂) :
    ∃ (e : ℕ), 0 < e ∧
      (∀ a : ↥A₂, ∃ c : Fin e → ↥A₁,
        a = ∑ j, (((IntermediateField.inclusion hK).toRingHom.comp A₁.subtype).codRestrict A₂ hA₁₂) (c j) * ϖ₂ ^ (j : ℕ)) ∧
      (LinearIndependent ↥K₁ (fun j : Fin e => (((ϖ₂ ^ (j : ℕ) : ↥A₂) : ↥K₂) : L))) := by
  classical
  haveI := hdvr₁
  haveI := hdvr₂
  haveI := hhens₁
  set ι₁₂ : ↥A₁ →+* ↥A₂ := ((IntermediateField.inclusion hK).toRingHom.comp A₁.subtype).codRestrict A₂ hA₁₂ with hιdef
  have hι : ∀ a : ↥A₁, (((ι₁₂ a : ↥A₂) : ↥K₂) : L) = ((a : ↥K₁) : L) := fun a => rfl
  have hιinj : Function.Injective ι₁₂ := by
    intro a b h
    have := congrArg (fun z : ↥A₂ => ((z : ↥K₂) : L)) h
    exact Subtype.ext (Subtype.ext this)

  letI algK : Algebra ↥K₁ ↥K₂ := (IntermediateField.inclusion hK).toRingHom.toAlgebra
  haveI : IsScalarTower k₀ ↥K₁ ↥K₂ := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI : Module.Finite k₀ ↥K₂ := hKfin₂
  haveI : Module.Finite ↥K₁ ↥K₂ := Module.Finite.of_restrictScalars_finite k₀ ↥K₁ ↥K₂
  haveI : CharZero ↥K₁ := (algebraMap ↥K₁ L).charZero
  haveI : PerfectField ↥K₁ := PerfectField.ofCharZero
  haveI : Algebra.IsAlgebraic ↥K₁ ↥K₂ := Algebra.IsAlgebraic.of_finite ↥K₁ ↥K₂
  haveI : Algebra.IsSeparable ↥K₁ ↥K₂ := Algebra.IsAlgebraic.isSeparable_of_perfectField
  letI algAK : Algebra ↥A₁ ↥K₂ := ((algebraMap ↥K₁ ↥K₂).comp A₁.subtype).toAlgebra
  haveI : IsScalarTower ↥A₁ ↥K₁ ↥K₂ := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have hO' : ∀ x : ↥K₁, algebraMap ↥K₁ ↥K₂ x ∈ A₂ ↔ x ∈ A₁ := by
    intro x; rw [hA₂, hA₁]; rfl
  obtain ⟨hIC, hfinIC, -⟩ :=
    ValuationSubring.toSubring_eq_integralClosure_and_finite_and_isDiscreteValuationRing_of_henselian A₁ A₂ hO'

  letI algA : Algebra ↥A₁ ↥A₂ := ι₁₂.toAlgebra
  have hcarrier : ∀ x : ↥K₂, x ∈ A₂ ↔ x ∈ integralClosure ↥A₁ ↥K₂ := by
    intro x
    have := congrArg (fun S : Subring ↥K₂ => x ∈ S) hIC
    exact Iff.of_eq this
  let E : ↥(integralClosure ↥A₁ ↥K₂) →ₗ[↥A₁] ↥A₂ :=
    { toFun := fun x => ⟨(x : ↥K₂), (hcarrier _).mpr x.2⟩
      map_add' := fun x y => Subtype.ext rfl
      map_smul' := fun a x => Subtype.ext (by
        show ((a • x : ↥(integralClosure ↥A₁ ↥K₂)) : ↥K₂) = ((a • (⟨(x : ↥K₂), (hcarrier _).mpr x.2⟩ : ↥A₂) : ↥A₂) : ↥K₂)
        rw [Algebra.smul_def, Algebra.smul_def, Subalgebra.coe_mul]
        rfl) }
  have hEsurj : Function.Surjective E := fun y => ⟨⟨(y : ↥K₂), (hcarrier _).mp y.2⟩, Subtype.ext rfl⟩
  haveI : Module.Finite ↥A₁ ↥A₂ := Module.Finite.of_surjective E hEsurj

  obtain ⟨ϖ₁, hϖ₁⟩ := IsDiscreteValuationRing.exists_irreducible ↥A₁
  have hϖ₂irr : Irreducible ϖ₂ := (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ₂).mpr hϖ₂

  let Λ : ↥A₂ →+* L := (algebraMap ↥K₂ L).comp A₂.subtype
  have hΛ : ∀ z : ↥A₂, Λ z = ((z : ↥K₂) : L) := fun z => rfl
  have hΛinj : Function.Injective Λ := fun a b h => Subtype.ext (Subtype.ext h)
  have hΛι : ∀ a : ↥A₁, Λ (ι₁₂ a) = ((a : ↥K₁) : L) := fun a => rfl

  have hunitA₂ : ∀ z : ↥A₂, IsUnit z → IsUnit (⟨((z : ↥K₂) : L), (hA₂ _).mp z.2⟩ : ↥A) := by
    intro z hz
    obtain ⟨w, hw⟩ := hz.exists_right_inv
    refine IsUnit.of_mul_eq_one (b := ⟨((w : ↥K₂) : L), (hA₂ _).mp w.2⟩) (Subtype.ext ?_)
    show ((z : ↥K₂) : L) * ((w : ↥K₂) : L) = 1
    have := congrArg Λ hw
    rwa [map_mul, map_one] at this
  have hιϖ₁0 : ι₁₂ ϖ₁ ≠ 0 := fun h => hϖ₁.ne_zero (hιinj (by rw [h, map_zero]))
  have hιϖ₁nu : ¬ IsUnit (ι₁₂ ϖ₁) := by
    intro hu
    apply hϖ₁.not_isUnit
    obtain ⟨w, hw⟩ := hu.exists_right_inv

    have hwL : ((w : ↥K₂) : L) = (((ϖ₁ : ↥A₁) : ↥K₁) : L)⁻¹ := by
      have := congrArg Λ hw
      rw [map_mul, map_one, hΛι] at this
      exact (eq_inv_of_mul_eq_one_right this)
    have hϖ₁K0 : ((ϖ₁ : ↥A₁) : ↥K₁) ≠ 0 := fun h => hϖ₁.ne_zero (Subtype.ext h)
    have hinvA₁ : ((ϖ₁ : ↥A₁) : ↥K₁)⁻¹ ∈ A₁ := by
      rw [hA₁]
      have : ((((ϖ₁ : ↥A₁) : ↥K₁)⁻¹ : ↥K₁) : L) = ((w : ↥K₂) : L) := by rw [hwL]; push_cast; rfl
      rw [this]; exact (hA₂ _).mp w.2
    exact IsUnit.of_mul_eq_one (b := ⟨_, hinvA₁⟩) (Subtype.ext (mul_inv_cancel₀ hϖ₁K0))
  obtain ⟨e, u, he⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hιϖ₁0 hϖ₂irr
  have he0 : 0 < e := by
    rcases Nat.eq_zero_or_pos e with h | h
    · exfalso; apply hιϖ₁nu; rw [he, h, pow_zero, mul_one]; exact Units.isUnit u
    · exact h

  have hres : ∀ a : ↥A₂, ∃ c : ↥A₁, ϖ₂ ∣ a - algebraMap ↥A₁ ↥A₂ c := by
    intro a
    obtain ⟨c, hc⟩ := hκ₁ (IsLocalRing.residue ↥A ⟨((a : ↥K₂) : L), (hA₂ _).mp a.2⟩)
    refine ⟨c, ?_⟩
    have hd : ¬ IsUnit (a - ι₁₂ c) := by
      intro hu
      have h1 := hunitA₂ _ hu
      have h2 : (⟨(((a - ι₁₂ c : ↥A₂) : ↥K₂) : L), (hA₂ _).mp (a - ι₁₂ c).2⟩ : ↥A) =
          ⟨((a : ↥K₂) : L), (hA₂ _).mp a.2⟩ - ⟨((c : ↥K₁) : L), (hA₁ c).mp c.2⟩ := by
        apply Subtype.ext
        show Λ (a - ι₁₂ c) = Λ a - ((c : ↥K₁) : L)
        rw [map_sub, hΛι]
      rw [h2] at h1
      have h3 : IsLocalRing.residue ↥A (⟨((a : ↥K₂) : L), (hA₂ _).mp a.2⟩ - ⟨((c : ↥K₁) : L), (hA₁ c).mp c.2⟩) = 0 := by
        rw [map_sub, sub_eq_zero]; exact hc.symm
      exact ((IsLocalRing.residue_ne_zero_iff_isUnit _).mpr h1) h3
    exact dvd_of_not_isUnit hϖ₂irr hd
  refine ⟨e, he0, ?_, ?_⟩
  ·
    exact exists_coords_of_finite ϖ₁ hϖ₁ ϖ₂ e u he hres
  ·
    rw [Fintype.linearIndependent_iff]
    intro g hg

    let dj : Fin e → ↥K₁ := fun j => if g j ∈ A₁ then 1 else (g j)⁻¹
    have hdjA : ∀ j, dj j ∈ A₁ := by
      intro j; by_cases h : g j ∈ A₁
      · simp only [dj, h, if_true]; exact one_mem _
      · simp only [dj, h, if_false]; exact (A₁.mem_or_inv_mem _).resolve_left h
    have hdj0 : ∀ j, dj j ≠ 0 := by
      intro j; by_cases h : g j ∈ A₁
      · simp only [dj, h, if_true]; exact one_ne_zero
      · simp only [dj, h, if_false]
        exact inv_ne_zero (fun h0 => h (by rw [h0]; exact A₁.zero_mem))
    have hdjg : ∀ j, dj j * g j ∈ A₁ := by
      intro j; by_cases h : g j ∈ A₁
      · simp [dj, h]
      · simp only [dj, h, if_false]
        rw [inv_mul_cancel₀ (fun h0 => h (by rw [h0]; exact A₁.zero_mem))]; exact one_mem _
    set d : ↥K₁ := ∏ j, dj j with hd
    have hd0 : d ≠ 0 := Finset.prod_ne_zero_iff.mpr fun j _ => hdj0 j
    have hdg : ∀ j, d * g j ∈ A₁ := by
      intro j
      rw [hd, ← Finset.prod_erase_mul _ _ (Finset.mem_univ j), mul_assoc]
      exact mul_mem (prod_mem fun i _ => hdjA i) (hdjg j)
    let a : Fin e → ↥A₁ := fun j => ⟨d * g j, hdg j⟩
    have hsum : ∑ j, ι₁₂ (a j) * ϖ₂ ^ (j : ℕ) = 0 := by
      apply hΛinj
      rw [map_sum, map_zero]
      have : ∑ j, Λ (ι₁₂ (a j) * ϖ₂ ^ (j : ℕ)) = (d : L) * ∑ j, g j • (((ϖ₂ ^ (j : ℕ) : ↥A₂) : ↥K₂) : L) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        have ha : (((a j : ↥A₁) : ↥K₁) : L) = ((d : ↥K₁) : L) * ((g j : ↥K₁) : L) := by
          show (((d * g j : ↥K₁)) : L) = _
          push_cast
          rfl
        rw [map_mul, hΛι, ha, Algebra.smul_def, IntermediateField.algebraMap_apply, hΛ]
        push_cast
        ring
      rw [this, hg, mul_zero]
    have hzero := forall_eq_zero_of_sum_mul_pow_eq_zero ι₁₂ hιinj ϖ₁ hϖ₁ ϖ₂ hϖ₂irr e u he a hsum
    intro j
    have : d * g j = 0 := congrArg Subtype.val (hzero j)
    exact (mul_eq_zero.mp this).resolve_left hd0

end L1BhEis

set_option autoImplicit false

open IsLocalRing

namespace BCb

theorem uniqueFactorizationMonoid_of_span_pair
    {S : Type*} [CommRing S] [IsDomain S] [IsLocalRing S] [IsNoetherianRing S]
    (t p : S) (hp : Prime p) (hm : maximalIdeal S = Ideal.span {t, p}) (hne : Ideal.span {p} ≠ maximalIdeal S) :
    IsRegularLocalRing S ∧ ringKrullDim S = 2 ∧ UniqueFactorizationMonoid S := by
  classical
  have hfin : (maximalIdeal S).spanFinrank ≤ 2 := by
    rw [hm]
    refine (Submodule.spanFinrank_span_le_ncard_of_finite (Set.toFinite _)).trans ?_
    exact (Set.ncard_insert_le t {p}).trans (by rw [Set.ncard_singleton])
  have hprime : (Ideal.span {p} : Ideal S).IsPrime := (Ideal.span_singleton_prime hp.ne_zero).mpr hp
  have hbot : (⊥ : Ideal S) < Ideal.span {p} :=
    bot_lt_iff_ne_bot.mpr (by rw [Ne, Ideal.span_singleton_eq_bot]; exact hp.ne_zero)
  have hlt : Ideal.span {p} < maximalIdeal S := by
    refine lt_of_le_of_ne ?_ hne
    rw [hm]; exact Ideal.span_mono (by simp)
  have hdim2 : (2 : WithBot ℕ∞) ≤ ringKrullDim S := by
    have : ((2 : ℕ) : WithBot ℕ∞) ≤ Order.krullDim (PrimeSpectrum S) := by
      rw [Order.le_krullDim_iff]
      let P0 : PrimeSpectrum S := ⟨⊥, Ideal.bot_prime⟩
      let P1 : PrimeSpectrum S := ⟨Ideal.span {p}, hprime⟩
      let P2 : PrimeSpectrum S := ⟨maximalIdeal S, (maximalIdeal.isMaximal S).isPrime⟩
      let l0 : LTSeries (PrimeSpectrum S) := RelSeries.singleton _ P0
      have r1 : l0.last < P1 := (PrimeSpectrum.asIdeal_lt_asIdeal (x := P0) (y := P1)).mp hbot
      let l1 : LTSeries (PrimeSpectrum S) := l0.snoc P1 r1
      have r2 : l1.last < P2 := by
        rw [RelSeries.last_snoc]; exact (PrimeSpectrum.asIdeal_lt_asIdeal (x := P1) (y := P2)).mp hlt
      exact ⟨l1.snoc P2 r2, by simp [l1, l0]⟩
    exact_mod_cast this
  have hdimle : ringKrullDim S ≤ 2 := by
    refine (ringKrullDim_le_spanFinrank_maximalIdeal S).trans ?_
    exact_mod_cast hfin
  have hfin' : ((maximalIdeal S).spanFinrank : WithBot ℕ∞) ≤ 2 := by exact_mod_cast hfin
  haveI hreg : IsRegularLocalRing S := IsRegularLocalRing.of_spanFinrank_maximalIdeal_le S (hfin'.trans hdim2)
  exact ⟨hreg, le_antisymm hdimle hdim2, IsRegularLocalRing.uniqueFactorizationMonoid_of_ringKrullDim_le_two S hdimle⟩

theorem maximalIdeal_eq_span_pair_of_section
    {S : Type*} [CommRing S] [IsLocalRing S]
    {A' : Type*} [CommRing A'] [IsLocalRing A']
    (c : A' →+* S) (χ₀ : S →+* A') (hsec : ∀ a : A', χ₀ (c a) = a)
    (t : S) (hker : RingHom.ker χ₀ = Ideal.span {t})
    (ϖ : A') (hmA : maximalIdeal A' = Ideal.span {ϖ})
    (hmS : ∀ s : S, s ∈ maximalIdeal S ↔ χ₀ s ∈ maximalIdeal A') :
    maximalIdeal S = Ideal.span {t, c ϖ} := by
  apply le_antisymm
  · intro s hs
    rw [hmS, hmA, Ideal.mem_span_singleton'] at hs
    obtain ⟨a, ha⟩ := hs
    have h1 : s - c (a * ϖ) ∈ RingHom.ker χ₀ := by
      rw [RingHom.mem_ker, map_sub, hsec, ha, sub_self]
    rw [hker, Ideal.mem_span_singleton'] at h1
    obtain ⟨b, hb⟩ := h1
    have : s = b * t + c a * c ϖ := by rw [← map_mul, hb]; ring
    rw [this]
    exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ (Ideal.subset_span (by simp)))
      (Ideal.mul_mem_left _ _ (Ideal.subset_span (by simp)))
  · rw [Ideal.span_le]
    intro x hx
    rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with h | h
    · rw [h, SetLike.mem_coe, hmS]
      have : χ₀ t = 0 := (RingHom.mem_ker).mp (hker ▸ Ideal.mem_span_singleton_self t)
      rw [this]; exact (maximalIdeal A').zero_mem
    · rw [h, SetLike.mem_coe, hmS, hsec, hmA]; exact Ideal.mem_span_singleton_self ϖ

end BCb

namespace BCb

theorem prime_of_reduction_of_descent {F : Type*} [Field F] (S₁ S₂ : Subring F) (hmono : S₁ ≤ S₂)
    (ϖ₁ : ↥S₁) (hϖ₁ : Prime ϖ₁) (π : ↥S₂) (hπ0 : π ≠ 0) (hπnu : ¬ IsUnit π)
    (hdiv : π ∣ ⟨(ϖ₁ : F), hmono ϖ₁.2⟩)
    (hred : ∀ x : ↥S₂, ∃ s : ↥S₁, π ∣ x - ⟨(s : F), hmono s.2⟩)
    (hdesc : ∀ s : ↥S₁, π ∣ ⟨(s : F), hmono s.2⟩ → ϖ₁ ∣ s) :
    Prime π := by
  let ι : ↥S₁ →+* ↥S₂ := Subring.inclusion hmono
  have hι : ∀ s : ↥S₁, ι s = ⟨(s : F), hmono s.2⟩ := fun s => rfl
  refine ⟨hπ0, hπnu, fun x y hxy => ?_⟩
  obtain ⟨s, hs⟩ := hred x
  obtain ⟨t, ht⟩ := hred y
  rw [← hι] at hs ht

  have hst : π ∣ ι (s * t) := by
    have : ι (s * t) = x * y - (x - ι s) * y - ι s * (y - ι t) := by rw [map_mul]; ring
    rw [this]
    exact dvd_sub (dvd_sub hxy (hs.mul_right _)) (ht.mul_left _)

  rcases hϖ₁.dvd_or_dvd (hdesc (s * t) (by rw [← hι]; exact hst)) with h | h
  · left
    have : π ∣ ι s := (hdiv.trans (by rw [← hι]; exact map_dvd ι h))
    have hx : x = (x - ι s) + ι s := by ring
    rw [hx]; exact dvd_add hs this
  · right
    have : π ∣ ι t := (hdiv.trans (by rw [← hι]; exact map_dvd ι h))
    have hy : y = (y - ι t) + ι t := by ring
    rw [hy]; exact dvd_add ht this

end BCb

namespace BCb

theorem isUnit_mk_iff {F : Type*} [Field F] (O : ValuationSubring F) (x : F) (hx : x ∈ O) :
    IsUnit (⟨x, hx⟩ : ↥O) ↔ x ≠ 0 ∧ x⁻¹ ∈ O := by
  constructor
  · intro hu
    obtain ⟨u, hu⟩ := hu
    have hx0 : x ≠ 0 := fun h0 => u.ne_zero (by rw [hu]; exact Subtype.ext h0)
    refine ⟨hx0, ?_⟩
    have : ((u⁻¹ : (↥O)ˣ) : ↥O).1 = x⁻¹ := by
      apply eq_inv_of_mul_eq_one_left
      have h1 : (((u⁻¹ : (↥O)ˣ) : ↥O) * (u : ↥O)).1 = 1 := by
        rw [Units.inv_mul]; rfl
      rw [hu] at h1
      exact h1
    rw [← this]; exact ((u⁻¹ : (↥O)ˣ) : ↥O).2
  · rintro ⟨hx0, hinv⟩
    exact isUnit_iff_exists_inv.mpr ⟨⟨x⁻¹, hinv⟩, Subtype.ext (mul_inv_cancel₀ hx0)⟩

theorem mem_iff_exists_not_dvd_of_layer {F : Type*} [Field F] (S₁ S₂ : Subring F) (hmono : S₁ ≤ S₂) [IsNoetherianRing ↥S₂]
    (O : ValuationSubring F) (hS₂O : ∀ x : ↥S₂, (x : F) ∈ O)
    (ϖ₁ : ↥S₁) (π : ↥S₂) (hπ : Prime π) (hπO : (⟨(π : F), hS₂O π⟩ : ↥O) ∈ maximalIdeal ↥O)
    (hdiv : π ∣ ⟨(ϖ₁ : F), hmono ϖ₁.2⟩)
    (hred : ∀ x : ↥S₂, ∃ s : ↥S₁, π ∣ x - ⟨(s : F), hmono s.2⟩)
    (hunit₁ : ∀ s : ↥S₁, ¬ ϖ₁ ∣ s → (s : F)⁻¹ ∈ O)
    (f : F) (hfrac : ∃ g h : ↥S₂, (h : F) ≠ 0 ∧ f * (h : F) = (g : F)) :
    f ∈ O ↔ ∃ g h : ↥S₂, ¬ π ∣ h ∧ f * (h : F) = (g : F) := by
  classical
  let ι : ↥S₁ →+* ↥S₂ := Subring.inclusion hmono
  have hι : ∀ s : ↥S₁, ι s = ⟨(s : F), hmono s.2⟩ := fun s => rfl
  let j : ↥S₂ →+* ↥O := (S₂.subtype).codRestrict O (fun x => hS₂O x)
  have hj : ∀ x : ↥S₂, j x = ⟨(x : F), hS₂O x⟩ := fun x => rfl

  have key : ∀ (x : ↥S₂) (s : ↥S₁), π ∣ x - ι s → ¬ ϖ₁ ∣ s → IsUnit (j x) := by
    intro x s hxs hs
    obtain ⟨w, hw⟩ := hxs
    have hs0 : (s : F) ≠ 0 := by
      intro h0; apply hs
      have : s = 0 := Subtype.ext h0
      rw [this]; exact dvd_zero _
    have hsu : IsUnit (j (ι s)) := by
      rw [hj]; exact (isUnit_mk_iff O _ _).mpr ⟨hs0, hunit₁ s hs⟩
    have hdecomp : j x = j (ι s) + j π * j w := by
      rw [← map_mul, ← map_add]; congr 1; rw [← hw]; ring
    by_contra hxu
    have hxm : j x ∈ maximalIdeal ↥O := (IsLocalRing.mem_maximalIdeal _).mpr hxu
    have hpm : j π * j w ∈ maximalIdeal ↥O := Ideal.mul_mem_right _ _ (by rw [hj]; exact hπO)
    have : j (ι s) ∈ maximalIdeal ↥O := by
      have := (maximalIdeal ↥O).sub_mem hxm hpm
      rwa [hdecomp, add_sub_cancel_right] at this
    exact (IsLocalRing.mem_maximalIdeal _).mp this hsu

  have hunit₂ : ∀ h : ↥S₂, ¬ π ∣ h → (h : F) ≠ 0 ∧ (h : F)⁻¹ ∈ O := by
    intro h hph
    obtain ⟨s, hs⟩ := hred h
    have hϖs : ¬ ϖ₁ ∣ s := by
      intro hd
      apply hph
      have h1 : π ∣ ι s := hdiv.trans (by rw [← hι]; exact map_dvd ι hd)
      have : h = (h - ι s) + ι s := by ring
      rw [this]; exact dvd_add hs h1
    exact (isUnit_mk_iff O _ _).mp (key h s hs hϖs)

  have hmult : ∀ x : ↥S₂, j x ∈ maximalIdeal ↥O → π ∣ x := by
    intro x hx
    obtain ⟨s, hs⟩ := hred x
    by_cases hϖs : ϖ₁ ∣ s
    · have h1 : π ∣ ι s := hdiv.trans (by rw [← hι]; exact map_dvd ι hϖs)
      have : x = (x - ι s) + ι s := by ring
      rw [this]; exact dvd_add hs h1
    · exact absurd (key x s hs hϖs) ((IsLocalRing.mem_maximalIdeal _).mp hx)
  constructor
  · intro hfO
    obtain ⟨g₀, h₀, hh₀, hfh⟩ := hfrac
    have hh₀' : h₀ ≠ 0 := fun h0 => hh₀ (by rw [h0]; rfl)
    by_cases hg0 : g₀ = 0
    · refine ⟨0, 1, fun hd => hπ.not_unit (isUnit_of_dvd_one hd), ?_⟩
      have : f = 0 := by
        have := hfh; rw [hg0] at this
        exact (mul_eq_zero.mp (by simpa using this)).resolve_right hh₀
      simp [this]
    obtain ⟨b, h', hph', hh'⟩ := WfDvdMonoid.max_power_factor hh₀' hπ.irreducible
    obtain ⟨a, g', hpg', hg'⟩ := WfDvdMonoid.max_power_factor hg0 hπ.irreducible
    have hp0F : ((π : ↥S₂) : F) ≠ 0 := fun h0 => hπ.ne_zero (Subtype.ext (by simpa using h0))
    have keyF : f * ((π : ↥S₂) : F) ^ b * (h' : F) = ((π : ↥S₂) : F) ^ a * (g' : F) := by
      have := hfh
      rw [hh', hg'] at this
      simpa [mul_assoc] using this
    rcases le_or_gt b a with hba | hab
    · refine ⟨π ^ (a - b) * g', h', hph', ?_⟩
      have hpb : ((π : ↥S₂) : F) ^ b ≠ 0 := pow_ne_zero _ hp0F
      apply mul_left_cancel₀ hpb
      push_cast
      calc ((π : ↥S₂) : F) ^ b * (f * (h' : F)) = f * ((π : ↥S₂) : F) ^ b * (h' : F) := by ring
        _ = ((π : ↥S₂) : F) ^ a * (g' : F) := keyF
        _ = ((π : ↥S₂) : F) ^ b * (((π : ↥S₂) : F) ^ (a - b) * (g' : F)) := by
          rw [← mul_assoc, ← pow_add, Nat.add_sub_cancel' hba]
    · exfalso
      apply hpg'
      apply hmult

      have hpa : ((π : ↥S₂) : F) ^ a ≠ 0 := pow_ne_zero _ hp0F
      have hg'eq : (g' : F) = f * ((π : ↥S₂) : F) ^ (b - a) * (h' : F) := by
        apply mul_left_cancel₀ hpa
        calc ((π : ↥S₂) : F) ^ a * (g' : F) = f * ((π : ↥S₂) : F) ^ b * (h' : F) := keyF.symm
          _ = ((π : ↥S₂) : F) ^ a * (f * ((π : ↥S₂) : F) ^ (b - a) * (h' : F)) := by
            have hb : ((π : ↥S₂) : F) ^ b = ((π : ↥S₂) : F) ^ a * ((π : ↥S₂) : F) ^ (b - a) := by
              rw [← pow_add, Nat.add_sub_cancel' hab.le]
            rw [hb]; ring
      obtain ⟨n, hn⟩ : ∃ n, b - a = n + 1 := ⟨b - a - 1, by omega⟩
      have : j g' = ⟨f, hfO⟩ * (j π) ^ n * j h' * j π := by
        apply Subtype.ext
        show (g' : F) = f * ((π : ↥S₂) : F) ^ n * (h' : F) * ((π : ↥S₂) : F)
        rw [hg'eq, hn, pow_succ]; ring
      rw [this]
      exact Ideal.mul_mem_left _ _ (by rw [hj]; exact hπO)
  · rintro ⟨g, h, hph, hfh⟩
    obtain ⟨hh0, hinv⟩ := hunit₂ h hph
    have : f = (g : F) * (h : F)⁻¹ := by rw [← hfh, mul_inv_cancel_right₀ hh0]
    rw [this]
    exact O.mul_mem _ _ (hS₂O g) hinv

end BCb

namespace BCb

theorem exists_frac_of_mem_adjoin_sup {k₀ L F : Type*} [Field k₀] [Field L] [Field F] [Algebra k₀ L] [Algebra L F]
    [Algebra k₀ F] [IsScalarTower k₀ L F]
    (K₂ : IntermediateField k₀ L) (A₂ : ValuationSubring ↥K₂) (F₀ : IntermediateField k₀ F) (S₂ : Subring F)
    (hcst : ∀ a : ↥A₂, algebraMap L F ((a : ↥K₂) : L) ∈ S₂)
    (hF₀ : ∀ f : F, f ∈ F₀ → ∃ g h : ↥S₂, (h : F) ≠ 0 ∧ f * (h : F) = (g : F)) :
    ∀ f : F, f ∈ IntermediateField.adjoin k₀ (⇑(algebraMap L F) '' (↑K₂ : Set L)) ⊔ F₀ →
      ∃ g h : ↥S₂, (h : F) ≠ 0 ∧ f * (h : F) = (g : F) := by
  classical

  let T : IntermediateField k₀ F :=
    { carrier := {f : F | ∃ g h : ↥S₂, (h : F) ≠ 0 ∧ f * (h : F) = (g : F)}
      mul_mem' := by
        rintro x y ⟨g, h, hh, hx⟩ ⟨g', h', hh', hy⟩
        exact ⟨g * g', h * h', by push_cast; exact mul_ne_zero hh hh', by push_cast; rw [← hx, ← hy]; ring⟩
      one_mem' := ⟨1, 1, by simp, by simp⟩
      add_mem' := by
        rintro x y ⟨g, h, hh, hx⟩ ⟨g', h', hh', hy⟩
        exact ⟨g * h' + g' * h, h * h', by push_cast; exact mul_ne_zero hh hh', by push_cast; rw [← hx, ← hy]; ring⟩
      zero_mem' := ⟨0, 1, by simp, by simp⟩
      algebraMap_mem' := by
        intro c
        have hc : algebraMap k₀ F c = algebraMap L F ((⟨algebraMap k₀ L c, K₂.algebraMap_mem c⟩ : ↥K₂) : L) := by
          rw [IsScalarTower.algebraMap_apply k₀ L F]
        rcases A₂.mem_or_inv_mem ⟨algebraMap k₀ L c, K₂.algebraMap_mem c⟩ with h | h
        · exact ⟨⟨_, hcst ⟨_, h⟩⟩, 1, by simp, by rw [hc]; simp⟩
        · by_cases hc0 : algebraMap k₀ F c = 0
          · exact ⟨0, 1, by simp, by rw [hc0]; simp⟩
          refine ⟨1, ⟨_, hcst ⟨_, h⟩⟩, ?_, ?_⟩
          · show algebraMap L F (((⟨algebraMap k₀ L c, K₂.algebraMap_mem c⟩ : ↥K₂)⁻¹ : ↥K₂) : L) ≠ 0
            rw [IntermediateField.coe_inv, map_inv₀, ← hc]; exact inv_ne_zero hc0
          · show algebraMap k₀ F c * algebraMap L F (((⟨algebraMap k₀ L c, K₂.algebraMap_mem c⟩ : ↥K₂)⁻¹ : ↥K₂) : L) = 1
            rw [IntermediateField.coe_inv, map_inv₀, ← hc]; exact mul_inv_cancel₀ hc0
      inv_mem' := by
        rintro x ⟨g, h, hh, hx⟩
        by_cases hg : (g : F) = 0
        · have : x = 0 := by
            have := hx; rw [hg] at this; exact (mul_eq_zero.mp this).resolve_right hh
          exact ⟨0, 1, by simp, by rw [this]; simp⟩
        · refine ⟨h, g, hg, ?_⟩
          have hx0 : x ≠ 0 := by rintro rfl; rw [zero_mul] at hx; exact hg hx.symm
          rw [← hx, ← mul_assoc, inv_mul_cancel₀ hx0, one_mul] }
  have hT : ∀ f : F, f ∈ T ↔ ∃ g h : ↥S₂, (h : F) ≠ 0 ∧ f * (h : F) = (g : F) := fun f => Iff.rfl

  have hle : IntermediateField.adjoin k₀ (⇑(algebraMap L F) '' (↑K₂ : Set L)) ⊔ F₀ ≤ T := by
    refine sup_le (IntermediateField.adjoin_le_iff.mpr ?_) (fun f hf => (hT f).mpr (hF₀ f hf))
    rintro _ ⟨x, hx, rfl⟩
    show algebraMap L F x ∈ T
    rw [hT]
    rcases A₂.mem_or_inv_mem ⟨x, hx⟩ with h | h
    · exact ⟨⟨_, hcst ⟨_, h⟩⟩, 1, by simp, by simp⟩
    · by_cases hx0 : algebraMap L F x = 0
      · exact ⟨0, 1, by simp, by rw [hx0]; simp⟩
      refine ⟨1, ⟨_, hcst ⟨_, h⟩⟩, ?_, ?_⟩
      · show algebraMap L F (((⟨x, hx⟩ : ↥K₂)⁻¹ : ↥K₂) : L) ≠ 0
        rw [IntermediateField.coe_inv, map_inv₀]; exact inv_ne_zero hx0
      · show algebraMap L F x * algebraMap L F (((⟨x, hx⟩ : ↥K₂)⁻¹ : ↥K₂) : L) = 1
        rw [IntermediateField.coe_inv, map_inv₀]; exact mul_inv_cancel₀ hx0
  intro f hf
  exact (hT f).mp (hle hf)

theorem closure_le_adjoin_sup {k₀ L F : Type*} [Field k₀] [Field L] [Field F] [Algebra k₀ L] [Algebra L F]
    [Algebra k₀ F] [IsScalarTower k₀ L F]
    (K₁ K₂ : IntermediateField k₀ L) (hK : K₁ ≤ K₂) (A₂ : ValuationSubring ↥K₂) (F₀ : IntermediateField k₀ F) (S₁ : Subring F)
    (hS₁F₁ : ∀ f : F, f ∈ S₁ → f ∈ IntermediateField.adjoin k₀ (⇑(algebraMap L F) '' (↑K₁ : Set L)) ⊔ F₀) :
    ∀ f : F, f ∈ Subring.closure ((S₁ : Set F) ∪ ((fun a : ↥A₂ => algebraMap L F ((a : ↥K₂) : L)) '' Set.univ)) →
      f ∈ IntermediateField.adjoin k₀ (⇑(algebraMap L F) '' (↑K₂ : Set L)) ⊔ F₀ := by
  intro f hf
  have h12 : IntermediateField.adjoin k₀ (⇑(algebraMap L F) '' (↑K₁ : Set L)) ⊔ F₀ ≤
      IntermediateField.adjoin k₀ (⇑(algebraMap L F) '' (↑K₂ : Set L)) ⊔ F₀ :=
    sup_le_sup_right (IntermediateField.adjoin.mono _ _ _ (Set.image_mono hK)) _
  have hle : Subring.closure ((S₁ : Set F) ∪ ((fun a : ↥A₂ => algebraMap L F ((a : ↥K₂) : L)) '' Set.univ)) ≤
      (IntermediateField.adjoin k₀ (⇑(algebraMap L F) '' (↑K₂ : Set L)) ⊔ F₀).toSubring := by
    refine Subring.closure_le.mpr (Set.union_subset (fun g hg => h12 (hS₁F₁ g hg)) ?_)
    rintro _ ⟨a, -, rfl⟩
    exact (le_sup_left : IntermediateField.adjoin k₀ (⇑(algebraMap L F) '' (↑K₂ : Set L)) ≤ _)
      (IntermediateField.subset_adjoin k₀ _ ⟨(a : ↥K₂), (a : ↥K₂).2, rfl⟩)
  exact hle hf

end BCb

set_option autoImplicit false
open AlgebraicCurve IsLocalRing Polynomial

namespace KFBC

theorem X_ne_C_of_linearDisjoint
    {k₀ L F : Type} [Field k₀] [Field L] [Field F] [Algebra k₀ L] [Algebra L F]
    (A : ValuationSubring L) (K₁ K₂ : IntermediateField k₀ L)
    (A₁ : ValuationSubring ↥K₁) (hA₁ : ∀ x : ↥K₁, x ∈ A₁ ↔ (x : L) ∈ A)
    (A₂ : ValuationSubring ↥K₂) (hA₂ : ∀ x : ↥K₂, x ∈ A₂ ↔ (x : L) ∈ A)
    (S₁ : Subring F) (φ₁ : Polynomial ↥A₁ →+* ↥S₁)
    (hφC : ∀ a : ↥A₁, ((φ₁ (Polynomial.C a) : ↥S₁) : F) = algebraMap L F ((a : ↥K₁) : L))
    (ht : ∀ c : ↥A₁, φ₁ Polynomial.X ≠ φ₁ (Polynomial.C c))
    (F₁ : Subfield F) (hS₁F₁ : ∀ f : F, f ∈ S₁ → f ∈ F₁)
    (hld : ∀ (m : ℕ) (c : Fin m → L) (a : Fin m → F), (∀ i, a i ∈ F₁) →
      LinearIndependent ↥K₁ c → ∑ i, algebraMap L F (c i) * a i = 0 → ∀ i, a i = 0)
    (S₂ : Subring F) (φ₂ : Polynomial ↥A₂ →+* ↥S₂)
    (hφ₂X : ((φ₂ Polynomial.X : ↥S₂) : F) = ((φ₁ Polynomial.X : ↥S₁) : F))
    (hφ₂C : ∀ a : ↥A₂, ((φ₂ (Polynomial.C a) : ↥S₂) : F) = algebraMap L F ((a : ↥K₂) : L)) :
    ∀ c : ↥A₂, φ₂ Polynomial.X ≠ φ₂ (Polynomial.C c) := by
  classical
  intro c heq
  have ht' : ((φ₁ Polynomial.X : ↥S₁) : F) = algebraMap L F ((c : ↥K₂) : L) := by
    rw [← hφ₂X, heq, hφ₂C]

  have hdep : ¬ LinearIndependent ↥K₁ ![(1 : L), ((c : ↥K₂) : L)] := by
    intro hli
    have h0 := hld 2 ![(1 : L), ((c : ↥K₂) : L)] ![((φ₁ Polynomial.X : ↥S₁) : F), -1]
      (fun i => by
        fin_cases i
        · exact hS₁F₁ _ (φ₁ Polynomial.X).2
        · exact F₁.neg_mem F₁.one_mem) hli
      (by simp [Fin.sum_univ_two, ht']) 1
    simp at h0
  obtain ⟨g, hg, i, hi⟩ := Fintype.not_linearIndependent_iff.mp hdep
  rw [Fin.sum_univ_two] at hg
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons] at hg
  set s := g 0 with hs
  set t := g 1 with htg
  have ht0 : t ≠ 0 := by
    intro ht0
    have hs0 : s = 0 := by
      have : (s : L) = 0 := by simpa [ht0, Algebra.smul_def] using hg
      exact_mod_cast this
    fin_cases i
    · exact hi hs0
    · exact hi ht0

  have hcK₁ : ((c : ↥K₂) : L) = (((-s / t : ↥K₁)) : L) := by
    have : (s : L) * 1 + (t : L) * ((c : ↥K₂) : L) = 0 := by
      simp only [Algebra.smul_def] at hg
      exact hg
    have htL : (t : L) ≠ 0 := fun h => ht0 (Subtype.ext (by simpa using h))
    rw [show (((-s / t : ↥K₁)) : L) = -(s : L) / (t : L) by push_cast; ring, eq_div_iff htL]
    linear_combination this
  set c₁ : ↥K₁ := -s / t with hc₁
  have hc₁A : c₁ ∈ A₁ := by rw [hA₁, ← hcK₁]; exact (hA₂ _).mp c.2
  apply ht ⟨c₁, hc₁A⟩
  apply Subtype.ext
  rw [hφC, ht', hcK₁]

theorem sections_and_ker
    {k₀ L F : Type} [Field k₀] [Field L] [Field F] [Algebra k₀ L] [Algebra L F]
    (A : ValuationSubring L) (K₂ : IntermediateField k₀ L)
    (A₂ : ValuationSubring ↥K₂) (hA₂ : ∀ x : ↥K₂, x ∈ A₂ ↔ (x : L) ∈ A)
    (hκ₂ : Function.Surjective (fun a : ↥A₂ => IsLocalRing.residue ↥A ⟨((a : ↥K₂) : L), (hA₂ a).mp a.2⟩))
    [IsDiscreteValuationRing ↥A₂] (hhens₂ : HenselianLocalRing ↥A₂)
    (S₂ : Subring F) [IsLocalRing ↥S₂] (φ₂ : Polynomial ↥A₂ →+* ↥S₂)
    (hφs₂ : φ₂.FormallySmooth) (hφu₂ : φ₂.FormallyUnramified) (hφf₂ : φ₂.EssFiniteType)
    (χ₂ : ↥S₂ →+* ResidueField ↥A) (hmax₂ : ∀ f : ↥S₂, f ∈ maximalIdeal ↥S₂ ↔ χ₂ f = 0)
    (hχC₂ : ∀ a : ↥A₂, χ₂ (φ₂ (Polynomial.C a)) = IsLocalRing.residue ↥A ⟨((a : ↥K₂) : L), (hA₂ a).mp a.2⟩)
    (hχt₂ : χ₂ (φ₂ Polynomial.X) = 0) :
    (∀ c : ↥A₂, IsLocalRing.residue ↥A ⟨((c : ↥K₂) : L), (hA₂ c).mp c.2⟩ = 0 →
      ∃! χ : ↥S₂ →+* ↥A₂, (∀ a : ↥A₂, χ (φ₂ (Polynomial.C a)) = a) ∧
        (∀ f : ↥S₂, IsLocalRing.residue ↥A ⟨((χ f : ↥K₂) : L), (hA₂ _).mp (χ f).2⟩ = χ₂ f) ∧
        χ (φ₂ Polynomial.X) = c) ∧
    (∀ χ : ↥S₂ →+* ↥A₂, (∀ a : ↥A₂, χ (φ₂ (Polynomial.C a)) = a) →
      (∀ f : ↥S₂, IsLocalRing.residue ↥A ⟨((χ f : ↥K₂) : L), (hA₂ _).mp (χ f).2⟩ = χ₂ f) →
      RingHom.ker χ = Ideal.span {φ₂ Polynomial.X - φ₂ (Polynomial.C (χ (φ₂ Polynomial.X)))}) := by
  classical
  haveI := hhens₂

  let ι : ↥A₂ →+* ↥A :=
    ((algebraMap ↥K₂ L).comp A₂.subtype).codRestrict A.toSubring (fun a => (hA₂ a).mp a.2)
  have hι : ∀ a : ↥A₂, ι a = ⟨((a : ↥K₂) : L), (hA₂ a).mp a.2⟩ := fun a => rfl
  have unitA : ∀ (B : ValuationSubring L) (x : ↥B), IsUnit x → (x : L) ≠ 0 → (x : L)⁻¹ ∈ B := by
    intro B x hx hx0
    obtain ⟨y, hy⟩ := hx.exists_left_inv
    have hyx : (y : L) * (x : L) = 1 := by
      have := congrArg Subtype.val hy
      simpa using this
    rw [← eq_inv_of_mul_eq_one_left hyx]; exact y.2
  haveI : IsLocalHom ι := by
    refine ⟨fun a ha => ?_⟩
    by_cases ha0 : ((a : ↥K₂) : L) = 0
    · exfalso
      have : ι a = 0 := Subtype.ext ha0
      rw [this] at ha; exact not_isUnit_zero ha
    have hinvA : ((a : ↥K₂) : L)⁻¹ ∈ A := unitA A (ι a) ha ha0
    have hinvA₂ : (a : ↥K₂)⁻¹ ∈ A₂ := by
      rw [hA₂]
      have : (((a : ↥K₂)⁻¹ : ↥K₂) : L) = ((a : ↥K₂) : L)⁻¹ := by push_cast; rfl
      rw [this]; exact hinvA
    have ha0' : (a : ↥K₂) ≠ 0 := fun h => ha0 (by rw [h]; rfl)
    exact isUnit_iff_exists_inv.mpr ⟨⟨_, hinvA₂⟩, Subtype.ext (mul_inv_cancel₀ ha0')⟩
  let e : ResidueField ↥A₂ →+* ResidueField ↥A := IsLocalRing.ResidueField.map ι
  have he_res : ∀ a : ↥A₂, e (IsLocalRing.residue ↥A₂ a) =
      IsLocalRing.residue ↥A ⟨((a : ↥K₂) : L), (hA₂ a).mp a.2⟩ := fun a =>
    IsLocalRing.ResidueField.map_residue ι a
  have hebij : Function.Bijective e := by
    refine ⟨e.injective, fun x => ?_⟩
    obtain ⟨a, ha⟩ := hκ₂ x
    exact ⟨IsLocalRing.residue ↥A₂ a, (he_res a).trans ha⟩
  let eE : ResidueField ↥A₂ ≃+* ResidueField ↥A := RingEquiv.ofBijective e hebij
  have heE : ∀ y, eE y = e y := fun _ => rfl

  let χ₀ : ↥S₂ →+* ResidueField ↥A₂ := eE.symm.toRingHom.comp χ₂
  have hχ₀ : ∀ f, χ₀ f = eE.symm (χ₂ f) := fun _ => rfl
  have hχ₀ker : RingHom.ker χ₀ = maximalIdeal ↥S₂ := by
    ext f
    rw [RingHom.mem_ker, hχ₀, map_eq_zero_iff _ eE.symm.injective, hmax₂]
  have hχ₀C : ∀ a : ↥A₂, χ₀ (φ₂ (Polynomial.C a)) = IsLocalRing.residue ↥A₂ a := by
    intro a
    rw [hχ₀, hχC₂, ← he_res, ← heE, RingEquiv.symm_apply_apply]
  have hχ₀t : χ₀ (φ₂ Polynomial.X) = 0 := by rw [hχ₀, hχt₂, map_zero]
  obtain ⟨hsec, hker⟩ :=
    HenselianLocalRing.existsUnique_section_and_ker_eq_span_of_formallySmooth_of_formallyUnramified
      φ₂ hφs₂ hφu₂ hφf₂ χ₀ hχ₀ker hχ₀C hχ₀t

  have key : ∀ (χ : ↥S₂ →+* ↥A₂) (f : ↥S₂),
      IsLocalRing.residue ↥A₂ (χ f) = χ₀ f ↔
        IsLocalRing.residue ↥A ⟨((χ f : ↥K₂) : L), (hA₂ _).mp (χ f).2⟩ = χ₂ f := by
    intro χ f
    rw [← he_res, ← heE, hχ₀]
    constructor
    · intro h; rw [h, RingEquiv.apply_symm_apply]
    · intro h; apply eE.injective; rw [h, RingEquiv.apply_symm_apply]
  have key0 : ∀ c : ↥A₂, IsLocalRing.residue ↥A ⟨((c : ↥K₂) : L), (hA₂ c).mp c.2⟩ = 0 ↔
      IsLocalRing.residue ↥A₂ c = 0 := by
    intro c
    rw [← he_res, ← heE, map_eq_zero_iff _ eE.injective]
  refine ⟨fun c hc => ?_, fun χ h1 h2 => hker χ h1 fun f => (key χ f).mpr (h2 f)⟩
  obtain ⟨χ, ⟨h1, h2, h3⟩, huniq⟩ := hsec c ((key0 c).mp hc)
  exact ⟨χ, ⟨h1, fun f => (key χ f).mp (h2 f), h3⟩,
    fun χ' ⟨h1', h2', h3'⟩ => huniq χ' ⟨h1', fun f => (key χ' f).mpr (h2' f), h3'⟩⟩

theorem essFiniteType_of_fg
    {k₀ L F : Type} [Field k₀] [Field L] [Field F] [Algebra k₀ L] [Algebra L F]
    (K₂ : IntermediateField k₀ L) (A₂ : ValuationSubring ↥K₂)
    (S₂ : Subring F) (φ₂ : Polynomial ↥A₂ →+* ↥S₂)
    (hφC₂ : ∀ a : ↥A₂, ((φ₂ (Polynomial.C a) : ↥S₂) : F) = algebraMap L F ((a : ↥K₂) : L))
    (hfg₂ : ∃ G : Finset F, ↑G ⊆ (S₂ : Set F) ∧ ∀ f ∈ S₂, ∃ g h : F,
        g ∈ Subring.closure (↑G ∪ ((fun a : ↥A₂ => algebraMap L F ((a : ↥K₂) : L)) '' Set.univ)) ∧
        h ∈ Subring.closure (↑G ∪ ((fun a : ↥A₂ => algebraMap L F ((a : ↥K₂) : L)) '' Set.univ)) ∧
        (∃ u : (↥S₂)ˣ, ((u : ↥S₂) : F) = h) ∧ f * h = g) :
    φ₂.EssFiniteType := by
  classical
  letI alg : Algebra (Polynomial ↥A₂) ↥S₂ := φ₂.toAlgebra
  obtain ⟨G, hGS, hfg⟩ := hfg₂
  show Algebra.EssFiniteType (Polynomial ↥A₂) ↥S₂
  rw [Algebra.essFiniteType_iff]
  let σ : Finset ↥S₂ := G.attach.image (fun x => ⟨x.1, hGS x.2⟩)
  refine ⟨σ, fun s => ?_⟩

  let T : Subring F := (Algebra.adjoin (Polynomial ↥A₂) (σ : Set ↥S₂)).toSubring.map S₂.subtype
  have hT : Subring.closure (↑G ∪ ((fun a : ↥A₂ => algebraMap L F ((a : ↥K₂) : L)) '' Set.univ)) ≤ T := by
    rw [Subring.closure_le]
    rintro y (hy | ⟨a, -, rfl⟩)
    · refine ⟨⟨y, hGS hy⟩, Algebra.subset_adjoin ?_, rfl⟩
      simp only [σ, Finset.coe_image, Set.mem_image, Finset.mem_coe, Finset.mem_attach, true_and,
        Subtype.exists]
      exact ⟨y, hy, rfl⟩
    · refine ⟨φ₂ (Polynomial.C a), ?_, hφC₂ a⟩
      exact Subalgebra.algebraMap_mem (Algebra.adjoin (Polynomial ↥A₂) (σ : Set ↥S₂)) (Polynomial.C a)
  have hmemT : ∀ (y : F) (z : ↥S₂), y ∈ T → (z : F) = y →
      z ∈ Algebra.adjoin (Polynomial ↥A₂) (σ : Set ↥S₂) := by
    rintro y z ⟨w, hw, rfl⟩ hzw
    have : z = w := Subtype.ext hzw
    rw [this]; exact hw
  obtain ⟨g, h, hg, hh, ⟨u, hu⟩, hfh⟩ := hfg (s : F) s.2
  refine ⟨(u : ↥S₂), hmemT h _ (hT hh) hu, u.isUnit, hmemT g _ (hT hg) ?_⟩
  rw [Subring.coe_mul, hu, hfh]

set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 6400000 in

theorem branch_baseChange
    {k₀ L F : Type} [Field k₀] [Field L] [Field F] [Algebra k₀ L] [Algebra L F]
    (A : ValuationSubring L) (K₁ K₂ : IntermediateField k₀ L) (hK : K₁ ≤ K₂)
    (A₁ : ValuationSubring ↥K₁) (hA₁ : ∀ x : ↥K₁, x ∈ A₁ ↔ (x : L) ∈ A)
    (A₂ : ValuationSubring ↥K₂) (hA₂ : ∀ x : ↥K₂, x ∈ A₂ ↔ (x : L) ∈ A)
    [IsDiscreteValuationRing ↥A₂]
    (S₁ S₂ : Subring F) (hmono : S₁ ≤ S₂)
    (φ₁ : Polynomial ↥A₁ →+* ↥S₁) (φ₂ : Polynomial ↥A₂ →+* ↥S₂)
    (hφC : ∀ a : ↥A₁, ((φ₁ (Polynomial.C a) : ↥S₁) : F) = algebraMap L F ((a : ↥K₁) : L))
    (hφ₂C : ∀ a : ↥A₂, ((φ₂ (Polynomial.C a) : ↥S₂) : F) = algebraMap L F ((a : ↥K₂) : L))
    (ϖ : ↥A₁) (hϖ : maximalIdeal ↥A₁ = Ideal.span {ϖ})
    (ϖ₂ : ↥A₂) (hϖ₂ : maximalIdeal ↥A₂ = Ideal.span {ϖ₂})
    (hufd : UniqueFactorizationMonoid ↥S₁)
    (hbranch : ∀ p : ↥S₁, Prime p → ¬ Associated p (φ₁ (Polynomial.C ϖ)) →
      ∀ x : ↥S₁, ∃ r : Polynomial ↥A₁, r.Monic ∧ p ∣ (r.map (φ₁.comp Polynomial.C)).eval x)
    (hprime₂ : Prime (φ₂ (Polynomial.C ϖ₂)))
    (hint₂ : ∀ x : ↥S₂, ∃ q : Polynomial ↥S₁, q.Monic ∧ (q.map (Subring.inclusion hmono)).eval x = 0) :
    ∀ p : ↥S₂, Prime p → ¬ Associated p (φ₂ (Polynomial.C ϖ₂)) →
      ∀ x : ↥S₂, ∃ r : Polynomial ↥A₂, r.Monic ∧ p ∣ (r.map (φ₂.comp Polynomial.C)).eval x := by
  classical
  intro p hp hnp x
  haveI := hufd

  let ι : ↥A₁ →+* ↥A₂ :=
    ((IntermediateField.inclusion hK).toRingHom.comp A₁.subtype).codRestrict A₂.toSubring
      (fun a => show IntermediateField.inclusion hK (a : ↥K₁) ∈ A₂ from (hA₂ _).mpr ((hA₁ a).mp a.2))
  have hι : ∀ a : ↥A₁, (((ι a : ↥A₂) : ↥K₂) : L) = ((a : ↥K₁) : L) := fun a => rfl
  let j : ↥S₁ →+* ↥S₂ := Subring.inclusion hmono
  have hj : ∀ s : ↥S₁, ((j s : ↥S₂) : F) = (s : F) := fun s => rfl
  have hjC : ∀ a : ↥A₁, j (φ₁ (Polynomial.C a)) = φ₂ (Polynomial.C (ι a)) := fun a =>
    Subtype.ext (by rw [hj, hφC, hφ₂C, hι])

  let I : Ideal ↥S₂ := Ideal.span {p}
  haveI hIp : I.IsPrime := (Ideal.span_singleton_prime hp.ne_zero).mpr hp
  let Q := ↥S₂ ⧸ I
  let mk : ↥S₂ →+* Q := Ideal.Quotient.mk I
  have hmkI : ∀ y : ↥S₂, mk y = 0 ↔ p ∣ y := fun y => by
    rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]

  letI algj : Algebra ↥S₁ ↥S₂ := j.toAlgebra
  have hpint : IsIntegral ↥S₁ p := by
    obtain ⟨q, hq, hq0⟩ := hint₂ p
    exact ⟨q, hq, by rwa [← Polynomial.eval_map]⟩
  have h𝔭ne : I.comap j ≠ ⊥ :=
    Ideal.comap_ne_bot_of_integral_mem hp.ne_zero (Ideal.mem_span_singleton_self p) hpint
  haveI : (I.comap j).IsPrime := Ideal.comap_isPrime j I
  obtain ⟨y, hy𝔭, hy0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h𝔭ne
  have hyu : ¬ IsUnit y := fun hu =>
    (Ideal.IsPrime.ne_top ‹(I.comap j).IsPrime›) (Ideal.eq_top_of_isUnit_mem _ hy𝔭 hu)
  obtain ⟨q₁, hq₁f, hq₁𝔭⟩ : ∃ q₁ ∈ UniqueFactorizationMonoid.factors y, q₁ ∈ I.comap j := by
    apply (Ideal.IsPrime.multiset_prod_mem_iff_exists_mem ‹(I.comap j).IsPrime› _).mp
    obtain ⟨u, hu⟩ := UniqueFactorizationMonoid.factors_prod hy0

    have : (UniqueFactorizationMonoid.factors y).prod = y * ↑u⁻¹ :=
      (Units.eq_mul_inv_iff_mul_eq u).mpr hu
    rw [this]
    exact Ideal.mul_mem_right _ _ hy𝔭
  have hq₁p : Prime q₁ := UniqueFactorizationMonoid.prime_of_factor q₁ hq₁f

  have h𝔭 : ∀ s : ↥S₁, s ∈ I.comap j ↔ p ∣ j s := fun s => by
    rw [Ideal.mem_comap, Ideal.mem_span_singleton]

  have hq₁ϖ : ¬ Associated q₁ (φ₁ (Polynomial.C ϖ)) := by
    intro hass

    have hϖ𝔭 : φ₁ (Polynomial.C ϖ) ∈ I.comap j := by
      obtain ⟨u, hu⟩ := hass
      rw [← hu]; exact Ideal.mul_mem_right _ _ hq₁𝔭
    have hpdvd : p ∣ φ₂ (Polynomial.C (ι ϖ)) := by rw [← hjC]; exact (h𝔭 _).mp hϖ𝔭

    have hϖmax : ϖ ∈ maximalIdeal ↥A₁ := by rw [hϖ]; exact Ideal.mem_span_singleton_self ϖ
    have hιϖ : ι ϖ ∈ maximalIdeal ↥A₂ := by
      rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at hϖmax ⊢
      intro hu
      apply hϖmax

      by_cases h0 : ((ϖ : ↥K₁) : L) = 0
      · exfalso
        have : ι ϖ = 0 := Subtype.ext (Subtype.ext (by rw [show (((ι ϖ : ↥A₂) : ↥K₂) : L) = _ from hι ϖ, h0]; rfl))
        rw [this] at hu; exact not_isUnit_zero hu
      · obtain ⟨w, hw⟩ := hu.exists_left_inv
        have hwL : (((w : ↥A₂) : ↥K₂) : L) * ((ϖ : ↥K₁) : L) = 1 := by
          have := congrArg (fun z : ↥A₂ => ((z : ↥K₂) : L)) hw
          simpa [hι] using this
        have hinvA : ((ϖ : ↥K₁) : L)⁻¹ ∈ A := by
          rw [← eq_inv_of_mul_eq_one_left hwL]; exact (hA₂ _).mp (w : ↥A₂).2
        have hinvA₁ : (ϖ : ↥K₁)⁻¹ ∈ A₁ := by
          rw [hA₁]
          have : (((ϖ : ↥K₁)⁻¹ : ↥K₁) : L) = ((ϖ : ↥K₁) : L)⁻¹ := by push_cast; rfl
          rw [this]; exact hinvA
        have h0' : (ϖ : ↥K₁) ≠ 0 := fun h => h0 (by rw [h]; rfl)
        exact isUnit_iff_exists_inv.mpr ⟨⟨_, hinvA₁⟩, Subtype.ext (mul_inv_cancel₀ h0')⟩
    have hιϖ0 : ι ϖ ≠ 0 := by
      intro h0
      have hϖ0 : ((ϖ : ↥K₁) : L) = 0 := by rw [← hι ϖ, h0]; rfl

      apply hq₁p.ne_zero
      obtain ⟨u, hu⟩ := hass
      have : φ₁ (Polynomial.C ϖ) = 0 := by
        have : ϖ = 0 := Subtype.ext (Subtype.ext hϖ0)
        rw [this, Polynomial.C_0, map_zero]
      rw [this] at hu
      exact (mul_eq_zero.mp hu).resolve_right (Units.ne_zero u)
    have hirr : Irreducible ϖ₂ := (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ₂).mpr hϖ₂
    obtain ⟨k, u, hku⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hιϖ0 hirr
    have hpdvd' : p ∣ φ₂ (Polynomial.C ϖ₂) ^ k := by
      rw [hku, map_mul, map_mul, map_pow, map_pow] at hpdvd
      exact (IsUnit.dvd_mul_left ((u.isUnit.map Polynomial.C).map φ₂)).mp hpdvd
    exact hnp (hp.irreducible.associated_of_dvd hprime₂.irreducible (hp.dvd_of_dvd_pow hpdvd'))

  let f₁ : ↥A₁ →+* Q := mk.comp (j.comp (φ₁.comp Polynomial.C))
  letI algA₁S₁ : Algebra ↥A₁ ↥S₁ := (φ₁.comp Polynomial.C).toAlgebra
  letI algA₁Q : Algebra ↥A₁ Q := f₁.toAlgebra
  haveI : IsScalarTower ↥A₁ ↥S₁ Q := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have halgS₁Q : ∀ s : ↥S₁, algebraMap ↥S₁ Q s = mk (j s) := fun _ => rfl
  have hS₁int : ∀ s : ↥S₁, IsIntegral ↥A₁ (algebraMap ↥S₁ Q s) := by
    intro s
    obtain ⟨r₁, hr₁, hdvd⟩ := hbranch q₁ hq₁p hq₁ϖ s
    refine ⟨r₁, hr₁, ?_⟩

    have e1 : Polynomial.eval₂ (algebraMap ↥A₁ Q) (algebraMap ↥S₁ Q s) r₁ =
        mk (j ((r₁.map (φ₁.comp Polynomial.C)).eval s)) := by
      rw [Polynomial.eval_map, Polynomial.hom_eval₂, Polynomial.hom_eval₂]; rfl
    rw [e1, hmkI]
    obtain ⟨c, hc⟩ := hdvd
    have : p ∣ j q₁ := (h𝔭 _).mp hq₁𝔭
    rw [hc, map_mul]
    exact Dvd.dvd.mul_right this _
  let T : Subalgebra ↥A₁ Q := (IsScalarTower.toAlgHom ↥A₁ ↥S₁ Q).range
  haveI : Algebra.IsIntegral ↥A₁ ↥T := by
    refine ⟨fun t => ?_⟩
    obtain ⟨s, hs⟩ := (AlgHom.mem_range _).mp t.2
    rw [← isIntegral_algHom_iff T.val Subtype.val_injective]
    show IsIntegral ↥A₁ (t : Q)
    rw [← hs]; exact hS₁int s

  have hxT : IsIntegral ↥T (mk x) := by
    obtain ⟨q, hq, hq0⟩ := hint₂ x
    let ρ : ↥S₁ →+* ↥T := (IsScalarTower.toAlgHom ↥A₁ ↥S₁ Q).rangeRestrict.toRingHom
    have hρ : ∀ s, ((ρ s : ↥T) : Q) = mk (j s) := fun _ => rfl
    refine ⟨q.map ρ, hq.map ρ, ?_⟩
    rw [Polynomial.eval₂_map]
    have : (algebraMap ↥T Q).comp ρ = mk.comp j := RingHom.ext fun s => hρ s
    rw [this, ← Polynomial.hom_eval₂, ← Polynomial.eval_map, hq0, map_zero]
  have hxA₁ : IsIntegral ↥A₁ (mk x) := isIntegral_trans (mk x) hxT

  letI algA₂Q : Algebra ↥A₂ Q := (mk.comp (φ₂.comp Polynomial.C)).toAlgebra
  letI algA₁A₂ : Algebra ↥A₁ ↥A₂ := ι.toAlgebra
  haveI : IsScalarTower ↥A₁ ↥A₂ Q := IsScalarTower.of_algebraMap_eq fun a => by
    show mk (j (φ₁ (Polynomial.C a))) = mk (φ₂ (Polynomial.C (ι a)))
    rw [hjC]
  obtain ⟨r, hr, hr0⟩ := hxA₁.tower_top (A := ↥A₂)
  refine ⟨r, hr, ?_⟩
  rw [← hmkI]
  have : mk ((r.map (φ₂.comp Polynomial.C)).eval x) = Polynomial.eval₂ (algebraMap ↥A₂ Q) (mk x) r := by
    rw [Polynomial.eval_map, Polynomial.hom_eval₂]; rfl
  rw [this, hr0]

set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 6400000 in

theorem isLocalRing_layer
    {k₀ L F : Type} [Field k₀] [Field L] [Field F] [Algebra k₀ L] [Algebra L F]
    (A : ValuationSubring L) (K₁ K₂ : IntermediateField k₀ L)
    (A₁ : ValuationSubring ↥K₁) (hA₁ : ∀ x : ↥K₁, x ∈ A₁ ↔ (x : L) ∈ A)
    (A₂ : ValuationSubring ↥K₂) (hA₂ : ∀ x : ↥K₂, x ∈ A₂ ↔ (x : L) ∈ A)
    [IsDiscreteValuationRing ↥A₂]
    (ϖ : ↥A₁) (hϖ : maximalIdeal ↥A₁ = Ideal.span {ϖ}) (hϖ0 : ϖ ≠ 0)
    (ϖ₂ : ↥A₂) (hϖ₂ : maximalIdeal ↥A₂ = Ideal.span {ϖ₂})
    (ι₁₂ : ↥A₁ →+* ↥A₂) (hι₁₂ : ∀ a : ↥A₁, (((ι₁₂ a : ↥A₂) : ↥K₂) : L) = ((a : ↥K₁) : L))
    (S₁ S₂ : Subring F) (hmono : S₁ ≤ S₂) [IsLocalRing ↥S₁]
    (φ₁ : Polynomial ↥A₁ →+* ↥S₁) (χ₁ : ↥S₁ →+* ResidueField ↥A)
    (hχC : ∀ a : ↥A₁, χ₁ (φ₁ (Polynomial.C a)) = IsLocalRing.residue ↥A ⟨((a : ↥K₁) : L), (hA₁ a).mp a.2⟩)
    (hχt : χ₁ (φ₁ Polynomial.X) = 0)
    (hmax : ∀ f : ↥S₁, f ∈ maximalIdeal ↥S₁ ↔ χ₁ f = 0)
    (hmax₁gen : maximalIdeal ↥S₁ = Ideal.span {φ₁ Polynomial.X, φ₁ (Polynomial.C ϖ)})
    (c₂ : ↥A₂ →+* ↥S₂)
    (hc₂ι : ∀ a : ↥A₁, ((c₂ (ι₁₂ a) : ↥S₂) : F) = ((φ₁ (Polynomial.C a) : ↥S₁) : F))
    (t₂ : ↥S₂) (ht₂ : (t₂ : F) = ((φ₁ Polynomial.X : ↥S₁) : F))
    (χ₂ : ↥S₂ →+* ResidueField ↥A)
    (hχ₂S : ∀ f : ↥S₁, χ₂ ⟨(f : F), hmono f.2⟩ = χ₁ f)
    (hχ₂c : ∀ a : ↥A₂, χ₂ (c₂ a) = IsLocalRing.residue ↥A ⟨((a : ↥K₂) : L), (hA₂ a).mp a.2⟩)
    (hκ₂ : Function.Surjective (fun a : ↥A₂ => IsLocalRing.residue ↥A ⟨((a : ↥K₂) : L), (hA₂ a).mp a.2⟩))
    (hred : ∀ x : ↥S₂, ∃ s : ↥S₁, c₂ ϖ₂ ∣ x - ⟨(s : F), hmono s.2⟩)
    (hint₂ : ∀ x : ↥S₂, ∃ q : Polynomial ↥S₁, q.Monic ∧ (q.map (Subring.inclusion hmono)).eval x = 0) :
    ∃ (_ : IsLocalRing ↥S₂), (∀ f : ↥S₂, f ∈ maximalIdeal ↥S₂ ↔ χ₂ f = 0) ∧
      maximalIdeal ↥S₂ = Ideal.span {t₂, c₂ ϖ₂} := by
  classical
  let j : ↥S₁ →+* ↥S₂ := Subring.inclusion hmono
  have hj : ∀ s : ↥S₁, j s = ⟨(s : F), hmono s.2⟩ := fun _ => rfl
  letI : Algebra ↥S₁ ↥S₂ := j.toAlgebra
  haveI : Algebra.IsIntegral ↥S₁ ↥S₂ := ⟨fun x => by
    obtain ⟨q, hq, hq0⟩ := hint₂ x
    exact ⟨q, hq, by rwa [← Polynomial.eval_map]⟩⟩
  set π₂ : ↥S₂ := c₂ ϖ₂ with hπ₂

  have hsurj : Function.Surjective χ₂ := fun r => by
    obtain ⟨a, ha⟩ := hκ₂ r
    exact ⟨c₂ a, (hχ₂c a).trans ha⟩
  set K : Ideal ↥S₂ := RingHom.ker χ₂ with hK
  haveI hKmax : K.IsMaximal := RingHom.ker_isMaximal_of_surjective χ₂ hsurj

  have hresA₂ : ∀ a : ↥A₂, a ∈ maximalIdeal ↥A₂ →
      IsLocalRing.residue ↥A ⟨((a : ↥K₂) : L), (hA₂ a).mp a.2⟩ = 0 := by
    intro a ha
    rw [IsLocalRing.residue_eq_zero_iff]
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at ha ⊢
    intro hu; apply ha
    by_cases h0 : ((a : ↥K₂) : L) = 0
    · exfalso
      have : (⟨((a : ↥K₂) : L), (hA₂ a).mp a.2⟩ : ↥A) = 0 := Subtype.ext h0
      rw [this] at hu; exact not_isUnit_zero hu
    obtain ⟨w, hw⟩ := hu.exists_left_inv
    have hwL : (w : L) * ((a : ↥K₂) : L) = 1 := by
      have := congrArg Subtype.val hw; simpa using this
    have hinvA : ((a : ↥K₂) : L)⁻¹ ∈ A := by rw [← eq_inv_of_mul_eq_one_left hwL]; exact w.2
    have hinvA₂ : (a : ↥K₂)⁻¹ ∈ A₂ := by
      rw [hA₂]
      have : (((a : ↥K₂)⁻¹ : ↥K₂) : L) = ((a : ↥K₂) : L)⁻¹ := by push_cast; rfl
      rw [this]; exact hinvA
    have h0' : (a : ↥K₂) ≠ 0 := fun h => h0 (by rw [h]; rfl)
    exact isUnit_iff_exists_inv.mpr ⟨⟨_, hinvA₂⟩, Subtype.ext (mul_inv_cancel₀ h0')⟩
  have hχπ : χ₂ π₂ = 0 := by
    rw [hπ₂, hχ₂c]
    exact hresA₂ ϖ₂ (by rw [hϖ₂]; exact Ideal.mem_span_singleton_self ϖ₂)

  have hjϖ : ∃ (n : ℕ) (u : ↥S₂), IsUnit u ∧ j (φ₁ (Polynomial.C ϖ)) = u * π₂ ^ (n + 1) := by
    have hϖmax : ϖ ∈ maximalIdeal ↥A₁ := by rw [hϖ]; exact Ideal.mem_span_singleton_self ϖ

    have hιϖ : ι₁₂ ϖ ∈ maximalIdeal ↥A₂ := by
      rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at hϖmax ⊢
      intro hu; apply hϖmax
      by_cases h0 : ((ϖ : ↥K₁) : L) = 0
      · exfalso
        have : ι₁₂ ϖ = 0 := Subtype.ext (Subtype.ext (by rw [show (((ι₁₂ ϖ : ↥A₂) : ↥K₂) : L) = _ from hι₁₂ ϖ, h0]; rfl))
        rw [this] at hu; exact not_isUnit_zero hu
      obtain ⟨w, hw⟩ := hu.exists_left_inv
      have hwL : (((w : ↥A₂) : ↥K₂) : L) * ((ϖ : ↥K₁) : L) = 1 := by
        have := congrArg (fun z : ↥A₂ => ((z : ↥K₂) : L)) hw
        simpa [hι₁₂] using this
      have hinvA : ((ϖ : ↥K₁) : L)⁻¹ ∈ A := by
        rw [← eq_inv_of_mul_eq_one_left hwL]; exact (hA₂ _).mp (w : ↥A₂).2
      have hinvA₁ : (ϖ : ↥K₁)⁻¹ ∈ A₁ := by
        rw [hA₁]
        have : (((ϖ : ↥K₁)⁻¹ : ↥K₁) : L) = ((ϖ : ↥K₁) : L)⁻¹ := by push_cast; rfl
        rw [this]; exact hinvA
      have h0' : (ϖ : ↥K₁) ≠ 0 := fun h => h0 (by rw [h]; rfl)
      exact isUnit_iff_exists_inv.mpr ⟨⟨_, hinvA₁⟩, Subtype.ext (mul_inv_cancel₀ h0')⟩
    have hιϖ0 : ι₁₂ ϖ ≠ 0 := fun h0 =>
      hϖ0 (Subtype.ext (Subtype.ext (by rw [← hι₁₂ ϖ, h0]; rfl)))
    have hirr : Irreducible ϖ₂ := (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ₂).mpr hϖ₂
    obtain ⟨n, u, hnu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hιϖ0 hirr
    have hn : n ≠ 0 := by
      rintro rfl
      rw [pow_zero, mul_one] at hnu
      rw [hnu] at hιϖ
      exact (IsLocalRing.mem_maximalIdeal _).mp hιϖ u.isUnit
    obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
    refine ⟨m, c₂ u, (u.isUnit.map c₂), ?_⟩
    have : j (φ₁ (Polynomial.C ϖ)) = c₂ (ι₁₂ ϖ) := Subtype.ext (by rw [hj]; exact (hc₂ι ϖ).symm)
    rw [this, hnu, map_mul, map_pow]
  obtain ⟨n, u, hu, hjϖ⟩ := hjϖ

  have hϖm₁ : φ₁ (Polynomial.C ϖ) ∈ maximalIdeal ↥S₁ := by
    rw [hmax₁gen]; exact Ideal.subset_span (by simp)
  have hunique : ∀ M : Ideal ↥S₂, M.IsMaximal → M = K := by
    intro M hM
    haveI := hM
    have hcomap : M.comap j = maximalIdeal ↥S₁ := by
      have : (M.comap (algebraMap ↥S₁ ↥S₂)).IsMaximal := Ideal.isMaximal_comap_of_isIntegral_of_isMaximal M
      exact IsLocalRing.eq_maximalIdeal this
    have hπM : π₂ ∈ M := by
      have h1 : j (φ₁ (Polynomial.C ϖ)) ∈ M := by
        have : φ₁ (Polynomial.C ϖ) ∈ M.comap j := by rw [hcomap]; exact hϖm₁
        exact this
      rw [hjϖ] at h1
      have h2 : π₂ ^ (n + 1) ∈ M := by
        rcases hM.isPrime.mem_or_mem h1 with h | h
        · exact absurd (Ideal.eq_top_of_isUnit_mem _ h hu) hM.ne_top
        · exact h
      exact hM.isPrime.mem_of_pow_mem _ h2
    symm
    refine hKmax.eq_of_le hM.ne_top fun x hx => ?_
    rw [hK, RingHom.mem_ker] at hx
    obtain ⟨s, hs⟩ := hred x
    have hχs : χ₁ s = 0 := by
      rw [← hχ₂S, ← hj]
      obtain ⟨y, hy⟩ := hs
      have : x = j s + π₂ * y := by rw [hj, ← hy]; ring
      rw [this, map_add, map_mul, hχπ, zero_mul, add_zero] at hx
      exact hx
    have hsM : j s ∈ M := by
      have : s ∈ M.comap j := by rw [hcomap]; exact (hmax s).mpr hχs
      exact this
    obtain ⟨y, hy⟩ := hs
    have : x = j s + π₂ * y := by rw [hj, ← hy]; ring
    rw [this]
    exact M.add_mem hsM (M.mul_mem_right _ hπM)

  haveI hloc : IsLocalRing ↥S₂ := IsLocalRing.of_unique_max_ideal ⟨K, hKmax, fun M hM => hunique M hM⟩
  have hmK : maximalIdeal ↥S₂ = K := (IsLocalRing.eq_maximalIdeal hKmax).symm
  refine ⟨hloc, fun f => by rw [hmK, hK, RingHom.mem_ker], ?_⟩

  rw [hmK]
  refine le_antisymm ?_ ?_
  · intro x hx
    rw [hK, RingHom.mem_ker] at hx
    obtain ⟨s, y, hy⟩ := hred x
    have hxe : x = j s + π₂ * y := by rw [hj, ← hy]; ring
    have hχs : χ₁ s = 0 := by
      rw [← hχ₂S, ← hj]
      rw [hxe, map_add, map_mul, hχπ, zero_mul, add_zero] at hx
      exact hx
    have hsm : s ∈ maximalIdeal ↥S₁ := (hmax s).mpr hχs
    rw [hmax₁gen, Ideal.mem_span_pair] at hsm
    obtain ⟨a, b, hab⟩ := hsm
    rw [hxe, ← hab, map_add, map_mul, map_mul, hjϖ]
    have ht : j (φ₁ Polynomial.X) = t₂ := Subtype.ext (by rw [hj]; exact ht₂.symm)
    rw [ht]
    refine Ideal.add_mem _ (Ideal.add_mem _ ?_ ?_) ?_
    · exact Ideal.mul_mem_left _ _ (Ideal.subset_span (by simp))
    · rw [pow_succ, ← mul_assoc, ← mul_assoc]
      exact Ideal.mul_mem_left _ _ (Ideal.subset_span (by simp))
    · exact Ideal.mul_mem_right _ _ (Ideal.subset_span (by simp))
  · rw [Ideal.span_le]
    intro y hy
    rcases hy with hy | hy
    · rw [hy, SetLike.mem_coe, hK, RingHom.mem_ker]
      have ht : t₂ = j (φ₁ Polynomial.X) := Subtype.ext (by rw [hj]; exact ht₂)
      rw [ht, hj, hχ₂S, hχt]
    · rw [Set.mem_singleton_iff] at hy
      rw [hy, SetLike.mem_coe, hK, RingHom.mem_ker]
      exact hχπ

end KFBC

set_option autoImplicit false
open Polynomial TensorProduct

namespace KFBC

set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 6400000 in

theorem formallySmooth_formallyUnramified_baseChange
    {A₁ A₂ S₁ S₂ : Type} [CommRing A₁] [CommRing A₂] [CommRing S₁] [CommRing S₂]
    (ι : A₁ →+* A₂) (j : S₁ →+* S₂)
    (φ₁ : Polynomial A₁ →+* S₁) (φ₂ : Polynomial A₂ →+* S₂)
    (hjC : ∀ a : A₁, j (φ₁ (Polynomial.C a)) = φ₂ (Polynomial.C (ι a)))
    (hjX : j (φ₁ Polynomial.X) = φ₂ Polynomial.X)
    (e : ℕ) (ϖ₂ : A₂)
    (hspanA : ∀ a : A₂, ∃ c : Fin e → A₁, a = ∑ i, ι (c i) * ϖ₂ ^ (i : ℕ))
    (hindA : ∀ c : Fin e → A₁, ∑ i, ι (c i) * ϖ₂ ^ (i : ℕ) = 0 → ∀ i, c i = 0)
    (hspanS : ∀ x : S₂, ∃ c : Fin e → S₁, x = ∑ i, j (c i) * φ₂ (Polynomial.C ϖ₂) ^ (i : ℕ))
    (hindS : ∀ c : Fin e → S₁, ∑ i, j (c i) * φ₂ (Polynomial.C ϖ₂) ^ (i : ℕ) = 0 → ∀ i, c i = 0)
    (hφs : φ₁.FormallySmooth) (hφu : φ₁.FormallyUnramified) :
    φ₂.FormallySmooth ∧ φ₂.FormallyUnramified := by
  classical

  letI aA : Algebra A₁ A₂ := ι.toAlgebra
  letI aP : Algebra (Polynomial A₁) (Polynomial A₂) := Polynomial.algebra A₁ A₂
  letI aφ₁ : Algebra (Polynomial A₁) S₁ := φ₁.toAlgebra
  letI aφ₂ : Algebra (Polynomial A₂) S₂ := φ₂.toAlgebra
  letI aj : Algebra S₁ S₂ := j.toAlgebra
  letI aA₁S₁ : Algebra A₁ S₁ := (φ₁.comp Polynomial.C).toAlgebra
  letI aA₂S₂ : Algebra A₂ S₂ := (φ₂.comp Polynomial.C).toAlgebra
  letI aA₁S₂ : Algebra A₁ S₂ := (j.comp (φ₁.comp Polynomial.C)).toAlgebra
  letI aP₁S₂ : Algebra (Polynomial A₁) S₂ := (j.comp φ₁).toAlgebra
  have hcomm : φ₂.comp (Polynomial.mapRingHom ι) = j.comp φ₁ := by
    apply Polynomial.ringHom_ext
    · intro a; simp [hjC]
    · simp [hjX]
  haveI : IsScalarTower A₁ (Polynomial A₁) S₁ := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : IsScalarTower A₂ (Polynomial A₂) S₂ := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : IsScalarTower A₁ S₁ S₂ := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : IsScalarTower (Polynomial A₁) S₁ S₂ := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : IsScalarTower A₁ A₂ S₂ := IsScalarTower.of_algebraMap_eq fun a => by
    show j (φ₁ (Polynomial.C a)) = φ₂ (Polynomial.C (ι a)); exact hjC a
  haveI : IsScalarTower (Polynomial A₁) (Polynomial A₂) S₂ := IsScalarTower.of_algebraMap_eq fun p => by
    show j (φ₁ p) = φ₂ (Polynomial.mapRingHom ι p)
    exact (RingHom.congr_fun hcomm p).symm
  haveI : IsScalarTower A₁ (Polynomial A₂) S₂ := IsScalarTower.of_algebraMap_eq fun a => by
    show j (φ₁ (Polynomial.C a)) = φ₂ (algebraMap A₁ (Polynomial A₂) a)
    rw [show algebraMap A₁ (Polynomial A₂) a = Polynomial.C (ι a) from rfl, ← hjC]
  haveI : IsScalarTower A₁ (Polynomial A₁) S₂ := IsScalarTower.of_algebraMap_eq fun _ => rfl

  set π₂ : S₂ := φ₂ (Polynomial.C ϖ₂) with hπ₂
  have hsmulA : ∀ (c : A₁) (a : A₂), c • a = ι c * a := fun _ _ => rfl
  have hsmulS : ∀ (c : S₁) (s : S₂), c • s = j c * s := fun _ _ => rfl
  have hliA : LinearIndependent A₁ (fun i : Fin e => ϖ₂ ^ (i : ℕ)) := by
    rw [Fintype.linearIndependent_iff]
    intro g hg i
    simp only [hsmulA] at hg
    exact hindA g hg i
  have hspA : ⊤ ≤ Submodule.span A₁ (Set.range fun i : Fin e => ϖ₂ ^ (i : ℕ)) := by
    intro a _
    obtain ⟨c, hc⟩ := hspanA a
    rw [hc]
    refine Submodule.sum_mem _ fun i _ => ?_
    rw [← hsmulA]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  let bA : Module.Basis (Fin e) A₁ A₂ := Module.Basis.mk hliA hspA
  have hbA : ∀ i : Fin e, bA i = ϖ₂ ^ (i : ℕ) := fun i => Module.Basis.mk_apply hliA hspA i
  have hliS : LinearIndependent S₁ (fun i : Fin e => π₂ ^ (i : ℕ)) := by
    rw [Fintype.linearIndependent_iff]
    intro g hg i
    simp only [hsmulS] at hg
    exact hindS g hg i
  have hspS : ⊤ ≤ Submodule.span S₁ (Set.range fun i : Fin e => π₂ ^ (i : ℕ)) := by
    intro x _
    obtain ⟨c, hc⟩ := hspanS x
    rw [hc]
    refine Submodule.sum_mem _ fun i _ => ?_
    rw [← hsmulS]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  let bS : Module.Basis (Fin e) S₁ S₂ := Module.Basis.mk hliS hspS
  have hbS : ∀ i : Fin e, bS i = π₂ ^ (i : ℕ) := fun i => Module.Basis.mk_apply hliS hspS i

  let bT : Module.Basis (Fin e) S₁ (S₁ ⊗[A₁] A₂) := Algebra.TensorProduct.basis S₁ bA
  have hbT : ∀ i : Fin e, bT i = (1 : S₁) ⊗ₜ (ϖ₂ ^ (i : ℕ)) := fun i => by
    rw [Algebra.TensorProduct.basis_apply, hbA]
  let eqv : S₁ ⊗[A₁] A₂ ≃ₗ[S₁] S₂ := bT.equiv bS (Equiv.refl _)
  have heqv : ∀ i : Fin e, eqv ((1 : S₁) ⊗ₜ (ϖ₂ ^ (i : ℕ))) = π₂ ^ (i : ℕ) := fun i => by
    rw [← hbT, Module.Basis.equiv_apply, Equiv.refl_apply, hbS]
  haveI hpush : Algebra.IsPushout A₁ S₁ A₂ S₂ := by
    rw [Algebra.isPushout_iff]
    refine IsBaseChange.of_equiv eqv fun a => ?_
    obtain ⟨c, hc⟩ := hspanA a
    show eqv ((1 : S₁) ⊗ₜ a) = algebraMap A₂ S₂ a
    rw [hc]
    simp only [TensorProduct.tmul_sum, map_sum, map_mul, map_pow]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← hsmulA, TensorProduct.tmul_smul, ← algebraMap_smul S₁, map_smul, heqv]
    show j (φ₁ (Polynomial.C (c i))) * π₂ ^ (i : ℕ) = φ₂ (Polynomial.C (ι (c i))) * φ₂ (Polynomial.C ϖ₂) ^ (i : ℕ)
    rw [hjC]

  haveI : Algebra.IsPushout (Polynomial A₁) S₁ (Polynomial A₂) S₂ :=
    (Algebra.IsPushout.comp_iff (R := A₁) (S := Polynomial A₁) (T := S₁)
      (R' := A₂) (S' := Polynomial A₂) (T' := S₂)).mp hpush
  have h1 : (algebraMap (Polynomial A₂) S₂).FormallySmooth :=
    RingHom.FormallySmooth.isStableUnderBaseChange _ _ _ _ ((RingHom.formallySmooth_algebraMap).mpr hφs)
  have h2 : (algebraMap (Polynomial A₂) S₂).FormallyUnramified :=
    RingHom.FormallyUnramified.isStableUnderBaseChange _ _ _ _ ((RingHom.formallyUnramified_algebraMap).mpr hφu)
  exact ⟨h1, h2⟩

set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 6400000 in

theorem formallySmooth_formallyUnramified_layer
    {k₀ L F : Type} [Field k₀] [Field L] [Field F] [Algebra k₀ L] [Algebra L F]
    (K₁ K₂ : IntermediateField k₀ L) (A₁ : ValuationSubring ↥K₁) (A₂ : ValuationSubring ↥K₂)
    (ι₁₂ : ↥A₁ →+* ↥A₂) (hι₁₂ : ∀ a : ↥A₁, (((ι₁₂ a : ↥A₂) : ↥K₂) : L) = ((a : ↥K₁) : L))
    (S₁ S₂ : Subring F) (hmono : S₁ ≤ S₂)
    (φ₁ : Polynomial ↥A₁ →+* ↥S₁) (φ₂ : Polynomial ↥A₂ →+* ↥S₂)
    (hCC : ∀ a : ↥A₁, ((φ₁ (Polynomial.C a) : ↥S₁) : F) = ((φ₂ (Polynomial.C (ι₁₂ a)) : ↥S₂) : F))
    (hXX : ((φ₁ Polynomial.X : ↥S₁) : F) = ((φ₂ Polynomial.X : ↥S₂) : F))
    (e : ℕ) (ϖ₂ : ↥A₂) (π : F) (hπ : π = ((φ₂ (Polynomial.C ϖ₂) : ↥S₂) : F))
    (hEis₁ : ∀ a : ↥A₂, ∃ c : Fin e → ↥A₁, a = ∑ i, ι₁₂ (c i) * ϖ₂ ^ (i : ℕ))
    (hEis₂ : LinearIndependent ↥K₁ (fun i : Fin e => (((ϖ₂ ^ (i : ℕ) : ↥A₂) : ↥K₂) : L)))
    (hcoord : ∀ x : F, x ∈ S₂ ↔ ∃ c : Fin e → ↥S₁, x = ∑ i, (c i : F) * π ^ (i : ℕ))
    (hcoord_uniq : ∀ c c' : Fin e → ↥S₁,
      ∑ i, (c i : F) * π ^ (i : ℕ) = ∑ i, (c' i : F) * π ^ (i : ℕ) → c = c')
    (hφs : φ₁.FormallySmooth) (hφu : φ₁.FormallyUnramified) :
    φ₂.FormallySmooth ∧ φ₂.FormallyUnramified := by
  classical
  let j : ↥S₁ →+* ↥S₂ := Subring.inclusion hmono
  have hcoeS : ∀ c : Fin e → ↥S₁,
      ((∑ i, j (c i) * φ₂ (Polynomial.C ϖ₂) ^ (i : ℕ) : ↥S₂) : F) = ∑ i, (c i : F) * π ^ (i : ℕ) := by
    intro c
    rw [AddSubmonoidClass.coe_finsetSum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Subring.coe_mul, Subring.coe_pow, hπ]; rfl
  refine formallySmooth_formallyUnramified_baseChange ι₁₂ j φ₁ φ₂
    (fun a => Subtype.ext (hCC a)) (Subtype.ext hXX) e ϖ₂ hEis₁ ?_ ?_ ?_ hφs hφu
  ·
    intro c hc i
    have hcoeA : (((∑ i, ι₁₂ (c i) * ϖ₂ ^ (i : ℕ) : ↥A₂) : ↥K₂) : L) =
        ∑ i, ((c i : ↥A₁) : ↥K₁) • ((((ϖ₂ ^ (i : ℕ) : ↥A₂) : ↥K₂) : L)) := by
      push_cast
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Algebra.smul_def, hι₁₂ (c i)]
      rfl
    have hL : ∑ i, ((c i : ↥A₁) : ↥K₁) • ((((ϖ₂ ^ (i : ℕ) : ↥A₂) : ↥K₂) : L)) = 0 := by
      rw [← hcoeA, hc]; rfl
    have := (Fintype.linearIndependent_iff.mp hEis₂) (fun i => ((c i : ↥A₁) : ↥K₁)) hL i
    exact Subtype.ext (by simpa using this)
  · intro x
    obtain ⟨c, hc⟩ := (hcoord (x : F)).mp x.2
    exact ⟨c, Subtype.ext (by rw [hcoeS]; exact hc)⟩
  · intro c hc i
    have h0 : ∑ i : Fin e, (c i : F) * π ^ (i : ℕ) = ∑ i : Fin e, (((fun _ => (0 : ↥S₁)) i : ↥S₁) : F) * π ^ (i : ℕ) := by
      rw [← hcoeS, hc]; simp
    have := hcoord_uniq c (fun _ => 0) h0
    exact congrFun this i

end KFBC

set_option autoImplicit false

open AlgebraicCurve IsLocalRing

namespace L1BBC

section General

variable {L F : Type} [Field L] [Field F] [Algebra L F]

theorem forall_residue_eq_of_closure
    (A : ValuationSubring L) {Fbar : Type} [Field Fbar] [Algebra (ResidueField ↥A) Fbar]
    (R : RegularProlongation A F Fbar) (Q : Place (ResidueField ↥A) Fbar)
    (S₁ S₂ : Subring F) (hmono : S₁ ≤ S₂) (Cst : Set F)
    (hS₂ : S₂ = Subring.closure ((S₁ : Set F) ∪ Cst))
    (χ₁ : ↥S₁ →+* ResidueField ↥A) (χ₂ : ↥S₂ →+* ResidueField ↥A)
    (hχ₂S : ∀ f : ↥S₁, χ₂ ⟨(f : F), hmono f.2⟩ = χ₁ f)
    (hres : ∀ f : ↥S₁, ∃ hR : (f : F) ∈ R.integers, ∃ hm : R.residue ⟨(f : F), hR⟩ ∈ Q.toValuationSubring,
      IsLocalRing.residue ↥Q.toValuationSubring ⟨R.residue ⟨(f : F), hR⟩, hm⟩ =
        algebraMap (ResidueField ↥A) Q.ResidueField (χ₁ f))
    (hcst : ∀ c : F, ∀ hc : c ∈ Cst, ∃ a : ↥A, c = algebraMap L F (a : L) ∧
      χ₂ ⟨c, hS₂ ▸ Subring.subset_closure (Or.inr hc)⟩ = IsLocalRing.residue ↥A a) :
    ∀ f : ↥S₂, ∃ hR : (f : F) ∈ R.integers, ∃ hm : R.residue ⟨(f : F), hR⟩ ∈ Q.toValuationSubring,
      IsLocalRing.residue ↥Q.toValuationSubring ⟨R.residue ⟨(f : F), hR⟩, hm⟩ =
        algebraMap (ResidueField ↥A) Q.ResidueField (χ₂ f) := by
  classical

  have key : ∀ (x : F) (hx : x ∈ Subring.closure ((S₁ : Set F) ∪ Cst)),
      ∃ hR : x ∈ R.integers, ∃ hm : R.residue ⟨x, hR⟩ ∈ Q.toValuationSubring,
        IsLocalRing.residue ↥Q.toValuationSubring ⟨R.residue ⟨x, hR⟩, hm⟩ =
          algebraMap (ResidueField ↥A) Q.ResidueField (χ₂ ⟨x, hS₂ ▸ hx⟩) := by
    intro x hx
    induction hx using Subring.closure_induction with
    | mem y hy =>
      rcases hy with hy | hy
      · obtain ⟨hR, hm, h⟩ := hres ⟨y, hy⟩
        refine ⟨hR, hm, ?_⟩
        rw [h, ← hχ₂S ⟨y, hy⟩]
      · obtain ⟨a, rfl, hχ⟩ := hcst y hy
        have hR : algebraMap L F (a : L) ∈ R.integers := (R.algebraMap_mem_iff _).mpr a.2
        have hres' : R.residue ⟨algebraMap L F (a : L), hR⟩ =
            algebraMap (ResidueField ↥A) Fbar (IsLocalRing.residue ↥A a) := R.residue_algebraMap a
        refine ⟨hR, ?_, ?_⟩
        · rw [hres']; exact Q.algebraMap_mem' _
        · have : (⟨R.residue ⟨algebraMap L F (a : L), hR⟩, hres' ▸ Q.algebraMap_mem' _⟩ : ↥Q.toValuationSubring) =
              algebraMap (ResidueField ↥A) ↥Q.toValuationSubring (IsLocalRing.residue ↥A a) :=
            Subtype.ext (by rw [Place.coe_algebraMap]; exact hres')
          rw [this, hχ]
          rfl
    | zero =>
      have hR0 : (0 : F) ∈ R.integers := zero_mem _
      have hres0 : R.residue ⟨(0 : F), hR0⟩ = 0 := by
        rw [show (⟨(0 : F), hR0⟩ : ↥R.integers) = 0 from rfl, map_zero]
      have hm0 : R.residue ⟨(0 : F), hR0⟩ ∈ Q.toValuationSubring := by rw [hres0]; exact zero_mem _
      refine ⟨hR0, hm0, ?_⟩
      have hel : (⟨R.residue ⟨(0 : F), hR0⟩, hm0⟩ : ↥Q.toValuationSubring) = 0 := Subtype.ext hres0
      have h0 : (⟨(0 : F), hS₂ ▸ (Subring.closure ((S₁ : Set F) ∪ Cst)).zero_mem⟩ : ↥S₂) = 0 := rfl
      rw [hel, map_zero, h0, map_zero, map_zero]
    | one =>
      have hR1 : (1 : F) ∈ R.integers := one_mem _
      have hres1 : R.residue ⟨(1 : F), hR1⟩ = 1 := by
        rw [show (⟨(1 : F), hR1⟩ : ↥R.integers) = 1 from rfl, map_one]
      have hm1 : R.residue ⟨(1 : F), hR1⟩ ∈ Q.toValuationSubring := by rw [hres1]; exact one_mem _
      refine ⟨hR1, hm1, ?_⟩
      have hel : (⟨R.residue ⟨(1 : F), hR1⟩, hm1⟩ : ↥Q.toValuationSubring) = 1 := Subtype.ext hres1
      have h1 : (⟨(1 : F), hS₂ ▸ (Subring.closure ((S₁ : Set F) ∪ Cst)).one_mem⟩ : ↥S₂) = 1 := rfl
      rw [hel, map_one, h1, map_one, map_one]
    | add x y hx hy ihx ihy =>
      obtain ⟨hRx, hmx, ex⟩ := ihx
      obtain ⟨hRy, hmy, ey⟩ := ihy
      have hRxy : x + y ∈ R.integers := add_mem hRx hRy
      have hres_add : R.residue ⟨x + y, hRxy⟩ = R.residue ⟨x, hRx⟩ + R.residue ⟨y, hRy⟩ := by
        rw [← map_add]; rfl
      refine ⟨hRxy, by rw [hres_add]; exact add_mem hmx hmy, ?_⟩
      have : (⟨R.residue ⟨x + y, hRxy⟩, hres_add ▸ add_mem hmx hmy⟩ : ↥Q.toValuationSubring) =
          ⟨R.residue ⟨x, hRx⟩, hmx⟩ + ⟨R.residue ⟨y, hRy⟩, hmy⟩ := Subtype.ext hres_add
      rw [this, map_add, ex, ey, ← map_add, ← map_add]
      rfl
    | neg x hx ihx =>
      obtain ⟨hRx, hmx, ex⟩ := ihx
      have hRn : -x ∈ R.integers := neg_mem hRx
      have hres_neg : R.residue ⟨-x, hRn⟩ = -R.residue ⟨x, hRx⟩ := by rw [← map_neg]; rfl
      refine ⟨hRn, by rw [hres_neg]; exact neg_mem hmx, ?_⟩
      have : (⟨R.residue ⟨-x, hRn⟩, hres_neg ▸ neg_mem hmx⟩ : ↥Q.toValuationSubring) =
          -⟨R.residue ⟨x, hRx⟩, hmx⟩ := Subtype.ext hres_neg
      rw [this, map_neg, ex, ← map_neg, ← map_neg]
      rfl
    | mul x y hx hy ihx ihy =>
      obtain ⟨hRx, hmx, ex⟩ := ihx
      obtain ⟨hRy, hmy, ey⟩ := ihy
      have hRxy : x * y ∈ R.integers := mul_mem hRx hRy
      have hres_mul : R.residue ⟨x * y, hRxy⟩ = R.residue ⟨x, hRx⟩ * R.residue ⟨y, hRy⟩ := by
        rw [← map_mul]; rfl
      refine ⟨hRxy, by rw [hres_mul]; exact mul_mem hmx hmy, ?_⟩
      have : (⟨R.residue ⟨x * y, hRxy⟩, hres_mul ▸ mul_mem hmx hmy⟩ : ↥Q.toValuationSubring) =
          ⟨R.residue ⟨x, hRx⟩, hmx⟩ * ⟨R.residue ⟨y, hRy⟩, hmy⟩ := Subtype.ext hres_mul
      rw [this, map_mul, ex, ey, ← map_mul, ← map_mul]
      rfl
  intro f
  have hf : (f : F) ∈ Subring.closure ((S₁ : Set F) ∪ Cst) := hS₂ ▸ f.2
  obtain ⟨hR, hm, h⟩ := key (f : F) hf
  exact ⟨hR, hm, h⟩

end General

end L1BBC

set_option autoImplicit false

open AlgebraicCurve IsLocalRing AlgebraicCurve.GaussReduction

namespace L1BBC

variable {L F : Type} [Field L] [Field F] [Algebra L F]

theorem evalAt_add_of_mem' (v : Place L F) (hv : v.IsRational) {f g : F}
    (hf : f ∈ v.toValuationSubring) (hg : g ∈ v.toValuationSubring) :
    v.evalAt (f + g) = v.evalAt f + v.evalAt g := by
  apply v.algebraMap_residueField_injective
  rw [map_add, v.algebraMap_evalAt hv (add_mem hf hg), v.algebraMap_evalAt hv hf,
    v.algebraMap_evalAt hv hg, ← map_add]
  rfl

theorem evalAt_neg_of_mem' (v : Place L F) (hv : v.IsRational) {f : F} (hf : f ∈ v.toValuationSubring) :
    v.evalAt (-f) = -v.evalAt f := by
  apply v.algebraMap_residueField_injective
  rw [map_neg, v.algebraMap_evalAt hv (neg_mem hf), v.algebraMap_evalAt hv hf, ← map_neg]
  rfl

theorem forall_mem_disc_iff_of_closure
    (A : ValuationSubring L) (S₁ S₂ : Subring F) (hmono : S₁ ≤ S₂) (Cst : Set F)
    (hS₂ : S₂ = Subring.closure ((S₁ : Set F) ∪ Cst))
    (χ₁ : ↥S₁ →+* ResidueField ↥A) (χ₂ : ↥S₂ →+* ResidueField ↥A)
    (hχ₂S : ∀ f : ↥S₁, χ₂ ⟨(f : F), hmono f.2⟩ = χ₁ f)
    (D₁ : Set (Place L F))
    (hD : ∀ P, P ∈ D₁ ↔ (P.IsRational ∧
      (∀ f : ↥S₁, (f : F) ∈ P.toValuationSubring ∧ P.evalAt (f : F) ∈ A) ∧
      (∀ f : ↥S₁, A.valuation (P.evalAt (f : F)) < 1 ↔ χ₁ f = 0)))
    (hκS₁ : ∀ z : ResidueField ↥A, ∃ a : ↥A, ∃ hc : algebraMap L F (a : L) ∈ S₁,
      IsLocalRing.residue ↥A a = z ∧ χ₁ ⟨algebraMap L F (a : L), hc⟩ = z)
    (hcst : ∀ c : F, ∀ hc : c ∈ Cst, ∃ a : ↥A, c = algebraMap L F (a : L) ∧
      χ₂ ⟨c, hS₂ ▸ Subring.subset_closure (Or.inr hc)⟩ = IsLocalRing.residue ↥A a) :
    ∀ P, P ∈ D₁ ↔ (P.IsRational ∧
      (∀ f : ↥S₂, (f : F) ∈ P.toValuationSubring ∧ P.evalAt (f : F) ∈ A) ∧
      (∀ f : ↥S₂, A.valuation (P.evalAt (f : F)) < 1 ↔ χ₂ f = 0)) := by
  classical
  intro P
  constructor
  · intro hP
    obtain ⟨hrat, hS, hval⟩ := (hD P).mp hP

    have key : ∀ (x : F) (hx : x ∈ Subring.closure ((S₁ : Set F) ∪ Cst)),
        x ∈ P.toValuationSubring ∧ ∃ h : P.evalAt x ∈ A,
          IsLocalRing.residue ↥A ⟨P.evalAt x, h⟩ = χ₂ ⟨x, hS₂ ▸ hx⟩ := by
      intro x hx
      induction hx using Subring.closure_induction with
      | mem y hy =>
        rcases hy with hy | hy
        · obtain ⟨hyP, hyA⟩ := hS ⟨y, hy⟩
          refine ⟨hyP, hyA, ?_⟩

          obtain ⟨a, haS, hres, hχa⟩ := hκS₁ (χ₁ ⟨y, hy⟩)
          set g : ↥S₁ := ⟨y, hy⟩ - ⟨algebraMap L F (a : L), haS⟩ with hg
          have hχg : χ₁ g = 0 := by rw [hg, map_sub, hχa, sub_self]
          have hvg := (hval g).mpr hχg
          obtain ⟨-, hgA⟩ := hS g
          have hgval : P.evalAt (g : F) = P.evalAt y - (a : L) := by
            rw [hg]
            show P.evalAt (y - algebraMap L F (a : L)) = _
            rw [evalAt_sub_of_mem P hrat hyP (P.algebraMap_mem' _), evalAt_algebraMap_const P hrat]
          have hmem : (⟨P.evalAt (g : F), hgA⟩ : ↥A) ∈ maximalIdeal ↥A := (A.valuation_lt_one_iff _).mpr hvg
          have hsub : (⟨P.evalAt (g : F), hgA⟩ : ↥A) = ⟨P.evalAt y, hyA⟩ - a := Subtype.ext (by simpa using hgval)
          rw [hsub, ← IsLocalRing.residue_eq_zero_iff, map_sub, sub_eq_zero] at hmem
          rw [hmem, hres, ← hχ₂S ⟨y, hy⟩]
        · obtain ⟨a, rfl, hχ⟩ := hcst y hy
          refine ⟨P.algebraMap_mem' _, ?_, ?_⟩
          · rw [evalAt_algebraMap_const P hrat]; exact a.2
          · have : (⟨P.evalAt (algebraMap L F (a : L)), by rw [evalAt_algebraMap_const P hrat]; exact a.2⟩ : ↥A) = a :=
              Subtype.ext (evalAt_algebraMap_const P hrat _)
            rw [this, hχ]
      | zero =>
        have h0v : P.evalAt (0 : F) = 0 := by
          have := evalAt_algebraMap_const P hrat (0 : L); rwa [map_zero] at this
        refine ⟨zero_mem _, by rw [h0v]; exact zero_mem _, ?_⟩
        have hel : (⟨P.evalAt (0 : F), by rw [h0v]; exact zero_mem _⟩ : ↥A) = 0 := Subtype.ext h0v
        have h0 : (⟨(0 : F), hS₂ ▸ (Subring.closure ((S₁ : Set F) ∪ Cst)).zero_mem⟩ : ↥S₂) = 0 := rfl
        rw [hel, map_zero, h0, map_zero]
      | one =>
        have h1v : P.evalAt (1 : F) = 1 := Place.evalAt_one P
        refine ⟨one_mem _, by rw [h1v]; exact one_mem _, ?_⟩
        have hel : (⟨P.evalAt (1 : F), by rw [h1v]; exact one_mem _⟩ : ↥A) = 1 := Subtype.ext h1v
        have h1 : (⟨(1 : F), hS₂ ▸ (Subring.closure ((S₁ : Set F) ∪ Cst)).one_mem⟩ : ↥S₂) = 1 := rfl
        rw [hel, map_one, h1, map_one]
      | add x y hx hy ihx ihy =>
        obtain ⟨hxP, hxA, ex⟩ := ihx
        obtain ⟨hyP, hyA, ey⟩ := ihy
        have hv : P.evalAt (x + y) = P.evalAt x + P.evalAt y := evalAt_add_of_mem' P hrat hxP hyP
        refine ⟨add_mem hxP hyP, by rw [hv]; exact add_mem hxA hyA, ?_⟩
        have hel : (⟨P.evalAt (x + y), by rw [hv]; exact add_mem hxA hyA⟩ : ↥A) = ⟨_, hxA⟩ + ⟨_, hyA⟩ := Subtype.ext hv
        rw [hel, map_add, ex, ey, ← map_add]
        rfl
      | neg x hx ihx =>
        obtain ⟨hxP, hxA, ex⟩ := ihx
        have hv : P.evalAt (-x) = -P.evalAt x := evalAt_neg_of_mem' P hrat hxP
        refine ⟨neg_mem hxP, by rw [hv]; exact neg_mem hxA, ?_⟩
        have hel : (⟨P.evalAt (-x), by rw [hv]; exact neg_mem hxA⟩ : ↥A) = -⟨_, hxA⟩ := Subtype.ext hv
        rw [hel, map_neg, ex, ← map_neg]
        rfl
      | mul x y hx hy ihx ihy =>
        obtain ⟨hxP, hxA, ex⟩ := ihx
        obtain ⟨hyP, hyA, ey⟩ := ihy
        have hv : P.evalAt (x * y) = P.evalAt x * P.evalAt y := evalAt_mul_of_mem P hrat hxP hyP
        refine ⟨mul_mem hxP hyP, by rw [hv]; exact mul_mem hxA hyA, ?_⟩
        have hel : (⟨P.evalAt (x * y), by rw [hv]; exact mul_mem hxA hyA⟩ : ↥A) = ⟨_, hxA⟩ * ⟨_, hyA⟩ := Subtype.ext hv
        rw [hel, map_mul, ex, ey, ← map_mul]
        rfl
    refine ⟨hrat, fun f => ?_, fun f => ?_⟩
    · obtain ⟨h1, h2, -⟩ := key (f : F) (hS₂ ▸ f.2); exact ⟨h1, h2⟩
    · obtain ⟨-, hA, hres⟩ := key (f : F) (hS₂ ▸ f.2)
      rw [← ValuationSubring.valuation_lt_one_iff A ⟨_, hA⟩, ← IsLocalRing.residue_eq_zero_iff, hres]
  · rintro ⟨hrat, hS, hval⟩
    exact (hD P).mpr ⟨hrat, fun f => hS ⟨(f : F), hmono f.2⟩, fun f => by rw [hval ⟨(f : F), hmono f.2⟩, hχ₂S]⟩

theorem exists_finset_fraction_of_closure
    (S₁ S₂ : Subring F) (hmono : S₁ ≤ S₂) (Cst Cst₁ : Set F) (hCst : Cst₁ ⊆ Cst)
    (hS₂ : S₂ = Subring.closure ((S₁ : Set F) ∪ Cst))
    (hfg : ∃ G : Finset F, ↑G ⊆ (S₁ : Set F) ∧ ∀ f ∈ S₁, ∃ g h : F,
      g ∈ Subring.closure (↑G ∪ Cst₁) ∧ h ∈ Subring.closure (↑G ∪ Cst₁) ∧
      (∃ u : (↥S₁)ˣ, ((u : ↥S₁) : F) = h) ∧ f * h = g) :
    ∃ G : Finset F, ↑G ⊆ (S₂ : Set F) ∧ ∀ f ∈ S₂, ∃ g h : F,
      g ∈ Subring.closure (↑G ∪ Cst) ∧ h ∈ Subring.closure (↑G ∪ Cst) ∧
      (∃ u : (↥S₂)ˣ, ((u : ↥S₂) : F) = h) ∧ f * h = g := by
  classical
  obtain ⟨G, hG, hfg⟩ := hfg
  refine ⟨G, hG.trans hmono, ?_⟩
  set C : Subring F := Subring.closure (↑G ∪ Cst) with hC
  have hC₁C : Subring.closure (↑G ∪ Cst₁) ≤ C := Subring.closure_mono (Set.union_subset_union_right _ hCst)
  have hCstC : ∀ c ∈ Cst, c ∈ C := fun c hc => Subring.subset_closure (Or.inr hc)

  let ι : ↥S₁ →+* ↥S₂ := Subring.inclusion hmono
  suffices key : ∀ x : F, x ∈ Subring.closure ((S₁ : Set F) ∪ Cst) → ∃ g h : F,
      g ∈ C ∧ h ∈ C ∧ (∃ u : (↥S₂)ˣ, ((u : ↥S₂) : F) = h) ∧ x * h = g by
    intro f hf; exact key f (hS₂ ▸ hf)
  intro x hx
  induction hx using Subring.closure_induction with
  | mem y hy =>
    rcases hy with hy | hy
    · obtain ⟨g, h, hg, hh, ⟨u, hu⟩, e⟩ := hfg y hy
      exact ⟨g, h, hC₁C hg, hC₁C hh, ⟨Units.map ι u, by rw [← hu]; rfl⟩, e⟩
    · exact ⟨y, 1, hCstC y hy, one_mem _, ⟨1, rfl⟩, mul_one y⟩
  | zero => exact ⟨0, 1, zero_mem _, one_mem _, ⟨1, rfl⟩, by ring⟩
  | one => exact ⟨1, 1, one_mem _, one_mem _, ⟨1, rfl⟩, by ring⟩
  | add x y _ _ ihx ihy =>
    obtain ⟨g₁, h₁, hg₁, hh₁, ⟨u₁, hu₁⟩, e₁⟩ := ihx
    obtain ⟨g₂, h₂, hg₂, hh₂, ⟨u₂, hu₂⟩, e₂⟩ := ihy
    refine ⟨g₁ * h₂ + g₂ * h₁, h₁ * h₂, add_mem (mul_mem hg₁ hh₂) (mul_mem hg₂ hh₁), mul_mem hh₁ hh₂,
      ⟨u₁ * u₂, by rw [Units.val_mul, Subring.coe_mul, hu₁, hu₂]⟩, ?_⟩
    linear_combination h₂ * e₁ + h₁ * e₂
  | neg x _ ihx =>
    obtain ⟨g, h, hg, hh, ⟨u, hu⟩, e⟩ := ihx
    exact ⟨-g, h, neg_mem hg, hh, ⟨u, hu⟩, by linear_combination (-1 : F) * e⟩
  | mul x y _ _ ihx ihy =>
    obtain ⟨g₁, h₁, hg₁, hh₁, ⟨u₁, hu₁⟩, e₁⟩ := ihx
    obtain ⟨g₂, h₂, hg₂, hh₂, ⟨u₂, hu₂⟩, e₂⟩ := ihy
    refine ⟨g₁ * g₂, h₁ * h₂, mul_mem hg₁ hg₂, mul_mem hh₁ hh₂,
      ⟨u₁ * u₂, by rw [Units.val_mul, Subring.coe_mul, hu₁, hu₂]⟩, ?_⟩
    rw [mul_mul_mul_comm, e₁, e₂]

end L1BBC

set_option autoImplicit false

namespace L1BBC

variable {F : Type} [Field F]

theorem moduleFinite_of_coords (S₁ S₂ : Subring F) (hmono : S₁ ≤ S₂) (π : F) (e : ℕ)
    (hcoord : ∀ x : F, x ∈ S₂ ↔ ∃ c : Fin e → ↥S₁, x = ∑ j, (c j : F) * π ^ (j : ℕ)) :
    letI := (Subring.inclusion hmono).toAlgebra
    Module.Finite ↥S₁ ↥S₂ := by
  classical
  letI := (Subring.inclusion hmono).toAlgebra
  have hsmul : ∀ (c : ↥S₁) (y : ↥S₂), ((c • y : ↥S₂) : F) = (c : F) * (y : F) := fun c y => by
    rw [Algebra.smul_def]; rfl
  have hπ : ∀ j : Fin e, π ^ (j : ℕ) ∈ S₂ := by
    intro j
    refine (hcoord _).mpr ⟨fun i => if i = j then 1 else 0, ?_⟩
    rw [Finset.sum_eq_single j]
    · simp
    · intro i _ hij; simp [hij]
    · intro h; exact absurd (Finset.mem_univ j) h
  let v : Fin e → ↥S₂ := fun j => ⟨π ^ (j : ℕ), hπ j⟩
  let f : (Fin e → ↥S₁) →ₗ[↥S₁] ↥S₂ :=
    { toFun := fun c => ∑ j, c j • v j
      map_add' := fun c d => by simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
      map_smul' := fun r c => by simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.smul_sum, smul_smul] }
  have hf : Function.Surjective f := by
    rintro ⟨x, hx⟩
    obtain ⟨c, hc⟩ := (hcoord x).mp hx
    refine ⟨c, Subtype.ext ?_⟩
    show ((∑ j, c j • v j : ↥S₂) : F) = x
    rw [AddSubmonoidClass.coe_finsetSum, hc]
    exact Finset.sum_congr rfl fun j _ => hsmul _ _
  exact Module.Finite.of_surjective f hf

theorem isNoetherianRing_of_coords (S₁ S₂ : Subring F) (hmono : S₁ ≤ S₂) (π : F) (e : ℕ)
    (hcoord : ∀ x : F, x ∈ S₂ ↔ ∃ c : Fin e → ↥S₁, x = ∑ j, (c j : F) * π ^ (j : ℕ))
    (hnoeth : IsNoetherianRing ↥S₁) : IsNoetherianRing ↥S₂ := by
  letI := (Subring.inclusion hmono).toAlgebra
  haveI : Module.Finite ↥S₁ ↥S₂ := moduleFinite_of_coords S₁ S₂ hmono π e hcoord
  haveI := hnoeth
  exact Algebra.FiniteType.isNoetherianRing ↥S₁ ↥S₂

theorem forall_exists_monic_of_coords (S₁ S₂ : Subring F) (hmono : S₁ ≤ S₂) (π : F) (e : ℕ)
    (hcoord : ∀ x : F, x ∈ S₂ ↔ ∃ c : Fin e → ↥S₁, x = ∑ j, (c j : F) * π ^ (j : ℕ)) :
    ∀ x : ↥S₂, ∃ q : Polynomial ↥S₁, q.Monic ∧ (q.map (Subring.inclusion hmono)).eval x = 0 := by
  letI := (Subring.inclusion hmono).toAlgebra
  haveI : Module.Finite ↥S₁ ↥S₂ := moduleFinite_of_coords S₁ S₂ hmono π e hcoord
  intro x
  obtain ⟨q, hq, hqx⟩ := (Algebra.IsIntegral.of_finite ↥S₁ ↥S₂).isIntegral x
  refine ⟨q, hq, ?_⟩
  rw [Polynomial.eval_map]
  exact hqx

end L1BBC

namespace BDescBC

theorem mem_closure_iff_exists_coords {F : Type*} [Field F] (S₁ : Subring F) (π : F) (e : ℕ) (he : 0 < e)
    (hπe : ∃ c : Fin e → ↥S₁, π ^ e = ∑ j, (c j : F) * π ^ (j : ℕ))
    (C : Set F) (hπC : π ∈ C)
    (hC : ∀ x ∈ C, ∃ c : Fin e → ↥S₁, x = ∑ j, (c j : F) * π ^ (j : ℕ)) :
    ∀ x : F, x ∈ Subring.closure ((S₁ : Set F) ∪ C) ↔ ∃ c : Fin e → ↥S₁, x = ∑ j, (c j : F) * π ^ (j : ℕ) := by
  classical

  let P : F → Prop := fun x => ∃ c : Fin e → ↥S₁, x = ∑ j, (c j : F) * π ^ (j : ℕ)
  have hP0 : P 0 := ⟨fun _ => 0, by simp⟩
  have hPadd : ∀ {x y}, P x → P y → P (x + y) := by
    rintro x y ⟨c, rfl⟩ ⟨d, rfl⟩
    exact ⟨fun j => c j + d j, by rw [← Finset.sum_add_distrib]; simp [add_mul]⟩
  have hPneg : ∀ {x}, P x → P (-x) := by
    rintro x ⟨c, rfl⟩
    exact ⟨fun j => -c j, by rw [← Finset.sum_neg_distrib]; simp [neg_mul]⟩
  have hPsmul : ∀ (s : ↥S₁) {x}, P x → P ((s : F) * x) := by
    rintro s x ⟨c, rfl⟩
    exact ⟨fun j => s * c j, by rw [Finset.mul_sum]; simp [mul_assoc]⟩
  have hPsum : ∀ {ι : Type} (t : Finset ι) (f : ι → F), (∀ i ∈ t, P (f i)) → P (∑ i ∈ t, f i) := by
    intro ι t f hf
    induction t using Finset.induction_on with
    | empty => simpa using hP0
    | insert a t ha ih =>
      rw [Finset.sum_insert ha]
      exact hPadd (hf a (Finset.mem_insert_self a t)) (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))

  have hPpow_lt : ∀ j : ℕ, j < e → P (π ^ j) := by
    intro j hj
    refine ⟨fun i => if (i : ℕ) = j then 1 else 0, ?_⟩
    rw [Finset.sum_eq_single ⟨j, hj⟩]
    · simp
    · intro i _ hi
      have : (i : ℕ) ≠ j := fun h => hi (Fin.ext h)
      simp [this]
    · intro h; exact absurd (Finset.mem_univ _) h
  have hPmulπ : ∀ {x}, P x → P (x * π) := by
    rintro x ⟨c, rfl⟩
    rw [Finset.sum_mul]
    refine hPsum _ _ (fun j _ => ?_)
    rw [mul_assoc, ← pow_succ]
    by_cases h : (j : ℕ) + 1 < e
    · exact hPsmul (c j) (hPpow_lt _ h)
    · have : (j : ℕ) + 1 = e := by omega
      rw [this]
      obtain ⟨d, hd⟩ := hπe
      exact hPsmul (c j) ⟨d, hd⟩
  have hPpow : ∀ n : ℕ, P (π ^ n) := by
    intro n
    induction n with
    | zero => rw [pow_zero]; simpa using hPpow_lt 0 he
    | succ n ih => rw [pow_succ]; exact hPmulπ ih
  have hPmul : ∀ {x y}, P x → P y → P (x * y) := by
    rintro x y ⟨c, rfl⟩ hy
    rw [Finset.sum_mul]
    refine hPsum _ _ (fun j _ => ?_)
    rw [mul_assoc]
    refine hPsmul (c j) ?_
    obtain ⟨d, rfl⟩ := hy
    rw [Finset.mul_sum]
    refine hPsum _ _ (fun i _ => ?_)
    rw [mul_comm, mul_assoc, ← pow_add]
    exact hPsmul (d i) (hPpow _)
  have hP1 : P 1 := by simpa using hPpow 0

  let M : Subring F :=
    { carrier := {x | P x}
      mul_mem' := fun hx hy => hPmul hx hy
      one_mem' := hP1
      add_mem' := fun hx hy => hPadd hx hy
      zero_mem' := hP0
      neg_mem' := fun hx => hPneg hx }
  have hS₁M : ∀ s : F, s ∈ S₁ → P s := by
    intro s hs
    simpa using hPsmul ⟨s, hs⟩ hP1
  intro x
  constructor
  · intro hx
    have : Subring.closure ((S₁ : Set F) ∪ C) ≤ M := by
      rw [Subring.closure_le]
      rintro y (hy | hy)
      · exact hS₁M y hy
      · exact hC y hy
    exact this hx
  · rintro ⟨c, rfl⟩
    apply Subring.sum_mem
    intro j _
    apply Subring.mul_mem
    · exact Subring.subset_closure (Set.mem_union_left C (c j).2)
    · exact Subring.pow_mem _ (Subring.subset_closure (Set.mem_union_right (S₁ : Set F) hπC)) _

end BDescBC

open AlgebraicCurve IsLocalRing

set_option maxHeartbeats 6400000 in
theorem solution
    {k₀ L F : Type} [Field k₀] [Field L] [Field F] [Algebra k₀ L] [Algebra L F]
    [CharZero L] [IsAlgClosed L] [IsCurveOver L F]
    (A : ValuationSubring L)
    {Fbar : Type} [Field Fbar] [Algebra (ResidueField ↥A) Fbar]
    (R : RegularProlongation A F Fbar) (Q : Place (ResidueField ↥A) Fbar)

    (K₁ K₂ : IntermediateField k₀ L) (hK : K₁ ≤ K₂) (halg : ∀ x : L, IsAlgebraic ↥K₁ x)
    (hKfin₂ : FiniteDimensional k₀ ↥K₂)
    (A₁ : ValuationSubring ↥K₁) (hA₁ : ∀ x : ↥K₁, x ∈ A₁ ↔ (x : L) ∈ A)
    (A₂ : ValuationSubring ↥K₂) (hA₂ : ∀ x : ↥K₂, x ∈ A₂ ↔ (x : L) ∈ A)
    (hκ₁ : Function.Surjective (fun a : ↥A₁ => IsLocalRing.residue ↥A ⟨((a : ↥K₁) : L), (hA₁ a).mp a.2⟩))
    (hκ₂ : Function.Surjective (fun a : ↥A₂ => IsLocalRing.residue ↥A ⟨((a : ↥K₂) : L), (hA₂ a).mp a.2⟩))
    (hdvr₁ : IsDiscreteValuationRing ↥A₁) (hdvr₂ : IsDiscreteValuationRing ↥A₂)
    (hhens₁ : HenselianLocalRing ↥A₁) (hhens₂ : HenselianLocalRing ↥A₂)
    (ϖ₂ : ↥A₂) (hϖ₂ : maximalIdeal ↥A₂ = Ideal.span {ϖ₂}) (hϖ₂0 : ϖ₂ ≠ 0)

    (S₁ : Subring F) (φ₁ : Polynomial ↥A₁ →+* ↥S₁) (χ₁ : ↥S₁ →+* ResidueField ↥A) (D₁ : Set (Place L F))
    (hAS : ∀ a : ↥A₁, algebraMap L F ((a : ↥K₁) : L) ∈ S₁)
    (hφs : φ₁.FormallySmooth) (hφu : φ₁.FormallyUnramified)
    (hφC : ∀ a : ↥A₁, ((φ₁ (Polynomial.C a) : ↥S₁) : F) = algebraMap L F ((a : ↥K₁) : L))
    (hχC : ∀ a : ↥A₁, χ₁ (φ₁ (Polynomial.C a)) = IsLocalRing.residue ↥A ⟨((a : ↥K₁) : L), (hA₁ a).mp a.2⟩)
    (hχt : χ₁ (φ₁ Polynomial.X) = 0)
    (hchart : ∀ c : ↥A₁, IsLocalRing.residue ↥A ⟨((c : ↥K₁) : L), (hA₁ c).mp c.2⟩ = 0 →
      ∃! χ : ↥S₁ →+* ↥A₁, (∀ a : ↥A₁, χ (φ₁ (Polynomial.C a)) = a) ∧
        (∀ f : ↥S₁, IsLocalRing.residue ↥A ⟨((χ f : ↥K₁) : L), (hA₁ _).mp (χ f).2⟩ = χ₁ f) ∧ χ (φ₁ Polynomial.X) = c)
    (hker : ∀ χ : ↥S₁ →+* ↥A₁, (∀ a : ↥A₁, χ (φ₁ (Polynomial.C a)) = a) →
      (∀ f : ↥S₁, IsLocalRing.residue ↥A ⟨((χ f : ↥K₁) : L), (hA₁ _).mp (χ f).2⟩ = χ₁ f) →
      RingHom.ker χ = Ideal.span {φ₁ Polynomial.X - φ₁ (Polynomial.C (χ (φ₁ Polynomial.X)))})
    (hres : ∀ f : ↥S₁, ∃ hR : (f : F) ∈ R.integers, ∃ hm : R.residue ⟨(f : F), hR⟩ ∈ Q.toValuationSubring,
      IsLocalRing.residue ↥Q.toValuationSubring ⟨R.residue ⟨(f : F), hR⟩, hm⟩ =
        algebraMap (ResidueField ↥A) Q.ResidueField (χ₁ f))
    (hordQ : ∃ hR : ((φ₁ Polynomial.X : ↥S₁) : F) ∈ R.integers,
      Q.ord (R.residue ⟨((φ₁ Polynomial.X : ↥S₁) : F), hR⟩) = 1)
    (hD : ∀ P, P ∈ D₁ ↔ (P.IsRational ∧
      (∀ f : ↥S₁, (f : F) ∈ P.toValuationSubring ∧ P.evalAt (f : F) ∈ A) ∧
      (∀ f : ↥S₁, A.valuation (P.evalAt (f : F)) < 1 ↔ χ₁ f = 0)))
    (ht : ∀ c : ↥A₁, φ₁ Polynomial.X ≠ φ₁ (Polynomial.C c))
    (hlocal : IsLocalRing ↥S₁) (hmax : ∀ f : ↥S₁, f ∈ maximalIdeal ↥S₁ ↔ χ₁ f = 0)
    (hnoeth : IsNoetherianRing ↥S₁) (hufd : UniqueFactorizationMonoid ↥S₁)
    (ϖ : ↥A₁) (hϖ : maximalIdeal ↥A₁ = Ideal.span {ϖ}) (hϖ0 : ϖ ≠ 0)
    (hprime : Prime (φ₁ (Polynomial.C ϖ)))
    (hbranch : ∀ p : ↥S₁, Prime p → ¬ Associated p (φ₁ (Polynomial.C ϖ)) →
      ∀ x : ↥S₁, ∃ r : Polynomial ↥A₁, r.Monic ∧ p ∣ (r.map (φ₁.comp Polynomial.C)).eval x)
    (hfg : ∃ G : Finset F, ↑G ⊆ (S₁ : Set F) ∧ ∀ f ∈ S₁, ∃ g h : F,
      g ∈ Subring.closure (↑G ∪ ((fun a : ↥A₁ => algebraMap L F ((a : ↥K₁) : L)) '' Set.univ)) ∧
      h ∈ Subring.closure (↑G ∪ ((fun a : ↥A₁ => algebraMap L F ((a : ↥K₁) : L)) '' Set.univ)) ∧
      (∃ u : (↥S₁)ˣ, ((u : ↥S₁) : F) = h) ∧ f * h = g) :
    letI : Algebra k₀ F := ((algebraMap L F).comp (algebraMap k₀ L)).toAlgebra
    ∀ (F₀ : IntermediateField k₀ F)
      (hgen : IntermediateField.adjoin k₀ (Set.range (algebraMap L F)) ⊔ F₀ = ⊤)
      (hS₁F₁ : ∀ f : F, f ∈ S₁ → f ∈ IntermediateField.adjoin k₀ (⇑(algebraMap L F) '' (↑K₁ : Set L)) ⊔ F₀)
      (hfrac : ∀ f : F, f ∈ IntermediateField.adjoin k₀ (⇑(algebraMap L F) '' (↑K₁ : Set L)) ⊔ F₀ → ∃ g h : ↥S₁, (h : F) ≠ 0 ∧ f * (h : F) = (g : F))
      (hld : ∀ (m : ℕ) (c : Fin m → L) (a : Fin m → F), (∀ i, a i ∈ IntermediateField.adjoin k₀ (⇑(algebraMap L F) '' (↑K₁ : Set L)) ⊔ F₀) →
        LinearIndependent ↥K₁ c → ∑ i, algebraMap L F (c i) * a i = 0 → ∀ i, a i = 0)
      (hRint : ∀ f : F, f ∈ IntermediateField.adjoin k₀ (⇑(algebraMap L F) '' (↑K₁ : Set L)) ⊔ F₀ →
        (f ∈ R.integers ↔ ∃ g h : ↥S₁, ¬ (φ₁ (Polynomial.C ϖ) ∣ h) ∧ f * (h : F) = (g : F))),
    ∃ (S₂ : Subring F) (φ₂ : Polynomial ↥A₂ →+* ↥S₂) (χ₂ : ↥S₂ →+* ResidueField ↥A),

      (∃ hmono : S₁ ≤ S₂,
        S₂ ≤ Subring.closure ((S₁ : Set F) ∪ ((fun a : ↥A₂ => algebraMap L F ((a : ↥K₂) : L)) '' Set.univ)) ∧
        ((φ₁ Polynomial.X : ↥S₁) : F) = ((φ₂ Polynomial.X : ↥S₂) : F) ∧
        (∀ f : ↥S₁, χ₂ ⟨(f : F), hmono f.2⟩ = χ₁ f)) ∧

      (∀ a : ↥A₂, algebraMap L F ((a : ↥K₂) : L) ∈ S₂) ∧
      φ₂.FormallySmooth ∧ φ₂.FormallyUnramified ∧
      (∀ a : ↥A₂, ((φ₂ (Polynomial.C a) : ↥S₂) : F) = algebraMap L F ((a : ↥K₂) : L)) ∧
      (∀ a : ↥A₂, χ₂ (φ₂ (Polynomial.C a)) = IsLocalRing.residue ↥A ⟨((a : ↥K₂) : L), (hA₂ a).mp a.2⟩) ∧
      χ₂ (φ₂ Polynomial.X) = 0 ∧
      (∀ c : ↥A₂, IsLocalRing.residue ↥A ⟨((c : ↥K₂) : L), (hA₂ c).mp c.2⟩ = 0 →
        ∃! χ : ↥S₂ →+* ↥A₂, (∀ a : ↥A₂, χ (φ₂ (Polynomial.C a)) = a) ∧
          (∀ f : ↥S₂, IsLocalRing.residue ↥A ⟨((χ f : ↥K₂) : L), (hA₂ _).mp (χ f).2⟩ = χ₂ f) ∧ χ (φ₂ Polynomial.X) = c) ∧
      (∀ f : ↥S₂, ∃ hR : (f : F) ∈ R.integers, ∃ hm : R.residue ⟨(f : F), hR⟩ ∈ Q.toValuationSubring,
        IsLocalRing.residue ↥Q.toValuationSubring ⟨R.residue ⟨(f : F), hR⟩, hm⟩ =
          algebraMap (ResidueField ↥A) Q.ResidueField (χ₂ f)) ∧
      (∃ hR : ((φ₂ Polynomial.X : ↥S₂) : F) ∈ R.integers,
        Q.ord (R.residue ⟨((φ₂ Polynomial.X : ↥S₂) : F), hR⟩) = 1) ∧
      (∀ P, P ∈ D₁ ↔ (P.IsRational ∧
        (∀ f : ↥S₂, (f : F) ∈ P.toValuationSubring ∧ P.evalAt (f : F) ∈ A) ∧
        (∀ f : ↥S₂, A.valuation (P.evalAt (f : F)) < 1 ↔ χ₂ f = 0))) ∧
      (∀ c : ↥A₂, φ₂ Polynomial.X ≠ φ₂ (Polynomial.C c)) ∧
      (∃ _ : IsLocalRing ↥S₂, ∀ f : ↥S₂, f ∈ maximalIdeal ↥S₂ ↔ χ₂ f = 0) ∧
      IsNoetherianRing ↥S₂ ∧ UniqueFactorizationMonoid ↥S₂ ∧
      (∀ f : F, f ∈ S₂ → f ∈ IntermediateField.adjoin k₀ (⇑(algebraMap L F) '' (↑K₂ : Set L)) ⊔ F₀) ∧
      (∀ f : F, f ∈ IntermediateField.adjoin k₀ (⇑(algebraMap L F) '' (↑K₂ : Set L)) ⊔ F₀ → ∃ g h : ↥S₂, (h : F) ≠ 0 ∧ f * (h : F) = (g : F)) ∧
      Prime (φ₂ (Polynomial.C ϖ₂)) ∧
      (∀ f : F, f ∈ IntermediateField.adjoin k₀ (⇑(algebraMap L F) '' (↑K₂ : Set L)) ⊔ F₀ →
        (f ∈ R.integers ↔ ∃ g h : ↥S₂, ¬ (φ₂ (Polynomial.C ϖ₂) ∣ h) ∧ f * (h : F) = (g : F))) ∧
      (∀ χ : ↥S₂ →+* ↥A₂, (∀ a : ↥A₂, χ (φ₂ (Polynomial.C a)) = a) →
        (∀ f : ↥S₂, IsLocalRing.residue ↥A ⟨((χ f : ↥K₂) : L), (hA₂ _).mp (χ f).2⟩ = χ₂ f) →
        RingHom.ker χ = Ideal.span {φ₂ Polynomial.X - φ₂ (Polynomial.C (χ (φ₂ Polynomial.X)))}) ∧
      (∀ p : ↥S₂, Prime p → ¬ Associated p (φ₂ (Polynomial.C ϖ₂)) →
        ∀ x : ↥S₂, ∃ r : Polynomial ↥A₂, r.Monic ∧ p ∣ (r.map (φ₂.comp Polynomial.C)).eval x) ∧
      (∃ G : Finset F, ↑G ⊆ (S₂ : Set F) ∧ ∀ f ∈ S₂, ∃ g h : F,
        g ∈ Subring.closure (↑G ∪ ((fun a : ↥A₂ => algebraMap L F ((a : ↥K₂) : L)) '' Set.univ)) ∧
        h ∈ Subring.closure (↑G ∪ ((fun a : ↥A₂ => algebraMap L F ((a : ↥K₂) : L)) '' Set.univ)) ∧
        (∃ u : (↥S₂)ˣ, ((u : ↥S₂) : F) = h) ∧ f * h = g) := by
  intro F₀ hgen hS₁F₁ hfrac hld hRint
  classical
  letI : Algebra k₀ F := ((algebraMap L F).comp (algebraMap k₀ L)).toAlgebra
  haveI : IsScalarTower k₀ L F := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI := hlocal
  haveI := hdvr₁
  haveI := hdvr₂

  let cstHom : ↥A₂ →+* F := (algebraMap L F).comp ((algebraMap ↥K₂ L).comp A₂.subtype)
  let cst : ↥A₂ → F := fun a => algebraMap L F ((a : ↥K₂) : L)
  have hcstHom : ∀ a : ↥A₂, cst a = cstHom a := fun a => rfl
  let S₂ : Subring F := Subring.closure ((S₁ : Set F) ∪ (cst '' Set.univ))
  have hmono : S₁ ≤ S₂ := fun f hf => Subring.subset_closure (Or.inl hf)
  have hcst : ∀ a : ↥A₂, cst a ∈ S₂ := fun a => Subring.subset_closure (Or.inr ⟨a, trivial, rfl⟩)
  have hgenS : S₂ ≤ Subring.closure ((S₁ : Set F) ∪ ((fun a : ↥A₂ => algebraMap L F ((a : ↥K₂) : L)) '' Set.univ)) :=
    le_rfl
  let c₂ : ↥A₂ →+* ↥S₂ :=
    (((algebraMap L F).comp ((algebraMap ↥K₂ L).comp A₂.subtype))).codRestrict S₂ (fun a => hcst a)
  have hc₂ : ∀ a : ↥A₂, ((c₂ a : ↥S₂) : F) = algebraMap L F ((a : ↥K₂) : L) := fun a => rfl
  let t₂ : ↥S₂ := ⟨((φ₁ Polynomial.X : ↥S₁) : F), hmono (φ₁ Polynomial.X).2⟩
  let φ₂ : Polynomial ↥A₂ →+* ↥S₂ := Polynomial.eval₂RingHom c₂ t₂
  have hφ₂C : ∀ a : ↥A₂, φ₂ (Polynomial.C a) = c₂ a := fun a => Polynomial.eval₂_C _ _
  have hφ₂X : φ₂ Polynomial.X = t₂ := Polynomial.eval₂_X _ _

  have hA₁₂ : ∀ a : ↥A₁, (IntermediateField.inclusion hK (a : ↥K₁)) ∈ A₂ := by
    intro a; rw [hA₂]; exact (hA₁ a).mp a.2
  let ι₁₂ : ↥A₁ →+* ↥A₂ := ((IntermediateField.inclusion hK).toRingHom.comp A₁.subtype).codRestrict A₂ hA₁₂
  have hι₁₂ : ∀ a : ↥A₁, (((ι₁₂ a : ↥A₂) : ↥K₂) : L) = ((a : ↥K₁) : L) := fun a => rfl
  have hcst₁ : ∀ a : ↥A₁, cst (ι₁₂ a) = ((φ₁ (Polynomial.C a) : ↥S₁) : F) := by
    intro a; rw [hφC]; rfl
  set π : F := cst ϖ₂ with hπdef

  let jA : ↥A₁ →+* ↥A := ((algebraMap ↥K₁ L).comp A₁.subtype).codRestrict A (fun x => (hA₁ x).mp x.2)
  have hjA : ∀ a : ↥A₁, jA a = ⟨((a : ↥K₁) : L), (hA₁ a).mp a.2⟩ := fun a => rfl

  have hunitA₁ : ∀ a : ↥A₁, a ∈ maximalIdeal ↥A₁ ↔ IsLocalRing.residue ↥A ⟨((a : ↥K₁) : L), (hA₁ a).mp a.2⟩ = 0 := by
    intro a
    rw [IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
      mem_nonunits_iff]
    constructor
    · intro h hu
      apply h
      have ha0 : ((a : ↥K₁) : L) ≠ 0 := by
        intro h0; rw [show (⟨((a : ↥K₁) : L), (hA₁ a).mp a.2⟩ : ↥A) = 0 from Subtype.ext h0] at hu; exact not_isUnit_zero hu
      have ha0' : (a : ↥K₁) ≠ 0 := fun h0 => ha0 (by rw [h0]; rfl)
      obtain ⟨u, hu'⟩ := hu
      have hinvA : (((a : ↥K₁) : L))⁻¹ ∈ A := by
        have e1 : (((u⁻¹ : (↥A)ˣ) : ↥A) : L) * ((u : ↥A) : L) = 1 := congrArg Subtype.val u.inv_mul
        rw [hu'] at e1
        rw [← eq_inv_of_mul_eq_one_left e1]; exact ((u⁻¹ : (↥A)ˣ) : ↥A).2
      have hinv : (a : ↥K₁)⁻¹ ∈ A₁ := by rw [hA₁]; push_cast; exact hinvA
      exact ⟨⟨a, ⟨_, hinv⟩, Subtype.ext (mul_inv_cancel₀ ha0'), Subtype.ext (inv_mul_cancel₀ ha0')⟩, rfl⟩
    · intro h hu; rw [← hjA] at h; exact h (hu.map jA)

  obtain ⟨χ₀, ⟨hχ₀a, hχ₀r, hχ₀t⟩, -⟩ := hchart 0 (by
    have : (⟨(((0 : ↥A₁) : ↥K₁) : L), (hA₁ 0).mp (0 : ↥A₁).2⟩ : ↥A) = 0 := Subtype.ext rfl
    rw [this, map_zero])
  have hkerχ₀ : RingHom.ker χ₀ = Ideal.span {φ₁ Polynomial.X} := by
    rw [hker χ₀ hχ₀a hχ₀r, hχ₀t, map_zero, map_zero, sub_zero]
  have hmSχ₀ : ∀ s : ↥S₁, s ∈ maximalIdeal ↥S₁ ↔ χ₀ s ∈ maximalIdeal ↥A₁ := by
    intro s; rw [hmax, hunitA₁, hχ₀r]
  have hmax₁gen : maximalIdeal ↥S₁ = Ideal.span {φ₁ Polynomial.X, φ₁ (Polynomial.C ϖ)} :=
    BCb.maximalIdeal_eq_span_pair_of_section (φ₁.comp Polynomial.C) χ₀ hχ₀a (φ₁ Polynomial.X) hkerχ₀ ϖ hϖ hmSχ₀

  have hEis : ∃ (e : ℕ), 0 < e ∧
      (∀ a : ↥A₂, ∃ c : Fin e → ↥A₁, a = ∑ j, ι₁₂ (c j) * ϖ₂ ^ (j : ℕ)) ∧
      (LinearIndependent ↥K₁ (fun j : Fin e => (((ϖ₂ ^ (j : ℕ) : ↥A₂) : ↥K₂) : L))) :=
    L1BhEis.exists_eisenstein A K₁ K₂ hK hKfin₂ A₁ hA₁ A₂ hA₂ hκ₁ hdvr₁ hdvr₂ hhens₁ ϖ₂ hϖ₂ hϖ₂0 hA₁₂
  obtain ⟨e, he, hcoordA, hindep⟩ := hEis

  have hcstmul : ∀ a b : ↥A₂, cst (a * b) = cst a * cst b := by intro a b; rw [hcstHom, hcstHom, hcstHom, map_mul]
  have hcstpow : ∀ (a : ↥A₂) (n : ℕ), cst (a ^ n) = cst a ^ n := by intro a n; rw [hcstHom, hcstHom, map_pow]
  have hcstsum : ∀ (c : Fin e → ↥A₁), cst (∑ j, ι₁₂ (c j) * ϖ₂ ^ (j : ℕ)) = ∑ j, ((φ₁ (Polynomial.C (c j)) : ↥S₁) : F) * π ^ (j : ℕ) := by
    intro c
    rw [hcstHom, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_mul, map_pow, ← hcstHom, ← hcstHom, ← hcst₁, hπdef]
  have hC : ∀ x ∈ cst '' Set.univ, ∃ c : Fin e → ↥S₁, x = ∑ j, (c j : F) * π ^ (j : ℕ) := by
    rintro x ⟨a, -, rfl⟩
    obtain ⟨c, hc⟩ := hcoordA a
    exact ⟨fun j => φ₁ (Polynomial.C (c j)), by rw [hc, hcstsum]⟩
  have hπe : ∃ c : Fin e → ↥S₁, π ^ e = ∑ j, (c j : F) * π ^ (j : ℕ) := by
    obtain ⟨c, hc⟩ := hcoordA (ϖ₂ ^ e)
    refine ⟨fun j => φ₁ (Polynomial.C (c j)), ?_⟩
    rw [hπdef, ← hcstpow, hc, hcstsum]
  have hcoord : ∀ x : F, x ∈ S₂ ↔ ∃ c : Fin e → ↥S₁, x = ∑ j, (c j : F) * π ^ (j : ℕ) :=
    BDescBC.mem_closure_iff_exists_coords S₁ π e he hπe (cst '' Set.univ) ⟨ϖ₂, trivial, rfl⟩ hC
  have hcoord_uniq : ∀ c c' : Fin e → ↥S₁,
      ∑ j, (c j : F) * π ^ (j : ℕ) = ∑ j, (c' j : F) * π ^ (j : ℕ) → c = c' := by
    intro c c' h
    have hπL : ∀ j : Fin e, π ^ (j : ℕ) = algebraMap L F (((ϖ₂ ^ (j : ℕ) : ↥A₂) : ↥K₂) : L) := by
      intro j; rw [hπdef, ← hcstpow]
    have h0 : ∑ j : Fin e, algebraMap L F ((((ϖ₂ ^ (j : ℕ) : ↥A₂) : ↥K₂) : L)) * (((c j : F) - (c' j : F))) = 0 := by
      rw [← sub_eq_zero] at h
      rw [← h, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [← hπL]; ring
    have := hld e _ (fun j => (c j : F) - (c' j : F)) (fun j => sub_mem (hS₁F₁ _ (c j).2) (hS₁F₁ _ (c' j).2)) hindep h0
    funext j
    exact Subtype.ext (sub_eq_zero.mp (this j))

  let π₂ : ↥S₂ := c₂ ϖ₂
  have hπ₂F : ((π₂ : ↥S₂) : F) = π := rfl
  have hS₂coe_inj : ∀ x y : ↥S₂, (x : F) = (y : F) → x = y := fun x y h => Subtype.ext h

  have hred : ∀ x : ↥S₂, ∃ s : ↥S₁, π₂ ∣ x - ⟨(s : F), hmono s.2⟩ := by
    intro x
    obtain ⟨c, hc⟩ := (hcoord x).mp x.2
    refine ⟨c ⟨0, he⟩, ?_⟩

    have hrest : ∀ j : Fin e, (j : ℕ) ≠ 0 → ((c j : F) * π ^ ((j : ℕ) - 1)) ∈ S₂ := fun j _ =>
      mul_mem (hmono (c j).2) (pow_mem (hcst ϖ₂) _)
    let y : F := ∑ j ∈ (Finset.univ : Finset (Fin e)).erase ⟨0, he⟩, (c j : F) * π ^ ((j : ℕ) - 1)
    have hyS : y ∈ S₂ := by
      refine sum_mem fun j hj => ?_
      exact mul_mem (hmono (c j).2) (pow_mem (hcst ϖ₂) _)
    refine ⟨⟨y, hyS⟩, hS₂coe_inj _ _ ?_⟩
    show (x : F) - (c ⟨0, he⟩ : F) = π * y
    rw [hc, ← Finset.sum_erase_add _ _ (Finset.mem_univ (⟨0, he⟩ : Fin e))]
    simp only [y, Finset.mul_sum, pow_zero, mul_one, add_sub_cancel_right]
    refine Finset.sum_congr rfl fun j hj => ?_
    have hj0 : (j : ℕ) ≠ 0 := fun h => (Finset.mem_erase.mp hj).1 (Fin.ext h)
    rw [mul_comm π, mul_assoc, ← pow_succ, Nat.sub_add_cancel (Nat.pos_of_ne_zero hj0)]

  have hdiv : π₂ ∣ ⟨((φ₁ (Polynomial.C ϖ) : ↥S₁) : F), hmono (φ₁ (Polynomial.C ϖ)).2⟩ := by
    have hm : ι₁₂ ϖ ∈ maximalIdeal ↥A₂ := by

      have h1 : IsLocalRing.residue ↥A ⟨((ϖ : ↥K₁) : L), (hA₁ ϖ).mp ϖ.2⟩ = 0 :=
        (hunitA₁ ϖ).mp (by rw [hϖ]; exact Ideal.mem_span_singleton_self ϖ)
      rw [IsLocalRing.residue_eq_zero_iff] at h1
      rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
      intro hu
      apply (IsLocalRing.mem_maximalIdeal _).mp h1
      let jA₂ : ↥A₂ →+* ↥A := ((algebraMap ↥K₂ L).comp A₂.subtype).codRestrict A (fun x => (hA₂ x).mp x.2)
      have : jA₂ (ι₁₂ ϖ) = ⟨((ϖ : ↥K₁) : L), (hA₁ ϖ).mp ϖ.2⟩ := Subtype.ext rfl
      rw [← this]; exact hu.map jA₂
    rw [hϖ₂, Ideal.mem_span_singleton] at hm
    obtain ⟨a', ha'⟩ := hm
    refine ⟨c₂ a', hS₂coe_inj _ _ ?_⟩
    show ((φ₁ (Polynomial.C ϖ) : ↥S₁) : F) = π * cst a'
    rw [← hcst₁, ha', hcstmul]

  have hdesc : ∀ s : ↥S₁, π₂ ∣ ⟨(s : F), hmono s.2⟩ → φ₁ (Polynomial.C ϖ) ∣ s := by
    intro s ⟨y, hy⟩
    have hyF : (s : F) = π * (y : F) := congrArg Subtype.val hy
    obtain ⟨c, hc⟩ := (hcoord y).mp y.2

    obtain ⟨a, ha⟩ := hcoordA (ϖ₂ ^ e)
    have hπe' : π ^ e = ∑ j, ((φ₁ (Polynomial.C (a j)) : ↥S₁) : F) * π ^ (j : ℕ) := by
      rw [hπdef, ← hcstpow, ha, hcstsum]

    have ha0 : a ⟨0, he⟩ ∈ maximalIdeal ↥A₁ := by
      rw [hunitA₁]

      have hsplit := ha
      rw [← Finset.sum_erase_add _ _ (Finset.mem_univ (⟨0, he⟩ : Fin e))] at hsplit
      simp only [pow_zero, mul_one] at hsplit
      have hmemA₂ : ι₁₂ (a ⟨0, he⟩) ∈ maximalIdeal ↥A₂ := by
        rw [hϖ₂]
        have : ι₁₂ (a ⟨0, he⟩) = ϖ₂ ^ e - ∑ j ∈ (Finset.univ : Finset (Fin e)).erase ⟨0, he⟩, ι₁₂ (a j) * ϖ₂ ^ (j : ℕ) := by
          rw [hsplit]; ring
        rw [this]
        refine sub_mem ?_ (sum_mem fun j hj => ?_)
        · rw [Ideal.mem_span_singleton]; exact dvd_pow_self ϖ₂ (Nat.pos_iff_ne_zero.mp he)
        · have hj0 : (j : ℕ) ≠ 0 := fun h => (Finset.mem_erase.mp hj).1 (Fin.ext h)
          rw [Ideal.mem_span_singleton]
          exact Dvd.dvd.mul_left (dvd_pow_self ϖ₂ hj0) _
      rw [IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
      intro hu
      apply (IsLocalRing.mem_maximalIdeal _).mp hmemA₂
      let jA₂ : ↥A₂ →+* ↥A := ((algebraMap ↥K₂ L).comp A₂.subtype).codRestrict A (fun x => (hA₂ x).mp x.2)

      have e2 : jA₂ (ι₁₂ (a ⟨0, he⟩)) = ⟨((a ⟨0, he⟩ : ↥K₁) : L), (hA₁ _).mp (a ⟨0, he⟩).2⟩ := Subtype.ext rfl
      rw [← e2] at hu
      obtain ⟨u, hu'⟩ := hu
      have hz0 : (((ι₁₂ (a ⟨0, he⟩) : ↥A₂) : ↥K₂)) ≠ 0 := by
        intro h0
        have : jA₂ (ι₁₂ (a ⟨0, he⟩)) = 0 := Subtype.ext (by show ((((ι₁₂ (a ⟨0, he⟩) : ↥A₂) : ↥K₂)) : L) = 0; rw [h0]; rfl)
        rw [this] at hu'; exact not_isUnit_zero ⟨u, hu'⟩
      have hinvA : ((((ι₁₂ (a ⟨0, he⟩) : ↥A₂) : ↥K₂) : L))⁻¹ ∈ A := by
        have e1 : (((u⁻¹ : (↥A)ˣ) : ↥A) : L) * ((u : ↥A) : L) = 1 := congrArg Subtype.val u.inv_mul
        rw [hu'] at e1
        show (((jA₂ (ι₁₂ (a ⟨0, he⟩)) : ↥A) : L))⁻¹ ∈ A
        rw [← eq_inv_of_mul_eq_one_left e1]; exact ((u⁻¹ : (↥A)ˣ) : ↥A).2
      have hinv : (((ι₁₂ (a ⟨0, he⟩) : ↥A₂) : ↥K₂))⁻¹ ∈ A₂ := by rw [hA₂]; push_cast; exact hinvA
      exact ⟨⟨_, ⟨_, hinv⟩, Subtype.ext (mul_inv_cancel₀ hz0), Subtype.ext (inv_mul_cancel₀ hz0)⟩, rfl⟩
    rw [hϖ, Ideal.mem_span_singleton] at ha0
    obtain ⟨a'', ha''⟩ := ha0

    obtain ⟨e', rfl⟩ : ∃ e', e = e' + 1 := ⟨e - 1, by omega⟩
    let b : Fin (e' + 1) → ↥S₁ := fun j => φ₁ (Polynomial.C (a j))
    let ylast : ↥S₁ := c (Fin.last e')
    let g : Fin e' → ↥S₁ := fun i => c i.castSucc
    let g0 : Fin (e' + 1) → ↥S₁ := Fin.cons (0 : ↥S₁) g
    let d : Fin (e' + 1) → ↥S₁ := fun j => b j * ylast + g0 j
    have hπy : π * (y : F) = ∑ j, (d j : F) * π ^ (j : ℕ) := by
      rw [hc, Finset.mul_sum]
      have step1 : ∑ j : Fin (e' + 1), π * ((c j : F) * π ^ (j : ℕ)) = ∑ j : Fin (e' + 1), (c j : F) * π ^ ((j : ℕ) + 1) := by
        refine Finset.sum_congr rfl fun j _ => ?_; ring
      rw [step1]
      have step2 : ∑ j : Fin (e' + 1), (d j : F) * π ^ (j : ℕ) =
          (ylast : F) * ∑ j : Fin (e' + 1), (b j : F) * π ^ (j : ℕ) +
          ∑ j : Fin (e' + 1), ((g0 j : ↥S₁) : F) * π ^ (j : ℕ) := by
        rw [Finset.mul_sum, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun j _ => ?_
        simp only [d]; push_cast; ring
      rw [step2, ← hπe', Fin.sum_univ_castSucc, Fin.sum_univ_succ]
      simp only [g0, Fin.cons_zero, Fin.cons_succ, Fin.coe_castSucc, Fin.val_last, Fin.val_succ, g, ylast]
      push_cast
      ring
    have hs_coord : (s : F) = ∑ j, (d j : F) * π ^ (j : ℕ) := by rw [hyF, hπy]

    let d₀ : Fin (e' + 1) → ↥S₁ := Fin.cons s (fun _ : Fin e' => (0 : ↥S₁))
    have hs_coord₀ : (s : F) = ∑ j, (d₀ j : F) * π ^ (j : ℕ) := by
      rw [Fin.sum_univ_succ]
      simp [d₀]
    have hdd := hcoord_uniq d₀ d (by rw [← hs_coord₀, ← hs_coord])
    have h0 := congrFun hdd 0
    simp only [d₀, d, g0, Fin.cons_zero, add_zero] at h0

    refine ⟨φ₁ (Polynomial.C a'') * ylast, ?_⟩
    have hb0 : b 0 = φ₁ (Polynomial.C ϖ) * φ₁ (Polynomial.C a'') := by
      show φ₁ (Polynomial.C (a 0)) = _
      have : a 0 = a ⟨0, he⟩ := rfl
      rw [this, ha'', Polynomial.C_mul, map_mul]
    rw [h0, hb0]; ring

  have hχ₂ex : ∃ χ₂ : ↥S₂ →+* ResidueField ↥A,
      (∀ f : ↥S₁, χ₂ ⟨(f : F), hmono f.2⟩ = χ₁ f) ∧
      (∀ a : ↥A₂, χ₂ (c₂ a) = IsLocalRing.residue ↥A ⟨((a : ↥K₂) : L), (hA₂ a).mp a.2⟩) := by
    let ι := algebraMap (ResidueField ↥A) Q.ResidueField
    have hιinj : Function.Injective ι := Q.algebraMap_residueField_injective

    let P : F → Prop := fun x => ∃ hx : x ∈ R.integers, ∃ hm : R.residue ⟨x, hx⟩ ∈ Q.toValuationSubring,
      ∃ z : ResidueField ↥A, IsLocalRing.residue ↥Q.toValuationSubring ⟨R.residue ⟨x, hx⟩, hm⟩ = ι z

    have hP_of : ∀ (x : F) (hx : x ∈ R.integers) (g : ↥Q.toValuationSubring) (z : ResidueField ↥A),
        (g : Fbar) = R.residue ⟨x, hx⟩ → IsLocalRing.residue ↥Q.toValuationSubring g = ι z → P x := by
      intro x hx g z hg hz
      refine ⟨hx, by rw [← hg]; exact g.2, z, ?_⟩
      have : (⟨R.residue ⟨x, hx⟩, by rw [← hg]; exact g.2⟩ : ↥Q.toValuationSubring) = g := Subtype.ext hg.symm
      rw [this, hz]
    let U : Subring F :=
      { carrier := {x | P x}
        mul_mem' := by
          rintro x y ⟨hx, hmx, zx, hzx⟩ ⟨hy, hmy, zy, hzy⟩
          refine hP_of (x * y) (mul_mem hx hy) (⟨_, hmx⟩ * ⟨_, hmy⟩) (zx * zy) ?_ ?_
          · show R.residue ⟨x, hx⟩ * R.residue ⟨y, hy⟩ = _
            rw [← map_mul]; rfl
          · rw [map_mul, hzx, hzy, map_mul]
        one_mem' := by
          refine hP_of 1 (one_mem _) 1 1 ?_ (by rw [map_one, map_one])
          show (1 : Fbar) = R.residue ⟨1, _⟩
          rw [show (⟨(1 : F), one_mem _⟩ : ↥R.integers) = 1 from rfl, map_one]
        add_mem' := by
          rintro x y ⟨hx, hmx, zx, hzx⟩ ⟨hy, hmy, zy, hzy⟩
          refine hP_of (x + y) (add_mem hx hy) (⟨_, hmx⟩ + ⟨_, hmy⟩) (zx + zy) ?_ ?_
          · show R.residue ⟨x, hx⟩ + R.residue ⟨y, hy⟩ = _
            rw [← map_add]; rfl
          · rw [map_add, hzx, hzy, map_add]
        zero_mem' := by
          refine hP_of 0 (zero_mem _) 0 0 ?_ (by rw [map_zero, map_zero])
          show (0 : Fbar) = R.residue ⟨0, _⟩
          rw [show (⟨(0 : F), zero_mem _⟩ : ↥R.integers) = 0 from rfl, map_zero]
        neg_mem' := by
          rintro x ⟨hx, hmx, zx, hzx⟩
          refine hP_of (-x) (neg_mem hx) (-⟨_, hmx⟩) (-zx) ?_ ?_
          · show -R.residue ⟨x, hx⟩ = _
            rw [← map_neg]; rfl
          · rw [map_neg, hzx, map_neg] }
    have hU : ∀ x : F, x ∈ U ↔ P x := fun x => Iff.rfl
    have hS₂U : S₂ ≤ U := by
      rw [Subring.closure_le]
      rintro x (hx | ⟨a, -, rfl⟩)
      · obtain ⟨hR, hm, hr⟩ := hres ⟨x, hx⟩
        exact (hU x).mpr ⟨hR, hm, χ₁ ⟨x, hx⟩, hr⟩
      · have hR : algebraMap L F ((a : ↥K₂) : L) ∈ R.integers := (R.algebraMap_mem_iff _).mpr ((hA₂ a).mp a.2)
        have e1 : R.residue ⟨algebraMap L F ((a : ↥K₂) : L), hR⟩ =
            algebraMap (ResidueField ↥A) Fbar (IsLocalRing.residue ↥A ⟨((a : ↥K₂) : L), (hA₂ a).mp a.2⟩) :=
          R.residue_algebraMap ⟨((a : ↥K₂) : L), (hA₂ a).mp a.2⟩
        refine (hU _).mpr (hP_of _ hR (algebraMap (ResidueField ↥A) ↥Q.toValuationSubring
          (IsLocalRing.residue ↥A ⟨((a : ↥K₂) : L), (hA₂ a).mp a.2⟩)) (IsLocalRing.residue ↥A ⟨((a : ↥K₂) : L), (hA₂ a).mp a.2⟩) ?_ ?_)
        · rw [Place.coe_algebraMap, e1]
        · first
            | rfl
            | (rw [← IsLocalRing.ResidueField.algebraMap_eq, ← IsScalarTower.algebraMap_apply])

    have hPS : ∀ f : ↥S₂, P (f : F) := fun f => (hU _).mp (hS₂U f.2)
    have hRmem : ∀ f : ↥S₂, (f : F) ∈ R.integers := fun f => (hPS f).1
    have hQmem : ∀ f : ↥S₂, R.residue ⟨(f : F), hRmem f⟩ ∈ Q.toValuationSubring := fun f => (hPS f).2.1
    let ψ : ↥S₂ → Q.ResidueField := fun f => IsLocalRing.residue ↥Q.toValuationSubring ⟨R.residue ⟨(f : F), hRmem f⟩, hQmem f⟩
    let ρ₀ : ↥S₂ →+* ↥R.integers := (S₂.subtype).codRestrict R.integers.toSubring (fun f => hRmem f)
    have hρ₀ : ∀ f : ↥S₂, ρ₀ f = ⟨(f : F), hRmem f⟩ := fun f => rfl
    let ρ : ↥S₂ →+* ↥Q.toValuationSubring :=
      (R.residue.comp ρ₀).codRestrict Q.toValuationSubring.toSubring (fun f => by
        show R.residue (ρ₀ f) ∈ Q.toValuationSubring; rw [hρ₀]; exact hQmem f)
    have hρ : ∀ f : ↥S₂, (ρ f : Fbar) = R.residue ⟨(f : F), hRmem f⟩ := fun f => rfl
    let ψh : ↥S₂ →+* Q.ResidueField := (IsLocalRing.residue ↥Q.toValuationSubring).comp ρ
    have hψh : ∀ f, ψh f = ψ f := fun f => by
      show IsLocalRing.residue ↥Q.toValuationSubring (ρ f) = _
      congr 1
    have hψconst : ∀ f : ↥S₂, ∃ z, ψ f = ι z := fun f => (hPS f).2.2
    let χfun : ↥S₂ → ResidueField ↥A := fun f => Classical.choose (hψconst f)
    have hχfun : ∀ f, ι (χfun f) = ψh f := fun f => by rw [hψh]; exact (Classical.choose_spec (hψconst f)).symm
    let χ₂ : ↥S₂ →+* ResidueField ↥A :=
      { toFun := χfun
        map_one' := hιinj (by rw [hχfun, map_one, map_one])
        map_mul' := fun f g => hιinj (by rw [hχfun, map_mul, map_mul, hχfun, hχfun])
        map_zero' := hιinj (by rw [hχfun, map_zero, map_zero])
        map_add' := fun f g => hιinj (by rw [hχfun, map_add, map_add, hχfun, hχfun]) }
    have hχ₂ : ∀ f : ↥S₂, ι (χ₂ f) = ψ f := fun f => by show ι (χfun f) = ψ f; rw [hχfun]; exact hψh f
    refine ⟨χ₂, fun f => hιinj ?_, fun a => hιinj ?_⟩
    · rw [hχ₂]
      obtain ⟨hR, hm, hr⟩ := hres f
      show IsLocalRing.residue ↥Q.toValuationSubring ⟨R.residue ⟨(f : F), _⟩, _⟩ = _
      rw [← hr]
    · rw [hχ₂]
      have hR : algebraMap L F ((a : ↥K₂) : L) ∈ R.integers := (R.algebraMap_mem_iff _).mpr ((hA₂ a).mp a.2)
      have e1 : R.residue ⟨algebraMap L F ((a : ↥K₂) : L), hR⟩ =
          algebraMap (ResidueField ↥A) Fbar (IsLocalRing.residue ↥A ⟨((a : ↥K₂) : L), (hA₂ a).mp a.2⟩) :=
        R.residue_algebraMap ⟨((a : ↥K₂) : L), (hA₂ a).mp a.2⟩
      show IsLocalRing.residue ↥Q.toValuationSubring ⟨R.residue ⟨algebraMap L F ((a : ↥K₂) : L), _⟩, _⟩ = _
      have e2 : (⟨R.residue ⟨algebraMap L F ((a : ↥K₂) : L), hRmem (c₂ a)⟩, hQmem (c₂ a)⟩ : ↥Q.toValuationSubring) =
          algebraMap (ResidueField ↥A) ↥Q.toValuationSubring (IsLocalRing.residue ↥A ⟨((a : ↥K₂) : L), (hA₂ a).mp a.2⟩) :=
        Subtype.ext (by rw [Place.coe_algebraMap]; exact e1)
      rw [e2]
      first
        | rfl
        | (rw [← IsLocalRing.ResidueField.algebraMap_eq, ← IsScalarTower.algebraMap_apply])
  obtain ⟨χ₂, hχ₂S, hχ₂c⟩ := hχ₂ex

  have hS₂eq : S₂ = Subring.closure ((S₁ : Set F) ∪ (cst '' Set.univ)) := rfl
  have hcstP : ∀ c : F, ∀ hc : c ∈ cst '' Set.univ, ∃ a : ↥A, c = algebraMap L F (a : L) ∧
      χ₂ ⟨c, hS₂eq ▸ Subring.subset_closure (Or.inr hc)⟩ = IsLocalRing.residue ↥A a := by
    rintro c ⟨a, -, rfl⟩
    refine ⟨⟨((a : ↥K₂) : L), (hA₂ a).mp a.2⟩, rfl, ?_⟩
    have : (⟨cst a, hS₂eq ▸ Subring.subset_closure (Or.inr ⟨a, trivial, rfl⟩)⟩ : ↥S₂) = c₂ a := Subtype.ext rfl
    rw [this, hχ₂c]
  have hκS₁ : ∀ z : ResidueField ↥A, ∃ a : ↥A, ∃ hc : algebraMap L F (a : L) ∈ S₁,
      IsLocalRing.residue ↥A a = z ∧ χ₁ ⟨algebraMap L F (a : L), hc⟩ = z := by
    intro z
    obtain ⟨a₁, ha₁⟩ := hκ₁ z
    refine ⟨jA a₁, hAS a₁, ha₁, ?_⟩
    have : (⟨algebraMap L F ((jA a₁ : ↥A) : L), hAS a₁⟩ : ↥S₁) = φ₁ (Polynomial.C a₁) := Subtype.ext (by rw [hφC]; rfl)
    rw [this, hχC]; exact ha₁
  have hφ₂C' : ∀ a : ↥A₂, ((φ₂ (Polynomial.C a) : ↥S₂) : F) = algebraMap L F ((a : ↥K₂) : L) := by
    intro a; rw [hφ₂C]; exact hc₂ a
  have hφ₂X' : ((φ₂ Polynomial.X : ↥S₂) : F) = ((φ₁ Polynomial.X : ↥S₁) : F) := by rw [hφ₂X]

  have hnoeth₂ : IsNoetherianRing ↥S₂ := L1BBC.isNoetherianRing_of_coords S₁ S₂ hmono π e hcoord hnoeth
  haveI := hnoeth₂
  have hint₂ : ∀ x : ↥S₂, ∃ q : Polynomial ↥S₁, q.Monic ∧ (q.map (Subring.inclusion hmono)).eval x = 0 :=
    L1BBC.forall_exists_monic_of_coords S₁ S₂ hmono π e hcoord
  have hcst₁' : ∀ a : ↥A₁, ((c₂ (ι₁₂ a) : ↥S₂) : F) = ((φ₁ (Polynomial.C a) : ↥S₁) : F) := fun a => by
    rw [hc₂]; exact hcst₁ a
  obtain ⟨hlocal₂, hmax₂, hmaxgen₂'⟩ := KFBC.isLocalRing_layer A K₁ K₂ A₁ hA₁ A₂ hA₂ ϖ hϖ hϖ0 ϖ₂ hϖ₂ ι₁₂ hι₁₂ S₁ S₂ hmono
    φ₁ χ₁ hχC hχt hmax hmax₁gen c₂ hcst₁' t₂ rfl χ₂ hχ₂S hχ₂c hκ₂ hred hint₂
  haveI := hlocal₂
  have hmaxgen₂ : maximalIdeal ↥S₂ = Ideal.span {φ₂ Polynomial.X, φ₂ (Polynomial.C ϖ₂)} := by
    rw [hφ₂X, hφ₂C]; exact hmaxgen₂'

  have hCC : ∀ a : ↥A₁, ((φ₁ (Polynomial.C a) : ↥S₁) : F) = ((φ₂ (Polynomial.C (ι₁₂ a)) : ↥S₂) : F) := by
    intro a; rw [hφ₂C, hc₂, ← hcst₁]
  have hXX : ((φ₁ Polynomial.X : ↥S₁) : F) = ((φ₂ Polynomial.X : ↥S₂) : F) := by rw [hφ₂X]
  have hππ : π = ((φ₂ (Polynomial.C ϖ₂) : ↥S₂) : F) := by rw [hφ₂C]; rfl
  obtain ⟨hφs₂, hφu₂⟩ := KFBC.formallySmooth_formallyUnramified_layer K₁ K₂ A₁ A₂ ι₁₂ hι₁₂ S₁ S₂ hmono φ₁ φ₂ hCC hXX
    e ϖ₂ π hππ hcoordA hindep hcoord hcoord_uniq hφs hφu
  have hres₂ : ∀ f : ↥S₂, ∃ hR : (f : F) ∈ R.integers, ∃ hm : R.residue ⟨(f : F), hR⟩ ∈ Q.toValuationSubring,
      IsLocalRing.residue ↥Q.toValuationSubring ⟨R.residue ⟨(f : F), hR⟩, hm⟩ =
        algebraMap (ResidueField ↥A) Q.ResidueField (χ₂ f) :=
    L1BBC.forall_residue_eq_of_closure A R Q S₁ S₂ hmono (cst '' Set.univ) hS₂eq χ₁ χ₂ hχ₂S hres hcstP
  have hD₂ : ∀ P, P ∈ D₁ ↔ (P.IsRational ∧
      (∀ f : ↥S₂, (f : F) ∈ P.toValuationSubring ∧ P.evalAt (f : F) ∈ A) ∧
      (∀ f : ↥S₂, A.valuation (P.evalAt (f : F)) < 1 ↔ χ₂ f = 0)) :=
    L1BBC.forall_mem_disc_iff_of_closure A S₁ S₂ hmono (cst '' Set.univ) hS₂eq χ₁ χ₂ hχ₂S D₁ hD hκS₁ hcstP

  have hunitA₂ : ∀ a : ↥A₂, a ∈ maximalIdeal ↥A₂ → IsLocalRing.residue ↥A ⟨((a : ↥K₂) : L), (hA₂ a).mp a.2⟩ = 0 := by
    intro a h
    rw [IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at h
    intro hu
    apply h
    have ha0 : ((a : ↥K₂) : L) ≠ 0 := by
      intro h0; rw [show (⟨((a : ↥K₂) : L), (hA₂ a).mp a.2⟩ : ↥A) = 0 from Subtype.ext h0] at hu; exact not_isUnit_zero hu
    have ha0' : (a : ↥K₂) ≠ 0 := fun h0 => ha0 (by rw [h0]; rfl)
    obtain ⟨u, hu'⟩ := hu
    have hinvA : (((a : ↥K₂) : L))⁻¹ ∈ A := by
      have e1 : (((u⁻¹ : (↥A)ˣ) : ↥A) : L) * ((u : ↥A) : L) = 1 := congrArg Subtype.val u.inv_mul
      rw [hu'] at e1
      rw [← eq_inv_of_mul_eq_one_left e1]; exact ((u⁻¹ : (↥A)ˣ) : ↥A).2
    have hinv : (a : ↥K₂)⁻¹ ∈ A₂ := by rw [hA₂]; push_cast; exact hinvA
    exact ⟨⟨a, ⟨_, hinv⟩, Subtype.ext (mul_inv_cancel₀ ha0'), Subtype.ext (inv_mul_cancel₀ ha0')⟩, rfl⟩
  have hϖ₂m : ϖ₂ ∈ maximalIdeal ↥A₂ := by rw [hϖ₂]; exact Ideal.mem_span_singleton_self ϖ₂
  have hχ₂π : χ₂ π₂ = 0 := by show χ₂ (c₂ ϖ₂) = 0; rw [hχ₂c]; exact hunitA₂ ϖ₂ hϖ₂m
  have hπ0 : π₂ ≠ 0 := by
    intro h0
    apply hϖ₂0
    have h1 : ((π₂ : ↥S₂) : F) = 0 := by rw [h0]; rfl
    rw [hπ₂F, hπdef] at h1
    have h2 : ((ϖ₂ : ↥K₂) : L) = 0 := (map_eq_zero_iff _ (algebraMap L F).injective).mp h1
    exact Subtype.ext (Subtype.ext (by rw [h2]; rfl))
  have hπnu : ¬ IsUnit π₂ := fun hu => (IsLocalRing.mem_maximalIdeal _).mp ((hmax₂ π₂).mpr hχ₂π) hu
  have hS₂O : ∀ x : ↥S₂, (x : F) ∈ R.integers := fun x => (hres₂ x).1
  have hπO : (⟨(π₂ : F), hS₂O π₂⟩ : ↥R.integers) ∈ maximalIdeal ↥R.integers := by
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    intro hu
    have hres0 : IsLocalRing.residue ↥A ⟨((ϖ₂ : ↥K₂) : L), (hA₂ ϖ₂).mp ϖ₂.2⟩ = 0 := hunitA₂ ϖ₂ hϖ₂m
    apply R.residue_ne_zero_of_isUnit hu
    have : (⟨(π₂ : F), hS₂O π₂⟩ : ↥R.integers) =
        ⟨algebraMap L F ((⟨((ϖ₂ : ↥K₂) : L), (hA₂ ϖ₂).mp ϖ₂.2⟩ : ↥A) : L), (R.algebraMap_mem_iff _).mpr ((hA₂ ϖ₂).mp ϖ₂.2)⟩ :=
      Subtype.ext rfl
    rw [this, R.residue_algebraMap, hres0, map_zero]
  have hunit₁ : ∀ s : ↥S₁, ¬ φ₁ (Polynomial.C ϖ) ∣ s → ((s : F))⁻¹ ∈ R.integers := by
    intro s hs
    have hs0 : (s : F) ≠ 0 := by
      intro h0; apply hs; rw [show s = 0 from Subtype.ext h0]; exact dvd_zero _
    refine (hRint _ (inv_mem (hS₁F₁ _ s.2))).mpr ⟨1, s, hs, ?_⟩
    rw [inv_mul_cancel₀ hs0]; rfl
  have hF₀ : ∀ f : F, f ∈ F₀ → ∃ g h : ↥S₂, (h : F) ≠ 0 ∧ f * (h : F) = (g : F) := by
    intro f hf
    obtain ⟨g, h, hh, hgh⟩ := hfrac f ((le_sup_right : F₀ ≤ _ ⊔ F₀) hf)
    exact ⟨⟨(g : F), hmono g.2⟩, ⟨(h : F), hmono h.2⟩, hh, hgh⟩
  have hS₂F₂ : ∀ f : F, f ∈ S₂ → f ∈ IntermediateField.adjoin k₀ (⇑(algebraMap L F) '' (↑K₂ : Set L)) ⊔ F₀ :=
    fun f hf => BCb.closure_le_adjoin_sup K₁ K₂ hK A₂ F₀ S₁ hS₁F₁ f hf
  have hfrac₂ : ∀ f : F, f ∈ IntermediateField.adjoin k₀ (⇑(algebraMap L F) '' (↑K₂ : Set L)) ⊔ F₀ → ∃ g h : ↥S₂, (h : F) ≠ 0 ∧ f * (h : F) = (g : F) :=
    BCb.exists_frac_of_mem_adjoin_sup K₂ A₂ F₀ S₂ hcst hF₀
  have hprimeπ : Prime π₂ :=
    BCb.prime_of_reduction_of_descent S₁ S₂ hmono (φ₁ (Polynomial.C ϖ)) hprime π₂ hπ0 hπnu hdiv hred hdesc
  have hprime₂ : Prime (φ₂ (Polynomial.C ϖ₂)) := by rw [hφ₂C]; exact hprimeπ
  have hRint₂ : ∀ f : F, f ∈ IntermediateField.adjoin k₀ (⇑(algebraMap L F) '' (↑K₂ : Set L)) ⊔ F₀ →
      (f ∈ R.integers ↔ ∃ g h : ↥S₂, ¬ (φ₂ (Polynomial.C ϖ₂) ∣ h) ∧ f * (h : F) = (g : F)) := by
    intro f hf
    rw [hφ₂C]
    exact BCb.mem_iff_exists_not_dvd_of_layer S₁ S₂ hmono R.integers hS₂O (φ₁ (Polynomial.C ϖ)) π₂ hprimeπ
      hπO hdiv hred hunit₁ f (hfrac₂ f hf)
  have hne : Ideal.span {φ₂ (Polynomial.C ϖ₂)} ≠ maximalIdeal ↥S₂ := by
    intro heq

    have ht₂m : t₂ ∈ maximalIdeal ↥S₂ := by
      rw [hmax₂]
      have : t₂ = ⟨((φ₁ Polynomial.X : ↥S₁) : F), hmono (φ₁ Polynomial.X).2⟩ := rfl
      rw [this, hχ₂S, hχt]
    rw [← heq, Ideal.mem_span_singleton, hφ₂C] at ht₂m
    have h1 : φ₁ (Polynomial.C ϖ) ∣ φ₁ Polynomial.X := hdesc (φ₁ Polynomial.X) ht₂m
    have ht0 : φ₁ Polynomial.X ≠ 0 := by
      intro h0; apply ht 0; rw [h0, map_zero, map_zero]
    have htprime : Prime (φ₁ Polynomial.X) := by
      rw [← Ideal.span_singleton_prime ht0, ← hkerχ₀]
      exact RingHom.ker_isPrime χ₀
    have h2 : φ₁ Polynomial.X ∣ φ₁ (Polynomial.C ϖ) :=
      (hprime.irreducible.dvd_symm htprime.irreducible h1)
    have h3 : φ₁ (Polynomial.C ϖ) ∈ RingHom.ker χ₀ := by
      rw [hkerχ₀, Ideal.mem_span_singleton]; exact h2
    rw [RingHom.mem_ker, hχ₀a] at h3
    exact hϖ0 h3
  have hufd₂ : UniqueFactorizationMonoid ↥S₂ :=
    (BCb.uniqueFactorizationMonoid_of_span_pair (φ₂ Polynomial.X) (φ₂ (Polynomial.C ϖ₂)) hprime₂ hmaxgen₂ hne).2.2

  have hfg₂ : ∃ G : Finset F, ↑G ⊆ (S₂ : Set F) ∧ ∀ f ∈ S₂, ∃ g h : F,
      g ∈ Subring.closure (↑G ∪ ((fun a : ↥A₂ => algebraMap L F ((a : ↥K₂) : L)) '' Set.univ)) ∧
      h ∈ Subring.closure (↑G ∪ ((fun a : ↥A₂ => algebraMap L F ((a : ↥K₂) : L)) '' Set.univ)) ∧
      (∃ u : (↥S₂)ˣ, ((u : ↥S₂) : F) = h) ∧ f * h = g := by
    have hCst : ((fun a : ↥A₁ => algebraMap L F ((a : ↥K₁) : L)) '' Set.univ) ⊆ cst '' Set.univ := by
      rintro x ⟨a, -, rfl⟩; exact ⟨ι₁₂ a, trivial, rfl⟩
    exact L1BBC.exists_finset_fraction_of_closure S₁ S₂ hmono (cst '' Set.univ) _ hCst hS₂eq hfg
  have hφf₂ : φ₂.EssFiniteType := KFBC.essFiniteType_of_fg K₂ A₂ S₂ φ₂ hφ₂C' hfg₂
  have hχC₂ : ∀ a : ↥A₂, χ₂ (φ₂ (Polynomial.C a)) = IsLocalRing.residue ↥A ⟨((a : ↥K₂) : L), (hA₂ a).mp a.2⟩ := by
    intro a; rw [hφ₂C, hχ₂c]
  have hχt₂ : χ₂ (φ₂ Polynomial.X) = 0 := by
    rw [hφ₂X]
    have : t₂ = ⟨((φ₁ Polynomial.X : ↥S₁) : F), hmono (φ₁ Polynomial.X).2⟩ := rfl
    rw [this, hχ₂S, hχt]
  obtain ⟨hchart₂, hker₂⟩ := KFBC.sections_and_ker A K₂ A₂ hA₂ hκ₂ hhens₂ S₂ φ₂ hφs₂ hφu₂ hφf₂ χ₂ hmax₂ hχC₂ hχt₂
  have ht₂ : ∀ c : ↥A₂, φ₂ Polynomial.X ≠ φ₂ (Polynomial.C c) :=
    KFBC.X_ne_C_of_linearDisjoint A K₁ K₂ A₁ hA₁ A₂ hA₂ S₁ φ₁ hφC ht
      (IntermediateField.adjoin k₀ (⇑(algebraMap L F) '' (↑K₁ : Set L)) ⊔ F₀).toSubfield
      (fun f hf => hS₁F₁ f hf) (fun m c a ha hli hs => hld m c a ha hli hs) S₂ φ₂ hφ₂X' hφ₂C'
  have hbranch₂ : ∀ p : ↥S₂, Prime p → ¬ Associated p (φ₂ (Polynomial.C ϖ₂)) →
      ∀ x : ↥S₂, ∃ r : Polynomial ↥A₂, r.Monic ∧ p ∣ (r.map (φ₂.comp Polynomial.C)).eval x :=
    KFBC.branch_baseChange A K₁ K₂ hK A₁ hA₁ A₂ hA₂ S₁ S₂ hmono φ₁ φ₂ hφC hφ₂C' ϖ hϖ ϖ₂ hϖ₂ hufd hbranch hprime₂ hint₂

  refine ⟨S₂, φ₂, χ₂, ⟨hmono, hgenS, by rw [hφ₂X], hχ₂S⟩, hcst, hφs₂, hφu₂, ?_, ?_, ?_, hchart₂, hres₂, ?_, hD₂, ht₂,
    ⟨hlocal₂, hmax₂⟩, hnoeth₂, hufd₂, hS₂F₂, hfrac₂, hprime₂, hRint₂, hker₂, hbranch₂, hfg₂⟩
  · intro a; rw [hφ₂C]; exact hc₂ a
  · intro a; rw [hφ₂C, hχ₂c]
  · rw [hφ₂X]
    have : t₂ = ⟨((φ₁ Polynomial.X : ↥S₁) : F), hmono (φ₁ Polynomial.X).2⟩ := rfl
    rw [this, hχ₂S, hχt]
  · obtain ⟨hR, hord⟩ := hordQ
    have e : ((φ₂ Polynomial.X : ↥S₂) : F) = ((φ₁ Polynomial.X : ↥S₁) : F) := by rw [hφ₂X]
    refine ⟨e ▸ hR, ?_⟩
    have : (⟨((φ₂ Polynomial.X : ↥S₂) : F), e ▸ hR⟩ : ↥R.integers) = ⟨_, hR⟩ := Subtype.ext e
    rw [this]; exact hord

end S_AlgebraicCurve_RegularProlongation_exists_smoothPointStalk_baseChange_layer
end P2MW
export P2MW.S_AlgebraicCurve_RegularProlongation_exists_smoothPointStalk_baseChange_layer (solution)

-- Prove2me | solution 1 for Algebra.TensorProduct.exists_mem_minimalPrimes_ne_and_le_of_mul_eq_pow_of_tmul_mem
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/3ccfc078-7c2e-5508-8c1d-d30513b256a6

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Algebra_TensorProduct_exists_mem_minimalPrimes_ne_and_le_of_mul_eq_pow_of_tmul_mem

set_option autoImplicit false

open scoped TensorProduct

namespace CrossLiftAux

universe u v w

theorem exists_minimalPrimes_le_not_mem {T : Type u} [CommRing T] [IsReduced T] (𝔮 : Ideal T) [𝔮.IsPrime] (c : T)
    (hAnn : ∀ u, u * c = 0 → u ∈ 𝔮) : ∃ P ∈ minimalPrimes T, P ≤ 𝔮 ∧ c ∉ P := by
  let S : Submonoid T := 𝔮.primeCompl ⊔ Submonoid.powers c
  have hS : Disjoint ((⊥ : Ideal T) : Set T) (S : Set T) := by
    rw [Set.disjoint_left]
    rintro x hx hxS
    have hx0 : x = 0 := hx
    obtain ⟨y, hy, z, hz, rfl⟩ := Submonoid.mem_sup.mp hxS
    obtain ⟨m, rfl⟩ := (Submonoid.mem_powers_iff _ _).mp hz
    apply hy
    cases m with
    | zero => rw [pow_zero, mul_one] at hx0; rw [hx0]; exact 𝔮.zero_mem
    | succ m =>
      apply hAnn
      apply IsReduced.eq_zero
      refine ⟨m + 1, ?_⟩
      rw [mul_pow, pow_succ y, mul_assoc, hx0, ]
      simp
  obtain ⟨P, hP, -, hPS⟩ := Ideal.exists_le_prime_disjoint ⊥ S hS
  have hP𝔮 : P ≤ 𝔮 := fun x hx => by
    by_contra hx'
    exact Set.disjoint_left.mp hPS hx (Submonoid.mem_sup_left hx')
  have hcP : c ∉ P := fun hc => Set.disjoint_left.mp hPS hc (Submonoid.mem_sup_right (Submonoid.mem_powers c))
  haveI := hP
  obtain ⟨P₂, hP₂, hP₂P⟩ := Ideal.exists_minimalPrimes_le (show (⊥ : Ideal T) ≤ P from bot_le)
  exact ⟨P₂, hP₂, hP₂P.trans hP𝔮, fun h => hcP (hP₂P h)⟩

section B

variable {R : Type u} [CommRing R] (π : R) {𝒪 : Type v} [CommRing 𝒪] [Algebra R 𝒪] {κ : Type w} [Field κ] [Algebra R κ]

theorem one_tmul_algebraMap_mul (hπκ : algebraMap R κ π = 0) (y : 𝒪) :
    (1 : κ) ⊗ₜ[R] (algebraMap R 𝒪 π * y) = 0 := by
  rw [← Algebra.smul_def, ← TensorProduct.smul_tmul, Algebra.smul_def, mul_one, hπκ, TensorProduct.zero_tmul]

theorem one_tmul_algebraMap (r : R) :
    (1 : κ) ⊗ₜ[R] (algebraMap R 𝒪 r) = (algebraMap R κ r) ⊗ₜ[R] (1 : 𝒪) := by
  rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]

noncomputable def φκ (hπκ : algebraMap R κ π = 0) : R ⧸ Ideal.span {π} →+* κ :=
  Ideal.Quotient.lift _ (algebraMap R κ) (by
    intro a ha
    obtain ⟨r, rfl⟩ := Ideal.mem_span_singleton'.mp ha
    rw [map_mul, hπκ, mul_zero])

noncomputable def φB : R ⧸ Ideal.span {π} →+* 𝒪 ⧸ Ideal.span {algebraMap R 𝒪 π} :=
  Ideal.Quotient.lift _ ((Ideal.Quotient.mk _).comp (algebraMap R 𝒪)) (by
    intro a ha
    obtain ⟨r, rfl⟩ := Ideal.mem_span_singleton'.mp ha
    rw [RingHom.comp_apply, map_mul, Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.mul_mem_left _ _ (Ideal.subset_span rfl))

noncomputable def ρ (hπκ : algebraMap R κ π = 0) : 𝒪 ⧸ Ideal.span {algebraMap R 𝒪 π} →+* κ ⊗[R] 𝒪 :=
  Ideal.Quotient.lift _ (Algebra.TensorProduct.includeRight (R := R) (A := κ) (B := 𝒪)).toRingHom (by
    intro a ha
    obtain ⟨t, rfl⟩ := Ideal.mem_span_singleton'.mp ha
    show (1 : κ) ⊗ₜ[R] (t * algebraMap R 𝒪 π) = 0
    rw [mul_comm]
    exact one_tmul_algebraMap_mul π hπκ t)

theorem ρ_mk (hπκ : algebraMap R κ π = 0) (s : 𝒪) :
    ρ π hπκ (Ideal.Quotient.mk _ s) = (1 : κ) ⊗ₜ[R] s := rfl

theorem ρ_φB (hπκ : algebraMap R κ π = 0) (c : R ⧸ Ideal.span {π}) :
    ρ π hπκ (φB π c) = (φκ π hπκ c) ⊗ₜ[R] (1 : 𝒪) := by
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective c
  show (1 : κ) ⊗ₜ[R] (algebraMap R 𝒪 r) = (algebraMap R κ r) ⊗ₜ[R] (1 : 𝒪)
  exact one_tmul_algebraMap r

theorem exists_tmul_not_mem_and_mul_eq [(Ideal.span {π}).IsMaximal] (hπκ : algebraMap R κ π = 0)
    (𝔮 : Ideal (κ ⊗[R] 𝒪)) [𝔮.IsPrime] (x : κ ⊗[R] 𝒪) (hx : x ∉ 𝔮) (c : 𝒪)
    (hxc : x * ((1 : κ) ⊗ₜ[R] c) = 0) :
    ∃ s t : 𝒪, (1 : κ) ⊗ₜ[R] s ∉ 𝔮 ∧ s * c = algebraMap R 𝒪 π * t := by
  classical
  letI : Field (R ⧸ Ideal.span {π}) := Ideal.Quotient.field _
  letI : Algebra (R ⧸ Ideal.span {π}) κ := (φκ π hπκ).toAlgebra
  haveI : IsScalarTower R (R ⧸ Ideal.span {π}) κ :=
    IsScalarTower.of_algebraMap_eq (fun r => (Ideal.Quotient.lift_mk (Ideal.span {π}) (algebraMap R κ) _).symm)
  let b := Module.Free.chooseBasis (R ⧸ Ideal.span {π}) κ

  have hsmul : ∀ (r : R) (a : κ), b.repr (r • a) = (Ideal.Quotient.mk (Ideal.span {π}) r) • b.repr a := by
    intro r a
    rw [← map_smul, ← IsScalarTower.algebraMap_smul (R ⧸ Ideal.span {π}) r a, Ideal.Quotient.algebraMap_eq]
  let Λ : Module.Free.ChooseBasisIndex (R ⧸ Ideal.span {π}) κ → (κ ⊗[R] 𝒪 →+ 𝒪 ⧸ Ideal.span {algebraMap R 𝒪 π}) :=
    fun j => TensorProduct.liftAddHom
      (AddMonoidHom.mk' (fun a => AddMonoidHom.mk' (fun s => φB π (b.repr a j) * Ideal.Quotient.mk _ s)
        (fun s s' => by simp only [map_add, mul_add]))
        (fun a a' => by ext s; simp only [AddMonoidHom.mk'_apply, AddMonoidHom.add_apply, map_add,
          Finsupp.add_apply, add_mul]))
      (fun r a s => by
        show φB π (b.repr (r • a) j) * Ideal.Quotient.mk _ s = φB π (b.repr a j) * Ideal.Quotient.mk _ (r • s)
        rw [hsmul, Finsupp.smul_apply, smul_eq_mul, map_mul, Algebra.smul_def, map_mul]
        have : φB π (Ideal.Quotient.mk (Ideal.span {π}) r) = Ideal.Quotient.mk _ (algebraMap R 𝒪 r) := rfl
        rw [this]; ring)
  have hΛ : ∀ j (a : κ) (s : 𝒪), Λ j (a ⊗ₜ[R] s) = φB π (b.repr a j) * Ideal.Quotient.mk _ s :=
    fun j a s => TensorProduct.liftAddHom_tmul _ _ _ _

  have hΛmul : ∀ j (y : κ ⊗[R] 𝒪), Λ j (y * ((1 : κ) ⊗ₜ[R] c)) = Λ j y * Ideal.Quotient.mk _ c := by
    intro j y
    induction y using TensorProduct.induction_on with
    | zero => rw [zero_mul, map_zero, zero_mul]
    | tmul a s => rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, hΛ, hΛ, map_mul, mul_assoc]
    | add y z hy hz => rw [add_mul, map_add, map_add, hy, hz, add_mul]

  have hterm : ∀ j (a : κ) (s : 𝒪), (b j ⊗ₜ[R] (1 : 𝒪)) * ρ π hπκ (Λ j (a ⊗ₜ[R] s)) = ((b.repr a j) • b j) ⊗ₜ[R] s := by
    intro j a s
    rw [hΛ, map_mul, ρ_φB, ρ_mk, ← mul_assoc, Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul]
    simp only [mul_one, one_mul]
    rw [Algebra.smul_def, mul_comm (b j)]
    rfl
  have hrec : ∀ y : κ ⊗[R] 𝒪, ∃ F : Finset (Module.Free.ChooseBasisIndex (R ⧸ Ideal.span {π}) κ),
      ∀ G, F ⊆ G → (∑ j ∈ G, (b j ⊗ₜ[R] (1 : 𝒪)) * ρ π hπκ (Λ j y)) = y := by
    intro y
    induction y using TensorProduct.induction_on with
    | zero => exact ⟨∅, fun G _ => by simp only [map_zero, mul_zero, Finset.sum_const_zero]⟩
    | tmul a s =>
      refine ⟨(b.repr a).support, fun G hG => ?_⟩
      simp_rw [hterm]
      rw [← TensorProduct.sum_tmul]
      congr 1
      rw [← Finset.sum_subset hG (fun j _ hj => by rw [Finsupp.notMem_support_iff.mp hj, zero_smul])]
      conv_rhs => rw [← b.linearCombination_repr a]
      rw [Finsupp.linearCombination_apply, Finsupp.sum]
    | add y z hy hz =>
      obtain ⟨Fy, hFy⟩ := hy
      obtain ⟨Fz, hFz⟩ := hz
      refine ⟨Fy ∪ Fz, fun G hG => ?_⟩
      simp_rw [map_add, mul_add]
      rw [Finset.sum_add_distrib, hFy G (Finset.union_subset_left hG), hFz G (Finset.union_subset_right hG)]

  obtain ⟨F, hF⟩ := hrec x
  have hj : ∃ j, ρ π hπκ (Λ j x) ∉ 𝔮 := by
    by_contra h
    push_neg at h
    apply hx
    rw [← hF F (Finset.Subset.refl F)]
    exact Ideal.sum_mem _ (fun j _ => Ideal.mul_mem_left _ _ (h j))
  obtain ⟨j, hj⟩ := hj
  obtain ⟨s, hs⟩ := Ideal.Quotient.mk_surjective (Λ j x)
  refine ⟨s, ?_⟩
  have hsc : Ideal.Quotient.mk (Ideal.span {algebraMap R 𝒪 π}) (s * c) = 0 := by
    rw [map_mul, hs, ← hΛmul, hxc, map_zero]
  obtain ⟨t, ht⟩ := Ideal.mem_span_singleton'.mp (Ideal.Quotient.eq_zero_iff_mem.mp hsc)
  refine ⟨t, ?_, ?_⟩
  · rw [← ρ_mk π hπκ, hs]; exact hj
  · rw [← ht, mul_comm]

end B

end CrossLiftAux

open CrossLiftAux in
theorem solution
    (R : Type*) [CommRing R] (π : R) (hπ : (Ideal.span {π}).IsMaximal)
    (𝒪 : Type*) [CommRing 𝒪] [Algebra R 𝒪] (hπ𝒪 : algebraMap R 𝒪 π ∈ nonZeroDivisors 𝒪)
    (κ : Type*) [Field κ] [Algebra R κ] (hπκ : algebraMap R κ π = 0)
    [IsReduced (κ ⊗[R] 𝒪)]
    (v v' : 𝒪) (n : ℕ) (hvv' : v * v' = algebraMap R 𝒪 π ^ n)
    (Q₀ 𝔮 : Ideal (κ ⊗[R] 𝒪)) (hQ₀ : Q₀ ∈ minimalPrimes (κ ⊗[R] 𝒪)) [𝔮.IsPrime] (hle : Q₀ ≤ 𝔮)
    (hv₀ : (1 : κ) ⊗ₜ[R] v ∉ Q₀) (hv : (1 : κ) ⊗ₜ[R] v ∈ 𝔮) :
    ∃ Q₁ ∈ minimalPrimes (κ ⊗[R] 𝒪), Q₁ ≠ Q₀ ∧ Q₁ ≤ 𝔮 := by
  haveI := hπ
  haveI hQ₀p : Q₀.IsPrime := hQ₀.1.1
  by_contra hne
  push_neg at hne

  have hkill : ∀ c ∈ Q₀, ∃ u ∉ 𝔮, u * c = 0 := by
    intro c hc
    by_contra h
    push_neg at h
    obtain ⟨P, hP, hP𝔮, hcP⟩ := exists_minimalPrimes_le_not_mem 𝔮 c (fun u hu => by
      by_contra hu'; exact h u hu' hu)
    exact hne P hP (fun hPQ => hcP (hPQ ▸ hc)) hP𝔮

  have key : ∀ (m : ℕ) (S t : 𝒪), (1 : κ) ⊗ₜ[R] S ∉ 𝔮 → S * algebraMap R 𝒪 π ^ m = t * v → False := by
    intro m
    induction m with
    | zero =>
      intro S t hS hSt
      apply hS
      rw [pow_zero, mul_one] at hSt
      have h1 : (1 : κ) ⊗ₜ[R] (t * v) = ((1 : κ) ⊗ₜ[R] t) * ((1 : κ) ⊗ₜ[R] v) := by
        rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]
      rw [hSt, h1]
      exact Ideal.mul_mem_left _ _ hv
    | succ m ih =>
      intro S t hS hSt

      have ht : (1 : κ) ⊗ₜ[R] t ∈ Q₀ := by
        have h0 : ((1 : κ) ⊗ₜ[R] t) * ((1 : κ) ⊗ₜ[R] v) ∈ Q₀ := by
          rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, ← hSt, pow_succ, mul_comm _ (algebraMap R 𝒪 π),
            ← mul_assoc, mul_comm S, mul_assoc, one_tmul_algebraMap_mul π hπκ]
          exact Q₀.zero_mem
        exact (hQ₀p.mem_or_mem h0).resolve_right hv₀
      obtain ⟨u, hu, hut⟩ := hkill _ ht
      obtain ⟨s, t', hs, hst⟩ := exists_tmul_not_mem_and_mul_eq π hπκ 𝔮 u hu t hut
      refine ih (S * s) t' ?_ ?_
      · rw [← one_mul (1 : κ), ← Algebra.TensorProduct.tmul_mul_tmul]
        exact fun h => ((inferInstance : 𝔮.IsPrime).mem_or_mem h).elim hS hs
      ·
        have h1 : (S * s * algebraMap R 𝒪 π ^ m - t' * v) * algebraMap R 𝒪 π = 0 := by
          have := congrArg (fun z => s * z) hSt
          rw [sub_mul, sub_eq_zero]
          calc S * s * algebraMap R 𝒪 π ^ m * algebraMap R 𝒪 π = s * (S * algebraMap R 𝒪 π ^ (m + 1)) := by ring
            _ = s * (t * v) := this
            _ = (s * t) * v := by ring
            _ = algebraMap R 𝒪 π * t' * v := by rw [hst]
            _ = t' * v * algebraMap R 𝒪 π := by ring
        have h2 := (mem_nonZeroDivisors_iff.mp hπ𝒪).2 _ h1
        rwa [sub_eq_zero] at h2
  refine key n 1 v' ?_ ?_
  · rw [← Algebra.TensorProduct.one_def]
    exact (inferInstance : 𝔮.IsPrime).ne_top ∘ (Ideal.eq_top_iff_one 𝔮).mpr
  · rw [one_mul, mul_comm, hvv']

end S_Algebra_TensorProduct_exists_mem_minimalPrimes_ne_and_le_of_mul_eq_pow_of_tmul_mem
end P2MW
export P2MW.S_Algebra_TensorProduct_exists_mem_minimalPrimes_ne_and_le_of_mul_eq_pow_of_tmul_mem (solution)

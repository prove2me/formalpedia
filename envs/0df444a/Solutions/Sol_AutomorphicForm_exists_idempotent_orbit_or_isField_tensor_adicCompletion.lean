-- Prove2me | solution 1 for AutomorphicForm.exists_idempotent_orbit_or_isField_tensor_adicCompletion
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/28da6018-2318-53b3-9428-55e072198d10

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_idempotent_orbit_or_isField_tensor_adicCompletion

set_option autoImplicit false

open NumberField IsDedekindDomain
open scoped TensorProduct

namespace AutomorphicForm
p2m_export "AutomorphicForm" "sigmaTensor"
namespace C2idem
p2m_open "AutomorphicForm"

namespace IdempotentOrbit

section Ind

variable {ι : Type*} [DecidableEq ι] {F : ι → Type*} [∀ i, Field (F i)]

def ind (S : Finset ι) : (Π i, F i) := fun i => if i ∈ S then 1 else 0

theorem ind_apply (S : Finset ι) (i : ι) : (ind S : Π i, F i) i = if i ∈ S then 1 else 0 := rfl

theorem ind_mul (S T : Finset ι) : (ind S : Π i, F i) * ind T = ind (S ∩ T) := by
  ext i
  by_cases hS : i ∈ S <;> by_cases hT : i ∈ T <;> simp [ind, hS, hT]

theorem isIdempotentElem_ind (S : Finset ι) : IsIdempotentElem (ind S : Π i, F i) := by
  show ind S * ind S = ind S
  rw [ind_mul, Finset.inter_self]

theorem ind_empty : (ind (∅ : Finset ι) : Π i, F i) = 0 := by
  ext i; simp [ind]

theorem ind_univ [Fintype ι] : (ind (Finset.univ : Finset ι) : Π i, F i) = 1 := by
  ext i; simp [ind]

theorem ind_injective : Function.Injective (ind (F := F)) := by
  intro S T h
  ext i
  have hi := congr_fun h i
  by_cases hS : i ∈ S <;> by_cases hT : i ∈ T <;> simp_all [ind]

theorem ind_eq_sum (S : Finset ι) : (ind S : Π i, F i) = ∑ k ∈ S, ind {k} := by
  ext i
  simp only [Finset.sum_apply, ind_apply, Finset.mem_singleton]
  rw [Finset.sum_ite_eq]

theorem ind_singleton_mul_ind_singleton {a b : ι} (h : a ≠ b) :
    (ind {a} : Π i, F i) * ind {b} = 0 := by
  ext j
  by_cases ha : j = a
  · subst ha; simp [ind, h]
  · simp [ind, ha]

theorem existsUnique_map_ind_singleton_eq_one [Fintype ι] {D : Type*} [Field D]
    (g : (Π i, F i) →+* D) : ∃! k, g (ind {k}) = 1 := by
  have h01 : ∀ k, g (ind {k}) = 0 ∨ g (ind {k}) = 1 := fun k =>
    IsIdempotentElem.iff_eq_zero_or_one.mp ((isIdempotentElem_ind {k}).map g)
  have hsum : ∑ k, g (ind {k}) = 1 := by
    rw [← map_sum, ← ind_eq_sum, ind_univ, map_one]
  obtain ⟨k, -, hk⟩ : ∃ k ∈ (Finset.univ : Finset ι), g (ind {k}) ≠ 0 :=
    Finset.exists_ne_zero_of_sum_ne_zero (by rw [hsum]; exact one_ne_zero)
  refine ⟨k, (h01 k).resolve_left hk, fun k' hk' => ?_⟩
  by_contra hne
  have h0 : g (ind {k'}) * g (ind {k}) = 0 := by
    rw [← map_mul, ind_singleton_mul_ind_singleton hne, map_zero]
  rw [hk', (h01 k).resolve_left hk, one_mul] at h0
  exact one_ne_zero h0

variable [Fintype ι]

noncomputable def kappa (t : (Π i, F i) →+* Π i, F i) (i : ι) : ι :=
  Classical.choose (existsUnique_map_ind_singleton_eq_one ((Pi.evalRingHom F i).comp t)).exists

theorem apply_ind_singleton_apply (t : (Π i, F i) →+* Π i, F i) (k i : ι) :
    t (ind {k}) i = if kappa t i = k then 1 else 0 := by
  have hu := existsUnique_map_ind_singleton_eq_one ((Pi.evalRingHom F i).comp t)
  have hspec : t (ind {kappa t i}) i = 1 := Classical.choose_spec hu.exists
  split_ifs with h
  · subst h; exact hspec
  · have h01 : t (ind {k}) i = 0 ∨ t (ind {k}) i = 1 :=
      IsIdempotentElem.iff_eq_zero_or_one.mp
        (((isIdempotentElem_ind {k}).map t).map (Pi.evalRingHom F i))
    rcases h01 with h0 | h1
    · exact h0
    · exact absurd (hu.unique h1 hspec).symm h

theorem apply_ind (t : (Π i, F i) →+* Π i, F i) (S : Finset ι) :
    t (ind S) = ind (Finset.univ.filter fun i => kappa t i ∈ S) := by
  ext i
  rw [ind_eq_sum S, map_sum, Finset.sum_apply]
  simp only [apply_ind_singleton_apply, ind_apply, Finset.mem_filter, Finset.mem_univ, true_and]
  rw [Finset.sum_ite_eq]

theorem exists_indexMap_of_iterate_eq (t : (Π i, F i) →+* Π i, F i) {n : ℕ} (hn : 0 < n)
    (htn : ∀ x, (⇑t)^[n] x = x) :
    ∃ ψ : ι → ι, (∀ m j, (⇑t)^[m] (ind {j}) = ind {ψ^[m] j}) ∧ (∀ i, ψ^[n] i = i) ∧
      (∀ S : Finset ι, (∀ i, ψ i ∈ S ↔ i ∈ S) → t (ind S) = ind S) := by
  obtain ⟨n', hn'⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩

  have hiter : ∀ (m : ℕ) (S : Finset ι),
      (⇑t)^[m] (ind S) = ind (Finset.univ.filter fun i => (kappa t)^[m] i ∈ S) := by
    intro m
    induction m with
    | zero => intro S; simp
    | succ m ih =>
      intro S
      rw [Function.iterate_succ_apply, apply_ind, ih]
      congr 1
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rw [← Function.iterate_succ_apply' (kappa t) m i, Function.iterate_succ_apply]

  have hκn : ∀ i, (kappa t)^[n] i = i := by
    intro i
    have h := hiter n {(kappa t)^[n] i}
    rw [htn] at h
    have h' := ind_injective h
    have hi : i ∈ Finset.univ.filter fun j => (kappa t)^[n] j ∈ ({(kappa t)^[n] i} : Finset ι) := by simp
    rw [← h'] at hi
    exact (Finset.mem_singleton.mp hi).symm
  refine ⟨(kappa t)^[n'], ?_, ?_, ?_⟩
  ·
    have hκψ : ∀ i, kappa t ((kappa t)^[n'] i) = i := fun i => by
      have := hκn i; rwa [hn', Function.iterate_succ_apply'] at this
    have hψκ : ∀ i, (kappa t)^[n'] (kappa t i) = i := fun i => by
      have := hκn i; rwa [hn', Function.iterate_succ_apply] at this
    have h1 : ∀ j, t (ind {j}) = ind {(kappa t)^[n'] j} := fun j => by
      rw [apply_ind]
      congr 1
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
      constructor
      · intro h; rw [← h, hψκ]
      · intro h; rw [h, hκψ]
    intro m
    induction m with
    | zero => intro j; rfl
    | succ m ih =>
      intro j
      rw [Function.iterate_succ_apply, h1, ih, ← Function.iterate_succ_apply]
  · intro i
    rw [← Function.iterate_mul, mul_comm, Function.iterate_mul]
    exact Function.iterate_fixed (hκn i) _
  · intro S hS
    have hκψ : ∀ i, kappa t ((kappa t)^[n'] i) = i := fun i => by
      have := hκn i; rwa [hn', Function.iterate_succ_apply'] at this
    rw [apply_ind]
    congr 1
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]

    have := hS (kappa t i)
    rw [show ((kappa t)^[n']) (kappa t i) = i from by
      have := hκn i; rwa [hn', Function.iterate_succ_apply] at this] at this
    exact this.symm

end Ind

section Core

variable {R : Type*} [CommRing R] {ι : Type*} {F : ι → Type*} [∀ i, Field (F i)]

def conj (φ : R ≃+* Π i, F i) (s : R →+* R) : (Π i, F i) →+* Π i, F i :=
  φ.toRingHom.comp (s.comp φ.symm.toRingHom)

theorem conj_apply (φ : R ≃+* Π i, F i) (s : R →+* R) (x : Π i, F i) :
    conj φ s x = φ (s (φ.symm x)) := rfl

theorem semiconj_conj (φ : R ≃+* Π i, F i) (s : R →+* R) :
    Function.Semiconj φ s (conj φ s) := fun a => by
  rw [conj_apply, RingEquiv.symm_apply_apply]

theorem exists_idempotent_orbit_or_isField [Finite ι] (φ : R ≃+* Π i, F i) (s : R →+* R)
    {n : ℕ} (hn : n.Prime) (hs : ∀ a, (⇑s)^[n] a = a)
    {k : Type*} [Field k] (f : k →+* R) (hfix : ∀ a, s a = a → a ∈ Set.range f) :
    (∃ e : R, IsIdempotentElem e ∧ (∀ i, 0 < i → i < n → e * (⇑s)^[i] e = 0) ∧
        (∑ i ∈ Finset.range n, (⇑s)^[i] e) = 1) ∨ IsField R := by
  classical
  letI := Fintype.ofFinite ι
  rcases isEmpty_or_nonempty ι with hι | ⟨⟨j₀⟩⟩
  ·
    haveI : Subsingleton R := φ.toEquiv.subsingleton
    exact Or.inl ⟨0, Subsingleton.elim _ _, fun _ _ _ => Subsingleton.elim _ _, Subsingleton.elim _ _⟩
  haveI : Nontrivial R := ⟨⟨φ.symm 0, φ.symm 1, fun h => by
    have := congr_fun (φ.symm.injective h) j₀; simp at this⟩⟩

  have hfix01 : ∀ a : R, IsIdempotentElem a → s a = a → a = 0 ∨ a = 1 := by
    intro a ha hsa
    obtain ⟨x, rfl⟩ := hfix a hsa
    have hx : IsIdempotentElem x := by
      apply f.injective
      rw [map_mul]; exact ha
    rcases IsIdempotentElem.iff_eq_zero_or_one.mp hx with h | h
    · exact Or.inl (by rw [h, map_zero])
    · exact Or.inr (by rw [h, map_one])

  have htn : ∀ x, (⇑(conj φ s))^[n] x = x := fun x => by
    have := (semiconj_conj φ s).iterate_right n (φ.symm x)
    rw [hs, RingEquiv.apply_symm_apply] at this
    exact this.symm
  obtain ⟨ψ, hψm, hψn, hψS⟩ := exists_indexMap_of_iterate_eq (conj φ s) hn.pos htn
  obtain ⟨n', hn'⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by have := hn.pos; omega⟩

  have hinv : ∀ S : Finset ι, (∀ i, ψ i ∈ S ↔ i ∈ S) → S = ∅ ∨ S = Finset.univ := by
    intro S hS
    have hfixS := hψS S hS
    have ha : s (φ.symm (ind S)) = φ.symm (ind S) := by
      apply φ.injective
      rw [← conj_apply, hfixS, RingEquiv.apply_symm_apply]
    rcases hfix01 _ ((isIdempotentElem_ind S).map φ.symm) ha with h0 | h1
    · left
      apply ind_injective (F := F)
      have := congrArg φ h0
      rwa [RingEquiv.apply_symm_apply, map_zero, ← ind_empty] at this
    · right
      apply ind_injective (F := F)
      have := congrArg φ h1
      rwa [RingEquiv.apply_symm_apply, map_one, ← ind_univ] at this

  set S : Finset ι := (Finset.range n).image fun m => ψ^[m] j₀ with hSdef
  have hmemS : ∀ m, ψ^[m] j₀ ∈ S := by
    intro m
    rw [hSdef, Finset.mem_image]
    refine ⟨m % n, Finset.mem_range.mpr (Nat.mod_lt m hn.pos), ?_⟩
    conv_rhs => rw [← Nat.mod_add_div m n, Function.iterate_add_apply, Function.iterate_mul]
    rw [Function.iterate_fixed (hψn j₀)]
  have hSinv : ∀ i, ψ i ∈ S ↔ i ∈ S := by
    intro i
    constructor
    · intro h
      obtain ⟨m, -, hm⟩ := Finset.mem_image.mp h
      have : i = ψ^[n' + m] j₀ := by
        rw [Function.iterate_add_apply, hm]
        have h2 := hψn i
        rw [hn', Function.iterate_succ_apply] at h2
        exact h2.symm
      rw [this]; exact hmemS _
    · intro h
      obtain ⟨m, -, hm⟩ := Finset.mem_image.mp h
      rw [← hm, ← Function.iterate_succ_apply' ψ m j₀]
      exact hmemS _
  have hSuniv : S = Finset.univ :=
    (hinv S hSinv).resolve_left (Finset.nonempty_iff_ne_empty.mp ⟨j₀, hmemS 0⟩)
  by_cases hfixpt : ψ j₀ = j₀
  ·
    right
    have hall : ∀ i : ι, i = j₀ := by
      intro i
      have hi : i ∈ S := hSuniv ▸ Finset.mem_univ i
      obtain ⟨m, -, hm⟩ := Finset.mem_image.mp hi
      rw [← hm]; exact Function.iterate_fixed hfixpt m
    letI : Unique ι := ⟨⟨j₀⟩, hall⟩
    exact MulEquiv.isField (Field.toIsField (F default))
      (φ.trans (RingEquiv.piUnique F)).toMulEquiv
  ·
    left
    have hper : Function.minimalPeriod ψ j₀ = n := by
      have hdvd : Function.minimalPeriod ψ j₀ ∣ n :=
        Function.IsPeriodicPt.minimalPeriod_dvd (hψn j₀)
      rcases (Nat.dvd_prime hn).mp hdvd with h1 | h2
      · exact absurd (Function.minimalPeriod_eq_one_iff_isFixedPt.mp h1) hfixpt
      · exact h2
    have hinj : Set.InjOn (fun m => ψ^[m] j₀) (Set.Iio n) :=
      hper ▸ Function.iterate_injOn_Iio_minimalPeriod
    have hne : ∀ i, 0 < i → i < n → j₀ ≠ ψ^[i] j₀ := by
      intro i hi0 hin h
      have : (0 : ℕ) = i := hinj (Set.mem_Iio.mpr hn.pos) (Set.mem_Iio.mpr hin) h
      omega
    refine ⟨φ.symm (ind {j₀}), (isIdempotentElem_ind {j₀}).map φ.symm, ?_, ?_⟩
    · intro i hi0 hin
      apply φ.injective
      rw [map_mul, map_zero, (semiconj_conj φ s).iterate_right i, RingEquiv.apply_symm_apply, hψm,
        ind_singleton_mul_ind_singleton (hne i hi0 hin)]
    · apply φ.injective
      rw [map_sum, map_one]
      simp_rw [(semiconj_conj φ s).iterate_right _ _, RingEquiv.apply_symm_apply, hψm]
      rw [← Finset.sum_image (f := fun k => (ind {k} : Π i, F i))
        (fun a ha b hb h => hinj (by simpa using ha) (by simpa using hb) h)]
      rw [← hSdef, hSuniv, ← ind_eq_sum, ind_univ]

end Core

end IdempotentOrbit

section SigmaTensor

variable (K L : Type) [Field K] [Field L] [Algebra K L] (A : Type) [CommRing A] [Algebra K A]

theorem sigmaTensor_tmul (σ : L ≃ₐ[K] L) (x : L) (y : A) :
    sigmaTensor K L A σ (x ⊗ₜ y) = σ x ⊗ₜ y := by
  simp [sigmaTensor]

theorem sigmaTensor_one_apply (a : L ⊗[K] A) : sigmaTensor K L A 1 a = a := by
  induction a using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul x y => rw [sigmaTensor_tmul, AlgEquiv.one_apply]
  | add x y hx hy => rw [map_add, hx, hy]

theorem sigmaTensor_mul_apply (σ τ : L ≃ₐ[K] L) (a : L ⊗[K] A) :
    sigmaTensor K L A (σ * τ) a = sigmaTensor K L A σ (sigmaTensor K L A τ a) := by
  induction a using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul x y => rw [sigmaTensor_tmul, sigmaTensor_tmul, sigmaTensor_tmul, AlgEquiv.mul_apply]
  | add x y hx hy => rw [map_add, map_add, map_add, hx, hy]

theorem sigmaTensor_iterate (σ : L ≃ₐ[K] L) (m : ℕ) (a : L ⊗[K] A) :
    (⇑(sigmaTensor K L A σ))^[m] a = sigmaTensor K L A (σ ^ m) a := by
  induction m generalizing a with
  | zero => rw [Function.iterate_zero_apply, pow_zero, sigmaTensor_one_apply]
  | succ m ih => rw [Function.iterate_succ_apply', ih, pow_succ', sigmaTensor_mul_apply]

end SigmaTensor

section PrimeDegree

variable (K L : Type) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]

theorem card_algEquiv_eq_finrank_of_prime (hdeg : (Module.finrank K L).Prime)
    (σ : L ≃ₐ[K] L) (hσ : σ ≠ 1) : Nat.card (L ≃ₐ[K] L) = Module.finrank K L := by
  have hdvd : Nat.card (L ≃ₐ[K] L) ∣ Module.finrank K L := by
    have h1 := IntermediateField.finrank_fixedField_eq_card (⊤ : Subgroup (L ≃ₐ[K] L))
    have h2 := Module.finrank_mul_finrank K
      (IntermediateField.fixedField (⊤ : Subgroup (L ≃ₐ[K] L))) L
    rw [h1, Subgroup.card_top] at h2
    exact ⟨_, h2.symm.trans (mul_comm _ _)⟩
  rcases (Nat.dvd_prime hdeg).mp hdvd with h1 | hn
  · exfalso
    apply hσ
    haveI : Subsingleton (L ≃ₐ[K] L) := (Nat.card_eq_one_iff_unique.mp h1).1
    exact Subsingleton.elim _ _
  · exact hn

theorem pow_finrank_eq_one_of_prime (hdeg : (Module.finrank K L).Prime)
    (σ : L ≃ₐ[K] L) (hσ : σ ≠ 1) : σ ^ Module.finrank K L = 1 := by
  rw [← card_algEquiv_eq_finrank_of_prime K L hdeg σ hσ]
  exact pow_card_eq_one'

theorem mem_range_algebraMap_of_prime (hdeg : (Module.finrank K L).Prime)
    (σ : L ≃ₐ[K] L) (hσ : σ ≠ 1) (x : L) (hx : σ x = x) : x ∈ (algebraMap K L).range := by
  have hcard := card_algEquiv_eq_finrank_of_prime K L hdeg σ hσ
  haveI : IsGalois K L := IsGalois.of_card_aut_eq_finrank K L hcard

  have htop : Subgroup.zpowers σ = ⊤ := by
    apply Subgroup.eq_top_of_card_eq
    rw [Nat.card_zpowers, hcard]
    have hdvd : orderOf σ ∣ Module.finrank K L := by
      rw [← hcard]; exact orderOf_dvd_natCard σ
    rcases (Nat.dvd_prime hdeg).mp hdvd with h1 | hn
    · exact absurd (orderOf_eq_one_iff.mp h1) hσ
    · exact hn
  have hpow : ∀ m : ℕ, (σ ^ m) x = x := by
    intro m
    induction m with
    | zero => rw [pow_zero, AlgEquiv.one_apply]
    | succ m ih => rw [pow_succ, AlgEquiv.mul_apply, hx, ih]
  have hall : ∀ f : L ≃ₐ[K] L, f x = x := by
    intro f
    have hf : f ∈ Subgroup.zpowers σ := htop ▸ Subgroup.mem_top f
    obtain ⟨m, rfl⟩ := (mem_powers_iff_mem_zpowers.mpr hf : f ∈ Submonoid.powers σ)
    exact hpow m
  exact RingHom.mem_range.mpr ((IsGalois.mem_range_algebraMap_iff_fixed x).mpr hall)

end PrimeDegree

end AutomorphicForm.C2idem

namespace SigmaTensorFix

variable {K L : Type*} [Field K] [Field L] [Algebra K L] {A : Type*} [CommRing A] [Algebra K A]
  (σ : L ≃ₐ[K] L)

theorem repr_map_sigma {ι : Type*} (b : Module.Basis ι K A) (a : L ⊗[K] A) (i : ι) :
    (Algebra.TensorProduct.basis L b).repr (Algebra.TensorProduct.map σ.toAlgHom (AlgHom.id K A) a) i =
      σ ((Algebra.TensorProduct.basis L b).repr a i) := by
  induction a using TensorProduct.induction_on with
  | zero => simp
  | tmul x m =>
      simp [Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.basis_repr_tmul, AlgEquiv.commutes]
  | add x y hx hy =>
      simp [map_add, hx, hy]

theorem map_sigma_eq_self_iff (hfix : ∀ x : L, σ x = x → x ∈ (algebraMap K L).range) (a : L ⊗[K] A) :
    Algebra.TensorProduct.map σ.toAlgHom (AlgHom.id K A) a = a ↔
      a ∈ Set.range (Algebra.TensorProduct.includeRight : A →ₐ[K] L ⊗[K] A) := by
  classical
  haveI : Module.Free K A := Module.Free.of_divisionRing K A
  set b := Module.Free.chooseBasis K A with hb
  set bL := Algebra.TensorProduct.basis L b with hbL
  constructor
  · intro h
    set c := bL.repr a with hc
    have hσc : ∀ i, σ (c i) = c i := by
      intro i
      rw [hc, ← repr_map_sigma σ b a i, h]
    have hk : ∀ i, ∃ k : K, algebraMap K L k = c i := fun i => by
      obtain ⟨k, hk⟩ := hfix _ (hσc i)
      exact ⟨k, hk⟩
    choose k hk using hk
    refine ⟨c.sum fun i _ => k i • b i, ?_⟩
    symm
    calc a = Finsupp.linearCombination L bL c := (bL.linearCombination_repr a).symm
      _ = c.sum (fun i x => x • bL i) := Finsupp.linearCombination_apply _ _
      _ = c.sum (fun i _ => (Algebra.TensorProduct.includeRight : A →ₐ[K] L ⊗[K] A) (k i • b i)) := by
          refine Finsupp.sum_congr (fun i _ => ?_)
          rw [hbL, Algebra.TensorProduct.basis_apply, ← hk i, algebraMap_smul,
            Algebra.TensorProduct.includeRight_apply, TensorProduct.tmul_smul]
      _ = (Algebra.TensorProduct.includeRight : A →ₐ[K] L ⊗[K] A) (c.sum fun i _ => k i • b i) := by
          rw [map_finsuppSum]
  · rintro ⟨a', rfl⟩
    rw [Algebra.TensorProduct.includeRight_apply, Algebra.TensorProduct.map_tmul]
    simp

end SigmaTensorFix

open _root_.AutomorphicForm _root_.P2MW.S_AutomorphicForm_exists_idempotent_orbit_or_isField_tensor_adicCompletion.AutomorphicForm AutomorphicForm.C2idem in

theorem solution
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (hdeg : (Module.finrank K L).Prime)
    (σ : L ≃ₐ[K] L) (hσ : σ ≠ 1)
    (v : HeightOneSpectrum (𝓞 K)) :
    (∃ e : L ⊗[K] v.adicCompletion K, IsIdempotentElem e ∧
        (∀ i, 0 < i → i < Module.finrank K L →
          e * (⇑(sigmaTensor K L (v.adicCompletion K) σ))^[i] e = 0) ∧
        (∑ i ∈ Finset.range (Module.finrank K L),
          (⇑(sigmaTensor K L (v.adicCompletion K) σ))^[i] e) = 1) ∨
      IsField (L ⊗[K] v.adicCompletion K) := by
  classical
  haveI : Finite (v.Extension (𝓞 L)) := HeightOneSpectrum.Extension.finite (𝓞 K) K L (𝓞 L) v
  have hσn : σ ^ Module.finrank K L = 1 := pow_finrank_eq_one_of_prime K L hdeg σ hσ
  have hsn : ∀ a : L ⊗[K] v.adicCompletion K,
      (⇑(sigmaTensor K L (v.adicCompletion K) σ))^[Module.finrank K L] a = a := fun a => by
    rw [sigmaTensor_iterate, hσn, sigmaTensor_one_apply]
  have hfix : ∀ a : L ⊗[K] v.adicCompletion K, sigmaTensor K L (v.adicCompletion K) σ a = a →
      a ∈ Set.range ((Algebra.TensorProduct.includeRight :
        v.adicCompletion K →ₐ[K] L ⊗[K] v.adicCompletion K).toRingHom) := fun a ha =>
    (SigmaTensorFix.map_sigma_eq_self_iff (A := v.adicCompletion K) σ
      (mem_range_algebraMap_of_prime K L hdeg σ hσ) a).mp ha
  exact IdempotentOrbit.exists_idempotent_orbit_or_isField
    (HeightOneSpectrum.adicCompletion.baseChangeAlgEquiv K L (𝓞 L) v).toRingEquiv
    (sigmaTensor K L (v.adicCompletion K) σ) hdeg hsn _ hfix

end S_AutomorphicForm_exists_idempotent_orbit_or_isField_tensor_adicCompletion
end P2MW
export P2MW.S_AutomorphicForm_exists_idempotent_orbit_or_isField_tensor_adicCompletion (solution)

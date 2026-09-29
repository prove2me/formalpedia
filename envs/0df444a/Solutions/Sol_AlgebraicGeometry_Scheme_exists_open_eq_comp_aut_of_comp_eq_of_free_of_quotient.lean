-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.exists_open_eq_comp_aut_of_comp_eq_of_free_of_quotient
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/855562ab-88ad-563c-8dfb-bb86eaeb0b34

import Mathlib
import Theorems.Thm_AlgebraicGeometry_Scheme_exists_ringAut_galois_sections_of_free_of_quotient
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_exists_open_eq_comp_aut_of_comp_eq_of_free_of_quotient

set_option autoImplicit false

universe u v

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open scoped TensorProduct
open TensorProduct

namespace CHRAux

variable {A₀ A : Type*} [CommRing A₀] [CommRing A] [Algebra A₀ A]
variable {G : Type*} [Group G]
variable (σ : G →* (A ≃+* A))

theorem σ_one_apply (x : A) : σ 1 x = x := by rw [map_one]; rfl

theorem σ_mul_apply (g h : G) (x : A) : σ (g * h) x = σ g (σ h x) := by rw [map_mul]; rfl

def σₐ (hσ : ∀ (g : G) (r : A₀), σ g (algebraMap A₀ A r) = algebraMap A₀ A r) (g : G) : A ≃ₐ[A₀] A := AlgEquiv.ofRingEquiv (f := σ g) (hσ g)

@[scoped simp] theorem σₐ_apply (hσ : ∀ (g : G) (r : A₀), σ g (algebraMap A₀ A r) = algebraMap A₀ A r) (g : G) (x : A) : σₐ σ hσ g x = σ g x := rfl

noncomputable def m (hσ : ∀ (g : G) (r : A₀), σ g (algebraMap A₀ A r) = algebraMap A₀ A r) (h : G) : A ⊗[A₀] A →ₐ[A₀] A :=
  Algebra.TensorProduct.lift (AlgHom.id A₀ A) ((σₐ σ hσ h : A ≃ₐ[A₀] A) : A →ₐ[A₀] A) (fun _ _ => Commute.all _ _)

@[scoped simp] theorem m_tmul (hσ : ∀ (g : G) (r : A₀), σ g (algebraMap A₀ A r) = algebraMap A₀ A r) (h : G) (a b : A) : m σ hσ h (a ⊗ₜ[A₀] b) = a * σ h b := by
  simp [m, Algebra.TensorProduct.lift_tmul]

noncomputable def φ (hσ : ∀ (g : G) (r : A₀), σ g (algebraMap A₀ A r) = algebraMap A₀ A r) : A ⊗[A₀] A →ₐ[A₀] (G → A) := Pi.algHom _ _ (fun h => m σ hσ h)

@[scoped simp] theorem φ_apply (hσ : ∀ (g : G) (r : A₀), σ g (algebraMap A₀ A r) = algebraMap A₀ A r) (t : A ⊗[A₀] A) (h : G) : φ σ hσ t h = m σ hσ h t := rfl

section Sep
variable [Fintype G] [DecidableEq G]

theorem exists_sep (hσ : ∀ (g : G) (r : A₀), σ g (algebraMap A₀ A r) = algebraMap A₀ A r)
    (hfree : ∀ P : Ideal A, P.IsPrime → ∀ g : G, g ≠ 1 → ∃ a : A, a - σ g a ∉ P) :
    ∃ e : A ⊗[A₀] A, ∀ h : G, m σ hσ h e = if h = 1 then 1 else 0 := by
  classical
  have key : ∀ g : G, g ≠ 1 → ∃ s : A ⊗[A₀] A, m σ hσ 1 s = 1 ∧ m σ hσ g s = 0 := by
    intro g hg
    have hI : Ideal.span (Set.range fun a : A => a - σ g a) = ⊤ := by
      by_contra hne
      obtain ⟨P, hP, hle⟩ := Ideal.exists_le_maximal _ hne
      obtain ⟨a, ha⟩ := hfree P hP.isPrime g hg
      exact ha (hle (Ideal.subset_span ⟨a, rfl⟩))
    have h1 : (1 : A) ∈ Ideal.span (Set.range fun a : A => a - σ g a) := by rw [hI]; trivial
    obtain ⟨n, u, v, huv⟩ := Submodule.mem_span_set'.mp h1
    choose a ha using fun i => (v i).2
    refine ⟨∑ i, u i ⊗ₜ[A₀] a i - (∑ i, u i * a i - 1) ⊗ₜ[A₀] (1 : A), ?_, ?_⟩
    · simp only [map_sub, map_sum, m_tmul, σ_one_apply, mul_one]
      ring
    · simp only [map_sub, map_sum, m_tmul, map_one, mul_one]
      have this : ∑ i, u i * (a i - σ g (a i)) = 1 := by
        rw [← huv]
        exact Finset.sum_congr rfl fun i _ => (congrArg (u i * ·) (ha i)).trans (smul_eq_mul _ _).symm
      have h2 : ∑ i, u i * σ g (a i) = ∑ i, u i * a i - 1 := by
        rw [← this, ← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl fun i _ => by ring
      rw [h2]; ring

  let s : G → A ⊗[A₀] A := fun g => if hg : g = 1 then 1 else (key g hg).choose
  have hs1 : ∀ g, m σ hσ 1 (s g) = 1 := by
    intro g
    by_cases hg : g = 1
    · simp [s, hg]
    · simp only [s, dif_neg hg]; exact (key g hg).choose_spec.1
  have hsg : ∀ g, g ≠ 1 → m σ hσ g (s g) = 0 := by
    intro g hg
    simp only [s, dif_neg hg]; exact (key g hg).choose_spec.2
  refine ⟨∏ g ∈ Finset.univ.erase 1, s g, fun h => ?_⟩
  rw [map_prod]
  split_ifs with hh
  · subst hh
    exact Finset.prod_eq_one fun g _ => hs1 g
  · exact Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨hh, Finset.mem_univ h⟩) (hsg h hh)

end Sep

section Main
variable [Fintype G] [DecidableEq G]

theorem key2 (S : Finset (A × A)) (hS : ∀ h : G, ∑ p ∈ S, p.1 * σ h p.2 = if h = 1 then 1 else 0) (h : G) : ∑ p ∈ S, σ h p.1 * p.2 = if h = 1 then 1 else 0 := by
  have := congrArg (σ h) (hS h⁻¹)
  rw [map_sum] at this
  simp only [RingEquiv.map_mul, ← σ_mul_apply, mul_inv_cancel, σ_one_apply, inv_eq_one] at this
  rw [this]
  split_ifs <;> simp

def Tr (c : A) : A := ∑ h, σ h c

theorem Tr_fixed (g : G) (c : A) : σ g (Tr σ c) = Tr σ c := by
  simp only [Tr, map_sum, ← σ_mul_apply]
  exact Fintype.sum_equiv (Equiv.mulLeft g) _ _ (fun _ => rfl)

noncomputable def tr (hfix : ∀ a : A, (∀ g : G, σ g a = a) → a ∈ Set.range (algebraMap A₀ A)) (c : A) : A₀ := (hfix (Tr σ c) (fun g => Tr_fixed σ g c)).choose

theorem algebraMap_tr (hfix : ∀ a : A, (∀ g : G, σ g a = a) → a ∈ Set.range (algebraMap A₀ A)) (c : A) : algebraMap A₀ A (tr σ hfix c) = Tr σ c :=
  (hfix (Tr σ c) (fun g => Tr_fixed σ g c)).choose_spec

noncomputable def trₗ (hσ : ∀ (g : G) (r : A₀), σ g (algebraMap A₀ A r) = algebraMap A₀ A r) (hinj : Function.Injective (algebraMap A₀ A)) (hfix : ∀ a : A, (∀ g : G, σ g a = a) → a ∈ Set.range (algebraMap A₀ A)) : A →ₗ[A₀] A₀ where
  toFun := tr σ hfix
  map_add' x y := hinj (by simp [algebraMap_tr, Tr, Finset.sum_add_distrib])
  map_smul' r x := hinj (by
    simp only [algebraMap_tr, Tr, smul_eq_mul, map_mul, RingHom.id_apply, Algebra.smul_def, hσ, Finset.mul_sum])

@[scoped simp] theorem trₗ_apply (hσ : ∀ (g : G) (r : A₀), σ g (algebraMap A₀ A r) = algebraMap A₀ A r) (hinj : Function.Injective (algebraMap A₀ A)) (hfix : ∀ a : A, (∀ g : G, σ g a = a) → a ∈ Set.range (algebraMap A₀ A)) (c : A) : trₗ σ hσ hinj hfix c = tr σ hfix c := rfl

theorem recon (S : Finset (A × A)) (hS : ∀ h : G, ∑ p ∈ S, p.1 * σ h p.2 = if h = 1 then 1 else 0) (hfix : ∀ a : A, (∀ g : G, σ g a = a) → a ∈ Set.range (algebraMap A₀ A)) (b : A) : ∑ p ∈ S, algebraMap A₀ A (tr σ hfix (b * p.1)) * p.2 = b := by
  simp only [algebraMap_tr, Tr, map_mul, Finset.sum_mul]
  rw [Finset.sum_comm]
  have : ∀ h : G, ∑ p ∈ S, σ h b * σ h p.1 * p.2 = σ h b * (if h = 1 then 1 else 0) := by
    intro h
    rw [← key2 σ S hS h, Finset.mul_sum]
    exact Finset.sum_congr rfl fun p _ => by ring
  simp only [this, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true, σ_one_apply]

noncomputable def coord (hσ : ∀ (g : G) (r : A₀), σ g (algebraMap A₀ A r) = algebraMap A₀ A r) (S : Finset (A × A)) (hinj : Function.Injective (algebraMap A₀ A)) (hfix : ∀ a : A, (∀ g : G, σ g a = a) → a ∈ Set.range (algebraMap A₀ A)) : A →ₗ[A₀] (S → A₀) :=
  LinearMap.pi fun p => (trₗ σ hσ hinj hfix).comp (LinearMap.mulRight A₀ p.1.1)

variable (A₀) in
noncomputable def cocoord (S : Finset (A × A)) : (S → A₀) →ₗ[A₀] A :=
  ∑ p : S, (LinearMap.toSpanSingleton A₀ A p.1.2).comp (LinearMap.proj p)

theorem cocoord_coord (hσ : ∀ (g : G) (r : A₀), σ g (algebraMap A₀ A r) = algebraMap A₀ A r) (S : Finset (A × A)) (hS : ∀ h : G, ∑ p ∈ S, p.1 * σ h p.2 = if h = 1 then 1 else 0) (hinj : Function.Injective (algebraMap A₀ A)) (hfix : ∀ a : A, (∀ g : G, σ g a = a) → a ∈ Set.range (algebraMap A₀ A)) : (cocoord A₀ S).comp (coord σ hσ S hinj hfix) = LinearMap.id := by
  ext b
  simp only [LinearMap.comp_apply, cocoord, coord, LinearMap.coe_sum, Finset.sum_apply, LinearMap.proj_apply,
    LinearMap.pi_apply, LinearMap.toSpanSingleton_apply, trₗ_apply, LinearMap.mulRight_apply, LinearMap.id_apply,
    Algebra.smul_def]
  conv_rhs => rw [← recon σ S hS hfix b]
  exact (Finset.sum_coe_sort S (fun p => algebraMap A₀ A (tr σ hfix (b * p.1)) * p.2))

theorem finite (hσ : ∀ (g : G) (r : A₀), σ g (algebraMap A₀ A r) = algebraMap A₀ A r) (S : Finset (A × A)) (hS : ∀ h : G, ∑ p ∈ S, p.1 * σ h p.2 = if h = 1 then 1 else 0) (hinj : Function.Injective (algebraMap A₀ A)) (hfix : ∀ a : A, (∀ g : G, σ g a = a) → a ∈ Set.range (algebraMap A₀ A)) : Module.Finite A₀ A :=
  Module.Finite.of_surjective (cocoord A₀ S) (fun b =>
    ⟨coord σ hσ S hinj hfix b, by
      have := congrArg (fun f => f b) (cocoord_coord σ hσ S hS hinj hfix); simpa using this⟩)

theorem projective (hσ : ∀ (g : G) (r : A₀), σ g (algebraMap A₀ A r) = algebraMap A₀ A r) (S : Finset (A × A)) (hS : ∀ h : G, ∑ p ∈ S, p.1 * σ h p.2 = if h = 1 then 1 else 0) (hinj : Function.Injective (algebraMap A₀ A)) (hfix : ∀ a : A, (∀ g : G, σ g a = a) → a ∈ Set.range (algebraMap A₀ A)) : Module.Projective A₀ A :=
  Module.Projective.of_split (coord σ hσ S hinj hfix) (cocoord A₀ S) (cocoord_coord σ hσ S hS hinj hfix)

noncomputable def ψ (S : Finset (A × A)) : (G → A) →ₗ[A₀] A ⊗[A₀] A :=
  ∑ g : G, ∑ p ∈ S, ((TensorProduct.mk A₀ A A).flip p.2).comp ((LinearMap.mulRight A₀ (σ g p.1)).comp (LinearMap.proj g))

theorem ψ_apply (S : Finset (A × A)) (c : G → A) : ψ σ S c = ∑ g : G, ∑ p ∈ S, (c g * σ g p.1) ⊗ₜ[A₀] p.2 := by
  simp [ψ, LinearMap.coe_sum]

theorem φ_ψ (hσ : ∀ (g : G) (r : A₀), σ g (algebraMap A₀ A r) = algebraMap A₀ A r) (S : Finset (A × A)) (hS : ∀ h : G, ∑ p ∈ S, p.1 * σ h p.2 = if h = 1 then 1 else 0) (c : G → A) : φ σ hσ (ψ σ S c) = c := by
  funext k
  rw [ψ_apply]
  simp only [φ_apply, map_sum, m_tmul]
  have : ∀ g : G, ∑ p ∈ S, c g * σ g p.1 * σ k p.2 = c g * (if g = k then 1 else 0) := by
    intro g
    have h1 := congrArg (σ g) (hS (g⁻¹ * k))
    rw [map_sum] at h1
    simp only [RingEquiv.map_mul, ← σ_mul_apply, mul_inv_cancel_left, inv_mul_eq_one] at h1
    have h2 : σ g (if g = k then 1 else 0) = if g = k then 1 else 0 := by split_ifs <;> simp
    rw [h2] at h1
    rw [← h1, Finset.mul_sum]
    exact Finset.sum_congr rfl fun p _ => by ring
  simp only [this, mul_ite, mul_one, mul_zero]
  simp [Finset.sum_ite_eq, Finset.sum_ite_eq']

theorem ψ_φ (hσ : ∀ (g : G) (r : A₀), σ g (algebraMap A₀ A r) = algebraMap A₀ A r) (S : Finset (A × A)) (hS : ∀ h : G, ∑ p ∈ S, p.1 * σ h p.2 = if h = 1 then 1 else 0) (hfix : ∀ a : A, (∀ g : G, σ g a = a) → a ∈ Set.range (algebraMap A₀ A)) (t : A ⊗[A₀] A) : ψ σ S (φ σ hσ t) = t := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => rw [map_add, map_add, hx, hy]
  | tmul a b =>
    rw [ψ_apply]
    simp only [φ_apply, m_tmul]
    rw [Finset.sum_comm]
    have : ∀ p ∈ S, ∑ g : G, (a * σ g b * σ g p.1) ⊗ₜ[A₀] p.2 = a ⊗ₜ[A₀] (algebraMap A₀ A (tr σ hfix (b * p.1)) * p.2) := by
      intro p _
      rw [← TensorProduct.sum_tmul]
      have : ∑ g : G, a * σ g b * σ g p.1 = (tr σ hfix (b * p.1)) • a := by
        rw [Algebra.smul_def, algebraMap_tr, Tr, mul_comm, Finset.mul_sum]
        exact Finset.sum_congr rfl fun g _ => by rw [map_mul]; ring
      rw [this, TensorProduct.smul_tmul, Algebra.smul_def]
    rw [Finset.sum_congr rfl this, ← TensorProduct.tmul_sum, recon σ S hS hfix b]

noncomputable def galois (hσ : ∀ (g : G) (r : A₀), σ g (algebraMap A₀ A r) = algebraMap A₀ A r) (S : Finset (A × A)) (hS : ∀ h : G, ∑ p ∈ S, p.1 * σ h p.2 = if h = 1 then 1 else 0) (hfix : ∀ a : A, (∀ g : G, σ g a = a) → a ∈ Set.range (algebraMap A₀ A)) : A ⊗[A₀] A ≃ₗ[A₀] (G → A) :=
  LinearEquiv.ofLinear ((φ σ hσ : A ⊗[A₀] A →ₐ[A₀] (G → A)) : A ⊗[A₀] A →ₗ[A₀] (G → A)) (ψ σ S)
    (LinearMap.ext fun c => φ_ψ σ hσ S hS c)
    (LinearMap.ext fun t => ψ_φ σ hσ S hS hfix t)

theorem galois_apply (hσ : ∀ (g : G) (r : A₀), σ g (algebraMap A₀ A r) = algebraMap A₀ A r) (S : Finset (A × A))
    (hS : ∀ h : G, ∑ p ∈ S, p.1 * σ h p.2 = if h = 1 then 1 else 0)
    (hfix : ∀ a : A, (∀ g : G, σ g a = a) → a ∈ Set.range (algebraMap A₀ A)) (t : A ⊗[A₀] A) :
    galois σ hσ S hS hfix t = φ σ hσ t := rfl

theorem φ_injective (hσ : ∀ (g : G) (r : A₀), σ g (algebraMap A₀ A r) = algebraMap A₀ A r) (S : Finset (A × A)) (hS : ∀ h : G, ∑ p ∈ S, p.1 * σ h p.2 = if h = 1 then 1 else 0) (hfix : ∀ a : A, (∀ g : G, σ g a = a) → a ∈ Set.range (algebraMap A₀ A)) : Function.Injective (φ σ hσ) := by
  intro x y hxy
  have := congrArg (ψ (A₀ := A₀) σ S) hxy
  rwa [ψ_φ σ hσ S hS hfix, ψ_φ σ hσ S hS hfix] at this

end Main

section Split
variable [Fintype G] [DecidableEq G]

theorem phi_eg (S : Finset (A × A)) (hS : ∀ h : G, ∑ p ∈ S, p.1 * σ h p.2 = if h = 1 then 1 else 0)
    (g k : G) : ∑ p ∈ S, σ g p.1 * σ k p.2 = if g = k then 1 else 0 := by
  have h1 := congrArg (σ g) (hS (g⁻¹ * k))
  rw [map_sum] at h1
  simp only [RingEquiv.map_mul, ← σ_mul_apply, mul_inv_cancel_left, inv_mul_eq_one] at h1
  have h2 : σ g (if g = k then 1 else 0) = if g = k then 1 else 0 := by split_ifs <;> simp
  rw [h2] at h1
  exact h1

theorem split (hσ : ∀ (g : G) (r : A₀), σ g (algebraMap A₀ A r) = algebraMap A₀ A r)
    (S : Finset (A × A)) (hS : ∀ h : G, ∑ p ∈ S, p.1 * σ h p.2 = if h = 1 then 1 else 0)
    (hfix : ∀ a : A, (∀ g : G, σ g a = a) → a ∈ Set.range (algebraMap A₀ A))
    {C : Type*} [CommRing C] (f₁ f₂ : A →+* C) (hagree : ∀ r : A₀, f₁ (algebraMap A₀ A r) = f₂ (algebraMap A₀ A r)) :
    ∃ ε : G → C, (∑ g, ε g = 1) ∧ ∀ (g : G) (b : A), f₂ b * ε g = f₁ (σ g b) * ε g := by
  refine ⟨fun g => ∑ p ∈ S, f₁ (σ g p.1) * f₂ p.2, ?_, ?_⟩
  ·
    have hrec := recon σ S hS hfix 1
    simp only [one_mul] at hrec
    calc ∑ g, ∑ p ∈ S, f₁ (σ g p.1) * f₂ p.2
        = ∑ p ∈ S, f₁ (Tr σ p.1) * f₂ p.2 := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun p _ => ?_
          rw [Tr, map_sum, Finset.sum_mul]
      _ = ∑ p ∈ S, f₂ (algebraMap A₀ A (tr σ hfix p.1) * p.2) := by
          refine Finset.sum_congr rfl fun p _ => ?_
          rw [← algebraMap_tr σ hfix, hagree, map_mul]
      _ = f₂ (∑ p ∈ S, algebraMap A₀ A (tr σ hfix p.1) * p.2) := by rw [map_sum]
      _ = 1 := by rw [hrec, map_one]
  · intro g b

    have hexp : ∀ p ∈ S, f₂ (b * p.2) = ∑ q ∈ S, f₁ (Tr σ (b * p.2 * q.1)) * f₂ q.2 := by
      intro p _
      conv_lhs => rw [← recon σ S hS hfix (b * p.2)]
      rw [map_sum]
      refine Finset.sum_congr rfl fun q _ => ?_
      rw [map_mul, ← hagree, algebraMap_tr]
    calc f₂ b * ∑ p ∈ S, f₁ (σ g p.1) * f₂ p.2
        = ∑ p ∈ S, f₁ (σ g p.1) * f₂ (b * p.2) := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun p _ => by rw [map_mul]; ring
      _ = ∑ p ∈ S, ∑ q ∈ S, f₁ (σ g p.1) * (f₁ (Tr σ (b * p.2 * q.1)) * f₂ q.2) := by
          refine Finset.sum_congr rfl fun p hp => ?_
          rw [hexp p hp, Finset.mul_sum]
      _ = ∑ q ∈ S, f₁ (∑ p ∈ S, σ g p.1 * Tr σ (b * p.2 * q.1)) * f₂ q.2 := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun q _ => ?_
          rw [map_sum, Finset.sum_mul]
          exact Finset.sum_congr rfl fun p _ => by rw [map_mul]; ring
      _ = ∑ q ∈ S, f₁ (σ g (b * q.1)) * f₂ q.2 := by
          refine Finset.sum_congr rfl fun q _ => ?_
          congr 2

          calc ∑ p ∈ S, σ g p.1 * Tr σ (b * p.2 * q.1)
              = ∑ h, σ h (b * q.1) * ∑ p ∈ S, σ g p.1 * σ h p.2 := by
                simp only [Tr, Finset.mul_sum, RingEquiv.map_mul]
                rw [Finset.sum_comm]
                exact Finset.sum_congr rfl fun h _ => Finset.sum_congr rfl fun p _ => by ring
            _ = σ g (b * q.1) := by
                simp only [phi_eg σ S hS, mul_ite, mul_one, mul_zero]
                simp [Finset.sum_ite_eq, Finset.sum_ite_eq']
      _ = f₁ (σ g b) * ∑ p ∈ S, f₁ (σ g p.1) * f₂ p.2 := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun p _ => by rw [RingEquiv.map_mul, map_mul]; ring

end Split

end CHRAux
p2m_reactivate "P2MW.S_AlgebraicGeometry_Scheme_exists_open_eq_comp_aut_of_comp_eq_of_free_of_quotient.CHRAux"

theorem appLE_congr_hom {X Y : Scheme.{u}} {f g : X ⟶ Y} (h : f = g) (U : Y.Opens) (V : X.Opens)
    (e : V ≤ f ⁻¹ᵁ U) (e' : V ≤ g ⁻¹ᵁ U) : f.appLE U V e = g.appLE U V e' := by
  subst h; rfl

theorem solution
    {X Y : Scheme.{u}} {G : Type v} [Group G] [Finite G] (ρ : G →* Aut X)
    (hadm : ∀ x : X, ∃ U : X.Opens, IsAffineOpen U ∧ x ∈ U ∧ ∀ g : G, (ρ g).hom ⁻¹ᵁ U = U)
    (π : X ⟶ Y) (hπ : ∀ g : G, (ρ g).hom ≫ π = π)
    (haff : IsAffineHom π) (hsurj : Function.Surjective π.base)
    (hfib : ∀ x x' : X, π.base x = π.base x' ↔ ∃ g : G, (ρ g).hom.base x = x')
    (hinj : ∀ V : Y.Opens, Function.Injective (π.app V))
    (hrange : ∀ V : Y.Opens, Set.range (π.app V) =
      {s | ∀ g : G, (ρ g).hom.appLE (π ⁻¹ᵁ V) (π ⁻¹ᵁ V) (by rw [← Scheme.Hom.comp_preimage, hπ g]) s = s})
    (hfree : ∀ (K : Type u) [Field K] (x : Spec (CommRingCat.of K) ⟶ X) (g : G), x ≫ (ρ g).hom = x → g = 1) :
    (∀ {T : Scheme.{u}} (t₁ t₂ : T ⟶ X), t₁ ≫ π = t₂ ≫ π →
      ∀ p : T, ∃ (g : G) (U : T.Opens), p ∈ U ∧ U.ι ≫ t₂ = U.ι ≫ t₁ ≫ (ρ g).hom) ∧
    (∀ {T : Scheme.{u}} (t : T ⟶ X) (g : G), Nonempty T → t ≫ (ρ g).hom = t → g = 1) := by
  classical
  haveI : Fintype G := Fintype.ofFinite G
  refine ⟨fun {T} t₁ t₂ ht p => ?_, fun {T} t g hT htg => ?_⟩
  swap
  · obtain ⟨p⟩ := hT
    exact hfree (T.residueField p) (T.fromSpecResidueField p ≫ t) g (by rw [Category.assoc, htg])

  obtain ⟨V, hV, hpV, -⟩ := Opens.isBasis_iff_nbhd.mp Y.isBasis_affineOpens (Opens.mem_top (π.base (t₁.base p)))
  obtain ⟨hU₀, σ, hσρ, hσ, hinj', hfix', hfree'⟩ :=
    AlgebraicGeometry.Scheme.exists_ringAut_galois_sections_of_free_of_quotient ρ hadm π hπ haff hsurj hfib hinj hrange hfree V hV
  letI alg : Algebra Γ(Y, V) Γ(X, π ⁻¹ᵁ V) := (π.app V).hom.toAlgebra
  obtain ⟨e, he⟩ := CHRAux.exists_sep σ hσ hfree'
  obtain ⟨S, hSe⟩ := TensorProduct.exists_finset e
  have hS : ∀ h : G, ∑ q ∈ S, q.1 * σ h q.2 = if h = 1 then 1 else 0 := by
    intro h
    rw [← he h, hSe, map_sum]
    exact Finset.sum_congr rfl fun q _ => (CHRAux.m_tmul σ hσ h q.1 q.2).symm

  have hp₁ : p ∈ t₁ ⁻¹ᵁ (π ⁻¹ᵁ V) := hpV
  have hp₂ : p ∈ t₂ ⁻¹ᵁ (π ⁻¹ᵁ V) := by
    change p ∈ (t₂ ≫ π) ⁻¹ᵁ V
    rw [← ht]; exact hpV
  obtain ⟨W, hW, hpW, hWle⟩ := Opens.isBasis_iff_nbhd.mp T.isBasis_affineOpens
    (show p ∈ t₁ ⁻¹ᵁ (π ⁻¹ᵁ V) ⊓ t₂ ⁻¹ᵁ (π ⁻¹ᵁ V) from ⟨hp₁, hp₂⟩)
  have e₁ : W ≤ t₁ ⁻¹ᵁ (π ⁻¹ᵁ V) := hWle.trans inf_le_left
  have e₂ : W ≤ t₂ ⁻¹ᵁ (π ⁻¹ᵁ V) := hWle.trans inf_le_right

  have hagree : ∀ r : Γ(Y, V), (t₁.appLE (π ⁻¹ᵁ V) W e₁).hom (algebraMap Γ(Y, V) Γ(X, π ⁻¹ᵁ V) r) =
      (t₂.appLE (π ⁻¹ᵁ V) W e₂).hom (algebraMap Γ(Y, V) Γ(X, π ⁻¹ᵁ V) r) := by
    intro r
    change (π.app V ≫ t₁.appLE (π ⁻¹ᵁ V) W e₁).hom r = (π.app V ≫ t₂.appLE (π ⁻¹ᵁ V) W e₂).hom r
    rw [Scheme.Hom.app_eq_appLE, Scheme.Hom.appLE_comp_appLE, Scheme.Hom.appLE_comp_appLE,
      appLE_congr_hom ht]
  obtain ⟨ε, hεsum, hεtw⟩ := CHRAux.split σ hσ S hS hfix' (t₁.appLE (π ⁻¹ᵁ V) W e₁).hom (t₂.appLE (π ⁻¹ᵁ V) W e₂).hom hagree

  have hspan : Ideal.span (Set.range ε) = ⊤ := by
    rw [Ideal.eq_top_iff_one, ← hεsum]
    exact Ideal.sum_mem _ fun g _ => Ideal.subset_span ⟨g, rfl⟩
  have hsup := AlgebraicGeometry.iSup_basicOpen_of_span_eq_top W (Set.range ε) hspan
  have hpU : ∃ g : G, p ∈ T.basicOpen (ε g) := by
    have : p ∈ ⨆ f ∈ Set.range ε, T.basicOpen f := by rw [hsup]; exact hpW
    simp only [Opens.mem_iSup, Set.mem_range] at this
    obtain ⟨f, ⟨g, rfl⟩, hp⟩ := this
    exact ⟨g, hp⟩
  obtain ⟨g, hpg⟩ := hpU
  refine ⟨g⁻¹, T.basicOpen (ε g), hpg, ?_⟩

  have hUW : T.basicOpen (ε g) ≤ W := T.basicOpen_le _
  have hρU : (π ⁻¹ᵁ V) ≤ (ρ g⁻¹).hom ⁻¹ᵁ (π ⁻¹ᵁ V) := by rw [← Scheme.Hom.comp_preimage, hπ g⁻¹]
  have hpre : (t₁ ≫ (ρ g⁻¹).hom) ⁻¹ᵁ (π ⁻¹ᵁ V) = t₁ ⁻¹ᵁ (π ⁻¹ᵁ V) := by
    rw [← Scheme.Hom.comp_preimage, Category.assoc, hπ, Scheme.Hom.comp_preimage]
  have eU₁ : T.basicOpen (ε g) ≤ (t₁ ≫ (ρ g⁻¹).hom) ⁻¹ᵁ (π ⁻¹ᵁ V) := by rw [hpre]; exact hUW.trans e₁
  have eU₂ : T.basicOpen (ε g) ≤ t₂ ⁻¹ᵁ (π ⁻¹ᵁ V) := hUW.trans e₂
  haveI : IsAffine (π ⁻¹ᵁ V) := hU₀
  have key : (t₁ ≫ (ρ g⁻¹).hom).appLE (π ⁻¹ᵁ V) (T.basicOpen (ε g)) eU₁ = t₂.appLE (π ⁻¹ᵁ V) (T.basicOpen (ε g)) eU₂ := by
    have hcomp₁ : (ρ g⁻¹).hom.appLE (π ⁻¹ᵁ V) (π ⁻¹ᵁ V) hρU ≫ t₁.appLE (π ⁻¹ᵁ V) W e₁ ≫ T.presheaf.map (homOfLE hUW).op =
        (t₁ ≫ (ρ g⁻¹).hom).appLE (π ⁻¹ᵁ V) (T.basicOpen (ε g)) eU₁ := by
      rw [Scheme.Hom.appLE_map, Scheme.Hom.appLE_comp_appLE]
    have hcomp₂ : t₂.appLE (π ⁻¹ᵁ V) W e₂ ≫ T.presheaf.map (homOfLE hUW).op = t₂.appLE (π ⁻¹ᵁ V) (T.basicOpen (ε g)) eU₂ :=
      Scheme.Hom.appLE_map _ _ _
    rw [← hcomp₁, ← hcomp₂]
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro b
    simp only [CommRingCat.hom_comp, RingHom.comp_apply]
    rw [← hσρ g b]
    haveI := hW.isLocalization_basicOpen (ε g)
    have hu : IsUnit (algebraMap Γ(T, W) Γ(T, T.basicOpen (ε g)) (ε g)) := IsLocalization.Away.algebraMap_isUnit (ε g)
    have htw := congrArg (algebraMap Γ(T, W) Γ(T, T.basicOpen (ε g))) (hεtw g b)
    rw [map_mul, map_mul, hu.mul_left_inj] at htw
    exact htw.symm
  have heq : (t₁ ≫ (ρ g⁻¹).hom).resLE (π ⁻¹ᵁ V) (T.basicOpen (ε g)) eU₁ = t₂.resLE (π ⁻¹ᵁ V) (T.basicOpen (ε g)) eU₂ :=
    ext_of_isAffine (by rw [Scheme.Hom.appTop, Scheme.Hom.appTop, Scheme.Hom.resLE_app_top, Scheme.Hom.resLE_app_top, key])
  calc (T.basicOpen (ε g)).ι ≫ t₂ = t₂.resLE (π ⁻¹ᵁ V) (T.basicOpen (ε g)) eU₂ ≫ (π ⁻¹ᵁ V).ι := (Scheme.Hom.resLE_comp_ι _ _).symm
    _ = (t₁ ≫ (ρ g⁻¹).hom).resLE (π ⁻¹ᵁ V) (T.basicOpen (ε g)) eU₁ ≫ (π ⁻¹ᵁ V).ι := by rw [heq]
    _ = (T.basicOpen (ε g)).ι ≫ t₁ ≫ (ρ g⁻¹).hom := by rw [Scheme.Hom.resLE_comp_ι]

end S_AlgebraicGeometry_Scheme_exists_open_eq_comp_aut_of_comp_eq_of_free_of_quotient
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_exists_open_eq_comp_aut_of_comp_eq_of_free_of_quotient (solution)

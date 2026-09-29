-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.isFinite_flat_etale_of_free_of_quotient
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/d552a9c1-d7bd-554e-ad9d-2fad189b52c8

import Mathlib
import Theorems.Thm_AlgebraicGeometry_Scheme_exists_ringAut_galois_sections_of_free_of_quotient
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_isFinite_flat_etale_of_free_of_quotient

set_option autoImplicit false

universe u v

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open scoped TensorProduct

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

end CHRAux
p2m_reactivate "P2MW.S_AlgebraicGeometry_Scheme_isFinite_flat_etale_of_free_of_quotient.CHRAux"

open CHRAux in
theorem CHRAux.main
    (A₀ A : Type*) [CommRing A₀] [CommRing A] [Algebra A₀ A]
    (G : Type*) [Group G] [Finite G] (σ : G →* (A ≃+* A))
    (hσ : ∀ (g : G) (r : A₀), σ g (algebraMap A₀ A r) = algebraMap A₀ A r)
    (hinj : Function.Injective (algebraMap A₀ A))
    (hfix : ∀ a : A, (∀ g : G, σ g a = a) → a ∈ Set.range (algebraMap A₀ A))
    (hfree : ∀ P : Ideal A, P.IsPrime → ∀ g : G, g ≠ 1 → ∃ a : A, a - σ g a ∉ P) :
    Module.Finite A₀ A ∧ Module.Projective A₀ A ∧ Module.FaithfullyFlat A₀ A ∧ Algebra.Etale A₀ A ∧
      ∃ e : A ⊗[A₀] A ≃ₗ[A₀] (G → A), ∀ a b : A, e (a ⊗ₜ[A₀] b) = fun g => a * σ g b := by
  classical
  haveI : Fintype G := Fintype.ofFinite G

  obtain ⟨e, he⟩ := exists_sep σ hσ hfree
  obtain ⟨S, hSe⟩ := TensorProduct.exists_finset e
  have hS : ∀ h : G, ∑ p ∈ S, p.1 * σ h p.2 = if h = 1 then 1 else 0 := by
    intro h
    rw [← he h, hSe, map_sum]
    exact Finset.sum_congr rfl fun p _ => (m_tmul σ hσ h p.1 p.2).symm

  haveI hfin : Module.Finite A₀ A := finite σ hσ S hS hinj hfix
  haveI hproj : Module.Projective A₀ A := projective σ hσ S hS hinj hfix

  have hff : Module.FaithfullyFlat A₀ A := by
    rw [Module.FaithfullyFlat.iff_flat_and_proper_ideal]
    refine ⟨inferInstance, fun I hI hI' => ?_⟩
    obtain ⟨m, hm, hIm⟩ := Ideal.exists_le_maximal I hI
    haveI : Algebra.IsIntegral A₀ A := Algebra.IsIntegral.of_finite A₀ A
    obtain ⟨Q, hQ, hQm⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral m
      (by rw [(RingHom.injective_iff_ker_eq_bot _).mp hinj]; exact bot_le)
    have h1 : m • (⊤ : Submodule A₀ A) = ⊤ := by
      refine le_antisymm le_top ?_
      calc (⊤ : Submodule A₀ A) = I • ⊤ := hI'.symm
        _ ≤ m • ⊤ := Submodule.smul_mono_left hIm
    rw [Ideal.smul_top_eq_map, Submodule.restrictScalars_eq_top_iff] at h1
    have h2 : Ideal.map (algebraMap A₀ A) m ≤ Q := Ideal.map_le_iff_le_comap.mpr hQm.ge
    rw [h1, top_le_iff] at h2
    exact hQ.ne_top h2

  have het : Algebra.Etale A₀ A := by
    haveI : Module.FinitePresentation A₀ A := Module.finitePresentation_of_projective A₀ A
    haveI : Algebra.FiniteType A₀ A := Module.Finite.finiteType (R := A₀) A
    haveI : Algebra.FormallyUnramified A₀ A := by
      rw [Algebra.FormallyUnramified.iff_exists_tensorProduct]
      refine ⟨e, fun s => ?_, ?_⟩
      · apply φ_injective σ hσ S hS hfix
        rw [map_mul, map_zero]
        funext k
        simp only [Pi.mul_apply, Pi.zero_apply, map_sub, Pi.sub_apply, φ_apply, m_tmul, he k, one_mul, map_one,
          mul_one]
        split_ifs with hk
        · subst hk; simp [σ_one_apply]
        · rw [mul_zero]
      · rw [hSe, map_sum]
        simp only [Algebra.TensorProduct.lmul'_apply_tmul]
        simpa [σ_one_apply] using hS 1
    exact Algebra.Etale.of_formallyUnramified_of_flat
  refine ⟨hfin, hproj, hff, het, ⟨galois σ hσ S hS hfix, fun a b => ?_⟩⟩
  rw [galois_apply]
  funext g
  rw [φ_apply, m_tmul]

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
    IsFinite π ∧ Flat π ∧ Etale π ∧ LocallyOfFinitePresentation π := by
  classical
  haveI := haff

  have key : ∀ (U : Y.Opens), IsAffineOpen U →
      (π.app U).hom.Finite ∧ (π.app U).hom.Flat ∧ (π.app U).hom.Etale ∧ (π.app U).hom.FinitePresentation := by
    intro U hU
    obtain ⟨-, σ, -, hσ, hinj', hfix', hfree'⟩ :=
      AlgebraicGeometry.Scheme.exists_ringAut_galois_sections_of_free_of_quotient ρ hadm π hπ haff hsurj hfib hinj hrange hfree U hU
    letI : Algebra Γ(Y, U) Γ(X, π ⁻¹ᵁ U) := (π.app U).hom.toAlgebra
    obtain ⟨hfin, hproj, -, het, -⟩ := CHRAux.main Γ(Y, U) Γ(X, π ⁻¹ᵁ U) G σ hσ hinj' hfix' hfree'
    haveI := hfin; haveI := hproj; haveI := het
    haveI : Module.FinitePresentation Γ(Y, U) Γ(X, π ⁻¹ᵁ U) := Module.finitePresentation_of_projective _ _
    exact ⟨hfin, (inferInstance : Module.Flat Γ(Y, U) Γ(X, π ⁻¹ᵁ U)), het,
      (inferInstance : Algebra.FinitePresentation Γ(Y, U) Γ(X, π ⁻¹ᵁ U))⟩

  have hP : ∀ (P : MorphismProperty Scheme.{u}) (Q : ∀ {R S : Type u} [CommRing R] [CommRing S], (R →+* S) → Prop)
      [HasRingHomProperty P Q], (∀ U : Y.Opens, IsAffineOpen U → Q (π.app U).hom) → P π := by
    intro P Q _ h
    have h1 := (targetAffineLocally_affineAnd_iff' (HasRingHomProperty.isLocal_ringHomProperty P).respectsIso π).mpr ⟨haff, h⟩
    have h2 := ((targetAffineLocally_affineAnd_iff_affineLocally (HasRingHomProperty.isLocal_ringHomProperty P) π).mp h1).2
    rw [HasRingHomProperty.eq_affineLocally (P := P)]
    exact h2
  refine ⟨⟨fun U hU => (key U hU).1⟩, hP @Flat (fun f => f.Flat) (fun U hU => (key U hU).2.1),
    hP @Etale (fun f => f.Etale) (fun U hU => (key U hU).2.2.1),
    hP @LocallyOfFinitePresentation (fun f => f.FinitePresentation) (fun U hU => (key U hU).2.2.2)⟩

end S_AlgebraicGeometry_Scheme_isFinite_flat_etale_of_free_of_quotient
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_isFinite_flat_etale_of_free_of_quotient (solution)

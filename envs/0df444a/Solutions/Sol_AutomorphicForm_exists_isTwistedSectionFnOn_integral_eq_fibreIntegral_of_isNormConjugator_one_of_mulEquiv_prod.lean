-- Prove2me | solution 1 for AutomorphicForm.exists_isTwistedSectionFnOn_integral_eq_fibreIntegral_of_isNormConjugator_one_of_mulEquiv_prod
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/b5d177d8-c4f1-5dfe-82e9-8290cf08dd73

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_isTwistedSectionFnOn_integral_eq_fibreIntegral_of_isNormConjugator_one_of_mulEquiv_prod

set_option autoImplicit false

open MeasureTheory
open scoped TensorProduct TensorProduct.RightActions

namespace SplitPlaceTransfer

open AutomorphicForm

section GLTopology

variable (A : Type) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]

omit [IsTopologicalRing A] in
private theorem secondCountableTopology_gl [SecondCountableTopology A] :
    SecondCountableTopology (GL (Fin 2) A) := by
  haveI : SecondCountableTopology (Matrix (Fin 2) (Fin 2) A) :=
    inferInstanceAs (SecondCountableTopology (Fin 2 → Fin 2 → A))
  haveI : SecondCountableTopology (Matrix (Fin 2) (Fin 2) A)ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.isInducing.secondCountableTopology
  exact Units.isInducing_embedProduct.secondCountableTopology

private theorem locallyCompactSpace_gl [T2Space A] [LocallyCompactSpace A] :
    LocallyCompactSpace (GL (Fin 2) A) := by
  haveI : LocallyCompactSpace (Matrix (Fin 2) (Fin 2) A) :=
    inferInstanceAs (LocallyCompactSpace (Fin 2 → Fin 2 → A))
  infer_instance

end GLTopology

section Centralizer

variable {A : Type} [CommRing A]

private theorem mul_comm_of_mem_centralizer {γ : GL (Fin 2) A} (hγ : IsRegularSemisimple γ)
    {s t : GL (Fin 2) A} (hs : s ∈ Subgroup.centralizer ({γ} : Set (GL (Fin 2) A)))
    (ht : t ∈ Subgroup.centralizer ({γ} : Set (GL (Fin 2) A))) : s * t = t * s := by

  have key : ∀ X : Matrix (Fin 2) (Fin 2) A, (γ : Matrix (Fin 2) (Fin 2) A) * X = X * γ →
      ∃ l m : A, X = l • (1 : Matrix (Fin 2) (Fin 2) A) + m • (γ : Matrix (Fin 2) (Fin 2) A) := by
    intro X hX
    obtain ⟨u, hu⟩ := hγ
    have hr : (↑u⁻¹ : A) * (((γ : Matrix (Fin 2) (Fin 2) A) 0 0 - (γ : Matrix (Fin 2) (Fin 2) A) 1 1) ^ 2 +
        4 * (γ : Matrix (Fin 2) (Fin 2) A) 0 1 * (γ : Matrix (Fin 2) (Fin 2) A) 1 0) = 1 := by
      have e : ((γ : Matrix (Fin 2) (Fin 2) A) 0 0 - (γ : Matrix (Fin 2) (Fin 2) A) 1 1) ^ 2 +
          4 * (γ : Matrix (Fin 2) (Fin 2) A) 0 1 * (γ : Matrix (Fin 2) (Fin 2) A) 1 0 =
          Matrix.trace (γ : Matrix (Fin 2) (Fin 2) A) ^ 2 - 4 * Matrix.det (γ : Matrix (Fin 2) (Fin 2) A) := by
        rw [Matrix.trace_fin_two, Matrix.det_fin_two]; ring
      rw [e, ← hu, Units.inv_mul]
    have e00 := congrFun (congrFun hX 0) 0
    have e01 := congrFun (congrFun hX 0) 1
    have e10 := congrFun (congrFun hX 1) 0
    simp only [Matrix.mul_apply, Fin.sum_univ_two] at e00 e01 e10
    refine ⟨X 1 1 - (↑u⁻¹ : A) * (((γ : Matrix (Fin 2) (Fin 2) A) 0 0 - (γ : Matrix (Fin 2) (Fin 2) A) 1 1) *
        (X 0 0 - X 1 1) + 4 * (γ : Matrix (Fin 2) (Fin 2) A) 1 0 * X 0 1) * (γ : Matrix (Fin 2) (Fin 2) A) 1 1,
      (↑u⁻¹ : A) * (((γ : Matrix (Fin 2) (Fin 2) A) 0 0 - (γ : Matrix (Fin 2) (Fin 2) A) 1 1) * (X 0 0 - X 1 1) +
        4 * (γ : Matrix (Fin 2) (Fin 2) A) 1 0 * X 0 1), ?_⟩
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Fin.zero_eta, Fin.mk_one, Fin.isValue,
        Matrix.one_apply_eq, Matrix.one_apply_ne (by decide : (0 : Fin 2) ≠ 1),
        Matrix.one_apply_ne (by decide : (1 : Fin 2) ≠ 0), mul_one, mul_zero, zero_add]
    · linear_combination (-(X 0 0 - X 1 1)) * hr + (-(4 * (↑u⁻¹ : A) * (γ : Matrix (Fin 2) (Fin 2) A) 1 0)) * e01
    · linear_combination (-(X 0 1)) * hr +
        ((↑u⁻¹ : A) * ((γ : Matrix (Fin 2) (Fin 2) A) 0 0 - (γ : Matrix (Fin 2) (Fin 2) A) 1 1)) * e01
    · linear_combination (-(X 1 0)) * hr +
        (-((↑u⁻¹ : A) * ((γ : Matrix (Fin 2) (Fin 2) A) 0 0 - (γ : Matrix (Fin 2) (Fin 2) A) 1 1))) * e10 +
        (4 * (↑u⁻¹ : A) * (γ : Matrix (Fin 2) (Fin 2) A) 1 0) * e00
    · ring
  have hs' : (γ : Matrix (Fin 2) (Fin 2) A) * s = s * γ := by
    simpa [Units.ext_iff] using (Subgroup.mem_centralizer_iff.mp hs) γ (Set.mem_singleton γ)
  have ht' : (γ : Matrix (Fin 2) (Fin 2) A) * t = t * γ := by
    simpa [Units.ext_iff] using (Subgroup.mem_centralizer_iff.mp ht) γ (Set.mem_singleton γ)
  obtain ⟨l, m, hX⟩ := key _ hs'
  have hst : Commute (s : Matrix (Fin 2) (Fin 2) A) (t : Matrix (Fin 2) (Fin 2) A) := by
    rw [hX]
    exact ((Commute.one_left _).smul_left l).add_left
      (Commute.smul_left (show Commute (γ : Matrix (Fin 2) (Fin 2) A) (t : Matrix (Fin 2) (Fin 2) A) from ht') m)
  rw [Units.ext_iff, Units.val_mul, Units.val_mul]
  exact hst

end Centralizer

section Psi

variable (K L : Type) [Field K] [Field L] [Algebra K L]
  (hdeg : Module.finrank K L = 2) (σ : L ≃ₐ[K] L)
  (A : Type) [CommRing A] [Algebra K A]

include hdeg in
private theorem normString_two (δ : GL (Fin 2) (L ⊗[K] A)) :
    normString K L A σ δ = δ * sigmaGL K L A σ δ := by
  simp [normString, hdeg, List.range_succ]

variable (Ψ : GL (Fin 2) A × GL (Fin 2) A ≃* GL (Fin 2) (L ⊗[K] A))
  (hΨ₁ : ∀ g : GL (Fin 2) A, Ψ (g, g) = toTensorGL K L A g)
  (hΨσ : ∀ p : GL (Fin 2) A × GL (Fin 2) A, sigmaGL K L A σ (Ψ p) = Ψ p.swap)

include hΨσ in
private theorem symm_sigmaGL (x : GL (Fin 2) (L ⊗[K] A)) :
    Ψ.symm (sigmaGL K L A σ x) = (Ψ.symm x).swap := by
  apply Ψ.injective
  rw [MulEquiv.apply_symm_apply, ← hΨσ, MulEquiv.apply_symm_apply]

include hΨσ in

private theorem symm_twistedConj (δ x : GL (Fin 2) (L ⊗[K] A)) :
    Ψ.symm (x⁻¹ * δ * sigmaGL K L A σ x) =
      (((Ψ.symm x).1)⁻¹ * (Ψ.symm δ).1 * (Ψ.symm x).2,
        ((Ψ.symm x).2)⁻¹ * (Ψ.symm δ).2 * (Ψ.symm x).1) := by
  rw [map_mul, map_mul, map_inv, symm_sigmaGL K L σ A Ψ hΨσ]
  rfl

include hdeg hΨ₁ hΨσ in

private theorem fst_mul_snd_of_isNormConjugator_one {γ : GL (Fin 2) A} {δ : GL (Fin 2) (L ⊗[K] A)}
    (hδ : IsNormConjugator K L A σ γ δ 1) :
    (Ψ.symm δ).1 * (Ψ.symm δ).2 = γ ∧ (Ψ.symm δ).2 * (Ψ.symm δ).1 = γ := by
  have h1 : toTensorGL K L A γ = δ * sigmaGL K L A σ δ := by
    have h := hδ
    simp only [IsNormConjugator, inv_one, one_mul, mul_one] at h
    rw [h, normString_two K L hdeg σ A]
  have h2 : Ψ (γ, γ) = Ψ (Ψ.symm δ * (Ψ.symm δ).swap) := by
    rw [hΨ₁, h1, map_mul, MulEquiv.apply_symm_apply, ← hΨσ, MulEquiv.apply_symm_apply]
  have h3 := Ψ.injective h2
  rw [Prod.ext_iff] at h3
  exact ⟨h3.1.symm, h3.2.symm⟩

end Psi

private theorem exists_plateau {X : Type*} [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
    {D : Set X} (hD : IsCompact D) :
    ∃ ρ : X → ℝ, Continuous ρ ∧ HasCompactSupport ρ ∧ (∀ x, 0 ≤ ρ x) ∧ (∀ x, ρ x ≤ 1) ∧
      ∀ x ∈ D, ρ x = 1 := by
  obtain ⟨f, hfD, -, hfc, hf01⟩ :=
    exists_continuous_one_zero_of_isCompact hD isClosed_empty (Set.disjoint_empty D)
  exact ⟨f, f.continuous, hfc, fun x => (hf01 x).1, fun x => (hf01 x).2, fun x hx => hfD hx⟩

section Fibre

private theorem exists_apply_ne_zero_of_fibre_ne_zero {G : Type*} [Group G] [MeasurableSpace G]
    (μ : Measure G) {k : G × G → ℂ} {g : G} (h : ∫ h, k (h, h⁻¹ * g) ∂μ ≠ 0) :
    ∃ h : G, k (h, h⁻¹ * g) ≠ 0 := by
  by_contra hne
  push Not at hne
  exact h (by simp [hne])

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G]
  (μ : Measure G)

private theorem continuous_fibre [T2Space G] [SecondCountableTopology G] [BorelSpace G]
    [IsFiniteMeasureOnCompacts μ] {k : G × G → ℂ} (hk : Continuous k) (hkc : HasCompactSupport k) :
    Continuous fun g : G => ∫ h, k (h, h⁻¹ * g) ∂μ := by
  obtain ⟨M, hM⟩ := hk.bounded_above_of_compact_support hkc
  have hS : IsCompact (Prod.fst '' tsupport k) := hkc.isCompact.image continuous_fst
  refine continuous_of_dominated (bound := (Prod.fst '' tsupport k).indicator fun _ => M) ?_ ?_ ?_ ?_
  · exact fun g => (hk.comp (continuous_id.prodMk (continuous_inv.mul continuous_const))).aestronglyMeasurable
  · refine fun g => ae_of_all _ fun h => ?_
    by_cases hh : h ∈ Prod.fst '' tsupport k
    · simpa [Set.indicator_of_mem hh] using hM (h, h⁻¹ * g)
    · have hzero : k (h, h⁻¹ * g) = 0 := by
        by_contra hne
        exact hh ⟨(h, h⁻¹ * g), subset_tsupport k hne, rfl⟩
      simp [Set.indicator_of_notMem hh, hzero]
  · exact (integrableOn_const (hS.measure_lt_top (μ := μ)).ne).integrable_indicator hS.isClosed.measurableSet
  · exact ae_of_all _ fun h => hk.comp (continuous_const.prodMk (continuous_const.mul continuous_id))

private theorem hasCompactSupport_fibre [T2Space G] {k : G × G → ℂ} (hkc : HasCompactSupport k) :
    HasCompactSupport fun g : G => ∫ h, k (h, h⁻¹ * g) ∂μ := by
  refine HasCompactSupport.intro (K := (fun p : G × G => p.1 * p.2) '' tsupport k)
    (hkc.isCompact.image (continuous_fst.mul continuous_snd)) fun g hg => ?_
  have hzero : ∀ h : G, k (h, h⁻¹ * g) = 0 := fun h => by
    by_contra hne
    exact hg ⟨(h, h⁻¹ * g), subset_tsupport k hne, by simp⟩
  simp [hzero]

end Fibre

section Transport

variable (K L : Type) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L] (σ : L ≃ₐ[K] L)
  (A : Type) [CommRing A] [Algebra K A] [TopologicalSpace A] [IsTopologicalRing A]
  (Ψ : GL (Fin 2) A × GL (Fin 2) A ≃* GL (Fin 2) (L ⊗[K] A))
  (hΨc : Continuous Ψ) (hΨc' : Continuous Ψ.symm)
  (hΨ₁ : ∀ g : GL (Fin 2) A, Ψ (g, g) = toTensorGL K L A g)

include hΨc hΨc' hΨ₁ in

private theorem integral_twistedCentralizer_eq_integral_centralizer
    {γ : GL (Fin 2) A} {δ : GL (Fin 2) (L ⊗[K] A)}
    {τ : @Measure (Subgroup.centralizer ({γ} : Set (GL (Fin 2) A))) (centralizerBorel A γ)}
    {τ' : @Measure (twistedCentralizer K L A σ δ) (twistedCentralizerBorel K L A σ δ)}
    (hc : Coupled K L A σ γ δ 1 τ τ') (F : GL (Fin 2) (L ⊗[K] A) → ℝ)
    (hF : Continuous fun p : GL (Fin 2) A × GL (Fin 2) A => F (Ψ p)) (x : GL (Fin 2) (L ⊗[K] A)) :
    letI : MeasurableSpace (Subgroup.centralizer ({γ} : Set (GL (Fin 2) A))) := centralizerBorel A γ
    letI : MeasurableSpace (twistedCentralizer K L A σ δ) := twistedCentralizerBorel K L A σ δ
    ∫ t : twistedCentralizer K L A σ δ, F (t * x) ∂τ' =
      ∫ s : Subgroup.centralizer ({γ} : Set (GL (Fin 2) A)),
        F (Ψ ((s : GL (Fin 2) A) * (Ψ.symm x).1, (s : GL (Fin 2) A) * (Ψ.symm x).2)) ∂τ := by
  letI mL : MeasurableSpace (GL (Fin 2) (L ⊗[K] A)) := glBorelOf (L ⊗[K] A)
  haveI : BorelSpace (GL (Fin 2) (L ⊗[K] A)) := borelSpace_glBorelOf (L ⊗[K] A)
  letI mT : MeasurableSpace (Subgroup.centralizer ({γ} : Set (GL (Fin 2) A))) := centralizerBorel A γ
  letI mT' : MeasurableSpace (twistedCentralizer K L A σ δ) := twistedCentralizerBorel K L A σ δ
  haveI : BorelSpace (Subgroup.centralizer ({γ} : Set (GL (Fin 2) A))) := ⟨rfl⟩
  haveI : BorelSpace (twistedCentralizer K L A σ δ) := ⟨rfl⟩

  have hc' : Measure.map (fun t : twistedCentralizer K L A σ δ => (t : GL (Fin 2) (L ⊗[K] A))) τ' =
      Measure.map (fun s : Subgroup.centralizer ({γ} : Set (GL (Fin 2) A)) =>
        Ψ ((s : GL (Fin 2) A), (s : GL (Fin 2) A))) τ := by
    have h := hc
    simp only [Coupled, inv_one, one_mul, mul_one] at h
    rw [h]
    congr 1
    funext s
    exact (hΨ₁ s).symm

  have hFx : Continuous fun g : GL (Fin 2) (L ⊗[K] A) => F (g * x) := by
    have e : (fun g : GL (Fin 2) (L ⊗[K] A) => F (g * x)) =
        fun g => (fun p : GL (Fin 2) A × GL (Fin 2) A => F (Ψ p)) (Ψ.symm g * Ψ.symm x) := by
      funext g
      simp [map_mul]
    rw [e]
    exact hF.comp (hΨc'.mul continuous_const)
  have e : ∀ s : Subgroup.centralizer ({γ} : Set (GL (Fin 2) A)),
      Ψ ((s : GL (Fin 2) A), (s : GL (Fin 2) A)) * x =
        Ψ ((s : GL (Fin 2) A) * (Ψ.symm x).1, (s : GL (Fin 2) A) * (Ψ.symm x).2) := fun s => by
    rw [← Prod.mk_mul_mk, map_mul, Prod.mk.eta, MulEquiv.apply_symm_apply]
  calc ∫ t : twistedCentralizer K L A σ δ, F (t * x) ∂τ'
      = ∫ g, F (g * x) ∂(Measure.map (fun t : twistedCentralizer K L A σ δ => (t : GL (Fin 2) (L ⊗[K] A))) τ') :=
        (integral_map continuous_subtype_val.measurable.aemeasurable hFx.aestronglyMeasurable).symm
    _ = ∫ g, F (g * x) ∂(Measure.map (fun s : Subgroup.centralizer ({γ} : Set (GL (Fin 2) A)) =>
          Ψ ((s : GL (Fin 2) A), (s : GL (Fin 2) A))) τ) := by rw [hc']
    _ = ∫ s : Subgroup.centralizer ({γ} : Set (GL (Fin 2) A)), F (Ψ ((s : GL (Fin 2) A), (s : GL (Fin 2) A)) * x) ∂τ :=
        integral_map (hΨc.comp (continuous_subtype_val.prodMk continuous_subtype_val)).measurable.aemeasurable
          hFx.aestronglyMeasurable
    _ = _ := by simp only [e]

end Transport

section Split

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G]
  (μ : Measure G) [μ.IsHaarMeasure]

private theorem integral_map_prod_eq [LocallyCompactSpace G] [SecondCountableTopology G]
    {H : Type*} [Group H] [TopologicalSpace H] [MeasurableSpace H] [BorelSpace H]
    (Ψ : G × G ≃* H) (hΨc : Continuous Ψ) (hΨc' : Continuous Ψ.symm) {ν : Measure H}
    (hν : ν = Measure.map Ψ (μ.prod μ)) (F : H → ℂ) (hF : Continuous fun p : G × G => F (Ψ p))
    (hFc : HasCompactSupport fun p : G × G => F (Ψ p)) :
    ∫ y, F y ∂ν = ∫ x₁, ∫ x₂, F (Ψ (x₁, x₂)) ∂μ ∂μ := by
  subst hν
  have hΨm : Measurable Ψ := hΨc.measurable
  have hFm : AEStronglyMeasurable F (Measure.map Ψ (μ.prod μ)) := by
    have e : F = fun y => (fun p : G × G => F (Ψ p)) (Ψ.symm y) := by
      funext y
      simp
    rw [e]
    exact (hF.comp hΨc').aestronglyMeasurable
  rw [integral_map hΨm.aemeasurable hFm]
  exact integral_prod _ (hF.integrable_of_hasCompactSupport hFc)

private theorem inner_identity (k : G × G → ℂ) {δ₁ δ₂ γ : G} (h12 : δ₁ * δ₂ = γ) (ρ : G → ℝ) (c : ℝ)
    (x₁ : G) (hρ : ∀ h : G, k (h, h⁻¹ * (x₁⁻¹ * γ * x₁)) ≠ 0 → ρ (δ₁⁻¹ * x₁ * h) = 1) :
    ∫ x₂, k (x₁⁻¹ * δ₁ * x₂, x₂⁻¹ * δ₂ * x₁) * ((c * ρ x₂ : ℝ) : ℂ) ∂μ =
      (∫ h, k (h, h⁻¹ * (x₁⁻¹ * γ * x₁)) ∂μ) * (c : ℂ) := by
  have hsub := integral_mul_left_eq_self (μ := μ)
    (fun x₂ => k (x₁⁻¹ * δ₁ * x₂, x₂⁻¹ * δ₂ * x₁) * ((c * ρ x₂ : ℝ) : ℂ)) (δ₁⁻¹ * x₁)
  rw [← hsub]
  have e1 : ∀ h : G, x₁⁻¹ * δ₁ * (δ₁⁻¹ * x₁ * h) = h := fun h => by group
  have e2 : ∀ h : G, (δ₁⁻¹ * x₁ * h)⁻¹ * δ₂ * x₁ = h⁻¹ * (x₁⁻¹ * γ * x₁) := fun h => by
    rw [← h12]; group
  simp only [e1, e2]
  rw [← integral_mul_const]
  refine integral_congr_ae (ae_of_all _ fun h => ?_)
  show k (h, h⁻¹ * (x₁⁻¹ * γ * x₁)) * ((c * ρ (δ₁⁻¹ * x₁ * h) : ℝ) : ℂ) =
    k (h, h⁻¹ * (x₁⁻¹ * γ * x₁)) * (c : ℂ)
  by_cases hh : k (h, h⁻¹ * (x₁⁻¹ * γ * x₁)) = 0
  · simp [hh]
  · rw [hρ h hh, mul_one]

end Split

section Homeo

variable {G H : Type*} [TopologicalSpace G] [TopologicalSpace H] [Mul G] [Mul H]

private def homeo (Ψ : G ≃* H) (hΨc : Continuous Ψ) (hΨc' : Continuous Ψ.symm) : G ≃ₜ H :=
  { Ψ.toEquiv with continuous_toFun := hΨc, continuous_invFun := hΨc' }

@[scoped simp] private theorem homeo_apply (Ψ : G ≃* H) (hΨc : Continuous Ψ) (hΨc' : Continuous Ψ.symm) (x : G) :
    homeo Ψ hΨc hΨc' x = Ψ x := rfl

@[scoped simp] private theorem homeo_symm_apply (Ψ : G ≃* H) (hΨc : Continuous Ψ) (hΨc' : Continuous Ψ.symm)
    (y : H) : (homeo Ψ hΨc hΨc').symm y = Ψ.symm y := rfl

end Homeo

end SplitPlaceTransfer
p2m_reactivate "P2MW.S_AutomorphicForm_exists_isTwistedSectionFnOn_integral_eq_fibreIntegral_of_isNormConjugator_one_of_mulEquiv_prod.SplitPlaceTransfer"

open AutomorphicForm in

theorem solution
    (K L : Type) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
    (hdeg : Module.finrank K L = 2) (σ : L ≃ₐ[K] L)
    (A : Type) [CommRing A] [Algebra K A] [TopologicalSpace A] [IsTopologicalRing A] [T2Space A]
    [LocallyCompactSpace A] [SecondCountableTopology A]
    (Ψ : GL (Fin 2) A × GL (Fin 2) A ≃* GL (Fin 2) (L ⊗[K] A))
    (hΨc : Continuous Ψ) (hΨc' : Continuous Ψ.symm)
    (hΨ₁ : ∀ g : GL (Fin 2) A, Ψ (g, g) = toTensorGL K L A g)
    (hΨσ : ∀ p : GL (Fin 2) A × GL (Fin 2) A, sigmaGL K L A σ (Ψ p) = Ψ p.swap)
    (μA : @Measure (GL (Fin 2) A) (glBorelOf A))
    (μL : @Measure (GL (Fin 2) (L ⊗[K] A)) (glBorelOf (L ⊗[K] A))) :
    letI : MeasurableSpace (GL (Fin 2) A) := glBorelOf A
    letI : MeasurableSpace (GL (Fin 2) (L ⊗[K] A)) := glBorelOf (L ⊗[K] A)
    μA.IsHaarMeasure → μL = Measure.map Ψ (μA.prod μA) →
    (∀ φ : GL (Fin 2) (L ⊗[K] A) → ℂ, Continuous φ → HasCompactSupport φ →
      (Continuous fun g : GL (Fin 2) A => ∫ h, φ (Ψ (h, h⁻¹ * g)) ∂μA) ∧
      (HasCompactSupport fun g : GL (Fin 2) A => ∫ h, φ (Ψ (h, h⁻¹ * g)) ∂μA)) ∧
    ∀ γ : GL (Fin 2) A, IsRegularSemisimple γ →
    ∀ δ : GL (Fin 2) (L ⊗[K] A), IsNormConjugator K L A σ γ δ 1 →
    ∀ (τ : @Measure (Subgroup.centralizer ({γ} : Set (GL (Fin 2) A))) (centralizerBorel A γ))
      (τ' : @Measure (twistedCentralizer K L A σ δ) (twistedCentralizerBorel K L A σ δ)),
      Coupled K L A σ γ δ 1 τ τ' →
    ∀ C : Set (GL (Fin 2) (L ⊗[K] A)), IsCompact C →
    ∀ w : GL (Fin 2) A → ℝ, Continuous w → HasCompactSupport w → (∀ x, 0 ≤ w x) →
      (∀ x : GL (Fin 2) A, (∃ h : GL (Fin 2) A, Ψ (h, h⁻¹ * (x⁻¹ * γ * x)) ∈ C) →
        ∫ t : Subgroup.centralizer ({γ} : Set (GL (Fin 2) A)), w (t * x) ∂τ = 1) →
    ∃ w' : GL (Fin 2) (L ⊗[K] A) → ℝ, Continuous w' ∧ HasCompactSupport w' ∧ (∀ x, 0 ≤ w' x) ∧
      ∀ φ : GL (Fin 2) (L ⊗[K] A) → ℂ, Continuous φ → tsupport φ ⊆ C →
        IsSectionFnOn A γ τ (fun g : GL (Fin 2) A => ∫ h, φ (Ψ (h, h⁻¹ * g)) ∂μA) w ∧
        IsTwistedSectionFnOn K L A σ δ τ' φ w' ∧
        ∫ x, φ (x⁻¹ * δ * sigmaGL K L A σ x) * (w' x : ℂ) ∂μL =
          ∫ x, (fun g : GL (Fin 2) A => ∫ h, φ (Ψ (h, h⁻¹ * g)) ∂μA) (x⁻¹ * γ * x) * (w x : ℂ) ∂μA := by
  intro hHaar hμL
  classical
  letI mA : MeasurableSpace (GL (Fin 2) A) := glBorelOf A
  letI mL : MeasurableSpace (GL (Fin 2) (L ⊗[K] A)) := glBorelOf (L ⊗[K] A)
  haveI : BorelSpace (GL (Fin 2) A) := borelSpace_glBorelOf A
  haveI : BorelSpace (GL (Fin 2) (L ⊗[K] A)) := borelSpace_glBorelOf (L ⊗[K] A)
  haveI : SecondCountableTopology (GL (Fin 2) A) := SplitPlaceTransfer.secondCountableTopology_gl A
  haveI : LocallyCompactSpace (GL (Fin 2) A) := SplitPlaceTransfer.locallyCompactSpace_gl A
  haveI : μA.IsHaarMeasure := hHaar

  have hk : ∀ φ : GL (Fin 2) (L ⊗[K] A) → ℂ, Continuous φ →
      Continuous fun p : GL (Fin 2) A × GL (Fin 2) A => φ (Ψ p) := fun φ hφ => hφ.comp hΨc
  have hkc : ∀ φ : GL (Fin 2) (L ⊗[K] A) → ℂ, HasCompactSupport φ →
      HasCompactSupport fun p : GL (Fin 2) A × GL (Fin 2) A => φ (Ψ p) := fun φ hφc => by
    simpa [Function.comp_def, SplitPlaceTransfer.homeo_apply] using
      hφc.comp_homeomorph (SplitPlaceTransfer.homeo Ψ hΨc hΨc')
  refine ⟨fun φ hφ hφc =>
    ⟨SplitPlaceTransfer.continuous_fibre μA (k := fun p => φ (Ψ p)) (hk φ hφ) (hkc φ hφc),
      SplitPlaceTransfer.hasCompactSupport_fibre μA (k := fun p => φ (Ψ p)) (hkc φ hφc)⟩, ?_⟩
  intro γ hγ δ hδ τ τ' hcoup C hC w hw hwc hw0 hwloc
  letI mT : MeasurableSpace (Subgroup.centralizer ({γ} : Set (GL (Fin 2) A))) := centralizerBorel A γ
  letI mT' : MeasurableSpace (twistedCentralizer K L A σ δ) := twistedCentralizerBorel K L A σ δ
  obtain ⟨h12, h21⟩ :=
    SplitPlaceTransfer.fst_mul_snd_of_isNormConjugator_one K L hdeg σ A Ψ hΨ₁ hΨσ hδ

  have hδ₁ : (Ψ.symm δ).1 ∈ Subgroup.centralizer ({γ} : Set (GL (Fin 2) A)) := by
    rw [Subgroup.mem_centralizer_iff]
    intro g hg
    rw [Set.mem_singleton_iff] at hg
    subst hg
    calc g * (Ψ.symm δ).1 = (Ψ.symm δ).1 * (Ψ.symm δ).2 * (Ψ.symm δ).1 := by rw [h12]
      _ = (Ψ.symm δ).1 * g := by rw [mul_assoc, h21]
  have hcomm : ∀ s : Subgroup.centralizer ({γ} : Set (GL (Fin 2) A)),
      (s : GL (Fin 2) A) * (Ψ.symm δ).1 = (Ψ.symm δ).1 * s := fun s =>
    SplitPlaceTransfer.mul_comm_of_mem_centralizer hγ s.2 hδ₁

  have hC₁ : IsCompact (Prod.fst '' (Ψ.symm '' C)) := (hC.image hΨc').image continuous_fst
  have hD : IsCompact ((fun p : GL (Fin 2) A × GL (Fin 2) A => ((Ψ.symm δ).1)⁻¹ * p.1 * p.2) ''
      (tsupport w ×ˢ (Prod.fst '' (Ψ.symm '' C)))) :=
    (hwc.prod hC₁).image ((continuous_const.mul continuous_fst).mul continuous_snd)
  obtain ⟨ρ, hρ, hρc, hρ0, -, hρD⟩ := SplitPlaceTransfer.exists_plateau hD

  have hmemD : ∀ x₁ h : GL (Fin 2) A, x₁ ∈ tsupport w → Ψ (h, h⁻¹ * (x₁⁻¹ * γ * x₁)) ∈ C →
      ρ (((Ψ.symm δ).1)⁻¹ * x₁ * h) = 1 := fun x₁ h hx₁ hh =>
    hρD _ ⟨(x₁, h), ⟨hx₁, ⟨(h, h⁻¹ * (x₁⁻¹ * γ * x₁)), ⟨Ψ (h, h⁻¹ * (x₁⁻¹ * γ * x₁)), hh,
      Ψ.symm_apply_apply _⟩, rfl⟩⟩, rfl⟩

  have hw'c : Continuous fun y : GL (Fin 2) (L ⊗[K] A) => w (Ψ.symm y).1 * ρ (Ψ.symm y).2 :=
    (hw.comp (continuous_fst.comp hΨc')).mul (hρ.comp (continuous_snd.comp hΨc'))
  have hg : HasCompactSupport fun p : GL (Fin 2) A × GL (Fin 2) A => w p.1 * ρ p.2 := by
    refine HasCompactSupport.intro (hwc.prod hρc) fun p hp => ?_
    rw [Set.mem_prod, not_and_or] at hp
    rcases hp with hp | hp
    · rw [image_eq_zero_of_notMem_tsupport hp, zero_mul]
    · rw [image_eq_zero_of_notMem_tsupport hp, mul_zero]
  have hw's : HasCompactSupport fun y : GL (Fin 2) (L ⊗[K] A) => w (Ψ.symm y).1 * ρ (Ψ.symm y).2 := by
    simpa [Function.comp_def, SplitPlaceTransfer.homeo_symm_apply] using
      hg.comp_homeomorph (SplitPlaceTransfer.homeo Ψ hΨc hΨc').symm
  refine ⟨fun y => w (Ψ.symm y).1 * ρ (Ψ.symm y).2, hw'c, hw's, fun y => mul_nonneg (hw0 _) (hρ0 _), ?_⟩
  intro φ hφ hφC
  have hφc : HasCompactSupport φ := hC.of_isClosed_subset (isClosed_tsupport φ) hφC

  have htw : ∀ p : GL (Fin 2) A × GL (Fin 2) A,
      (Ψ p)⁻¹ * δ * sigmaGL K L A σ (Ψ p) =
        Ψ ((p.1)⁻¹ * (Ψ.symm δ).1 * p.2, (p.2)⁻¹ * (Ψ.symm δ).2 * p.1) := fun p => by
    apply Ψ.symm.injective
    rw [SplitPlaceTransfer.symm_twistedConj K L σ A Ψ hΨσ, Ψ.symm_apply_apply, Ψ.symm_apply_apply]

  have hwit : ∀ x₁ x₂ : GL (Fin 2) A,
      φ (Ψ (x₁⁻¹ * (Ψ.symm δ).1 * x₂, x₂⁻¹ * (Ψ.symm δ).2 * x₁)) ≠ 0 →
        Ψ (x₁⁻¹ * (Ψ.symm δ).1 * x₂, (x₁⁻¹ * (Ψ.symm δ).1 * x₂)⁻¹ * (x₁⁻¹ * γ * x₁)) ∈ C :=
      fun x₁ x₂ hne => by
    have e : (x₁⁻¹ * (Ψ.symm δ).1 * x₂)⁻¹ * (x₁⁻¹ * γ * x₁) = x₂⁻¹ * (Ψ.symm δ).2 * x₁ := by
      rw [← h12]; group
    rw [e]
    exact hφC (subset_tsupport _ hne)
  refine ⟨?_, ?_, ?_⟩
  ·
    dsimp only [IsSectionFnOn]
    refine ⟨hw0, hw.measurable, hwc, fun x hx => hwloc x ?_⟩
    obtain ⟨h, hh⟩ := SplitPlaceTransfer.exists_apply_ne_zero_of_fibre_ne_zero μA (k := fun p => φ (Ψ p)) hx
    exact ⟨h, hφC (subset_tsupport _ hh)⟩
  ·
    dsimp only [IsTwistedSectionFnOn]
    refine ⟨fun y => mul_nonneg (hw0 _) (hρ0 _), hw'c.measurable, hw's, fun x hx => ?_⟩
    rw [SplitPlaceTransfer.integral_twistedCentralizer_eq_integral_centralizer K L σ A Ψ hΨc hΨc' hΨ₁ hcoup
      (fun y => w (Ψ.symm y).1 * ρ (Ψ.symm y).2)
      (by have h__af := (hw.comp continuous_fst).mul (hρ.comp continuous_snd); simp at h__af ⊢; exact h__af) x]
    have hx' := hx
    rw [← MulEquiv.apply_symm_apply Ψ x, htw] at hx'
    have hCmem := hwit _ _ hx'
    have hone := hwloc (Ψ.symm x).1 ⟨_, hCmem⟩
    rw [← hone]
    refine integral_congr_ae (ae_of_all _ fun s => ?_)
    simp only [MulEquiv.symm_apply_apply]
    by_cases hw1 : w ((s : GL (Fin 2) A) * (Ψ.symm x).1) = 0
    · rw [hw1, zero_mul]
    · have hs : γ * (s : GL (Fin 2) A) = (s : GL (Fin 2) A) * γ :=
        (Subgroup.mem_centralizer_iff.mp s.2) γ (Set.mem_singleton γ)
      have hsγ : ((s : GL (Fin 2) A) * (Ψ.symm x).1)⁻¹ * γ * ((s : GL (Fin 2) A) * (Ψ.symm x).1) =
          ((Ψ.symm x).1)⁻¹ * γ * (Ψ.symm x).1 := by
        calc ((s : GL (Fin 2) A) * (Ψ.symm x).1)⁻¹ * γ * ((s : GL (Fin 2) A) * (Ψ.symm x).1)
            = ((Ψ.symm x).1)⁻¹ * ((s : GL (Fin 2) A)⁻¹ * (γ * (s : GL (Fin 2) A))) * (Ψ.symm x).1 := by group
          _ = ((Ψ.symm x).1)⁻¹ * ((s : GL (Fin 2) A)⁻¹ * ((s : GL (Fin 2) A) * γ)) * (Ψ.symm x).1 := by rw [hs]
          _ = ((Ψ.symm x).1)⁻¹ * γ * (Ψ.symm x).1 := by group
      have e2 : ((Ψ.symm δ).1)⁻¹ * ((s : GL (Fin 2) A) * (Ψ.symm x).1) *
          (((Ψ.symm x).1)⁻¹ * (Ψ.symm δ).1 * (Ψ.symm x).2) = (s : GL (Fin 2) A) * (Ψ.symm x).2 := by
        calc ((Ψ.symm δ).1)⁻¹ * ((s : GL (Fin 2) A) * (Ψ.symm x).1) *
              (((Ψ.symm x).1)⁻¹ * (Ψ.symm δ).1 * (Ψ.symm x).2)
            = ((Ψ.symm δ).1)⁻¹ * ((s : GL (Fin 2) A) * (Ψ.symm δ).1) * (Ψ.symm x).2 := by group
          _ = ((Ψ.symm δ).1)⁻¹ * ((Ψ.symm δ).1 * (s : GL (Fin 2) A)) * (Ψ.symm x).2 := by rw [hcomm s]
          _ = (s : GL (Fin 2) A) * (Ψ.symm x).2 := by group
      rw [← e2, hmemD _ _ (subset_tsupport _ hw1) (by rwa [hsγ]), mul_one]
  ·
    dsimp only
    have hF : Continuous fun p : GL (Fin 2) A × GL (Fin 2) A =>
        φ ((Ψ p)⁻¹ * δ * sigmaGL K L A σ (Ψ p)) * ((w (Ψ.symm (Ψ p)).1 * ρ (Ψ.symm (Ψ p)).2 : ℝ) : ℂ) := by
      simp only [htw, MulEquiv.symm_apply_apply]
      exact ((hφ.comp hΨc).comp (by fun_prop)).mul
        (Complex.continuous_ofReal.comp ((hw.comp continuous_fst).mul (hρ.comp continuous_snd)))
    have hFc : HasCompactSupport fun p : GL (Fin 2) A × GL (Fin 2) A =>
        φ ((Ψ p)⁻¹ * δ * sigmaGL K L A σ (Ψ p)) * ((w (Ψ.symm (Ψ p)).1 * ρ (Ψ.symm (Ψ p)).2 : ℝ) : ℂ) := by
      simp only [MulEquiv.symm_apply_apply]
      exact (hg.comp_left Complex.ofReal_zero).mul_left
    rw [SplitPlaceTransfer.integral_map_prod_eq μA Ψ hΨc hΨc' hμL
      (fun y => φ (y⁻¹ * δ * sigmaGL K L A σ y) * ((w (Ψ.symm y).1 * ρ (Ψ.symm y).2 : ℝ) : ℂ)) hF hFc]
    refine integral_congr_ae (ae_of_all _ fun x₁ => ?_)
    simp only [htw, MulEquiv.symm_apply_apply]
    by_cases hx₁ : w x₁ = 0
    · simp [hx₁]
    · exact SplitPlaceTransfer.inner_identity μA (fun p => φ (Ψ p)) h12 ρ (w x₁) x₁
        (fun h hh => hmemD x₁ h (subset_tsupport _ hx₁) (hφC (subset_tsupport _ hh)))

end S_AutomorphicForm_exists_isTwistedSectionFnOn_integral_eq_fibreIntegral_of_isNormConjugator_one_of_mulEquiv_prod
end P2MW
export P2MW.S_AutomorphicForm_exists_isTwistedSectionFnOn_integral_eq_fibreIntegral_of_isNormConjugator_one_of_mulEquiv_prod (solution)

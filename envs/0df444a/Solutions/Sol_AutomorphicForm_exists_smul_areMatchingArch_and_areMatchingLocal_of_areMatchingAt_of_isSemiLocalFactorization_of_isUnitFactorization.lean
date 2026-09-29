-- Prove2me | solution 1 for AutomorphicForm.exists_smul_areMatchingArch_and_areMatchingLocal_of_areMatchingAt_of_isSemiLocalFactorization_of_isUnitFactorization
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/6f9de933-59e0-5fec-91ab-18209b3762fa

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Theorems.Thm_AutomorphicForm_exists_smul_eq_of_isSemiLocalFactorization_of_isSemiLocalFactorization_of_exists_ne_zero
import Theorems.Thm_AutomorphicForm_exists_smul_eq_of_isUnitFactorization_of_isUnitFactorization_of_exists_ne_zero
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_smul_areMatchingArch_and_areMatchingLocal_of_areMatchingAt_of_isSemiLocalFactorization_of_isUnitFactorization
p2m_attr_erase "simp" "AdelicDock.coe_finEmbed AdelicDock.splice_apply_self AdelicDock.coe_localEmbed"

set_option autoImplicit false

open MeasureTheory NumberField IsDedekindDomain

open scoped TensorProduct TensorProduct.RightActions

namespace MatchedRescaling

open AutomorphicForm

section Untwisted

variable (A : Type) [CommRing A] [TopologicalSpace A]

theorem isSectionFnOn_smul (γ : GL (Fin 2) A)
    (τ : @Measure (Subgroup.centralizer ({γ} : Set (GL (Fin 2) A))) (centralizerBorel A γ))
    (f : GL (Fin 2) A → ℂ) (w : GL (Fin 2) A → ℝ) (a : ℂ)
    (h : IsSectionFnOn A γ τ f w) : IsSectionFnOn A γ τ (a • f) w := by
  refine ⟨h.1, h.2.1, h.2.2.1, fun x hx => h.2.2.2 x ?_⟩
  intro h0
  apply hx
  simp [Pi.smul_apply, h0]

theorem isOrbitalIntegralOn_smul (μ : @Measure (GL (Fin 2) A) (glBorelOf A)) (γ : GL (Fin 2) A)
    (τ : @Measure (Subgroup.centralizer ({γ} : Set (GL (Fin 2) A))) (centralizerBorel A γ))
    (f : GL (Fin 2) A → ℂ) (I : ℂ) (a : ℂ)
    (h : IsOrbitalIntegralOn A μ γ τ f I) : IsOrbitalIntegralOn A μ γ τ (a • f) (a * I) := by
  letI := glBorelOf A
  obtain ⟨w, hw, rfl⟩ := h
  refine ⟨w, isSectionFnOn_smul A γ τ f w a hw, ?_⟩
  rw [← integral_const_mul]
  congr 1
  funext x
  simp [Pi.smul_apply, mul_assoc]

end Untwisted

section Twisted

variable (K L : Type) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
  (A : Type) [CommRing A] [Algebra K A] [TopologicalSpace A] (σ : L ≃ₐ[K] L)

theorem isTwistedSectionFnOn_smul (δ : GL (Fin 2) (L ⊗[K] A))
    (τ' : @Measure (twistedCentralizer K L A σ δ) (twistedCentralizerBorel K L A σ δ))
    (φ : GL (Fin 2) (L ⊗[K] A) → ℂ) (w : GL (Fin 2) (L ⊗[K] A) → ℝ) (a : ℂ)
    (h : IsTwistedSectionFnOn K L A σ δ τ' φ w) : IsTwistedSectionFnOn K L A σ δ τ' (a • φ) w := by
  refine ⟨h.1, h.2.1, h.2.2.1, fun x hx => h.2.2.2 x ?_⟩
  intro h0
  apply hx
  simp [Pi.smul_apply, h0]

theorem isTwistedOrbitalIntegralOn_smul
    (μ : @Measure (GL (Fin 2) (L ⊗[K] A)) (glBorelOf (L ⊗[K] A))) (δ : GL (Fin 2) (L ⊗[K] A))
    (τ' : @Measure (twistedCentralizer K L A σ δ) (twistedCentralizerBorel K L A σ δ))
    (φ : GL (Fin 2) (L ⊗[K] A) → ℂ) (I' : ℂ) (a : ℂ)
    (h : IsTwistedOrbitalIntegralOn K L A σ μ δ τ' φ I') :
    IsTwistedOrbitalIntegralOn K L A σ μ δ τ' (a • φ) (a * I') := by
  letI := glBorelOf (L ⊗[K] A)
  obtain ⟨w, hw, rfl⟩ := h
  refine ⟨w, isTwistedSectionFnOn_smul K L A σ δ τ' φ w a hw, ?_⟩
  rw [← integral_const_mul]
  congr 1
  funext x
  simp [Pi.smul_apply, mul_assoc]

theorem areMatchingOn_of_smul
    (μL : @Measure (GL (Fin 2) (L ⊗[K] A)) (glBorelOf (L ⊗[K] A)))
    (μK : @Measure (GL (Fin 2) A) (glBorelOf A))
    (Φ : GL (Fin 2) (L ⊗[K] A) → ℂ) (F : GL (Fin 2) A → ℂ) (a b : ℂ) (ha : a ≠ 0)
    (h : AreMatchingOn K L A σ μL μK (a • Φ) (b • F)) :
    AreMatchingOn K L A σ μL μK Φ ((b / a) • F) := by
  have hab : a • ((b / a) • F) = b • F := by
    funext x
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [← mul_assoc, mul_div_cancel₀ b ha]
  refine ⟨fun δ hδ γ hγ y hy τ τ' hτ hτ' hc I I' hI' hI => ?_, fun γ hγ hn τ hτ I hI => ?_⟩
  · have h1 := isTwistedOrbitalIntegralOn_smul K L A σ μL δ τ' Φ I' a hI'
    have h2 := isOrbitalIntegralOn_smul A μK γ τ ((b / a) • F) I a hI
    rw [hab] at h2
    exact mul_left_cancel₀ ha (h.1 δ hδ γ hγ y hy τ τ' hτ hτ' hc _ _ h1 h2)
  · have h2 := isOrbitalIntegralOn_smul A μK γ τ ((b / a) • F) I a hI
    rw [hab] at h2
    have := h.2 γ hγ hn τ hτ _ h2
    rcases mul_eq_zero.1 this with h0 | h0
    · exact absurd h0 ha
    · exact h0

end Twisted

section TestFactors

open scoped Classical in
theorem isArchTestFactor_smul (F : Type) [Field F] [NumberField F]
    (fa : GL (Fin 2) (InfiniteAdeleRing F) → ℂ) (c : ℂ) (h : IsArchTestFactor F fa) :
    IsArchTestFactor F (c • fa) := by
  obtain ⟨⟨Φ, hΦ, hfa⟩, hsupp⟩ := h
  refine ⟨⟨fun x => c * Φ x, contDiff_const.mul hΦ, fun g => ?_⟩, ?_⟩
  · simp [Pi.smul_apply, hfa g]
  · exact hsupp.mono (Function.support_const_smul_subset c fa)

theorem isLocalTestFn_smul (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))
    (fv : GL (Fin 2) (v.adicCompletion K) → ℂ) (c : ℂ) (h : IsLocalTestFn K v fv) :
    IsLocalTestFn K v (c • fv) := by
  refine ⟨?_, h.2.mono (Function.support_const_smul_subset c fv)⟩
  have : c • fv = (fun z : ℂ => c * z) ∘ fv := by
    funext x; simp [Pi.smul_apply]
  rw [this]
  exact h.1.comp _

end TestFactors

end MatchedRescaling

open MatchedRescaling in
theorem solution
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (σ : L ≃ₐ[K] L) (S : Finset (HeightOneSpectrum (𝓞 K)))
    (φ : GL (Fin 2) (AdeleRing (𝓞 L) L) → ℂ)
    (φa : GL (Fin 2) (InfiniteAdeleRing L) → ℂ) (φf : GL (Fin 2) (FiniteAdeleRing (𝓞 L) L) → ℂ)
    (φS : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) (L ⊗[K] v.adicCompletion K) → ℂ)
    (hφ : AutomorphicForm.IsSemiLocalFactorization K L S φ φa φf φS)
    (f : GL (Fin 2) (AdeleRing (𝓞 K) K) → ℂ)
    (fa : GL (Fin 2) (InfiniteAdeleRing K) → ℂ) (ff : GL (Fin 2) (FiniteAdeleRing (𝓞 K) K) → ℂ)
    (fS : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) (v.adicCompletion K) → ℂ)
    (hf : AutomorphicForm.IsUnitFactorization K S f fa ff fS)
    (hm : AutomorphicForm.AreMatchingAt K L σ S φ f)

    (hφ0 : ∃ g, φ g ≠ 0) (hf0 : ∃ g, f g ≠ 0) :
    ∃ (ρa : ℂ) (ρ : HeightOneSpectrum (𝓞 K) → ℂ),
      ρa ≠ 0 ∧ (∀ v ∈ S, ρ v ≠ 0) ∧ ρa * ∏ v ∈ S, ρ v = 1 ∧
      AutomorphicForm.IsArchTestFactor K (ρa • fa) ∧ (∀ v ∈ S, AutomorphicForm.IsLocalTestFn K v (ρ v • fS v)) ∧
      AutomorphicForm.AreMatchingArch K L σ φa (ρa • fa) ∧
      ∀ v ∈ S, AutomorphicForm.AreMatchingLocal K L v σ (φS v) (ρ v • fS v) := by
  obtain ⟨φa', φf', φS', fa', ff', fS', hφ', hf', hmA, hmS⟩ := hm

  obtain ⟨ca, c, hca, hc, hcprod, hφa', hφS'⟩ :=
    AutomorphicForm.exists_smul_eq_of_isSemiLocalFactorization_of_isSemiLocalFactorization_of_exists_ne_zero
      K L S φ φa φf φS hφ φa' φf' φS' hφ' hφ0
  obtain ⟨da, d, hda, hd, hdprod, hfa', hfS'⟩ :=
    AutomorphicForm.exists_smul_eq_of_isUnitFactorization_of_isUnitFactorization_of_exists_ne_zero
      K S f fa ff fS hf fa' ff' fS' hf' hf0
  refine ⟨da / ca, fun v => d v / c v, div_ne_zero hda hca, fun v hv => div_ne_zero (hd v hv) (hc v hv),
    ?_, ?_, ?_, ?_, ?_⟩
  ·
    rw [Finset.prod_div_distrib, div_mul_div_comm, hdprod, hcprod, div_one]
  · exact isArchTestFactor_smul K fa _ hf.1
  · exact fun v hv => isLocalTestFn_smul K v (fS v) _ (hf.2.2.1 v hv)
  ·
    have hmA' : AutomorphicForm.AreMatchingArch K L σ (ca • φa) (da • fa) := by
      rw [← hφa', ← hfa']; exact hmA
    exact areMatchingOn_of_smul K L (InfiniteAdeleRing K) σ _ _ (φa ∘ AutomorphicForm.archIdentGL K L) fa
      ca da hca hmA'
  ·
    intro v hv
    have hmS' : AutomorphicForm.AreMatchingLocal K L v σ (c v • φS v) (d v • fS v) := by
      rw [← hφS' v hv, ← hfS' v hv]; exact hmS v hv
    exact areMatchingOn_of_smul K L (v.adicCompletion K) σ _ _ (φS v) (fS v) (c v) (d v) (hc v hv) hmS'

end S_AutomorphicForm_exists_smul_areMatchingArch_and_areMatchingLocal_of_areMatchingAt_of_isSemiLocalFactorization_of_isUnitFactorization
end P2MW
export P2MW.S_AutomorphicForm_exists_smul_areMatchingArch_and_areMatchingLocal_of_areMatchingAt_of_isSemiLocalFactorization_of_isUnitFactorization (solution)

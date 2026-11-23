-- Prove2me | Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_ContinuousHermScal
-- name    : CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_ContinuousHermScal
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T05:33:49.289304+00:00
-- url     : https://prove2.me/theorems/480e82fb-9beb-4ebc-91b5-abe5520ca612
-- title:
--   Continuous Herm Scal
-- statement:
--   Definitions and structural lemmas for Continuous Herm Scal, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/ContinuousHermScal.lean

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_IsEulerProd
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
noncomputable section
namespace GlobalTheory.CompanionTheory.SW.OneHerm
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
theorem sigma_sigma {σ : E →ₐ[F] E} (hσ : IsCMExt F E σ) (x : E) : σ (σ x) = x := by
  obtain ⟨-, -, -, h⟩ := hσ
  let τ : E →+* ℂ := Classical.choice (inferInstance : Nonempty (E →+* ℂ))
  apply τ.injective
  rw [h τ, h τ, star_star]
theorem exists_basis {σ : E →ₐ[F] E} (hσ : IsCMExt F E σ) :
    ∃ bb : Module.Basis (Fin 2) F E, bb 0 = 1 ∧ σ (bb 1) = - bb 1 := by
  have hcm := hσ
  obtain ⟨-, hc, h2, h⟩ := hσ
  let τ : E →+* ℂ := Classical.choice (inferInstance : Nonempty (E →+* ℂ))
  have hnr : ∃ x : E, star (τ x) ≠ τ x := by
    by_contra hcon
    push_neg at hcon
    have hreal : NumberField.ComplexEmbedding.IsReal τ := by
      ext x
      exact hcon x
    have := hc.isComplex (NumberField.InfinitePlace.mk τ)
    rw [← NumberField.InfinitePlace.not_isReal_iff_isComplex] at this
    exact this ⟨τ, hreal, rfl⟩
  obtain ⟨x, hx⟩ := hnr
  set δ : E := x - σ x with hδ
  have hσδ : σ δ = -δ := by
    simp [hδ, sigma_sigma hcm]
  have hδ0 : δ ≠ 0 := by
    intro h0
    apply hx
    have : τ δ = 0 := by rw [h0, map_zero]
    rw [hδ, map_sub, h τ, sub_eq_zero] at this
    exact this.symm
  have hli : LinearIndependent F ![(1 : E), δ] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    have hσs : ∀ (c : F) (z : E), σ (c • z) = c • σ z := fun c z => by
      rw [Algebra.smul_def, Algebra.smul_def, map_mul, AlgHom.commutes]
    have h' := congrArg σ hst
    simp only [map_add, hσs, map_one, hσδ, map_zero, smul_neg] at h'
    have hs2 : (s + s) • (1 : E) = 0 := by
      rw [add_smul]
      linear_combination hst + h'
    have hs : s = 0 := by
      have h3 : s + s = 0 := by simpa using hs2
      have h4 : (2 : F) * s = 0 := by rw [two_mul]; exact h3
      simpa using h4
    refine ⟨hs, ?_⟩
    rw [hs, zero_smul, zero_add] at hst
    exact (smul_eq_zero.mp hst).resolve_right hδ0
  refine ⟨basisOfLinearIndependentOfCardEqFinrank hli (by simpa using h2.symm), ?_, ?_⟩
  · simp
  · simpa using hσδ
variable (R : Type) [CommRing R] [Algebra F R]
theorem half_add (r : R) : algebraMap F R (1 / 2) * (r + r) = r := by
  have h : r + r = algebraMap F R 2 * r := by
    rw [map_ofNat, two_mul]
  rw [h, ← mul_assoc, ← map_mul]
  norm_num
variable {R}
theorem fixed_eq {σ : E →ₐ[F] E} (hσ : IsCMExt F E σ) {y : R ⊗[F] E} (hy : sigR R σ y = y) :
    ∃ r : R, y = r ⊗ₜ[F] (1 : E) := by
  obtain ⟨bb, h0, h1⟩ := exists_basis hσ
  set B := Algebra.TensorProduct.basis R bb with hB
  have hy' : y = (B.repr y 0) ⊗ₜ[F] (1 : E) + (B.repr y 1) ⊗ₜ[F] bb 1 := by
    conv_lhs => rw [← B.sum_repr y]
    simp [Fin.sum_univ_two, hB, Algebra.TensorProduct.basis_apply, h0, TensorProduct.smul_tmul']
  generalize B.repr y 0 = c0 at hy'
  generalize hc1 : B.repr y 1 = c1 at hy'
  have hs : sigR R σ y = c0 ⊗ₜ[F] (1 : E) - c1 ⊗ₜ[F] bb 1 := by
    rw [hy']
    simp [sigR, h1, TensorProduct.tmul_neg, sub_eq_add_neg]
  have hz : c1 ⊗ₜ[F] bb 1 + c1 ⊗ₜ[F] bb 1 = 0 := by
    have := hs.symm.trans hy
    rw [hy'] at this
    linear_combination (-1 : ℤ) • this
  have hr : ∀ c : R, (B.repr (c ⊗ₜ[F] bb 1)) 1 = c := by
    intro c
    simp [hB, Algebra.TensorProduct.basis_repr_tmul]
  have hc : c1 = 0 := by
    have := congrArg (fun z => B.repr z 1) hz
    simp only [map_add, Finsupp.add_apply, hr, map_zero, Finsupp.zero_apply] at this
    rw [← half_add (F := F) R c1, this, mul_zero]
  exact ⟨c0, by rw [hy', hc]; simp⟩
theorem trace_tmul_one {σ : E →ₐ[F] E} (hσ : IsCMExt F E σ) (r : R) :
    Algebra.trace R (R ⊗[F] E) (r ⊗ₜ[F] (1 : E)) = r + r := by
  obtain ⟨bb, -, -⟩ := exists_basis hσ
  have := Algebra.trace_algebraMap_of_basis (Algebra.TensorProduct.basis R bb) r
  rw [Algebra.TensorProduct.algebraMap_apply] at this
  simpa [two_smul] using this
end GlobalTheory.CompanionTheory.SW.OneHerm
namespace GlobalTheory.CompanionTheory.SW.OneHerm
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
section Top
variable (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [IsTopologicalRing R]
theorem continuous_tmul_one : Continuous fun s : R => s ⊗ₜ[F] (1 : E) := by
  haveI : IsModuleTopology R (R ⊗[F] E) := ⟨rfl⟩
  haveI : ContinuousAdd (R ⊗[F] E) := IsModuleTopology.toContinuousAdd R (R ⊗[F] E)
  have h := IsModuleTopology.continuous_of_linearMap (Algebra.linearMap R (R ⊗[F] E))
  convert h using 2 with s
  simp [Algebra.TensorProduct.algebraMap_apply]
theorem continuous_trace : Continuous (Algebra.trace R (R ⊗[F] E)) := by
  haveI : IsModuleTopology R (R ⊗[F] E) := ⟨rfl⟩
  exact IsModuleTopology.continuous_of_linearMap (Algebra.trace R (R ⊗[F] E))
def hermHalf (σ : E →ₐ[F] E) (S : HermR R σ 1) : R :=
  algebraMap F R (1 / 2) * Algebra.trace R (R ⊗[F] E) ((S : Matrix (Fin 1) (Fin 1) (R ⊗[F] E)) 0 0)
theorem hermScal_hermHalf {σ : E →ₐ[F] E} (hσ : IsCMExt F E σ) (S : HermR R σ 1) :
    hermScal R σ (hermHalf R σ S) = S := by
  have hfix : sigR R σ ((S : Matrix (Fin 1) (Fin 1) (R ⊗[F] E)) 0 0) = (S : Matrix (Fin 1) (Fin 1) (R ⊗[F] E)) 0 0 :=
    S.2 0 0
  obtain ⟨r, hr⟩ := fixed_eq hσ hfix
  apply Subtype.ext
  ext a b
  have ha : a = 0 := Subsingleton.elim _ _
  have hb : b = 0 := Subsingleton.elim _ _
  subst ha hb
  change (hermHalf R σ S) ⊗ₜ[F] (1 : E) = _
  rw [hr, hermHalf, hr, trace_tmul_one hσ, half_add]
theorem hermHalf_hermScal {σ : E →ₐ[F] E} (hσ : IsCMExt F E σ) (s : R) :
    hermHalf R σ (hermScal R σ s) = s := by
  change algebraMap F R (1 / 2) * Algebra.trace R (R ⊗[F] E) (s ⊗ₜ[F] (1 : E)) = s
  rw [trace_tmul_one hσ, half_add]
theorem continuous_hermScal (σ : E →ₐ[F] E) : Continuous (hermScal R σ) := by
  refine Continuous.subtype_mk ?_ _
  exact continuous_pi fun _ => continuous_pi fun _ => continuous_tmul_one R
theorem continuous_hermHalf (σ : E →ₐ[F] E) : Continuous (hermHalf R σ) := by
  refine continuous_const.mul ((continuous_trace R).comp ?_)
  exact (continuous_apply 0).comp ((continuous_apply 0).comp continuous_subtype_val)
def hermHomeo {σ : E →ₐ[F] E} (hσ : IsCMExt F E σ) : R ≃ₜ HermR R σ 1 where
  toFun := hermScal R σ
  invFun := hermHalf R σ
  left_inv := hermHalf_hermScal R hσ
  right_inv := hermScal_hermHalf R hσ
  continuous_toFun := continuous_hermScal R σ
  continuous_invFun := continuous_hermHalf R σ
end Top
section Meas
variable (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [IsTopologicalRing R]
  [LocallyCompactSpace R] [SecondCountableTopology R] [T2Space R] [MeasurableSpace R] [BorelSpace R]
instance : IsEmpty {p : Fin 1 × Fin 1 // p.1 < p.2} :=
  ⟨fun p => by
    have h := p.2
    rw [Subsingleton.elim p.1.1 p.1.2] at h
    exact lt_irrefl _ h⟩
end Meas
end GlobalTheory.CompanionTheory.SW.OneHerm



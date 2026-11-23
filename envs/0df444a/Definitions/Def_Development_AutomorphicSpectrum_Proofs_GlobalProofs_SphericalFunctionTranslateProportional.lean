-- Prove2me | Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_SphericalFunctionTranslateProportional
-- name    : Development_AutomorphicSpectrum_Proofs_GlobalProofs_SphericalFunctionTranslateProportional
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T20:08:16.504523+00:00
-- url     : https://prove2.me/theorems/2f68bac3-50b4-490e-869a-9f1696855919
-- title:
--   Spherical Function Translate Proportional
-- statement:
--   Definitions and structural lemmas for Spherical Function Translate Proportional, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/SphericalFunctionTranslateProportional.lean

import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_InstBorelGL
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix GlobalTheory.CompanionTheory.QL
open scoped ComplexConjugate ValuativeRel
noncomputable section
namespace GlobalTheory.CompanionTheory.SphericalRep
open Topology
section Alg
variable {G : Type} [Group G]
def translates (φ : G → ℂ) : Submodule ℂ (G → ℂ) :=
  Submodule.span ℂ (Set.range fun (x : G) (g : G) => φ (g * x))
def rightTr (h : G) : (G → ℂ) →ₗ[ℂ] (G → ℂ) where
  toFun f := fun g => f (g * h)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
@[simp] theorem rightTr_apply (h : G) (f : G → ℂ) (g : G) : rightTr h f g = f (g * h) := rfl
theorem gen_mem (φ : G → ℂ) (x : G) : (fun g => φ (g * x)) ∈ translates φ :=
  Submodule.subset_span ⟨x, rfl⟩
theorem rightTr_mem (φ : G → ℂ) (h : G) {f : G → ℂ} (hf : f ∈ translates φ) :
    rightTr h f ∈ translates φ := by
  induction hf using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨x, rfl⟩ := hf
    have : rightTr h (fun g => φ (g * x)) = fun g => φ (g * (h * x)) := by
      funext g; simp [mul_assoc]
    rw [this]; exact gen_mem φ _
  | zero => simp
  | add f f' _ _ h1 h2 => rw [map_add]; exact add_mem h1 h2
  | smul c f _ h1 => rw [map_smul]; exact Submodule.smul_mem _ _ h1
def rightEquiv (φ : G → ℂ) (h : G) : translates φ ≃ₗ[ℂ] translates φ where
  toFun f := ⟨rightTr h f.1, rightTr_mem φ h f.2⟩
  invFun f := ⟨rightTr h⁻¹ f.1, rightTr_mem φ h⁻¹ f.2⟩
  map_add' f f' := by ext g; simp
  map_smul' c f := by ext g; simp
  left_inv f := by ext g; simp
  right_inv f := by ext g; simp
@[simp] theorem rightEquiv_coe (φ : G → ℂ) (h : G) (f : translates φ) (g : G) :
    (rightEquiv φ h f : G → ℂ) g = (f : G → ℂ) (g * h) := rfl
theorem eval_eq_of_mem {φ : G → ℂ} {g k : G} {z : ℂ} (h : ∀ x, φ (g * x) = z * φ (k * x))
    {f : G → ℂ} (hf : f ∈ translates φ) : f g = z * f k := by
  induction hf using Submodule.span_induction with
  | mem f hf => obtain ⟨x, rfl⟩ := hf; exact h x
  | zero => simp
  | add f f' _ _ h1 h2 => simp [h1, h2, mul_add]
  | smul c f _ h1 => simp only [Pi.smul_apply, smul_eq_mul, h1]; ring
end Alg
section Top
variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
theorem exists_open_stabilizer {K : Subgroup G} (hKo : IsOpen (K : Set G)) {φ : G → ℂ}
    (hr : ∀ g, ∀ k ∈ K, φ (g * k) = φ g) {f : G → ℂ} (hf : f ∈ translates φ) :
    ∃ U : Subgroup G, IsOpen (U : Set G) ∧ ∀ u ∈ U, ∀ g, f (g * u) = f g := by
  induction hf using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨x, rfl⟩ := hf
    refine ⟨K.comap (MulAut.conj x⁻¹).toMonoidHom, ?_, ?_⟩
    · have hc : Continuous fun u : G => x⁻¹ * u * x⁻¹⁻¹ := by fun_prop
      exact hKo.preimage hc
    · intro u hu g
      have hu' : x⁻¹ * u * x ∈ K := by simpa [MulAut.conj_apply] using hu
      have := hr (g * x) _ hu'
      simpa [mul_assoc] using this
  | zero => exact ⟨⊤, isOpen_univ, by simp⟩
  | add f f' _ _ h1 h2 =>
    obtain ⟨U, hU, h⟩ := h1
    obtain ⟨U', hU', h'⟩ := h2
    exact ⟨U ⊓ U', hU.inter hU', fun u hu g => by simp [h u hu.1, h' u hu.2]⟩
  | smul c f _ h1 =>
    obtain ⟨U, hU, h⟩ := h1
    exact ⟨U, hU, fun u hu g => by simp [h u hu]⟩
theorem continuous_of_stabilizer {f : G → ℂ} {U : Subgroup G} (hU : IsOpen (U : Set G))
    (h : ∀ u ∈ U, ∀ g, f (g * u) = f g) : Continuous f := by
  rw [continuous_iff_continuousAt]
  intro g
  have hopen : IsOpen ((fun y => g⁻¹ * y) ⁻¹' (U : Set G)) :=
    hU.preimage (by fun_prop)
  have hev : ∀ᶠ y in 𝓝 g, f g = f y := by
    filter_upwards [hopen.mem_nhds (by simp [U.one_mem])] with y hy
    have := h _ hy g
    simpa using this.symm
  exact continuousAt_const.congr hev
theorem continuous_of_mem {K : Subgroup G} (hKo : IsOpen (K : Set G)) {φ : G → ℂ}
    (hr : ∀ g, ∀ k ∈ K, φ (g * k) = φ g) {f : G → ℂ} (hf : f ∈ translates φ) : Continuous f := by
  obtain ⟨U, hU, h⟩ := exists_open_stabilizer hKo hr hf
  exact continuous_of_stabilizer hU h
end Top
section Form
variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [T2Space G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
def ip (κ : Measure G) (K : Subgroup G) (f f' : G → ℂ) : ℂ :=
  ∫ k in (K : Set G), conj (f k) * f' k ∂κ
variable {κ : Measure G} [κ.IsHaarMeasure] {K : Subgroup G}
theorem integrableOn_mul (hKc : IsCompact (K : Set G)) {f f' : G → ℂ} (hf : Continuous f)
    (hf' : Continuous f') : IntegrableOn (fun k => conj (f k) * f' k) (K : Set G) κ := by
  have : Continuous fun k => conj (f k) * f' k := by
    have := Complex.continuous_conj
    fun_prop
  exact this.continuousOn.integrableOn_compact hKc
theorem ip_add_left (hKc : IsCompact (K : Set G)) {f f' f'' : G → ℂ} (hf : Continuous f)
    (hf' : Continuous f') (hf'' : Continuous f'') :
    ip κ K (f + f') f'' = ip κ K f f'' + ip κ K f' f'' := by
  unfold ip
  rw [← integral_add (integrableOn_mul hKc hf hf'') (integrableOn_mul hKc hf' hf'')]
  congr 1; funext k; simp [add_mul]
theorem ip_smul_left (c : ℂ) (f f' : G → ℂ) : ip κ K (c • f) f' = conj c * ip κ K f f' := by
  unfold ip
  rw [← integral_const_mul]
  congr 1; funext k; simp [mul_assoc]
theorem conj_ip (f f' : G → ℂ) : conj (ip κ K f' f) = ip κ K f f' := by
  unfold ip
  rw [← integral_conj]
  congr 1; funext k; simp [mul_comm]
theorem ip_self (f : G → ℂ) :
    ip κ K f f = ((∫ k in (K : Set G), ‖f k‖ ^ 2 ∂κ : ℝ) : ℂ) := by
  unfold ip
  rw [← integral_complex_ofReal]
  congr 1; funext k
  rw [Complex.conj_mul']; push_cast; rfl
theorem eq_zero_on_of_ip_self (hKo : IsOpen (K : Set G)) (hKc : IsCompact (K : Set G))
    {f : G → ℂ} (hf : Continuous f) (h0 : ip κ K f f = 0) : ∀ k ∈ K, f k = 0 := by
  rw [ip_self, Complex.ofReal_eq_zero] at h0
  have hint : IntegrableOn (fun k => ‖f k‖ ^ 2) (K : Set G) κ :=
    (by fun_prop : Continuous fun k => ‖f k‖ ^ 2).continuousOn.integrableOn_compact hKc
  have hae := (setIntegral_eq_zero_iff_of_nonneg_ae
    (Filter.Eventually.of_forall fun k => by positivity) hint).1 h0
  have hae' := (ae_restrict_iff' hKo.measurableSet).1 hae
  have hopen : IsOpen ((K : Set G) ∩ {k | f k ≠ 0}) :=
    hKo.inter (isOpen_ne_fun hf continuous_const)
  have hnull : κ ((K : Set G) ∩ {k | f k ≠ 0}) = 0 := by
    refine measure_mono_null ?_ (ae_iff.1 hae')
    rintro k ⟨hk, hne⟩ hcon
    exact hne (by simpa using hcon hk)
  have hempty := (hopen.measure_eq_zero_iff κ).1 hnull
  intro k hk
  by_contra hne
  have : k ∈ (K : Set G) ∩ {k | f k ≠ 0} := ⟨hk, hne⟩
  rw [hempty] at this
  exact this
def core (hKo : IsOpen (K : Set G)) (hKc : IsCompact (K : Set G)) (κ : Measure G)
    [κ.IsHaarMeasure] (φ : G → ℂ) (hr : ∀ g, ∀ k ∈ K, φ (g * k) = φ g)
    (hz : ∀ g, ∃ (z : ℂ) (k : G), k ∈ K ∧ ∀ x, φ (g * x) = z * φ (k * x)) :
    InnerProductSpace.Core ℂ (translates φ) where
  inner f f' := ip κ K f f'
  conj_inner_symm f f' := conj_ip _ _
  re_inner_nonneg f := by
    change 0 ≤ RCLike.re (ip κ K f f)
    rw [ip_self]
    simpa using integral_nonneg fun k => by positivity
  add_left f f' f'' := by
    change ip κ K ((f + f' : translates φ) : G → ℂ) f'' = ip κ K f f'' + ip κ K f' f''
    rw [Submodule.coe_add]
    exact ip_add_left hKc (continuous_of_mem hKo hr f.2) (continuous_of_mem hKo hr f'.2)
      (continuous_of_mem hKo hr f''.2)
  smul_left f f' c := by
    change ip κ K ((c • f : translates φ) : G → ℂ) f' = conj c * ip κ K f f'
    rw [Submodule.coe_smul]
    exact ip_smul_left c _ _
  definite f h0 := by
    have hK := eq_zero_on_of_ip_self hKo hKc (continuous_of_mem hKo hr f.2) h0
    ext g
    obtain ⟨z, k, hk, hzk⟩ := hz g
    rw [eval_eq_of_mem hzk f.2, hK k hk]
    simp
end Form
end GlobalTheory.CompanionTheory.SphericalRep



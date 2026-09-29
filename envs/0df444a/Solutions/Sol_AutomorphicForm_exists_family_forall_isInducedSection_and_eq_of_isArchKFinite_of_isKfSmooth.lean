-- Prove2me | solution 1 for AutomorphicForm.exists_family_forall_isInducedSection_and_eq_of_isArchKFinite_of_isKfSmooth
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/7c9529ae-bede-5923-8fd0-6dd3111f8056

import Mathlib
import Definitions.Def_AutomorphicForm_InducedSection
import Definitions.Def_AutomorphicForm_EtaFamily
import Definitions.Def_AutomorphicForm_SmoothAutomorphicFnAt
import Definitions.Def_AutomorphicForm_ArchKFinite
import Definitions.Def_NumberField_AdelicHaar
import Definitions.Def_NumberField_AdelicHeight
import Theorems.Thm_AutomorphicForm_isInducedSection_adelicHeight_cpow
import Theorems.Thm_NumberField_AdelicHeight_continuous_adelicHeight
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_family_forall_isInducedSection_and_eq_of_isArchKFinite_of_isKfSmooth
p2m_attr_erase "instance" "instCountableOfNumberField_definitions"

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicHeight NumberField.AdelicLevel
p2m_open "AutomorphicForm P2MW.S_AutomorphicForm_exists_family_forall_isInducedSection_and_eq_of_isArchKFinite_of_isKfSmooth.AutomorphicForm AutomorphicForm.WindowedSiegel FLT.SmoothVectors IsDedekindDomain"
open scoped NNReal

noncomputable section

namespace AutomorphicForm
p2m_export "AutomorphicForm" "IsInducedSection AdelicGL2 IsUnitaryChar cpowChar cpowChar_apply_val etaFst etaSnd etaFst_apply etaSnd_apply finiteAdelicGL2Subgroup IsKfSmooth isKfSmooth_iff archRowIsometrySubgroup IsArchKFiniteAt IsArchKFinite archGLIncl archComponent_archGLIncl_self archComponent_archGLIncl_of_ne adelicArchGLInclAt glArch_adelicArchGLIncl glFin_adelicArchGLIncl isInducedSection_adelicHeight_cpow"
namespace FlatFamilySol
p2m_open "AutomorphicForm"

section Local

variable {K : Type*} [NormedField K] [IsUltrametricDist K]

theorem rowMaxNorm_mul_le (M k : Matrix (Fin 2) (Fin 2) K) (hk : ∀ i j, ‖k i j‖ ≤ 1) :
    rowMaxNorm (M * k) ≤ rowMaxNorm M := by
  have hentry : ∀ j : Fin 2, ‖(M * k) 1 j‖ ≤ rowMaxNorm M := by
    intro j
    rw [Matrix.mul_apply, Fin.sum_univ_two]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
    · rw [norm_mul]
      exact (mul_le_of_le_one_right (norm_nonneg _) (hk 0 j)).trans (le_max_left _ _)
    · rw [norm_mul]
      exact (mul_le_of_le_one_right (norm_nonneg _) (hk 1 j)).trans (le_max_right _ _)
  exact max_le (hentry 0) (hentry 1)

theorem norm_det_eq_one_of_integral (k : GL (Fin 2) K)
    (h : ∀ i j, ‖(k : Matrix (Fin 2) (Fin 2) K) i j‖ ≤ 1)
    (h' : ∀ i j, ‖((k⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) i j‖ ≤ 1) :
    ‖(k : Matrix (Fin 2) (Fin 2) K).det‖ = 1 := by
  have hd : ‖(k : Matrix (Fin 2) (Fin 2) K).det‖ ≤ 1 := norm_det_le_one h
  have hd' : ‖((k⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K).det‖ ≤ 1 := norm_det_le_one h'
  have hprod : ‖(k : Matrix (Fin 2) (Fin 2) K).det‖
      * ‖((k⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K).det‖ = 1 := by
    rw [← norm_mul, ← Matrix.det_mul, ← Matrix.GeneralLinearGroup.coe_mul, mul_inv_cancel,
      Units.val_one, Matrix.det_one, norm_one]
  refine le_antisymm hd ?_
  by_contra hlt
  push Not at hlt
  have := mul_lt_one_of_nonneg_of_lt_one_left (norm_nonneg _) hlt hd'
  rw [hprod] at this
  exact lt_irrefl _ this

theorem finLocalHeight_mul_of_integral (g k : GL (Fin 2) K)
    (h : ∀ i j, ‖(k : Matrix (Fin 2) (Fin 2) K) i j‖ ≤ 1)
    (h' : ∀ i j, ‖((k⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) i j‖ ≤ 1) :
    finLocalHeight (g * k) = finLocalHeight g := by
  have hle : rowMaxNorm ((g * k : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)
      ≤ rowMaxNorm (g : Matrix (Fin 2) (Fin 2) K) := by
    rw [Matrix.GeneralLinearGroup.coe_mul]
    exact rowMaxNorm_mul_le _ _ h
  have hge : rowMaxNorm (g : Matrix (Fin 2) (Fin 2) K)
      ≤ rowMaxNorm ((g * k : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) := by
    have hg : (g : Matrix (Fin 2) (Fin 2) K)
        = ((g * k : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)
          * ((k⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) := by
      rw [← Matrix.GeneralLinearGroup.coe_mul, mul_inv_cancel_right]
    conv_lhs => rw [hg]
    exact rowMaxNorm_mul_le _ _ h'
  unfold finLocalHeight
  rw [le_antisymm hle hge, Matrix.GeneralLinearGroup.coe_mul, Matrix.det_mul, norm_mul,
    norm_det_eq_one_of_integral k h h', mul_one]

end Local

section Adelic

variable (F : Type) [Field F] [NumberField F]

theorem finHeight_mul_of_mem (g : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F))
    {k : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F)} (hk : k ∈ finiteIntegralGL2 (𝓞 F) F) :
    finHeight F (g * k) = finHeight F g := by
  rw [mem_finiteIntegralGL2_iff] at hk
  unfold finHeight
  refine finprod_congr fun v => ?_
  rw [map_mul]
  refine finLocalHeight_mul_of_integral _ _ (fun i j => ?_) (fun i j => ?_)
  · rw [finComponent_apply]
    exact norm_le_one_of_mem_adicCompletionIntegers (hk.1 i j v)
  · rw [← map_inv, finComponent_apply]
    exact norm_le_one_of_mem_adicCompletionIntegers (hk.2 i j v)

theorem adelicHeight_mul_of_mem_finite (g u : AdelicGL2 (𝓞 F) F)
    (hu : u ∈ finiteAdelicGL2Subgroup F) (hu' : u ∈ levelZero (𝓞 F) F ⊤) :
    adelicHeight F (g * u) = adelicHeight F g := by
  have h1 : glArch (𝓞 F) F u = 1 := hu
  unfold adelicHeight
  rw [map_mul, map_mul, h1, mul_one, finHeight_mul_of_mem F _ hu']

theorem adelicHeight_mul_of_mem_archRowIsometrySubgroup (w : InfinitePlace F)
    (g k : AdelicGL2 (𝓞 F) F) (hk : k ∈ archRowIsometrySubgroup F w) :
    adelicHeight F (g * k) = adelicHeight F g := by
  obtain ⟨k₀, hk₀, rfl⟩ := Subgroup.mem_map.mp hk
  have hfin : glFin (𝓞 F) F (adelicArchGLInclAt F w k₀) = 1 :=
    glFin_adelicArchGLIncl F (archGLIncl F w k₀)
  have harch : glArch (𝓞 F) F (adelicArchGLInclAt F w k₀) = archGLIncl F w k₀ :=
    glArch_adelicArchGLIncl F (archGLIncl F w k₀)
  unfold adelicHeight
  rw [map_mul, map_mul, hfin, mul_one, harch]
  congr 1
  refine archHeight_mul_rowIsometry F _ fun v => ?_
  by_cases hvw : v = w
  · subst hvw
    rw [archComponent_archGLIncl_self]
    exact hk₀
  · rw [archComponent_archGLIncl_of_ne F hvw]
    exact isRowIsometry_one

theorem isOpen_levelZero_top :
    IsOpen (levelZero (𝓞 F) F (⊤ : Ideal (𝓞 F)) : Set (AdelicGL2 (𝓞 F) F)) :=
  isOpen_levelZero (𝓞 F) F (N := ⊤) (by simp)

end Adelic

section Sections

variable {R K : Type*} [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K]
  [IsFractionRing R K]

theorem isInducedSection_mul {χ₁ χ₂ χ₁' χ₂' : (AdeleRing R K)ˣ →* ℂˣ}
    {φ ψ : AdelicGL2 R K → ℂ}
    (hφ : IsInducedSection R K χ₁ χ₂ φ) (hψ : IsInducedSection R K χ₁' χ₂' ψ) :
    IsInducedSection R K (χ₁ * χ₁') (χ₂ * χ₂') (fun g => φ g * ψ g) := by
  intro b hb g
  show φ (b * g) * ψ (b * g) = _ * (φ g * ψ g)
  rw [hφ b hb g, hψ b hb g, MonoidHom.mul_apply, MonoidHom.mul_apply, Units.val_mul,
    Units.val_mul]
  ring

theorem isInducedSection_congr {χ₁ χ₂ χ₁' χ₂' : (AdeleRing R K)ˣ →* ℂˣ}
    {φ : AdelicGL2 R K → ℂ} (hφ : IsInducedSection R K χ₁ χ₂ φ)
    (h₁ : χ₁ = χ₁') (h₂ : χ₂ = χ₂') : IsInducedSection R K χ₁' χ₂' φ := by
  subst h₁; subst h₂; exact hφ

theorem cpowChar_mul_cpowChar (α : (AdeleRing R K)ˣ →* ℝˣ) (hα : ∀ x, 0 < ((α x : ℝˣ) : ℝ))
    (a b : ℂ) : cpowChar α hα a * cpowChar α hα b = cpowChar α hα (a + b) := by
  ext x
  rw [MonoidHom.mul_apply, Units.val_mul, cpowChar_apply_val, cpowChar_apply_val,
    cpowChar_apply_val, Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr (hα x).ne')]

theorem etaFst_mul_etaFst_one (μ : (AdeleRing R K)ˣ →* ℂˣ) (α : (AdeleRing R K)ˣ →* ℝˣ)
    (hα : ∀ x, 0 < ((α x : ℝˣ) : ℝ)) (s₀ s : ℂ) :
    etaFst μ α hα s₀ * etaFst 1 α hα (s - s₀ - 1 / 2) = etaFst μ α hα s := by
  have hexp : s + 1 / 2 = (s₀ + 1 / 2) + (s - s₀ - 1 / 2 + 1 / 2) := by ring
  refine MonoidHom.ext fun x => ?_
  rw [MonoidHom.mul_apply, etaFst_apply, etaFst_apply, etaFst_apply, MonoidHom.one_apply,
    one_mul, mul_assoc, ← MonoidHom.mul_apply (cpowChar α hα (s₀ + 1 / 2)),
    cpowChar_mul_cpowChar, ← hexp]

theorem etaSnd_mul_etaSnd_one (ν : (AdeleRing R K)ˣ →* ℂˣ) (α : (AdeleRing R K)ˣ →* ℝˣ)
    (hα : ∀ x, 0 < ((α x : ℝˣ) : ℝ)) (s₀ s : ℂ) :
    etaSnd ν α hα s₀ * etaSnd 1 α hα (s - s₀ - 1 / 2) = etaSnd ν α hα s := by
  have hexp : -(s + 1 / 2) = -(s₀ + 1 / 2) + -(s - s₀ - 1 / 2 + 1 / 2) := by ring
  refine MonoidHom.ext fun x => ?_
  rw [MonoidHom.mul_apply, etaSnd_apply, etaSnd_apply, etaSnd_apply, MonoidHom.one_apply,
    one_mul, mul_assoc, ← MonoidHom.mul_apply (cpowChar α hα (-(s₀ + 1 / 2))),
    cpowChar_mul_cpowChar, ← hexp]

end Sections

section Family

variable (F : Type) [Field F] [NumberField F]

def flatFactor (H : AdelicGL2 (𝓞 F) F → ℝ) (t : ℂ) (g : AdelicGL2 (𝓞 F) F) : ℂ :=
  ((H g : ℝ) : ℂ) ^ t

def flatFamily (H : AdelicGL2 (𝓞 F) F → ℝ) (s₀ : ℂ) (φ : AdelicGL2 (𝓞 F) F → ℂ)
    (s : ℂ) (g : AdelicGL2 (𝓞 F) F) : ℂ :=
  φ g * flatFactor F H (s - s₀) g

variable {F}

theorem flatFamily_apply (H : AdelicGL2 (𝓞 F) F → ℝ) (s₀ : ℂ) (φ : AdelicGL2 (𝓞 F) F → ℂ)
    (s : ℂ) (g : AdelicGL2 (𝓞 F) F) :
    flatFamily F H s₀ φ s g = φ g * ((H g : ℝ) : ℂ) ^ (s - s₀) := rfl

theorem flatFamily_self (H : AdelicGL2 (𝓞 F) F → ℝ) (s₀ : ℂ) (φ : AdelicGL2 (𝓞 F) F → ℂ) :
    flatFamily F H s₀ φ s₀ = φ := by
  funext g
  rw [flatFamily_apply, sub_self, Complex.cpow_zero, mul_one]

theorem isInducedSection_flatFamily (H : AdelicGL2 (𝓞 F) F → ℝ)
    (α : (AdeleRing (𝓞 F) F)ˣ →* ℝˣ) (hα : ∀ x, 0 < ((α x : ℝˣ) : ℝ))
    (hH : ∀ t : ℂ, IsInducedSection (𝓞 F) F (etaFst 1 α hα t) (etaSnd 1 α hα t)
      (fun g => ((H g : ℝ) : ℂ) ^ (t + 1 / 2)))
    (μ ν : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) (s₀ : ℂ) (φ : AdelicGL2 (𝓞 F) F → ℂ)
    (hφ : IsInducedSection (𝓞 F) F (etaFst μ α hα s₀) (etaSnd ν α hα s₀) φ) (s : ℂ) :
    IsInducedSection (𝓞 F) F (etaFst μ α hα s) (etaSnd ν α hα s) (flatFamily F H s₀ φ s) := by
  have hflat : IsInducedSection (𝓞 F) F (etaFst 1 α hα (s - s₀ - 1 / 2))
      (etaSnd 1 α hα (s - s₀ - 1 / 2)) (fun g => ((H g : ℝ) : ℂ) ^ (s - s₀)) := by
    have h := hH (s - s₀ - 1 / 2)
    have hexp : s - s₀ - 1 / 2 + 1 / 2 = s - s₀ := by ring
    rw [hexp] at h
    exact h
  exact isInducedSection_congr (isInducedSection_mul hφ hflat) (etaFst_mul_etaFst_one μ α hα s₀ s)
    (etaSnd_mul_etaSnd_one ν α hα s₀ s)

theorem continuous_flatFamily (H : AdelicGL2 (𝓞 F) F → ℝ) (hHc : Continuous H)
    (hHpos : ∀ g, 0 < H g) (s₀ : ℂ) (φ : AdelicGL2 (𝓞 F) F → ℂ) (hφc : Continuous φ) :
    Continuous (fun p : ℂ × AdelicGL2 (𝓞 F) F => flatFamily F H s₀ φ p.1 p.2) := by
  simp only [flatFamily_apply]
  refine (hφc.comp continuous_snd).mul ?_
  refine Continuous.cpow (Complex.continuous_ofReal.comp (hHc.comp continuous_snd))
    (continuous_fst.sub continuous_const) fun p => ?_
  exact Complex.ofReal_mem_slitPlane.mpr (hHpos p.2)

theorem differentiable_flatFamily (H : AdelicGL2 (𝓞 F) F → ℝ) (hHpos : ∀ g, 0 < H g) (s₀ : ℂ)
    (φ : AdelicGL2 (𝓞 F) F → ℂ) (g : AdelicGL2 (𝓞 F) F) :
    Differentiable ℂ (fun s => flatFamily F H s₀ φ s g) := by
  simp only [flatFamily_apply]
  refine Differentiable.const_mul ?_ (φ g)
  exact (differentiable_id.sub_const s₀).const_cpow
    (Or.inl (Complex.ofReal_ne_zero.mpr (hHpos g).ne'))

theorem flatFamily_mul_of_height_eq (H : AdelicGL2 (𝓞 F) F → ℝ) (s₀ : ℂ)
    (φ : AdelicGL2 (𝓞 F) F → ℂ) (s : ℂ) {g k : AdelicGL2 (𝓞 F) F} (hk : H (g * k) = H g) :
    flatFamily F H s₀ φ s (g * k) = φ (g * k) * ((H g : ℝ) : ℂ) ^ (s - s₀) := by
  rw [flatFamily_apply, hk]

theorem isArchKFinite_flatFamily (H : AdelicGL2 (𝓞 F) F → ℝ)
    (hHK : ∀ (w : InfinitePlace F) (g k : AdelicGL2 (𝓞 F) F),
      k ∈ archRowIsometrySubgroup F w → H (g * k) = H g)
    (s₀ : ℂ) (φ : AdelicGL2 (𝓞 F) F → ℂ) (hφK : IsArchKFinite F φ) (s : ℂ) :
    IsArchKFinite F (flatFamily F H s₀ φ s) := by
  classical
  intro w
  obtain ⟨S, hS⟩ := hφK w
  let m : AdelicGL2 (𝓞 F) F → ℂ := fun x => ((H x : ℝ) : ℂ) ^ (s - s₀)
  let L : (AdelicGL2 (𝓞 F) F → ℂ) →ₗ[ℂ] (AdelicGL2 (𝓞 F) F → ℂ) := LinearMap.mulRight ℂ m
  refine ⟨S.image L, fun k hk => ?_⟩
  have hmem : L (fun x => φ (x * k)) ∈ Submodule.map L (Submodule.span ℂ (S : Set _)) :=
    Submodule.mem_map_of_mem (hS k hk)
  rw [Submodule.map_span, ← Finset.coe_image] at hmem
  have heq : (fun x => flatFamily F H s₀ φ s (x * k)) = L (fun x => φ (x * k)) := by
    funext x
    rw [LinearMap.mulRight_apply, Pi.mul_apply, flatFamily_mul_of_height_eq H s₀ φ s (hHK w x k hk)]
  rw [heq]
  exact hmem

theorem isKfSmooth_flatFamily (H : AdelicGL2 (𝓞 F) F → ℝ)
    (U : Subgroup (AdelicGL2 (𝓞 F) F)) (hUo : IsOpen (U : Set (AdelicGL2 (𝓞 F) F)))
    (hHU : ∀ g u : AdelicGL2 (𝓞 F) F, u ∈ finiteAdelicGL2Subgroup F → u ∈ U → H (g * u) = H g)
    (s₀ : ℂ) (φ : AdelicGL2 (𝓞 F) F → ℂ) (hφf : IsKfSmooth F φ) (s : ℂ) :
    IsKfSmooth F (flatFamily F H s₀ φ s) := by
  rw [isKfSmooth_iff, isSmoothVector_iff_isOpen_stabilizer] at hφf ⊢
  set Hf := finiteAdelicGL2Subgroup F with hHf
  let U' : Subgroup ↥Hf := U.comap Hf.subtype
  have hU'o : IsOpen (U' : Set ↥Hf) := hUo.preimage continuous_subtype_val
  refine Subgroup.isOpen_mono
    (H₁ := MulAction.stabilizer ↥Hf (RightTranslationFn.mk φ) ⊓ U') (fun u hu => ?_) ?_
  · obtain ⟨hu1, hu2⟩ := Subgroup.mem_inf.mp hu
    rw [MulAction.mem_stabilizer_iff] at hu1 ⊢
    refine RightTranslationFn.ext fun x => ?_
    have hφx : φ (x * (u : AdelicGL2 (𝓞 F) F)) = φ x :=
      congrArg (fun f => RightTranslationFn.toFun f x) hu1
    have hHx : H (x * (u : AdelicGL2 (𝓞 F) F)) = H x := hHU x u u.2 hu2
    show flatFamily F H s₀ φ s (x * (u : AdelicGL2 (𝓞 F) F)) = flatFamily F H s₀ φ s x
    rw [flatFamily_apply, flatFamily_apply, hφx, hHx]
  · rw [Subgroup.coe_inf]
    exact hφf.inter hU'o

theorem exists_submodule_coeff_flatFamily (H : AdelicGL2 (𝓞 F) F → ℝ) (w : InfinitePlace F)
    (hHK : ∀ g k : AdelicGL2 (𝓞 F) F, k ∈ archRowIsometrySubgroup F w → H (g * k) = H g)
    (s₀ : ℂ) (φ : AdelicGL2 (𝓞 F) F → ℂ) (hφK : IsArchKFiniteAt F w φ) :
    ∃ W : Submodule ℂ (↥(archRowIsometrySubgroup F w) → ℂ),
      FiniteDimensional ℂ W ∧ ∀ (s : ℂ) (g : AdelicGL2 (𝓞 F) F),
        (fun k : ↥(archRowIsometrySubgroup F w) =>
          flatFamily F H s₀ φ s (g * (k : AdelicGL2 (𝓞 F) F))) ∈ W := by
  classical
  obtain ⟨S, hS⟩ := hφK

  let V₀ : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ) := Submodule.span ℂ (S : Set _)
  haveI : FiniteDimensional ℂ V₀ := FiniteDimensional.span_finset ℂ S

  let Θ : ↥(archRowIsometrySubgroup F w) → V₀ := fun k =>
    ⟨fun x => φ (x * (k : AdelicGL2 (𝓞 F) F)), hS k k.2⟩

  let T : Module.Dual ℂ V₀ →ₗ[ℂ] (↥(archRowIsometrySubgroup F w) → ℂ) :=
    LinearMap.pi fun k => Module.Dual.eval ℂ V₀ (Θ k)
  refine ⟨LinearMap.range T, inferInstance, fun s g => ?_⟩

  let ℓ : Module.Dual ℂ V₀ := (LinearMap.proj g).comp V₀.subtype
  refine ⟨(((H g : ℝ) : ℂ) ^ (s - s₀)) • ℓ, ?_⟩
  rw [map_smul]
  funext k
  rw [Pi.smul_apply, LinearMap.pi_apply, Module.Dual.eval_apply, smul_eq_mul,
    flatFamily_mul_of_height_eq H s₀ φ s (hHK g k k.2), mul_comm]
  rfl

end Family

end AutomorphicForm.FlatFamilySol

end

open AutomorphicForm.FlatFamilySol in
theorem solution
    (F : Type) [Field F] [NumberField F] :
    let α : (AdeleRing (𝓞 F) F)ˣ →* ℝˣ :=
      ((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp
        (distribHaarChar (AdeleRing (𝓞 F) F))).toHomUnits
    ∀ (hα : ∀ x, 0 < ((α x : ℝˣ) : ℝ))
      (μ ν : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ)
      (_hμ : AutomorphicForm.IsUnitaryChar (𝓞 F) F μ) (_hν : AutomorphicForm.IsUnitaryChar (𝓞 F) F ν)
      (s₀ : ℂ) (φ : AdelicGL2 (𝓞 F) F → ℂ)
      (_hφ : AutomorphicForm.IsInducedSection (𝓞 F) F
        (AutomorphicForm.etaFst μ α hα s₀) (AutomorphicForm.etaSnd ν α hα s₀) φ)
      (_hφc : Continuous φ) (_hφK : AutomorphicForm.IsArchKFinite F φ) (_hφf : AutomorphicForm.IsKfSmooth F φ),
    ∃ Φ : ℂ → AdelicGL2 (𝓞 F) F → ℂ,
      Φ s₀ = φ ∧
      (∀ s, AutomorphicForm.IsInducedSection (𝓞 F) F
        (AutomorphicForm.etaFst μ α hα s) (AutomorphicForm.etaSnd ν α hα s) (Φ s)) ∧
      (∀ s, AutomorphicForm.IsArchKFinite F (Φ s)) ∧
      (∀ s, AutomorphicForm.IsKfSmooth F (Φ s)) ∧
      Continuous (fun p : ℂ × AdelicGL2 (𝓞 F) F => Φ p.1 p.2) ∧
      (∀ g, Differentiable ℂ (fun s => Φ s g)) ∧
      (∀ w : NumberField.InfinitePlace F,
        ∃ W : Submodule ℂ (↥(AutomorphicForm.archRowIsometrySubgroup F w) → ℂ),
          FiniteDimensional ℂ W ∧ ∀ (s : ℂ) (g : AdelicGL2 (𝓞 F) F),
            (fun k : ↥(AutomorphicForm.archRowIsometrySubgroup F w) =>
              Φ s (g * (k : AdelicGL2 (𝓞 F) F))) ∈ W) := by
  intro α hα μ ν _hμ _hν s₀ φ hφ hφc hφK hφf
  obtain ⟨-, -, hind⟩ := AutomorphicForm.isInducedSection_adelicHeight_cpow F
  have hH : ∀ t : ℂ, IsInducedSection (𝓞 F) F (etaFst 1 α hα t) (etaSnd 1 α hα t)
      (fun g => ((adelicHeight F g : ℝ) : ℂ) ^ (t + 1 / 2)) := fun t => hind hα t
  have hHK : ∀ (w : InfinitePlace F) (g k : AdelicGL2 (𝓞 F) F),
      k ∈ archRowIsometrySubgroup F w → adelicHeight F (g * k) = adelicHeight F g :=
    fun w g k hk => adelicHeight_mul_of_mem_archRowIsometrySubgroup F w g k hk
  refine ⟨flatFamily F (adelicHeight F) s₀ φ, flatFamily_self _ s₀ φ,
    fun s => isInducedSection_flatFamily (adelicHeight F) α hα hH μ ν s₀ φ hφ s,
    fun s => isArchKFinite_flatFamily (adelicHeight F) hHK s₀ φ hφK s,
    fun s => isKfSmooth_flatFamily (adelicHeight F) (levelZero (𝓞 F) F ⊤) (isOpen_levelZero_top F)
      (fun g u hu hu' => adelicHeight_mul_of_mem_finite F g u hu hu') s₀ φ hφf s,
    continuous_flatFamily (adelicHeight F) (continuous_adelicHeight F) adelicHeight_pos s₀ φ hφc,
    fun g => differentiable_flatFamily (adelicHeight F) adelicHeight_pos s₀ φ g,
    fun w => exists_submodule_coeff_flatFamily (adelicHeight F) w (hHK w) s₀ φ (hφK w)⟩

end S_AutomorphicForm_exists_family_forall_isInducedSection_and_eq_of_isArchKFinite_of_isKfSmooth
end P2MW
export P2MW.S_AutomorphicForm_exists_family_forall_isInducedSection_and_eq_of_isArchKFinite_of_isKfSmooth (solution)

-- Prove2me | solution 1 for AutomorphicForm.exists_measure_lintegral_translate_eq_mul_and_setLIntegral_le_mul_of_coversModCentre_of_finite
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/64d120ac-605c-54bc-8eb6-257d62258897

import Theorems.Thm_AutomorphicForm_exists_measurableSet_isFundamentalDomain_subset_iUnion_integralWindowedSiegelSet_of_coversModCentre
import Theorems.Thm_NumberField_AdeleRing_distribHaarChar_algebraMap
import Theorems.Thm_NumberField_TateGlobal_compactSpace_normOneIdeleClass
import Theorems.Thm_NumberField_TateGlobal_ideleNorm_det_eq_prod_archDetNorm_pow_mult
import Theorems.Thm_AutomorphicForm_exists_finset_globalPoints_mul_mul_centralScalar_mem_of_coversModCentre_of_ideleNorm_det_mem_Icc
import Definitions.Def_AutomorphicForm_ProductionPinsGeneral
import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_measure_lintegral_translate_eq_mul_and_setLIntegral_le_mul_of_coversModCentre_of_finite
p2m_attr_erase "instance" "instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions instCountableOfNumberField_definitions"

set_option autoImplicit false
set_option maxHeartbeats 3200000

open IsDedekindDomain NumberField NumberField.AdelicLevel NumberField.AdelicHaar NumberField.AdelicVolume NumberField.TateGlobal MeasureTheory

open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open scoped ENNReal NNReal Pointwise

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel

noncomputable section

namespace K1aOfFinite

variable {F : Type} [Field F] [NumberField F]

local notation "𝔸" => AdeleRing (𝓞 F) F
local notation "𝔾" => AdelicGL2 (𝓞 F) F
local notation "Γp" => MonoidHom.range (globalPoints (𝓞 F) F)
local notation "μH" => adelicGLHaar (Fin 2) (𝓞 F) F

theorem globalPoints_apply (γ : GL (Fin 2) F) (i j : Fin 2) :
    ((globalPoints (𝓞 F) F γ : 𝔾) : Matrix (Fin 2) (Fin 2) 𝔸) i j =
      algebraMap F 𝔸 ((γ : Matrix (Fin 2) (Fin 2) F) i j) := rfl

theorem det_globalPoints (γ : GL (Fin 2) F) :
    Matrix.GeneralLinearGroup.det (globalPoints (𝓞 F) F γ) =
      Units.map (algebraMap F 𝔸).toMonoidHom (Matrix.GeneralLinearGroup.det γ) := by
  unfold globalPoints
  rw [Matrix.GeneralLinearGroup.map_det]
  rfl

theorem det_centralScalar (z : 𝔸ˣ) :
    Matrix.GeneralLinearGroup.det (centralScalar (𝓞 F) F z) = z ^ 2 := by
  show Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.scalar (Fin 2) z) = z ^ 2
  rw [Matrix.GeneralLinearGroup.det_scalar, Fintype.card_fin]

theorem globalPoints_scalar (a : Fˣ) :
    globalPoints (𝓞 F) F (Matrix.GeneralLinearGroup.scalar (Fin 2) a) =
      centralScalar (𝓞 F) F (Units.map (algebraMap F 𝔸).toMonoidHom a) := by
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  rw [globalPoints_apply]
  by_cases h : i = j
  · subst h
    rw [centralScalar_apply_eq]
    show algebraMap F 𝔸 ((Matrix.scalar (Fin 2) (a : F)) i i) = _
    simp
  · rw [centralScalar_apply_ne _ h]
    show algebraMap F 𝔸 ((Matrix.scalar (Fin 2) (a : F)) i j) = _
    simp [h]

theorem ideleNorm_principal (a : Fˣ) :
    ideleNorm F (Units.map (algebraMap F 𝔸).toMonoidHom a) = 1 := by
  unfold ideleNorm
  rw [@NumberField.AdeleRing.distribHaarChar_algebraMap F _ _ (adeleBorel (𝓞 F) F)
    (borelSpace_adeleBorel (𝓞 F) F) a]
  simp

theorem ideleNorm_det_globalPoints_mul (γ : GL (Fin 2) F) (g : 𝔾) :
    ideleNorm F (Matrix.GeneralLinearGroup.det (globalPoints (𝓞 F) F γ * g)) =
      ideleNorm F (Matrix.GeneralLinearGroup.det g) := by
  rw [map_mul, ideleNorm_mul, det_globalPoints, ideleNorm_principal, one_mul]

theorem ideleNorm_det_mul (g h : 𝔾) :
    ideleNorm F (Matrix.GeneralLinearGroup.det (g * h)) =
      ideleNorm F (Matrix.GeneralLinearGroup.det g) *
        ideleNorm F (Matrix.GeneralLinearGroup.det h) := by
  rw [map_mul, ideleNorm_mul]

scoped instance countable_gl2 : Countable (GL (Fin 2) F) := by
  haveI : Countable F := Finsupp.Countable.of_moduleFinite (R := ℚ)
  refine Function.Injective.countable
    (f := fun g : GL (Fin 2) F => fun i j => (g : Matrix (Fin 2) (Fin 2) F) i j) ?_
  intro a b h
  exact Matrix.GeneralLinearGroup.ext fun i j => congrFun (congrFun h i) j

scoped instance countable_range : Countable Γp :=
  Function.Surjective.countable (MonoidHom.rangeRestrict_surjective (globalPoints (𝓞 F) F))

theorem exists_eq_globalPoints (γ : Γp) : ∃ δ : GL (Fin 2) F, globalPoints (𝓞 F) F δ = γ :=
  γ.2

def pre (γ : Γp) : GL (Fin 2) F := Classical.choose (exists_eq_globalPoints γ)

theorem globalPoints_pre (γ : Γp) : globalPoints (𝓞 F) F (pre γ) = γ :=
  Classical.choose_spec (exists_eq_globalPoints γ)

theorem smul_def' (γ : Γp) (g : 𝔾) : γ • g = (γ : 𝔾) * g := rfl

theorem continuous_gldet : Continuous (Matrix.GeneralLinearGroup.det : 𝔾 → 𝔸ˣ) := by
  rw [Units.continuous_iff]
  constructor
  · show Continuous fun g : 𝔾 => ((g : 𝔾) : Matrix (Fin 2) (Fin 2) 𝔸).det
    exact Units.continuous_val.matrix_det
  · show Continuous fun g : 𝔾 => (((g : 𝔾)⁻¹ : 𝔾) : Matrix (Fin 2) (Fin 2) 𝔸).det
    exact (Units.continuous_val.comp continuous_inv).matrix_det

theorem continuous_scalarMatrix : Continuous fun z : 𝔸 => Matrix.scalar (Fin 2) z := by
  refine continuous_pi fun i => continuous_pi fun j => ?_
  by_cases h : i = j
  · subst h
    simp only [Matrix.scalar_apply, Matrix.diagonal_apply_eq]
    exact continuous_id
  · simp only [Matrix.scalar_apply, Matrix.diagonal_apply_ne _ h]
    exact continuous_const

theorem continuous_centralScalar : Continuous (centralScalar (𝓞 F) F : 𝔸ˣ → 𝔾) := by
  rw [Units.continuous_iff]
  constructor
  · show Continuous fun z : 𝔸ˣ => Matrix.scalar (Fin 2) ((z : 𝔸ˣ) : 𝔸)
    exact continuous_scalarMatrix.comp Units.continuous_val
  · show Continuous fun z : 𝔸ˣ =>
      ((centralScalar (𝓞 F) F z)⁻¹ : 𝔾).val
    have : (fun z : 𝔸ˣ => ((centralScalar (𝓞 F) F z)⁻¹ : 𝔾).val) =
        fun z : 𝔸ˣ => Matrix.scalar (Fin 2) (((z⁻¹ : 𝔸ˣ) : 𝔸)) := by
      funext z
      rw [← map_inv]
      rfl
    rw [this]
    exact continuous_scalarMatrix.comp Units.continuous_coe_inv

theorem continuous_diagOne : Continuous (diagOne : 𝔸ˣ → 𝔾) := by
  rw [Units.continuous_iff]
  constructor
  · show Continuous fun z : 𝔸ˣ => Matrix.diagonal ![((z : 𝔸ˣ) : 𝔸), 1]
    refine continuous_pi fun i => continuous_pi fun j => ?_
    by_cases h : i = j
    · subst h
      simp only [Matrix.diagonal_apply_eq]
      fin_cases i
      · exact Units.continuous_val
      · exact continuous_const
    · simp only [Matrix.diagonal_apply_ne _ h]
      exact continuous_const
  · show Continuous fun z : 𝔸ˣ => ((diagOne z)⁻¹ : 𝔾).val
    have : (fun z : 𝔸ˣ => ((diagOne z)⁻¹ : 𝔾).val) =
        fun z : 𝔸ˣ => Matrix.diagonal ![((z⁻¹ : 𝔸ˣ) : 𝔸), 1] := by
      funext z
      rw [← map_inv]
      rfl
    rw [this]
    refine continuous_pi fun i => continuous_pi fun j => ?_
    by_cases h : i = j
    · subst h
      simp only [Matrix.diagonal_apply_eq]
      fin_cases i
      · exact Units.continuous_coe_inv
      · exact continuous_const
    · simp only [Matrix.diagonal_apply_ne _ h]
      exact continuous_const

theorem det_diagOne (z : 𝔸ˣ) : Matrix.GeneralLinearGroup.det (diagOne z : 𝔾) = z := by
  refine Units.ext ?_
  show (Matrix.diagonal ![((z : 𝔸ˣ) : 𝔸), 1]).det = z
  simp

variable (ξ : (⊤ : Subgroup (AdeleRing (𝓞 F) F)ˣ) →* ℂˣ)

def toTop (z : 𝔸ˣ) : (⊤ : Subgroup (AdeleRing (𝓞 F) F)ˣ) := ⟨z, Subgroup.mem_top z⟩

@[scoped simp] theorem toTop_mul (z z' : 𝔸ˣ) : toTop (F := F) (z * z') = toTop z * toTop z' := rfl

def absXi : 𝔸ˣ →* ℝ≥0 where
  toFun z := ‖((ξ (toTop z) : ℂˣ) : ℂ)‖₊
  map_one' := by
    show ‖((ξ (toTop 1) : ℂˣ) : ℂ)‖₊ = 1
    have : toTop (F := F) 1 = 1 := rfl
    rw [this, map_one]; simp
  map_mul' z z' := by
    show ‖((ξ (toTop (z * z')) : ℂˣ) : ℂ)‖₊ = ‖((ξ (toTop z) : ℂˣ) : ℂ)‖₊ * ‖((ξ (toTop z') : ℂˣ) : ℂ)‖₊
    rw [toTop_mul, map_mul, Units.val_mul, nnnorm_mul]

theorem absXi_apply (z : 𝔸ˣ) : absXi ξ z = ‖((ξ (toTop z) : ℂˣ) : ℂ)‖₊ := rfl

theorem absXi_pos (z : 𝔸ˣ) : 0 < absXi ξ z := by
  rw [absXi_apply, pos_iff_ne_zero, ne_eq, nnnorm_eq_zero]
  exact (ξ (toTop z)).ne_zero

theorem absXi_ne_zero (z : 𝔸ˣ) : absXi ξ z ≠ 0 := (absXi_pos ξ z).ne'

def ω (g : 𝔾) : ℝ≥0 := absXi ξ (Matrix.GeneralLinearGroup.det g)

theorem ω_apply (g : 𝔾) : ω ξ g = ‖((ξ (toTop (Matrix.GeneralLinearGroup.det g)) : ℂˣ) : ℂ)‖₊ :=
  rfl

theorem ω_pos (g : 𝔾) : 0 < ω ξ g := absXi_pos ξ _

theorem ω_ne_zero (g : 𝔾) : ω ξ g ≠ 0 := (ω_pos ξ g).ne'

theorem ω_mul (g h : 𝔾) : ω ξ (g * h) = ω ξ g * ω ξ h := by
  unfold ω; rw [map_mul, map_mul]

theorem ω_inv (g : 𝔾) : ω ξ g⁻¹ = (ω ξ g)⁻¹ := by
  unfold ω; rw [map_inv, map_inv]

theorem ω_centralScalar (z : 𝔸ˣ) : ω ξ (centralScalar (𝓞 F) F z) = absXi ξ z ^ 2 := by
  unfold ω; rw [det_centralScalar, map_pow]

theorem ω_diagOne (z : 𝔸ˣ) : ω ξ (diagOne z) = absXi ξ z := by
  unfold ω; rw [det_diagOne]

structure Good (φ₀ : 𝔾 → ℂ) (g₀ : 𝔾) : Prop where
  cont : Continuous φ₀
  ls : IsLsXiFunction (𝓞 F) F ⊤ ξ φ₀
  ne : φ₀ g₀ ≠ 0

variable {ξ}

theorem central_law {φ : 𝔾 → ℂ} (hφ : IsLsXiFunction (𝓞 F) F ⊤ ξ φ) (z : 𝔸ˣ) (g : 𝔾) :
    φ (centralScalar (𝓞 F) F z * g) = ((ξ (toTop z) : ℂˣ) : ℂ) * φ g :=
  hφ.central_transform (toTop z) g

theorem xi_principal {φ₀ : 𝔾 → ℂ} {g₀ : 𝔾} (h : Good ξ φ₀ g₀) (a : Fˣ) :
    ξ (toTop (Units.map (algebraMap F 𝔸).toMonoidHom a)) = 1 := by
  have h1 := h.ls.left_invariant (Matrix.GeneralLinearGroup.scalar (Fin 2) a) g₀
  rw [globalPoints_scalar, central_law h.ls] at h1
  have h2 : ((ξ (toTop (Units.map (algebraMap F 𝔸).toMonoidHom a)) : ℂˣ) : ℂ) = 1 := by
    have := mul_right_cancel₀ h.ne (h1.trans (one_mul _).symm)
    exact this
  exact Units.ext h2

theorem absXi_principal {φ₀ : 𝔾 → ℂ} {g₀ : 𝔾} (h : Good ξ φ₀ g₀) (a : Fˣ) :
    absXi ξ (Units.map (algebraMap F 𝔸).toMonoidHom a) = 1 := by
  rw [absXi_apply, xi_principal h]; simp

theorem ω_globalPoints_mul {φ₀ : 𝔾 → ℂ} {g₀ : 𝔾} (h : Good ξ φ₀ g₀) (γ : GL (Fin 2) F) (g : 𝔾) :
    ω ξ (globalPoints (𝓞 F) F γ * g) = ω ξ g := by
  rw [ω_mul]
  unfold ω
  rw [det_globalPoints, absXi_principal h, one_mul]

theorem ω_range_mul {φ₀ : 𝔾 → ℂ} {g₀ : 𝔾} (h : Good ξ φ₀ g₀) (γ : Γp) (g : 𝔾) : ω ξ ((γ : 𝔾) * g) = ω ξ g := by
  obtain ⟨δ, hδ⟩ := exists_eq_globalPoints γ
  rw [← hδ, ω_globalPoints_mul h]

theorem ω_eq_quot {φ₀ : 𝔾 → ℂ} {g₀ : 𝔾} (h : Good ξ φ₀ g₀) (g : 𝔾) :
    (ω ξ g : ℝ) = ‖φ₀ (centralScalar (𝓞 F) F (Matrix.GeneralLinearGroup.det g) * g₀)‖ / ‖φ₀ g₀‖ := by
  rw [central_law h.ls, norm_mul, mul_div_assoc, div_self (norm_ne_zero_iff.mpr h.ne), mul_one]
  rfl

theorem continuous_ω {φ₀ : 𝔾 → ℂ} {g₀ : 𝔾} (h : Good ξ φ₀ g₀) : Continuous (ω ξ) := by
  have hc : Continuous fun g : 𝔾 => (ω ξ g : ℝ) := by
    have : (fun g : 𝔾 => (ω ξ g : ℝ)) = fun g =>
        ‖φ₀ (centralScalar (𝓞 F) F (Matrix.GeneralLinearGroup.det g) * g₀)‖ / ‖φ₀ g₀‖ :=
      funext (ω_eq_quot h)
    rw [this]
    refine Continuous.div_const (Continuous.norm ?_) _
    exact h.cont.comp ((continuous_centralScalar.comp continuous_gldet).mul continuous_const)
  exact continuous_induced_rng.2 hc

theorem continuous_absXi {φ₀ : 𝔾 → ℂ} {g₀ : 𝔾} (h : Good ξ φ₀ g₀) : Continuous (absXi ξ) := by
  have : (absXi ξ : 𝔸ˣ → ℝ≥0) = fun z => ω ξ (diagOne z) := funext fun z => (ω_diagOne ξ z).symm
  rw [this]
  exact (continuous_ω h).comp continuous_diagOne

theorem absXi_le_one_of_pow_le {x : ℝ≥0} {C : ℝ≥0} (hC : ∀ n : ℕ, x ^ n ≤ C) : x ≤ 1 := by
  by_contra hx
  rw [not_le] at hx
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt C hx
  exact absurd (hC n) (not_le.mpr hn)

theorem absXi_eq_one_of_mem_normOneIdeles {φ₀ : 𝔾 → ℂ} {g₀ : 𝔾} (h : Good ξ φ₀ g₀) {z : 𝔸ˣ}
    (hz : z ∈ normOneIdeles F) : absXi ξ z = 1 := by
  haveI := NumberField.TateGlobal.compactSpace_normOneIdeleClass F
  set H := normOneIdeles F with hH
  set P := (M4aHerbrand.principalIdeles (𝓞 F) F).subgroupOf H with hP

  let ψ : H → ℝ := fun t => (absXi ξ (t : 𝔸ˣ) : ℝ)
  have hψc : Continuous ψ :=
    NNReal.continuous_coe.comp ((continuous_absXi h).comp continuous_subtype_val)
  have hψP : ∀ p : H, p ∈ P → absXi ξ (p : 𝔸ˣ) = 1 := by
    intro p hp
    rw [hP, Subgroup.mem_subgroupOf] at hp
    obtain ⟨a, ha⟩ := hp
    rw [← ha]
    exact absXi_principal h a
  have hψinv : ∀ a b : H, QuotientGroup.leftRel P a b → ψ a = ψ b := by
    intro a b hab
    rw [QuotientGroup.leftRel_apply] at hab
    have h1 := hψP _ hab
    have : (b : 𝔸ˣ) = (a : 𝔸ˣ) * ((a⁻¹ * b : H) : 𝔸ˣ) := by
      simp
    show (absXi ξ (a : 𝔸ˣ) : ℝ) = (absXi ξ (b : 𝔸ˣ) : ℝ)
    rw [this, map_mul, h1, mul_one]
  let ψ' : H ⧸ P → ℝ := Quotient.lift ψ hψinv
  have hψ'c : Continuous ψ' := hψc.quotient_lift hψinv
  obtain ⟨C, hC⟩ := isCompact_univ.exists_bound_of_continuousOn hψ'c.continuousOn
  have hbound : ∀ t : H, (absXi ξ (t : 𝔸ˣ) : ℝ) ≤ C := by
    intro t
    have := hC (QuotientGroup.mk t : H ⧸ P) (Set.mem_univ _)
    rw [Real.norm_eq_abs, abs_le] at this
    exact this.2
  have hC0 : 0 ≤ C := le_trans (NNReal.coe_nonneg _) (hbound 1)

  have hle : ∀ t : H, absXi ξ (t : 𝔸ˣ) ≤ 1 := by
    intro t
    refine absXi_le_one_of_pow_le (C := ⟨C, hC0⟩) fun n => ?_
    have := hbound (t ^ n)
    rw [Subgroup.coe_pow, map_pow] at this
    exact_mod_cast this
  have h1 := hle ⟨z, hz⟩
  have h2 := hle ⟨z, hz⟩⁻¹
  rw [Subgroup.coe_inv, map_inv] at h2
  simp only at h1 h2
  have hpos := absXi_pos ξ z
  have : 1 ≤ absXi ξ z := by
    rwa [inv_le_one₀ hpos] at h2
  exact le_antisymm h1 this

def realEmb (w : InfinitePlace F) : ℝ →+* w.Completion := by
  classical
  exact if hw : w.IsReal then (InfinitePlace.Completion.ringEquivRealOfIsReal hw).symm.toRingHom
  else ((InfinitePlace.Completion.ringEquivComplexOfIsComplex
    (InfinitePlace.not_isReal_iff_isComplex.mp hw)).symm.toRingHom).comp Complex.ofRealHom

theorem extensionEmbedding_realEmb (w : InfinitePlace F) (r : ℝ) :
    InfinitePlace.Completion.extensionEmbedding w (realEmb w r) = (r : ℂ) := by
  unfold realEmb
  split_ifs with hw
  · rw [RingEquiv.toRingHom_eq_coe, RingHom.coe_coe,
      ← InfinitePlace.Completion.extensionEmbeddingOfIsReal_apply hw,
      ← InfinitePlace.Completion.ringEquivRealOfIsReal_apply hw, RingEquiv.apply_symm_apply]
  · rw [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe,
      ← InfinitePlace.Completion.ringEquivComplexOfIsComplex_apply
        (InfinitePlace.not_isReal_iff_isComplex.mp hw), RingEquiv.apply_symm_apply]
    rfl

theorem norm_realEmb (w : InfinitePlace F) (r : ℝ) : ‖realEmb w r‖ = |r| := by
  rw [← (InfinitePlace.Completion.isometry_extensionEmbedding w).norm_map_of_map_zero (map_zero _),
    extensionEmbedding_realEmb, Complex.norm_real, Real.norm_eq_abs]

theorem continuous_realEmb (w : InfinitePlace F) : Continuous (realEmb w) := by
  unfold realEmb
  split_ifs with hw
  · exact (InfinitePlace.Completion.isometryEquivRealOfIsReal hw).symm.continuous
  · exact (InfinitePlace.Completion.isometryEquivComplexOfIsComplex
      (InfinitePlace.not_isReal_iff_isComplex.mp hw)).symm.continuous.comp Complex.continuous_ofReal

theorem realEmb_ne_zero (w : InfinitePlace F) {r : ℝ} (hr : r ≠ 0) : realEmb w r ≠ 0 := by
  intro h
  have := norm_realEmb w r
  rw [h, norm_zero] at this
  exact hr (abs_eq_zero.mp this.symm)

def realUnit (w : InfinitePlace F) (r : ℝ) (hr : r ≠ 0) : (w.Completion)ˣ :=
  Units.mk0 (realEmb w r) (realEmb_ne_zero w hr)

theorem archComponent_archCentralUnit_of_ne (w₀ : InfinitePlace F) (a : (w₀.Completion)ˣ)
    {w : InfinitePlace F} (hw : w ≠ w₀) :
    archComponent F w (glArch (𝓞 F) F (centralScalar (𝓞 F) F (archCentralUnit F w₀ a))) = 1 := by
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  rw [archComponent_apply, glArch_apply, Units.val_one]
  by_cases h : i = j
  · subst h
    rw [centralScalar_apply_eq, Matrix.one_apply_eq]
    exact archCentralUnit_fst_of_ne w₀ a hw
  · rw [centralScalar_apply_ne _ h, Matrix.one_apply_ne h]
    rfl

theorem archDetNorm_one (w : InfinitePlace F) : archDetNorm w (1 : 𝔾) = 1 := by
  unfold archDetNorm
  rw [map_one, map_one, Units.val_one, Matrix.det_one, norm_one]

theorem archDetNorm_archCentralUnit_self (w₀ : InfinitePlace F) (a : (w₀.Completion)ˣ) :
    archDetNorm w₀ (centralScalar (𝓞 F) F (archCentralUnit F w₀ a)) =
      ‖(a : w₀.Completion)‖ * ‖(a : w₀.Completion)‖ := by
  have := archDetNorm_centralScalar_mul w₀ a (1 : 𝔾)
  rw [mul_one, archDetNorm_one, mul_one] at this
  exact this

theorem archDetNorm_archCentralUnit_of_ne (w₀ : InfinitePlace F) (a : (w₀.Completion)ˣ)
    {w : InfinitePlace F} (hw : w ≠ w₀) :
    archDetNorm w (centralScalar (𝓞 F) F (archCentralUnit F w₀ a)) = 1 := by
  unfold archDetNorm
  rw [archComponent_archCentralUnit_of_ne w₀ a hw, Units.val_one, Matrix.det_one, norm_one]

theorem ideleNorm_archCentralUnit (w₀ : InfinitePlace F) (a : (w₀.Completion)ˣ) :
    ideleNorm F (archCentralUnit F w₀ a) = ‖(a : w₀.Completion)‖ ^ w₀.mult := by
  set X : 𝔾 := centralScalar (𝓞 F) F (archCentralUnit F w₀ a) with hX
  have hint : glFin (𝓞 F) F X ∈ finiteIntegralGL2 (𝓞 F) F := by
    rw [hX, glFin_centralScalar_archCentralUnit]
    exact Subgroup.one_mem _
  have hcard := NumberField.TateGlobal.ideleNorm_det_eq_prod_archDetNorm_pow_mult F X hint
  rw [hX, det_centralScalar, sq, ideleNorm_mul] at hcard
  have hprod : ∏ w : InfinitePlace F, archDetNorm w X ^ w.mult =
      (‖(a : w₀.Completion)‖ * ‖(a : w₀.Completion)‖) ^ w₀.mult := by
    rw [Finset.prod_eq_single w₀]
    · rw [hX, archDetNorm_archCentralUnit_self]
    · intro w _ hw
      rw [hX, archDetNorm_archCentralUnit_of_ne w₀ a hw, one_pow]
    · intro hw; exact absurd (Finset.mem_univ w₀) hw
  rw [hprod] at hcard
  have h1 : ideleNorm F (archCentralUnit F w₀ a) ^ 2 = (‖(a : w₀.Completion)‖ ^ w₀.mult) ^ 2 := by
    rw [sq, hcard]; ring
  have hpos : 0 ≤ ideleNorm F (archCentralUnit F w₀ a) := (ideleNorm_pos _).le
  exact (pow_left_inj₀ hpos (by positivity) two_ne_zero).mp h1

def sec (w₀ : InfinitePlace F) (r : ℝ) (hr : 0 < r) : 𝔸ˣ :=
  archCentralUnit F w₀ (realUnit w₀ r hr.ne')

theorem ideleNorm_sec (w₀ : InfinitePlace F) (r : ℝ) (hr : 0 < r) :
    ideleNorm F (sec w₀ r hr) = r ^ w₀.mult := by
  unfold sec realUnit
  rw [ideleNorm_archCentralUnit, Units.val_mk0, norm_realEmb, abs_of_pos hr]

theorem continuousOn_absXi_sec {φ₀ : 𝔾 → ℂ} {g₀ : 𝔾} (h : Good ξ φ₀ g₀) (w₀ : InfinitePlace F) :
    ContinuousOn (fun r : ℝ => if hr : 0 < r then (absXi ξ (sec w₀ r hr) : ℝ) else 0)
      (Set.Ioi 0) := by

  classical

  have hacu : Continuous fun b : (w₀.Completion)ˣ => (archCentralUnit F w₀ b : 𝔸ˣ) := by
    rw [Units.continuous_iff]
    constructor
    · show Continuous fun b : (w₀.Completion)ˣ => ((archCentralUnit F w₀ b : 𝔸ˣ) : 𝔸)
      have : (fun b : (w₀.Completion)ˣ => ((archCentralUnit F w₀ b : 𝔸ˣ) : 𝔸)) =
          fun b : (w₀.Completion)ˣ => (Function.update (1 : InfiniteAdeleRing F) w₀ b.val,
            (1 : FiniteAdeleRing (𝓞 F) F)) := rfl
      rw [this]
      refine Continuous.prodMk ?_ continuous_const
      exact continuous_pi fun w => by
        by_cases hw : w = w₀
        · subst hw
          simp only [Function.update_self]
          exact Units.continuous_val
        · simp only [Function.update_of_ne hw]
          exact continuous_const
    · show Continuous fun b : (w₀.Completion)ˣ => (((archCentralUnit F w₀ b)⁻¹ : 𝔸ˣ) : 𝔸)
      have : (fun b : (w₀.Completion)ˣ => (((archCentralUnit F w₀ b)⁻¹ : 𝔸ˣ) : 𝔸)) =
          fun b : (w₀.Completion)ˣ => (Function.update (1 : InfiniteAdeleRing F) w₀ (b⁻¹).val,
            (1 : FiniteAdeleRing (𝓞 F) F)) := rfl
      rw [this]
      refine Continuous.prodMk ?_ continuous_const
      exact continuous_pi fun w => by
        by_cases hw : w = w₀
        · subst hw
          simp only [Function.update_self]
          exact Units.continuous_coe_inv
        · simp only [Function.update_of_ne hw]
          exact continuous_const

  have hru : ContinuousOn (fun r : ℝ => if hr : 0 < r then (realUnit w₀ r hr.ne' : (w₀.Completion)ˣ)
      else 1) (Set.Ioi 0) := by
    rw [continuousOn_iff_continuous_restrict]
    have heq : (Set.Ioi (0:ℝ)).domRestrict (fun r : ℝ => if hr : 0 < r then
        (realUnit w₀ r hr.ne' : (w₀.Completion)ˣ) else 1) =
        fun r : Set.Ioi (0:ℝ) => realUnit w₀ r.1 (ne_of_gt r.2) := by
      funext r
      rw [Set.domRestrict_apply, dif_pos (show (0:ℝ) < r.1 from r.2)]
    rw [heq, Units.continuous_iff]
    constructor
    · show Continuous fun r : Set.Ioi (0:ℝ) => realEmb w₀ r.1
      exact (continuous_realEmb w₀).comp continuous_subtype_val
    · show Continuous fun r : Set.Ioi (0:ℝ) => ((realUnit w₀ r.1 (ne_of_gt r.2))⁻¹ :
        (w₀.Completion)ˣ).val
      have : (fun r : Set.Ioi (0:ℝ) => ((realUnit w₀ r.1 (ne_of_gt r.2))⁻¹ :
          (w₀.Completion)ˣ).val) = fun r : Set.Ioi (0:ℝ) => (realEmb w₀ r.1)⁻¹ := by
        funext r; rfl
      rw [this]
      refine Continuous.inv₀ ((continuous_realEmb w₀).comp continuous_subtype_val) fun r => ?_
      exact realEmb_ne_zero w₀ (ne_of_gt r.2)
  have hcomp : ContinuousOn (fun r : ℝ => (absXi ξ (archCentralUnit F w₀
      (if hr : 0 < r then (realUnit w₀ r hr.ne' : (w₀.Completion)ˣ) else 1)) : ℝ)) (Set.Ioi 0) :=
    (NNReal.continuous_coe.comp ((continuous_absXi h).comp hacu)).comp_continuousOn hru
  refine hcomp.congr fun r hr => ?_
  simp only [Set.mem_Ioi] at hr
  simp only [dif_pos hr]
  rfl

theorem exists_bounds_ω {φ₀ : 𝔾 → ℂ} {g₀ : 𝔾} (h : Good ξ φ₀ g₀) {e₁ e₂ : ℝ} (he₁ : 0 < e₁) (he : e₁ ≤ e₂) :
    ∃ lo hi : ℝ≥0, 0 < lo ∧ ∀ g : 𝔾,
      ideleNorm F (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc e₁ e₂ → lo ≤ ω ξ g ∧ ω ξ g ≤ hi := by
  classical
  obtain ⟨w₀⟩ := (inferInstance : Nonempty (InfinitePlace F))
  set m : ℕ := w₀.mult with hm
  have hm0 : m ≠ 0 := by
    rw [hm]; unfold InfinitePlace.mult; split_ifs <;> norm_num

  let θ : ℝ → ℝ := fun r => if hr : 0 < r then (absXi ξ (sec w₀ r hr) : ℝ) else 0
  have hθ : ContinuousOn θ (Set.Ioi 0) := continuousOn_absXi_sec h w₀
  let ρ : ℝ → ℝ := fun r => r ^ ((m : ℝ)⁻¹)
  have hρc : Continuous ρ := Real.continuous_rpow_const (by positivity)
  have hρpos : ∀ r, 0 < r → 0 < ρ r := fun r hr => Real.rpow_pos_of_pos hr _
  have hρmaps : Set.MapsTo ρ (Set.Icc e₁ e₂) (Set.Ioi 0) := fun r hr =>
    hρpos r (lt_of_lt_of_le he₁ hr.1)
  have hΘ : ContinuousOn (θ ∘ ρ) (Set.Icc e₁ e₂) := hθ.comp hρc.continuousOn hρmaps
  have hK : IsCompact (Set.Icc e₁ e₂) := isCompact_Icc
  have hne : (Set.Icc e₁ e₂).Nonempty := ⟨e₁, le_rfl, he⟩
  obtain ⟨rmin, hrmin, hmin⟩ := hK.exists_isMinOn hne hΘ
  obtain ⟨rmax, hrmax, hmax⟩ := hK.exists_isMaxOn hne hΘ

  have hval : ∀ g : 𝔾, ideleNorm F (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc e₁ e₂ →
      (ω ξ g : ℝ) = (θ ∘ ρ) (ideleNorm F (Matrix.GeneralLinearGroup.det g)) := by
    intro g hg
    set r := ideleNorm F (Matrix.GeneralLinearGroup.det g) with hr
    have hr0 : 0 < r := ideleNorm_pos _
    have hρr : 0 < ρ r := hρpos r hr0
    show (ω ξ g : ℝ) = θ (ρ r)
    simp only [θ, dif_pos hρr]

    have hns : ideleNorm F (sec w₀ (ρ r) hρr) = r := by
      rw [ideleNorm_sec]
      show (r ^ ((m : ℝ)⁻¹)) ^ m = r
      exact Real.rpow_inv_natCast_pow hr0.le hm0
    have hmem : Matrix.GeneralLinearGroup.det g * (sec w₀ (ρ r) hρr)⁻¹ ∈ normOneIdeles F := by
      rw [mem_normOneIdeles_iff, ideleNorm_mul]
      have : ideleNorm F (sec w₀ (ρ r) hρr)⁻¹ = r⁻¹ := by
        have h1 := ideleNorm_mul (F := F) (sec w₀ (ρ r) hρr) (sec w₀ (ρ r) hρr)⁻¹
        rw [mul_inv_cancel, hns] at h1
        have h2 : ideleNorm F (1 : 𝔸ˣ) = 1 := by
          have := ideleNorm_mul (F := F) 1 1
          rw [mul_one] at this
          have hp := ideleNorm_pos (F := F) 1
          field_simp at this
          nlinarith [this, hp]
        rw [h2] at h1
        field_simp
        linarith
      rw [this, ← hr]
      field_simp
    have h1 := absXi_eq_one_of_mem_normOneIdeles h hmem
    rw [map_mul, map_inv] at h1
    have h2 : absXi ξ (Matrix.GeneralLinearGroup.det g) = absXi ξ (sec w₀ (ρ r) hρr) := by
      have hne := absXi_ne_zero ξ (sec w₀ (ρ r) hρr)
      rw [mul_inv_eq_one₀ hne] at h1
      exact h1
    show ((absXi ξ (Matrix.GeneralLinearGroup.det g) : ℝ≥0) : ℝ) = _
    rw [h2]

  have hlo_pos : 0 < (θ ∘ ρ) rmin := by
    have hρr : 0 < ρ rmin := hρpos rmin (lt_of_lt_of_le he₁ hrmin.1)
    show 0 < θ (ρ rmin)
    simp only [θ, dif_pos hρr]
    exact_mod_cast absXi_pos ξ _
  refine ⟨⟨(θ ∘ ρ) rmin, hlo_pos.le⟩, ⟨max ((θ ∘ ρ) rmax) 0, le_max_right _ _⟩, ?_, ?_⟩
  · exact_mod_cast hlo_pos
  · intro g hg
    have hv := hval g hg
    constructor
    · have := hmin hg
      rw [Set.mem_setOf_eq] at this
      rw [← NNReal.coe_le_coe]
      change (θ ∘ ρ) rmin ≤ (ω ξ g : ℝ)
      rw [hv]
      exact this
    · have := hmax hg
      rw [Set.mem_setOf_eq] at this
      rw [← NNReal.coe_le_coe]
      change (ω ξ g : ℝ) ≤ max ((θ ∘ ρ) rmax) 0
      rw [hv]
      exact le_max_of_le_left this

theorem isHaar : (μH).IsHaarMeasure := isHaarMeasure_adelicGLHaar (Fin 2) (𝓞 F) F

theorem regular_μH : (μH).Regular := by
  show (adelicGLHaar (Fin 2) (𝓞 F) F).Regular
  unfold adelicGLHaar
  infer_instance

theorem exists_map_mulRight (x : 𝔾) : ∃ c : ℝ≥0, 0 < c ∧ (μH).map (· * x) = c • μH := by
  haveI := isHaar (F := F)
  haveI := regular_μH (F := F)
  haveI : ((μH).map (· * x)).Regular := Measure.Regular.map (Homeomorph.mulRight x)
  refine ⟨((μH).map (· * x)).haarScalarFactor μH, ?_,
    Measure.isMulLeftInvariant_eq_smul_of_regular _ _⟩
  rw [pos_iff_ne_zero]
  intro h0
  have heq := Measure.isMulLeftInvariant_eq_smul_of_regular ((μH).map (· * x)) μH
  rw [h0, zero_smul] at heq
  have h1 : ((μH).map (· * x)) Set.univ = 0 := by rw [heq]; rfl
  rw [Measure.map_apply (measurable_mul_const x) MeasurableSet.univ, Set.preimage_univ] at h1
  exact (NeZero.ne ((μH) Set.univ)) h1

def cR (x : 𝔾) : ℝ≥0 := Classical.choose (exists_map_mulRight x)

theorem cR_pos (x : 𝔾) : 0 < cR x := (Classical.choose_spec (exists_map_mulRight x)).1

theorem map_mulRight (x : 𝔾) : (μH).map (· * x) = cR x • μH :=
  (Classical.choose_spec (exists_map_mulRight x)).2

theorem lintegral_mulRight (x : 𝔾) (f : 𝔾 → ℝ≥0∞) :
    ∫⁻ y, f (y * x) ∂μH = (cR x : ℝ≥0∞) * ∫⁻ y, f y ∂μH := by
  have h := lintegral_map_equiv f (MeasurableEquiv.mulRight x) (μ := μH)
  rw [MeasurableEquiv.coe_mulRight, map_mulRight, lintegral_smul_measure] at h
  rw [← h]
  rfl

def rt (A : Set 𝔾) (x : 𝔾) : Set 𝔾 := (fun y => y * x⁻¹) ⁻¹' A

theorem mem_rt {A : Set 𝔾} {x y : 𝔾} : y ∈ rt A x ↔ y * x⁻¹ ∈ A := Iff.rfl

theorem mul_mem_rt {A : Set 𝔾} {x y : 𝔾} : y * x ∈ rt A x ↔ y ∈ A := by
  rw [mem_rt, mul_inv_cancel_right]

theorem measurableSet_rt {A : Set 𝔾} (hA : MeasurableSet A) (x : 𝔾) : MeasurableSet (rt A x) :=
  measurable_mul_const _ hA

theorem rt_mono {A B : Set 𝔾} (h : A ⊆ B) (x : 𝔾) : rt A x ⊆ rt B x := fun _ hy => h hy

theorem indicator_rt (A : Set 𝔾) (x : 𝔾) (f : 𝔾 → ℝ≥0∞) (y : 𝔾) :
    A.indicator (fun y => f (y * x)) y = (rt A x).indicator f (y * x) := by
  by_cases hy : y ∈ A
  · rw [Set.indicator_of_mem hy, Set.indicator_of_mem (mul_mem_rt.mpr hy)]
  · rw [Set.indicator_of_notMem hy, Set.indicator_of_notMem (mt mul_mem_rt.mp hy)]

theorem setLIntegral_rt {A : Set 𝔾} (hA : MeasurableSet A) (x : 𝔾) (f : 𝔾 → ℝ≥0∞) :
    (cR x : ℝ≥0∞) * ∫⁻ y in rt A x, f y ∂μH = ∫⁻ y in A, f (y * x) ∂μH := by
  rw [← lintegral_indicator hA, ← lintegral_indicator (measurableSet_rt hA x)]
  simp_rw [indicator_rt A x f]
  rw [lintegral_mulRight x ((rt A x).indicator f)]

theorem lintegral_mul_centralScalar (z : 𝔸ˣ) (f : 𝔾 → ℝ≥0∞) :
    ∫⁻ y, f (y * centralScalar (𝓞 F) F z) ∂μH = ∫⁻ y, f y ∂μH := by
  haveI := isHaar (F := F)
  simp_rw [mul_centralScalar_comm z]
  exact lintegral_mul_left_eq_self _ _

theorem setLIntegral_rt_centralScalar {A : Set 𝔾} (hA : MeasurableSet A) (z : 𝔸ˣ) (f : 𝔾 → ℝ≥0∞) :
    ∫⁻ y in rt A (centralScalar (𝓞 F) F z), f y ∂μH =
      ∫⁻ y in A, f (y * centralScalar (𝓞 F) F z) ∂μH := by
  rw [← lintegral_indicator hA, ← lintegral_indicator (measurableSet_rt hA _)]
  simp_rw [indicator_rt A _ f]
  rw [lintegral_mul_centralScalar z ((rt A (centralScalar (𝓞 F) F z)).indicator f)]

def K0 : Set 𝔾 :=
  {k | k ∈ finiteAdelicGL2Subgroup F ∧ glFin (𝓞 F) F k ∈ finiteIntegralGL2 (𝓞 F) F}

theorem glArch_eq_one_of_K0 {k : 𝔾} (hk : k ∈ K0) : glArch (𝓞 F) F k = 1 := hk.1

theorem inv_mem_K0 {k : 𝔾} (hk : k ∈ K0) : k⁻¹ ∈ K0 :=
  ⟨Subgroup.inv_mem _ hk.1, by rw [map_inv]; exact Subgroup.inv_mem _ hk.2⟩

theorem pow_mem_K0 {k : 𝔾} (hk : k ∈ K0) (n : ℕ) : k ^ n ∈ K0 :=
  ⟨Subgroup.pow_mem _ hk.1 n, by rw [map_pow]; exact Subgroup.pow_mem _ hk.2 n⟩

def blk : Set 𝔾 := cappedSiegelBlock F (1/2) 1 (1/2) 2

theorem isCompact_blk : IsCompact (blk (F := F)) :=
  isCompact_cappedSiegelBlock (by norm_num) (by norm_num)

theorem measurableSet_blk : MeasurableSet (blk (F := F)) :=
  (isClosed_cappedSiegelBlock _ _ _ _).measurableSet

theorem one_mem_interior_blk : (1 : 𝔾) ∈ interior (blk (F := F)) := by
  unfold blk cappedSiegelBlock
  rw [interior_inter]
  refine ⟨one_mem_interior_centreCutSiegelSet (by norm_num) (by norm_num) (by norm_num) (by norm_num), ?_⟩
  rw [mem_interior]
  refine ⟨{g : 𝔾 | ∀ w : InfinitePlace F, localHeight (archComponent F w (glArch (𝓞 F) F g)) < 2},
    fun g hg w => ?_, ?_, fun w => ?_⟩
  · have := hg w; norm_num; linarith
  · have hset : {g : 𝔾 | ∀ w : InfinitePlace F, localHeight (archComponent F w (glArch (𝓞 F) F g)) < 2}
        = ⋂ w : InfinitePlace F, {g : 𝔾 | localHeight (archComponent F w (glArch (𝓞 F) F g)) < 2} := by
      ext g; simp [Set.mem_iInter]
    rw [hset]
    exact isOpen_iInter_of_finite fun w => isOpen_lt (continuous_localHeight_place w) continuous_const
  · show localHeight (archComponent F w (glArch (𝓞 F) F 1)) < 2
    rw [map_one, map_one, localHeight_one]; norm_num

theorem blk_pos : 0 < (μH) blk := by
  haveI := isHaar (F := F)
  exact Measure.measure_pos_of_nonempty_interior _ ⟨1, one_mem_interior_blk⟩

theorem blk_lt_top : (μH) blk < ⊤ := by
  haveI := isHaar (F := F)
  exact isCompact_blk.measure_lt_top

theorem archComponent_mul_of_glArch_eq_one {k : 𝔾} (hk : glArch (𝓞 F) F k = 1) (g : 𝔾)
    (w : InfinitePlace F) :
    archComponent F w (glArch (𝓞 F) F (g * k)) = archComponent F w (glArch (𝓞 F) F g) := by
  rw [map_mul, map_mul, hk, map_one, mul_one]

theorem archDetNorm_mul_of_glArch_eq_one {k : 𝔾} (hk : glArch (𝓞 F) F k = 1) (g : 𝔾)
    (w : InfinitePlace F) : archDetNorm w (g * k) = archDetNorm w g := by
  unfold archDetNorm; rw [archComponent_mul_of_glArch_eq_one hk]

theorem mul_mem_centreCutSiegelSet_iff_of_K0 {k : 𝔾} (hk : k ∈ K0) (g : 𝔾) (c u d₁ d₂ : ℝ) :
    g * k ∈ centreCutSiegelSet F c u d₁ d₂ ↔ g ∈ centreCutSiegelSet F c u d₁ d₂ := by
  simp only [mem_centreCutSiegelSet_iff, archComponent_mul_of_glArch_eq_one hk.1,
    archDetNorm_mul_of_glArch_eq_one hk.1]
  rw [map_mul, Subgroup.mul_mem_cancel_right _ hk.2]

theorem mul_mem_blk_iff {k : 𝔾} (hk : k ∈ K0) (g : 𝔾) : g * k ∈ blk ↔ g ∈ blk := by
  unfold blk
  rw [mem_cappedSiegelBlock_iff, mem_cappedSiegelBlock_iff, mul_mem_centreCutSiegelSet_iff_of_K0 hk]
  simp only [archComponent_mul_of_glArch_eq_one hk.1]

theorem rt_blk_of_K0 {k : 𝔾} (hk : k ∈ K0) : rt blk k = blk := by
  ext y
  rw [mem_rt, mul_mem_blk_iff (inv_mem_K0 hk)]

theorem K0_subset_blk : (K0 : Set 𝔾) ⊆ blk := by
  intro k hk
  have h1 : (1 : 𝔾) * k ∈ blk ↔ (1 : 𝔾) ∈ blk := mul_mem_blk_iff hk 1
  rw [one_mul] at h1
  exact h1.mpr (interior_subset one_mem_interior_blk)

theorem cR_eq_one_of_K0 {k : 𝔾} (hk : k ∈ K0) : cR k = 1 := by
  have h := setLIntegral_rt measurableSet_blk k (fun _ => (1 : ℝ≥0∞))
  rw [rt_blk_of_K0 hk, setLIntegral_one] at h
  have hne := (blk_pos (F := F)).ne'
  have htop := (blk_lt_top (F := F)).ne
  have : (cR k : ℝ≥0∞) = 1 := by
    have h' : (cR k : ℝ≥0∞) * (μH) blk = 1 * (μH) blk := by rw [h, one_mul]
    exact (ENNReal.mul_left_inj hne htop).mp h'
  exact_mod_cast this

theorem ω_eq_one_of_K0 {φ₀ : 𝔾 → ℂ} {g₀ : 𝔾} (h : Good ξ φ₀ g₀) {k : 𝔾} (hk : k ∈ K0) :
    ω ξ k = 1 := by
  obtain ⟨C, hC⟩ := isCompact_blk.exists_bound_of_continuousOn
    ((NNReal.continuous_coe.comp (continuous_ω h)).continuousOn (s := blk))
  have hC0 : 0 ≤ C := by
    have := hC 1 (interior_subset one_mem_interior_blk)
    exact le_trans (norm_nonneg _) this
  have hle : ∀ k : 𝔾, k ∈ K0 → ω ξ k ≤ 1 := by
    intro k hk
    refine absXi_le_one_of_pow_le (C := ⟨C, hC0⟩) fun n => ?_
    have := hC (k ^ n) (K0_subset_blk (pow_mem_K0 hk n))
    have hpow : ω ξ (k ^ n) = ω ξ k ^ n := by unfold ω; rw [map_pow, map_pow]
    have h' : ((ω ξ k ^ n : ℝ≥0) : ℝ) ≤ C := by
      rw [← hpow]
      have h2 : |(ω ξ (k ^ n) : ℝ)| ≤ C := this
      rwa [abs_of_nonneg (NNReal.coe_nonneg _)] at h2
    exact_mod_cast h'
  have h1 := hle k hk
  have h2 := hle k⁻¹ (inv_mem_K0 hk)
  rw [ω_inv, inv_le_one₀ (ω_pos ξ k)] at h2
  exact le_antisymm h1 h2

section Unfold

variable {G α : Type*} [Group G] [MulAction G α] [MeasurableSpace α] [MeasurableConstSMul G α]
  [Countable G] {μ : Measure α} [SMulInvariantMeasure G α μ]

theorem setLIntegral_fd_le_of_cover {𝓕 A : Set α} (h𝓕 : IsFundamentalDomain G 𝓕 μ)
    (f : α → ℝ≥0∞) (hf : ∀ (γ : G) (y : α), f (γ • y) = f y) (hcov : 𝓕 ⊆ ⋃ γ : G, γ • A) :
    ∫⁻ y in 𝓕, f y ∂μ ≤ ∫⁻ y in A, f y ∂μ := by
  rw [h𝓕.setLIntegral_eq_tsum' f A]
  simp_rw [hf]
  calc ∫⁻ y in 𝓕, f y ∂μ ≤ ∫⁻ y in ⋃ γ : G, (γ • A ∩ 𝓕), f y ∂μ := by
        refine lintegral_mono_set fun y hy => ?_
        obtain ⟨γ, hγ⟩ := Set.mem_iUnion.mp (hcov hy)
        exact Set.mem_iUnion.mpr ⟨γ, hγ, hy⟩
    _ ≤ ∑' γ : G, ∫⁻ y in γ • A ∩ 𝓕, f y ∂μ := lintegral_iUnion_le _ _

theorem setLIntegral_le_mul_fd_of_card_le {𝓕 A : Set α} (h𝓕 : IsFundamentalDomain G 𝓕 μ)
    (hA : MeasurableSet A) (f : α → ℝ≥0∞) (hfm : Measurable f)
    (hf : ∀ (γ : G) (y : α), f (γ • y) = f y) (K : ℕ)
    (hK : ∀ y : α, ∃ s : Finset G, s.card ≤ K ∧ ∀ γ : G, γ⁻¹ • y ∈ A → γ ∈ s) :
    ∫⁻ y in A, f y ∂μ ≤ (K : ℝ≥0∞) * ∫⁻ y in 𝓕, f y ∂μ := by
  rw [h𝓕.setLIntegral_eq_tsum' f A]
  simp_rw [hf]
  have hterm : ∀ γ : G, ∫⁻ y in γ • A ∩ 𝓕, f y ∂μ = ∫⁻ y in 𝓕, (γ • A).indicator f y ∂μ := by
    intro γ
    rw [lintegral_indicator (hA.const_smul γ), Measure.restrict_restrict (hA.const_smul γ)]
  simp_rw [hterm]
  rw [← lintegral_tsum fun γ => ((hfm.indicator (hA.const_smul γ)).aemeasurable)]
  calc ∫⁻ y in 𝓕, ∑' γ : G, (γ • A).indicator f y ∂μ
      ≤ ∫⁻ y in 𝓕, (K : ℝ≥0∞) * f y ∂μ := by
        refine lintegral_mono fun y => ?_
        obtain ⟨s, hs, hmem⟩ := hK y
        have hzero : ∀ γ : G, γ ∉ s → (γ • A).indicator f y = 0 := by
          intro γ hγ
          rw [Set.indicator_of_notMem]
          intro hy
          exact hγ (hmem γ (Set.mem_smul_set_iff_inv_smul_mem.mp hy))
        rw [tsum_eq_sum hzero]
        calc ∑ γ ∈ s, (γ • A).indicator f y ≤ ∑ γ ∈ s, f y := by
              refine Finset.sum_le_sum fun γ _ => ?_
              by_cases hy : y ∈ γ • A
              · rw [Set.indicator_of_mem hy]
              · rw [Set.indicator_of_notMem hy]; exact zero_le
          _ = (s.card : ℝ≥0∞) * f y := by rw [Finset.sum_const, nsmul_eq_mul]
          _ ≤ (K : ℝ≥0∞) * f y := by gcongr
    _ = (K : ℝ≥0∞) * ∫⁻ y in 𝓕, f y ∂μ := lintegral_const_mul' _ _ ENNReal.coe_ne_top

end Unfold

theorem smulInvariantMeasure_restrict {X : Set 𝔾} (hX : ∀ (γ : Γp) (g : 𝔾), (γ : 𝔾) * g ∈ X ↔ g ∈ X) :
    SMulInvariantMeasure Γp 𝔾 ((μH).restrict X) := by
  haveI := isHaar (F := F)
  refine ⟨fun γ A hA => ?_⟩
  have hpre : (fun y : 𝔾 => γ • y) ⁻¹' A = (fun y : 𝔾 => (γ : 𝔾) * y) ⁻¹' A := rfl
  rw [hpre, Measure.restrict_apply (measurable_const_mul _ hA), Measure.restrict_apply hA]
  have hset : (fun y : 𝔾 => (γ : 𝔾) * y) ⁻¹' A ∩ X = (fun y : 𝔾 => (γ : 𝔾) * y) ⁻¹' (A ∩ X) := by
    ext y
    simp only [Set.mem_inter_iff, Set.mem_preimage, hX]
  rw [hset, measure_preimage_mul]

theorem rt_invariant {X : Set 𝔾} (hX : ∀ (γ : Γp) (g : 𝔾), (γ : 𝔾) * g ∈ X ↔ g ∈ X) (x : 𝔾)
    (γ : Γp) (g : 𝔾) : (γ : 𝔾) * g ∈ rt X x ↔ g ∈ rt X x := by
  rw [mem_rt, mem_rt, mul_assoc, hX]

theorem isFundamentalDomain_rt {X 𝓕 : Set 𝔾} (h𝓕 : IsFundamentalDomain Γp 𝓕 ((μH).restrict X))
    (x : 𝔾) : IsFundamentalDomain Γp (rt 𝓕 x) ((μH).restrict (rt X x)) := by
  haveI := isHaar (F := F)
  have hqmp : Measure.QuasiMeasurePreserving (fun y : 𝔾 => y * x⁻¹) ((μH).restrict (rt X x))
      ((μH).restrict X) := by
    refine ⟨measurable_mul_const _, ?_⟩
    have hemb := (MeasurableEquiv.mulRight (x⁻¹ : 𝔾)).measurableEmbedding
    have h1 := hemb.restrict_map (μH) X
    rw [MeasurableEquiv.coe_mulRight] at h1
    have h2 : (fun y : 𝔾 => y * x⁻¹) ⁻¹' X = rt X x := rfl
    rw [h2, map_mulRight] at h1
    rw [← h1, Measure.restrict_smul]
    rw [ENNReal.smul_def]
    exact Measure.smul_absolutelyContinuous
  exact h𝓕.preimage_of_equiv hqmp Function.bijective_id fun γ y => by
    show (γ : 𝔾) * y * x⁻¹ = (γ : 𝔾) * (y * x⁻¹)
    rw [mul_assoc]

def toRange (δ : GL (Fin 2) F) : Γp := ⟨globalPoints (𝓞 F) F δ, δ, rfl⟩

@[scoped simp] theorem coe_toRange (δ : GL (Fin 2) F) : ((toRange δ : Γp) : 𝔾) = globalPoints (𝓞 F) F δ := rfl

theorem toRange_pre (γ : Γp) : toRange (pre γ) = γ := Subtype.ext (globalPoints_pre γ)

theorem card_translates_le (c u d₁ d₂ : ℝ) (T : Finset 𝔾)
    (hfin : Set.Finite {γ : GL (Fin 2) F |
      ∃ s ∈ centreCutSiegelSet F c u d₁ d₂, globalPoints (𝓞 F) F γ * s ∈ centreCutSiegelSet F c u d₁ d₂})
    (y : 𝔾) :
    ∃ s : Finset Γp, s.card ≤ T.card * hfin.toFinset.card ∧
      ∀ γ : Γp, γ⁻¹ • y ∈ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂) → γ ∈ s := by
  classical
  set 𝔖 := centreCutSiegelSet F c u d₁ d₂ with h𝔖
  set S := hfin.toFinset with hS

  have hx : ∀ x : 𝔾, ∃ sx : Finset Γp, sx.card ≤ S.card ∧
      ∀ γ : Γp, (γ : 𝔾)⁻¹ * y * x⁻¹ ∈ 𝔖 → γ ∈ sx := by
    intro x
    by_cases hne : ∃ γ₀ : Γp, (γ₀ : 𝔾)⁻¹ * y * x⁻¹ ∈ 𝔖
    · obtain ⟨γ₀, hγ₀⟩ := hne
      refine ⟨S.image (fun δ => γ₀ * (toRange δ)⁻¹), Finset.card_image_le, fun γ hγ => ?_⟩
      rw [Finset.mem_image]
      refine ⟨pre (γ⁻¹ * γ₀), ?_, ?_⟩
      · rw [hS, Set.Finite.mem_toFinset]
        refine ⟨(γ₀ : 𝔾)⁻¹ * y * x⁻¹, hγ₀, ?_⟩
        rw [globalPoints_pre, Subgroup.coe_mul, Subgroup.coe_inv]
        have : (γ : 𝔾)⁻¹ * (γ₀ : 𝔾) * ((γ₀ : 𝔾)⁻¹ * y * x⁻¹) = (γ : 𝔾)⁻¹ * y * x⁻¹ := by group
        rw [this]; exact hγ
      · rw [toRange_pre]; group
    · refine ⟨∅, by simp, fun γ hγ => ?_⟩
      exact absurd ⟨γ, hγ⟩ hne
  choose sx hsx hmem using hx
  refine ⟨T.biUnion sx, ?_, fun γ hγ => ?_⟩
  · calc (T.biUnion sx).card ≤ ∑ x ∈ T, (sx x).card := Finset.card_biUnion_le
      _ ≤ T.card • S.card := Finset.sum_le_card_nsmul _ _ _ fun x _ => hsx x
      _ = T.card * S.card := smul_eq_mul _ _
  · rw [Finset.mem_biUnion]
    have hγ' : (γ : 𝔾)⁻¹ * y ∈ ⋃ x ∈ T, (· * x) '' 𝔖 := hγ
    simp only [Set.mem_iUnion, Set.mem_image, exists_prop] at hγ'
    obtain ⟨x, hxT, s, hs, hsx'⟩ := hγ'
    refine ⟨x, hxT, hmem x γ ?_⟩
    rw [← hsx', mul_inv_cancel_right]
    exact hs

variable (ξ)

def fN (φ : 𝔾 → ℂ) (y : 𝔾) : ℝ≥0 := ‖φ y‖₊ ^ 2 * (ω ξ y)⁻¹

def fE (φ : 𝔾 → ℂ) (y : 𝔾) : ℝ≥0∞ := (fN ξ φ y : ℝ≥0∞)

theorem inv_ω_mul_nnnorm_sq (φ : 𝔾 → ℂ) (y : 𝔾) :
    ((ω ξ y : ℝ≥0∞))⁻¹ * (‖φ y‖₊ : ℝ≥0∞) ^ 2 = fE ξ φ y := by
  unfold fE fN
  rw [← ENNReal.coe_inv (ω_ne_zero ξ y), ENNReal.coe_mul, ENNReal.coe_pow, mul_comm]

theorem nnnorm_sq_eq_ω_mul_fE (φ : 𝔾 → ℂ) (y : 𝔾) :
    (‖φ y‖₊ : ℝ≥0∞) ^ 2 = (ω ξ y : ℝ≥0∞) * fE ξ φ y := by
  unfold fE fN
  rw [← ENNReal.coe_pow, ← ENNReal.coe_mul, ← mul_assoc, mul_comm (ω ξ y), mul_assoc,
    mul_inv_cancel₀ (ω_ne_zero ξ y), mul_one]

theorem fE_le_of_le {φ : 𝔾 → ℂ} {y : 𝔾} {lo : ℝ≥0} (hlo : 0 < lo) (h : lo ≤ ω ξ y) :
    fE ξ φ y ≤ ((lo : ℝ≥0∞))⁻¹ * (‖φ y‖₊ : ℝ≥0∞) ^ 2 := by
  rw [← inv_ω_mul_nnnorm_sq]
  exact mul_le_mul_left (ENNReal.inv_le_inv.mpr (ENNReal.coe_le_coe.mpr h)) _

theorem nnnorm_sq_le_of_le {φ : 𝔾 → ℂ} {y : 𝔾} {hi : ℝ≥0} (h : ω ξ y ≤ hi) :
    (‖φ y‖₊ : ℝ≥0∞) ^ 2 ≤ (hi : ℝ≥0∞) * fE ξ φ y := by
  rw [nnnorm_sq_eq_ω_mul_fE ξ φ y]
  exact mul_le_mul_left (ENNReal.coe_le_coe.mpr h) _

theorem fE_translate (φ : 𝔾 → ℂ) (x y : 𝔾) :
    ((ω ξ y : ℝ≥0∞))⁻¹ * (‖φ (y * x)‖₊ : ℝ≥0∞) ^ 2 = (ω ξ x : ℝ≥0∞) * fE ξ φ (y * x) := by
  unfold fE fN
  rw [← ENNReal.coe_inv (ω_ne_zero ξ y), ← ENNReal.coe_pow, ← ENNReal.coe_mul, ← ENNReal.coe_mul,
    ENNReal.coe_inj, ω_mul, mul_inv]
  have hx : ω ξ x ≠ 0 := ω_ne_zero ξ x
  field_simp

theorem measurable_fE {φ₀ : 𝔾 → ℂ} {g₀ : 𝔾} (h : Good ξ φ₀ g₀) {φ : 𝔾 → ℂ} (hφ : Continuous φ) :
    Measurable (fE ξ φ) := by
  unfold fE fN
  refine ENNReal.continuous_coe.measurable.comp ?_
  exact ((hφ.nnnorm.pow 2).mul ((continuous_ω h).inv₀ fun y => ω_ne_zero ξ y)).measurable

theorem fN_central {φ : 𝔾 → ℂ} (hφ : IsLsXiFunction (𝓞 F) F ⊤ ξ φ) (z : 𝔸ˣ) (y : 𝔾) :
    fN ξ φ (centralScalar (𝓞 F) F z * y) = fN ξ φ y := by
  unfold fN
  rw [central_law hφ, nnnorm_mul, ω_mul, ω_centralScalar]
  have ha : absXi ξ z ≠ 0 := absXi_ne_zero ξ z
  rw [show ‖((ξ (toTop z) : ℂˣ) : ℂ)‖₊ = absXi ξ z from rfl, mul_pow, mul_inv, mul_mul_mul_comm,
    mul_inv_cancel₀ (pow_ne_zero 2 ha), one_mul]

theorem fE_central {φ : 𝔾 → ℂ} (hφ : IsLsXiFunction (𝓞 F) F ⊤ ξ φ) (z : 𝔸ˣ) (y : 𝔾) :
    fE ξ φ (centralScalar (𝓞 F) F z * y) = fE ξ φ y := by
  unfold fE; rw [fN_central ξ hφ]

theorem fE_mul_central {φ : 𝔾 → ℂ} (hφ : IsLsXiFunction (𝓞 F) F ⊤ ξ φ) (z : 𝔸ˣ) (y : 𝔾) :
    fE ξ φ (y * centralScalar (𝓞 F) F z) = fE ξ φ y := by
  rw [mul_centralScalar_comm, fE_central ξ hφ]

theorem fE_smul {φ₀ : 𝔾 → ℂ} {g₀ : 𝔾} (h : Good ξ φ₀ g₀) {φ : 𝔾 → ℂ}
    (hφ : IsLsXiFunction (𝓞 F) F ⊤ ξ φ) (γ : Γp) (y : 𝔾) : fE ξ φ (γ • y) = fE ξ φ y := by
  obtain ⟨δ, hδ⟩ := exists_eq_globalPoints γ
  rw [smul_def', ← hδ]
  unfold fE fN
  rw [hφ.left_invariant, ω_globalPoints_mul h]

theorem prod_pow_mult_le {a b : InfinitePlace F → ℝ} (h0 : ∀ w, 0 ≤ a w) (h : ∀ w, a w ≤ b w) :
    ∏ w : InfinitePlace F, a w ^ w.mult ≤ ∏ w : InfinitePlace F, b w ^ w.mult :=
  Finset.prod_le_prod (fun w _ => pow_nonneg (h0 w) _)
    (fun w _ => pow_le_pow_left₀ (h0 w) (h w) _)

theorem ideleNorm_det_siegel {c u d₁ d₂ : ℝ} (hd₁ : 0 < d₁) {s : 𝔾}
    (hs : s ∈ centreCutSiegelSet F c u d₁ d₂) :
    d₁ ^ (∑ w : InfinitePlace F, w.mult) ≤ ideleNorm F (Matrix.GeneralLinearGroup.det s) ∧
      ideleNorm F (Matrix.GeneralLinearGroup.det s) ≤ d₂ ^ (∑ w : InfinitePlace F, w.mult) := by
  have hint := (mem_centreCutSiegelSet_iff.mp hs).1
  have hdet := (mem_centreCutSiegelSet_iff.mp hs).2.2.2
  rw [NumberField.TateGlobal.ideleNorm_det_eq_prod_archDetNorm_pow_mult F s hint,
    ← Finset.prod_pow_eq_pow_sum, ← Finset.prod_pow_eq_pow_sum]
  exact ⟨prod_pow_mult_le (fun _ => hd₁.le) fun w => (hdet w).1,
    prod_pow_mult_le (fun w => (archDetNorm_pos w s).le) fun w => (hdet w).2⟩

theorem ideleNorm_inv (z : 𝔸ˣ) : ideleNorm F z⁻¹ = (ideleNorm F z)⁻¹ := by
  unfold ideleNorm; rw [map_inv, NNReal.coe_inv]

theorem measurableSet_window (c u d₁ d₂ : ℝ) (T : Finset 𝔾) :
    MeasurableSet (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂ : Set 𝔾) := by
  refine MeasurableSet.biUnion T.countable_toSet fun x _ => ?_
  have h := (MeasurableEquiv.mulRight x).measurableEmbedding.measurableSet_image.mpr
    (measurableSet_centreCutSiegelSet (F := F) c u d₁ d₂)
  rw [MeasurableEquiv.coe_mulRight] at h
  exact h

theorem main_good (c u d₁ d₂ : ℝ) (T : Finset 𝔾) (hc : 0 < c) (hd₁ : 0 < d₁) (hd : d₁ < d₂)
    (hcov : CoversModCentre F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂))
    (hfin : Set.Finite {γ : Matrix.GeneralLinearGroup (Fin 2) F |
      ∃ s ∈ centreCutSiegelSet F c u d₁ d₂, globalPoints (𝓞 F) F γ * s ∈ centreCutSiegelSet F c u d₁ d₂})
    {φ₀ : 𝔾 → ℂ} {g₀ : 𝔾} (h : Good ξ φ₀ g₀) :
    ∃ (ν : Measure 𝔾) (M : ℝ≥0∞) (χ : 𝔾 → ℝ≥0∞),
      M ≠ ⊤ ∧ (∀ x, χ x ≠ 0 ∧ χ x ≠ ⊤) ∧
      (∀ k ∈ finiteAdelicGL2Subgroup F, glFin (𝓞 F) F k ∈ finiteIntegralGL2 (𝓞 F) F → χ k = 1) ∧
      ∀ φ : 𝔾 → ℂ, Continuous φ → IsLsXiFunction (𝓞 F) F ⊤ ξ φ →
        ∫⁻ y, (‖φ y‖₊ : ℝ≥0∞) ^ 2 ∂ν ≤
            M * ∫⁻ y in ⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂,
              (‖φ y‖₊ : ℝ≥0∞) ^ 2 ∂μH ∧
        ∫⁻ y in ⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂, (‖φ y‖₊ : ℝ≥0∞) ^ 2 ∂μH ≤
            M * ∫⁻ y, (‖φ y‖₊ : ℝ≥0∞) ^ 2 ∂ν ∧
        ∀ x : 𝔾, ∫⁻ y, (‖φ (y * x)‖₊ : ℝ≥0∞) ^ 2 ∂ν = χ x * ∫⁻ y, (‖φ y‖₊ : ℝ≥0∞) ^ 2 ∂ν := by
  classical
  haveI := isHaar (F := F)
  set 𝔖 : Set 𝔾 := centreCutSiegelSet F c u d₁ d₂ with h𝔖def
  set D : Set 𝔾 := ⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂ with hDdef
  have hDmeas : MeasurableSet D := measurableSet_window c u d₁ d₂ T

  have hTne : T.Nonempty := by
    obtain ⟨γ, z, hγ⟩ := hcov 1
    obtain ⟨x, hx, -⟩ := Set.mem_iUnion₂.mp hγ
    exact ⟨x, hx⟩

  set deg : ℕ := ∑ w : InfinitePlace F, w.mult with hdegdef
  have hdeg : deg ≠ 0 := by
    have : 0 < deg := Finset.sum_pos (fun w _ => InfinitePlace.mult_pos) Finset.univ_nonempty
    exact this.ne'
  set NT : 𝔾 → ℝ := fun g => ideleNorm F (Matrix.GeneralLinearGroup.det g) with hNTdef
  set m₁ : ℝ := T.inf' hTne NT with hm₁def
  set m₂ : ℝ := T.sup' hTne NT with hm₂def
  have hm₁ : 0 < m₁ := (Finset.lt_inf'_iff hTne).2 fun x _ => ideleNorm_pos _
  have hm₁₂ : m₁ ≤ m₂ := by
    obtain ⟨x₀, hx₀⟩ := hTne
    exact le_trans (Finset.inf'_le NT hx₀) (Finset.le_sup' NT hx₀)
  set e₁ : ℝ := d₁ ^ deg * m₁ with he₁def
  set e₂ : ℝ := d₂ ^ deg * m₂ with he₂def
  have he₁ : 0 < e₁ := mul_pos (pow_pos hd₁ _) hm₁
  have he : e₁ < e₂ := by
    calc e₁ = d₁ ^ deg * m₁ := rfl
      _ < d₂ ^ deg * m₁ := by
          refine mul_lt_mul_of_pos_right ?_ hm₁
          exact pow_lt_pow_left₀ hd hd₁.le hdeg
      _ ≤ d₂ ^ deg * m₂ := by
          refine mul_le_mul_of_nonneg_left hm₁₂ (pow_nonneg (hd₁.le.trans hd.le) _)
  set X : Set 𝔾 := {g : 𝔾 | ideleNorm F (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc e₁ e₂}
    with hXdef
  have hDX : D ⊆ X := by
    intro y hy
    rw [hDdef] at hy
    simp only [Set.mem_iUnion, Set.mem_image, exists_prop] at hy
    obtain ⟨x, hxT, s, hs, rfl⟩ := hy
    have hs' := ideleNorm_det_siegel (F := F) hd₁ hs
    have hx1 : m₁ ≤ NT x := Finset.inf'_le NT hxT
    have hx2 : NT x ≤ m₂ := Finset.le_sup' NT hxT
    show ideleNorm F (Matrix.GeneralLinearGroup.det (s * x)) ∈ Set.Icc e₁ e₂
    rw [ideleNorm_det_mul]
    constructor
    · exact mul_le_mul hs'.1 hx1 hm₁.le (le_trans (pow_nonneg hd₁.le _) hs'.1)
    · exact mul_le_mul hs'.2 hx2 (ideleNorm_pos _).le (pow_nonneg (hd₁.le.trans hd.le) _)
  have hXinv : ∀ (γ : Γp) (g : 𝔾), (γ : 𝔾) * g ∈ X ↔ g ∈ X := by
    intro γ g
    obtain ⟨δ, hδ⟩ := exists_eq_globalPoints γ
    simp only [hXdef, Set.mem_setOf_eq]
    rw [← hδ, ideleNorm_det_globalPoints_mul]
  haveI hSI : SMulInvariantMeasure Γp 𝔾 ((μH).restrict X) := smulInvariantMeasure_restrict hXinv

  obtain ⟨-, -, -, 𝓕, -, h𝓕m, h𝓕X, h𝓕, -⟩ :=
    AutomorphicForm.exists_measurableSet_isFundamentalDomain_subset_iUnion_integralWindowedSiegelSet_of_coversModCentre
      F c u d₁ d₂ T hc hd₁ hd hcov e₁ e₂ he₁ he
  obtain ⟨Zfin, hZ⟩ :=
    AutomorphicForm.exists_finset_globalPoints_mul_mul_centralScalar_mem_of_coversModCentre_of_ideleNorm_det_mem_Icc
      F c u d₁ d₂ T hd₁ hd hcov e₁ e₂ he₁ he.le
  obtain ⟨lo, hi, hlo, hbd⟩ := exists_bounds_ω h he₁ he.le

  set Dt : Set 𝔾 := ⋃ z ∈ Zfin, rt D (centralScalar (𝓞 F) F z⁻¹) with hDtdef
  have hcover : 𝓕 ⊆ ⋃ γ : Γp, γ • Dt := by
    intro y hy
    obtain ⟨γ, z, hz, hmem⟩ := hZ y (h𝓕X hy)
    refine Set.mem_iUnion.mpr ⟨(toRange γ)⁻¹, ?_⟩
    rw [Set.mem_smul_set_iff_inv_smul_mem, inv_inv, smul_def', coe_toRange, hDtdef]
    simp only [Set.mem_iUnion]
    refine ⟨z, hz, ?_⟩
    rw [mem_rt, map_inv, inv_inv]
    exact hmem
  have hDt : ∀ φ : 𝔾 → ℂ, IsLsXiFunction (𝓞 F) F ⊤ ξ φ →
      ∫⁻ y in Dt, fE ξ φ y ∂μH ≤ (Zfin.card : ℝ≥0∞) * ∫⁻ y in D, fE ξ φ y ∂μH := by
    intro φ hφl
    have hDt' : Dt = ⋃ z : ↥Zfin, rt D (centralScalar (𝓞 F) F ((z : 𝔸ˣ)⁻¹)) := by
      rw [hDtdef]
      ext y
      simp only [Set.mem_iUnion]
      constructor
      · rintro ⟨z, hz, hy⟩; exact ⟨⟨z, hz⟩, hy⟩
      · rintro ⟨z, hy⟩; exact ⟨z, z.2, hy⟩
    calc ∫⁻ y in Dt, fE ξ φ y ∂μH
        ≤ ∑' z : ↥Zfin, ∫⁻ y in rt D (centralScalar (𝓞 F) F ((z : 𝔸ˣ)⁻¹)), fE ξ φ y ∂μH := by
          rw [hDt']; exact lintegral_iUnion_le _ _
      _ = ∑' z : ↥Zfin, ∫⁻ y in D, fE ξ φ y ∂μH := by
          refine tsum_congr fun z => ?_
          rw [setLIntegral_rt_centralScalar hDmeas]
          simp_rw [fE_mul_central ξ hφl]
      _ = (Zfin.card : ℝ≥0∞) * ∫⁻ y in D, fE ξ φ y ∂μH := by
          rw [tsum_fintype, Finset.sum_const, Finset.card_univ, Fintype.card_coe, nsmul_eq_mul]

  set K : ℕ := T.card * hfin.toFinset.card with hKdef
  set M₁ : ℝ≥0∞ := (Zfin.card : ℝ≥0∞) * ((lo : ℝ≥0∞))⁻¹ with hM₁def
  set M₂ : ℝ≥0∞ := (hi : ℝ≥0∞) * (K : ℝ≥0∞) with hM₂def
  have hloinv : ((lo : ℝ≥0∞))⁻¹ ≠ ⊤ := ENNReal.inv_ne_top.mpr (ENNReal.coe_ne_zero.mpr hlo.ne')
  have hM₁ : M₁ ≠ ⊤ := ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) hloinv
  have hM₂ : M₂ ≠ ⊤ := ENNReal.mul_ne_top ENNReal.coe_ne_top (ENNReal.natCast_ne_top _)
  refine ⟨((μH).restrict 𝓕).withDensity (fun y => ((ω ξ y : ℝ≥0∞))⁻¹), max M₁ M₂,
    fun x => ((ω ξ x * cR x : ℝ≥0) : ℝ≥0∞), ?_, ?_, ?_, ?_⟩
  · exact (max_lt (lt_top_iff_ne_top.mpr hM₁) (lt_top_iff_ne_top.mpr hM₂)).ne
  · intro x
    exact ⟨ENNReal.coe_ne_zero.mpr (mul_ne_zero (ω_ne_zero ξ x) (cR_pos x).ne'), ENNReal.coe_ne_top⟩
  · intro k hk1 hk2
    have hk : k ∈ K0 := ⟨hk1, hk2⟩
    show ((ω ξ k * cR k : ℝ≥0) : ℝ≥0∞) = 1
    rw [ω_eq_one_of_K0 h hk, cR_eq_one_of_K0 hk, one_mul, ENNReal.coe_one]
  · intro φ hφc hφl
    have hν : ∀ gfun : 𝔾 → ℝ≥0∞,
        ∫⁻ y, gfun y ∂((μH).restrict 𝓕).withDensity (fun y => ((ω ξ y : ℝ≥0∞))⁻¹) =
          ∫⁻ y in 𝓕, ((ω ξ y : ℝ≥0∞))⁻¹ * gfun y ∂μH := by
      intro gfun
      have hmeas : Measurable (fun y : 𝔾 => ((ω ξ y : ℝ≥0∞))⁻¹) :=
        (ENNReal.continuous_coe.comp (continuous_ω h)).measurable.inv
      rw [lintegral_withDensity_eq_lintegral_mul_non_measurable _ hmeas
        (Filter.Eventually.of_forall fun y =>
          ENNReal.inv_lt_top.mpr (ENNReal.coe_pos.mpr (ω_pos ξ y)))]
      rfl
    have hνφ : ∫⁻ y, (‖φ y‖₊ : ℝ≥0∞) ^ 2 ∂((μH).restrict 𝓕).withDensity
        (fun y => ((ω ξ y : ℝ≥0∞))⁻¹) = ∫⁻ y in 𝓕, fE ξ φ y ∂μH := by
      rw [hν]; simp_rw [inv_ω_mul_nnnorm_sq]
    have hfinv : ∀ (γ : Γp) (y : 𝔾), fE ξ φ (γ • y) = fE ξ φ y := fE_smul ξ h hφl
    have hfm : Measurable (fE ξ φ) := measurable_fE ξ h hφc
    have h𝓕X' : ∫⁻ y in 𝓕, fE ξ φ y ∂((μH).restrict X) = ∫⁻ y in 𝓕, fE ξ φ y ∂μH := by
      rw [Measure.restrict_restrict h𝓕m, Set.inter_eq_self_of_subset_left h𝓕X]
    have hDX' : ∫⁻ y in D, fE ξ φ y ∂((μH).restrict X) = ∫⁻ y in D, fE ξ φ y ∂μH := by
      rw [Measure.restrict_restrict hDmeas, Set.inter_eq_self_of_subset_left hDX]
    refine ⟨?_, ?_, ?_⟩
    ·
      calc ∫⁻ y, (‖φ y‖₊ : ℝ≥0∞) ^ 2 ∂((μH).restrict 𝓕).withDensity (fun y => ((ω ξ y : ℝ≥0∞))⁻¹)
          = ∫⁻ y in 𝓕, fE ξ φ y ∂((μH).restrict X) := by rw [hνφ, h𝓕X']
        _ ≤ ∫⁻ y in Dt, fE ξ φ y ∂((μH).restrict X) := setLIntegral_fd_le_of_cover h𝓕 _ hfinv hcover
        _ ≤ ∫⁻ y in Dt, fE ξ φ y ∂μH :=
            lintegral_mono' (Measure.restrict_mono subset_rfl Measure.restrict_le_self) le_rfl
        _ ≤ (Zfin.card : ℝ≥0∞) * ∫⁻ y in D, fE ξ φ y ∂μH := hDt φ hφl
        _ ≤ (Zfin.card : ℝ≥0∞) * (((lo : ℝ≥0∞))⁻¹ * ∫⁻ y in D, (‖φ y‖₊ : ℝ≥0∞) ^ 2 ∂μH) := by
            gcongr
            rw [← lintegral_const_mul' _ _ hloinv]
            exact setLIntegral_mono' hDmeas fun y hy => fE_le_of_le ξ hlo (hbd y (hDX hy)).1
        _ = M₁ * ∫⁻ y in D, (‖φ y‖₊ : ℝ≥0∞) ^ 2 ∂μH := by rw [hM₁def, mul_assoc]
        _ ≤ max M₁ M₂ * ∫⁻ y in D, (‖φ y‖₊ : ℝ≥0∞) ^ 2 ∂μH :=
            mul_le_mul_left (le_max_left _ _) _
    ·
      calc ∫⁻ y in D, (‖φ y‖₊ : ℝ≥0∞) ^ 2 ∂μH
          ≤ ∫⁻ y in D, (hi : ℝ≥0∞) * fE ξ φ y ∂μH :=
            setLIntegral_mono' hDmeas fun y hy => nnnorm_sq_le_of_le ξ (hbd y (hDX hy)).2
        _ = (hi : ℝ≥0∞) * ∫⁻ y in D, fE ξ φ y ∂((μH).restrict X) := by
            rw [lintegral_const_mul' _ _ ENNReal.coe_ne_top, hDX']
        _ ≤ (hi : ℝ≥0∞) * ((K : ℝ≥0∞) * ∫⁻ y in 𝓕, fE ξ φ y ∂((μH).restrict X)) := by
            gcongr
            exact setLIntegral_le_mul_fd_of_card_le h𝓕 hDmeas _ hfm hfinv K
              (card_translates_le c u d₁ d₂ T hfin)
        _ = M₂ * ∫⁻ y, (‖φ y‖₊ : ℝ≥0∞) ^ 2 ∂((μH).restrict 𝓕).withDensity
              (fun y => ((ω ξ y : ℝ≥0∞))⁻¹) := by
            rw [h𝓕X', hνφ, hM₂def, mul_assoc]
        _ ≤ max M₁ M₂ * _ := mul_le_mul_left (le_max_right _ _) _
    ·
      intro x
      haveI : SMulInvariantMeasure Γp 𝔾 ((μH).restrict (rt X x)) :=
        smulInvariantMeasure_restrict (rt_invariant hXinv x)
      obtain ⟨w₀⟩ := (inferInstance : Nonempty (InfinitePlace F))
      set r : ℝ := ideleNorm F (Matrix.GeneralLinearGroup.det x) with hrdef
      have hr : 0 < r := ideleNorm_pos _
      set m : ℕ := w₀.mult with hmdef
      have hm0 : m ≠ 0 := by
        rw [hmdef]; unfold InfinitePlace.mult; split_ifs <;> norm_num
      have hρ : 0 < (Real.sqrt r) ^ ((m : ℝ)⁻¹) := Real.rpow_pos_of_pos (Real.sqrt_pos.mpr hr) _
      set a : 𝔸ˣ := sec w₀ ((Real.sqrt r) ^ ((m : ℝ)⁻¹)) hρ with hadef
      have ha : ideleNorm F a ^ 2 = r := by
        rw [hadef, ideleNorm_sec, Real.rpow_inv_natCast_pow (Real.sqrt_nonneg _) hm0,
          Real.sq_sqrt hr.le]
      set za : 𝔾 := centralScalar (𝓞 F) F a with hzadef
      have hXeq : rt X x = rt X za := by
        ext y
        simp only [mem_rt, hXdef, Set.mem_setOf_eq]
        rw [ideleNorm_det_mul, ideleNorm_det_mul, map_inv, map_inv, ideleNorm_inv, ideleNorm_inv,
          hzadef, det_centralScalar, sq, ideleNorm_mul, ← sq, ha]
      have h𝓕x := isFundamentalDomain_rt h𝓕 x
      have h𝓕a : IsFundamentalDomain Γp (rt 𝓕 za) ((μH).restrict (rt X x)) := by
        rw [hXeq]; exact isFundamentalDomain_rt h𝓕 za
      calc ∫⁻ y, (‖φ (y * x)‖₊ : ℝ≥0∞) ^ 2 ∂((μH).restrict 𝓕).withDensity
              (fun y => ((ω ξ y : ℝ≥0∞))⁻¹)
          = ∫⁻ y in 𝓕, ((ω ξ y : ℝ≥0∞))⁻¹ * (‖φ (y * x)‖₊ : ℝ≥0∞) ^ 2 ∂μH := hν _
        _ = ∫⁻ y in 𝓕, (ω ξ x : ℝ≥0∞) * fE ξ φ (y * x) ∂μH := by simp_rw [fE_translate]
        _ = (ω ξ x : ℝ≥0∞) * ∫⁻ y in 𝓕, fE ξ φ (y * x) ∂μH :=
            lintegral_const_mul' _ _ ENNReal.coe_ne_top
        _ = (ω ξ x : ℝ≥0∞) * ((cR x : ℝ≥0∞) * ∫⁻ y in rt 𝓕 x, fE ξ φ y ∂μH) := by
            rw [setLIntegral_rt h𝓕m]
        _ = (ω ξ x : ℝ≥0∞) * ((cR x : ℝ≥0∞) * ∫⁻ y in rt 𝓕 x, fE ξ φ y ∂((μH).restrict (rt X x))) := by
            rw [Measure.restrict_restrict (measurableSet_rt h𝓕m x),
              Set.inter_eq_self_of_subset_left (rt_mono h𝓕X x)]
        _ = (ω ξ x : ℝ≥0∞) * ((cR x : ℝ≥0∞) * ∫⁻ y in rt 𝓕 za, fE ξ φ y ∂((μH).restrict (rt X x))) := by
            rw [h𝓕x.setLIntegral_eq h𝓕a _ hfinv]
        _ = (ω ξ x : ℝ≥0∞) * ((cR x : ℝ≥0∞) * ∫⁻ y in rt 𝓕 za, fE ξ φ y ∂μH) := by
            rw [hXeq, Measure.restrict_restrict (measurableSet_rt h𝓕m za),
              Set.inter_eq_self_of_subset_left (rt_mono h𝓕X za)]
        _ = (ω ξ x : ℝ≥0∞) * ((cR x : ℝ≥0∞) * ∫⁻ y in 𝓕, fE ξ φ (y * za) ∂μH) := by
            rw [hzadef, setLIntegral_rt_centralScalar h𝓕m]
        _ = (ω ξ x : ℝ≥0∞) * ((cR x : ℝ≥0∞) * ∫⁻ y in 𝓕, fE ξ φ y ∂μH) := by
            simp_rw [hzadef, fE_mul_central ξ hφl]
        _ = ((ω ξ x * cR x : ℝ≥0) : ℝ≥0∞) * ∫⁻ y, (‖φ y‖₊ : ℝ≥0∞) ^ 2
              ∂((μH).restrict 𝓕).withDensity (fun y => ((ω ξ y : ℝ≥0∞))⁻¹) := by
            rw [hνφ, ENNReal.coe_mul, mul_assoc]

theorem main_bad (D : Set 𝔾) (hbad : ¬ ∃ (φ₀ : 𝔾 → ℂ) (g₀ : 𝔾), Good ξ φ₀ g₀) :
    ∃ (ν : Measure 𝔾) (M : ℝ≥0∞) (χ : 𝔾 → ℝ≥0∞),
      M ≠ ⊤ ∧ (∀ x, χ x ≠ 0 ∧ χ x ≠ ⊤) ∧
      (∀ k ∈ finiteAdelicGL2Subgroup F, glFin (𝓞 F) F k ∈ finiteIntegralGL2 (𝓞 F) F → χ k = 1) ∧
      ∀ φ : 𝔾 → ℂ, Continuous φ → IsLsXiFunction (𝓞 F) F ⊤ ξ φ →
        ∫⁻ y, (‖φ y‖₊ : ℝ≥0∞) ^ 2 ∂ν ≤ M * ∫⁻ y in D, (‖φ y‖₊ : ℝ≥0∞) ^ 2 ∂μH ∧
        ∫⁻ y in D, (‖φ y‖₊ : ℝ≥0∞) ^ 2 ∂μH ≤ M * ∫⁻ y, (‖φ y‖₊ : ℝ≥0∞) ^ 2 ∂ν ∧
        ∀ x : 𝔾, ∫⁻ y, (‖φ (y * x)‖₊ : ℝ≥0∞) ^ 2 ∂ν = χ x * ∫⁻ y, (‖φ y‖₊ : ℝ≥0∞) ^ 2 ∂ν := by
  refine ⟨0, 0, fun _ => 1, ENNReal.zero_ne_top, fun _ => ⟨one_ne_zero, ENNReal.one_ne_top⟩,
    fun _ _ _ => rfl, fun φ hφc hφl => ?_⟩
  have hzero : ∀ g, φ g = 0 := fun g => by
    by_contra hg
    exact hbad ⟨φ, g, ⟨hφc, hφl, hg⟩⟩
  simp [hzero]

end K1aOfFinite
p2m_reactivate "P2MW.S_AutomorphicForm_exists_measure_lintegral_translate_eq_mul_and_setLIntegral_le_mul_of_coversModCentre_of_finite.K1aOfFinite"

end
p2m_reactivate "P2MW.S_AutomorphicForm_exists_measure_lintegral_translate_eq_mul_and_setLIntegral_le_mul_of_coversModCentre_of_finite.K1aOfFinite"

open K1aOfFinite in
theorem solution
    (F : Type) [Field F] [NumberField F] (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 F) F))
    (hc : 0 < c) (hd₁ : 0 < d₁) (hd : d₁ < d₂)
    (hcov : CoversModCentre F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂))
    (hfin : Set.Finite {γ : Matrix.GeneralLinearGroup (Fin 2) F |
      ∃ s ∈ centreCutSiegelSet F c u d₁ d₂, globalPoints (𝓞 F) F γ * s ∈ centreCutSiegelSet F c u d₁ d₂})
    (ξ : (⊤ : Subgroup (AdeleRing (𝓞 F) F)ˣ) →* ℂˣ) :
    ∃ (ν : @Measure (AdelicGL2 (𝓞 F) F) (glBorel (Fin 2) (𝓞 F) F)) (M : ℝ≥0∞)
      (χ : AdelicGL2 (𝓞 F) F → ℝ≥0∞),
      M ≠ ⊤ ∧ (∀ x, χ x ≠ 0 ∧ χ x ≠ ⊤) ∧
      (∀ k ∈ finiteAdelicGL2Subgroup F, glFin (𝓞 F) F k ∈ finiteIntegralGL2 (𝓞 F) F → χ k = 1) ∧
      ∀ φ : AdelicGL2 (𝓞 F) F → ℂ, Continuous φ → IsLsXiFunction (𝓞 F) F ⊤ ξ φ →
        @lintegral _ (glBorel (Fin 2) (𝓞 F) F) ν (fun y => (‖φ y‖₊ : ℝ≥0∞) ^ 2) ≤
            M * @lintegral _ (glBorel (Fin 2) (𝓞 F) F)
              ((adelicGLHaar (Fin 2) (𝓞 F) F).restrict
                (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂))
              (fun y => (‖φ y‖₊ : ℝ≥0∞) ^ 2) ∧
        @lintegral _ (glBorel (Fin 2) (𝓞 F) F)
              ((adelicGLHaar (Fin 2) (𝓞 F) F).restrict
                (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂))
              (fun y => (‖φ y‖₊ : ℝ≥0∞) ^ 2) ≤
            M * @lintegral _ (glBorel (Fin 2) (𝓞 F) F) ν (fun y => (‖φ y‖₊ : ℝ≥0∞) ^ 2) ∧
        ∀ x : AdelicGL2 (𝓞 F) F,
          @lintegral _ (glBorel (Fin 2) (𝓞 F) F) ν (fun y => (‖φ (y * x)‖₊ : ℝ≥0∞) ^ 2) =
            χ x * @lintegral _ (glBorel (Fin 2) (𝓞 F) F) ν (fun y => (‖φ y‖₊ : ℝ≥0∞) ^ 2) := by
  classical
  by_cases hex : ∃ (φ₀ : AdelicGL2 (𝓞 F) F → ℂ) (g₀ : AdelicGL2 (𝓞 F) F), Good ξ φ₀ g₀
  · obtain ⟨φ₀, g₀, h⟩ := hex
    exact main_good ξ c u d₁ d₂ T hc hd₁ hd hcov hfin h
  · exact main_bad ξ _ hex

end S_AutomorphicForm_exists_measure_lintegral_translate_eq_mul_and_setLIntegral_le_mul_of_coversModCentre_of_finite
end P2MW
export P2MW.S_AutomorphicForm_exists_measure_lintegral_translate_eq_mul_and_setLIntegral_le_mul_of_coversModCentre_of_finite (solution)

-- Prove2me | Definitions.Def_ChapterMackeyCocycle
-- name    : ChapterMackeyCocycle
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-10-16T20:26:29.393524+00:00
-- url     : https://prove2.me/theorems/281842eb-a7e6-4cd5-a43d-31df9edf339d
-- title:
--   The Lean 4 theorem `measurableSet_smul_image` in the `?` chapter of the timepiece formalization
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (source chapter `BookProof/ChapterMackeyCocycle.lean`): generated def bundle for ChapterMackeyCocycle. See BookProof/ChapterMackeyCocycle.lean for full context.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterMackeyCocycle.lean

import Definitions.Def_ChapterMackeyQuasiInvariant
import Definitions.Def_ChapterPvmCyclicUnitary
import Mathlib


/-!
# Covariant unitaries of `L²` of a finite measure are induced representations

Third step towards the converse of Mackey's imprimitivity theorem over a *continuous*
base.  `BookProof.ChapterMackeyQuasiInvariant` builds, from a quasi-invariant measure and a
measurable unitary cocycle, the induced representation
`(V g f)(x) = √(dens g x) · L g x (f (g⁻¹ x))`
and shows it is a system of imprimitivity together with the multiplication projections.
This file proves the **converse at the level of `L²`**: *any* unitary representation `V` of
`G` on `L²(X, μ)` (`μ` finite) which is covariant for the multiplication projections is of
that form, with a scalar (modulus-one) cocycle `u`:

  `(V g f)(x) = u g x · √(dens g x) · f (g⁻¹ x)`   (`μ`-a.e.).

Moreover the measure is automatically quasi-invariant — the covariance relation forces it.

The proof is the classical one.  Writing `1` for the constant function and
`w = V g 1`, covariance gives `V g 1_E = 1_{g·E} · w`, hence, by unitarity,
`∫_{F} |w|² dμ = μ(g⁻¹ · F)` for every measurable `F`; that is, `|w|²` is the
Radon–Nikodym cocycle `dens μ g`.  Normalizing `u = w / |w|` gives a modulus-one cocycle,
and `V g` agrees with `f ↦ w · (f ∘ g⁻¹)` on indicators, hence everywhere by density.

Together with the spectral theorem for a cyclic projection-valued measure
(`BookProof.ChapterPvmCyclicUnitary`) this gives the converse of Mackey's theorem over a
measure-theoretic base, in `BookProof.ChapterMackeyConverse`.

Everything is `sorry`-free and uses only the standard axioms.
-/

open MeasureTheory
open scoped InnerProductSpace

namespace BookProof.ChapterMackeyCocycle

open BookProof.ChapterMackeyQuasiInvariant BookProof.ChapterPvmCyclicUnitary

variable {G X : Type*} [Group G] [MeasurableSpace X] [MulAction G X]

/-! ## Indicators in `L²` -/

/-- The indicator of a measurable set, as an element of `L²` of a finite measure. -/
noncomputable def indSet (μ : Measure X) [IsFiniteMeasure μ] {E : Set X}
    (hE : MeasurableSet E) : Lp ℂ 2 μ :=
  indicatorConstLp 2 hE (measure_ne_top μ E) (1 : ℂ)

theorem norm_indSet_sq (μ : Measure X) [IsFiniteMeasure μ] {E : Set X} (hE : MeasurableSet E) :
    ‖indSet μ hE‖ ^ 2 = (μ E).toReal := by
  rw [indSet, norm_indicatorConstLp (by norm_num) (by norm_num), norm_one, one_mul,
    show ((2 : ENNReal).toReal) = (2 : ℝ) by norm_num, ← Real.rpow_natCast _ 2,
    ← Real.rpow_mul measureReal_nonneg]
  norm_num
  simp [measureReal_def]

theorem proj_eq_zero_of_measure_zero (μ : Measure X) {E : Set X} (hE : MeasurableSet E)
    (h0 : μ E = 0) (f : Lp ℂ 2 μ) : proj μ hE f = 0 := by
  have hae : ∀ᵐ x ∂μ, x ∉ E := by
    rw [ae_iff]
    simpa using h0
  rw [Lp.eq_zero_iff_ae_eq_zero]
  filter_upwards [proj_coeFn μ hE f, hae] with x e1 e3
  simp [e1, Set.indicator_of_notMem e3]

theorem proj_indSet_univ (μ : Measure X) [IsFiniteMeasure μ] {E : Set X}
    (hE : MeasurableSet E) :
    proj μ hE (indSet μ (MeasurableSet.univ (α := X))) = indSet μ hE := by
  refine Lp.ext ?_
  filter_upwards [proj_coeFn μ hE (indSet μ (MeasurableSet.univ (α := X))),
    indicatorConstLp_coeFn (μ := μ) (p := 2) (s := (Set.univ : Set X))
      (hs := MeasurableSet.univ) (hμs := measure_ne_top μ Set.univ) (c := (1 : ℂ)),
    indicatorConstLp_coeFn (μ := μ) (p := 2) (s := E)
      (hs := hE) (hμs := measure_ne_top μ E) (c := (1 : ℂ))] with x e1 e2 e3
  rw [indSet, indSet]
  rw [indSet] at e1
  rw [e1, e3]
  by_cases hx : x ∈ E
  · simp only [Set.indicator_of_mem hx, e2, Set.indicator_of_mem (Set.mem_univ x)]
  · simp only [Set.indicator_of_notMem hx]

/-! ## The set-up: a covariant unitary representation -/

/-- The image of a measurable set under the action, as a measurable set. -/
theorem measurableSet_smul_image (hm : ∀ g : G, Measurable fun x : X => g • x)
    {E : Set X} (hE : MeasurableSet E) (g : G) :
    MeasurableSet ((fun x : X => g • x) '' E) :=
  (actEquiv hm g).measurableSet_image.mpr hE

/-- Mackey's covariance relation for a unitary representation on `L²(X, μ)` and the
multiplication projections. -/
def Covariant (μ : Measure X) (hm : ∀ g : G, Measurable fun x : X => g • x)
    (V : G → (Lp ℂ 2 μ ≃ₗᵢ[ℂ] Lp ℂ 2 μ)) : Prop :=
  ∀ (g : G) (E : Set X) (hE : MeasurableSet E) (f : Lp ℂ 2 μ),
    V g (proj μ hE f) = proj μ (measurableSet_smul_image hm hE g) (V g f)

/-- Covariance moves the indicator of `E` to the indicator of `g·E` times `V g 1`. -/
theorem vmap_indSet {μ : Measure X} [IsFiniteMeasure μ]
    {hm : ∀ g : G, Measurable fun x : X => g • x}
    {V : G → (Lp ℂ 2 μ ≃ₗᵢ[ℂ] Lp ℂ 2 μ)} (hcov : Covariant μ hm V) (g : G)
    {E : Set X} (hE : MeasurableSet E) :
    V g (indSet μ hE)
      = proj μ (measurableSet_smul_image hm hE g)
          (V g (indSet μ (MeasurableSet.univ (α := X)))) := by
  rw [← proj_indSet_univ μ hE, hcov g E hE]

theorem image_preimage_smul (g : G) (F : Set X) :
    (fun x : X => g • x) '' ((fun x : X => g • x) ⁻¹' F) = F := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact hx
  · intro hy
    exact ⟨g⁻¹ • y, by simpa [smul_smul] using hy, by simp [smul_smul]⟩

/-- **The measure is automatically quasi-invariant.** -/
theorem quasiInvariant_of_covariant {μ : Measure X} [IsFiniteMeasure μ]
    {hm : ∀ g : G, Measurable fun x : X => g • x}
    {V : G → (Lp ℂ 2 μ ≃ₗᵢ[ℂ] Lp ℂ 2 μ)} (hcov : Covariant μ hm V) :
    QuasiInvariant μ G := by
  refine ⟨hm, fun g => Measure.AbsolutelyContinuous.mk fun E hE h0 => ?_⟩
  have hFmeas : MeasurableSet ((fun x : X => g • x) ⁻¹' E) := (hm g) hE
  have hsub : (fun x : X => g • x) '' ((fun x : X => g • x) ⁻¹' E) ⊆ E := by
    rintro _ ⟨x, hx, rfl⟩
    exact hx
  have h0' : μ ((fun x : X => g • x) '' ((fun x : X => g • x) ⁻¹' E)) = 0 :=
    measure_mono_null hsub h0
  have hzero : proj μ (measurableSet_smul_image hm hFmeas g)
      (V g (indSet μ (MeasurableSet.univ (α := X)))) = 0 :=
    proj_eq_zero_of_measure_zero μ _ h0' _
  have hnorm : ‖indSet μ hFmeas‖ = 0 := by
    have h1 : ‖V g (indSet μ hFmeas)‖ = ‖indSet μ hFmeas‖ := (V g).norm_map _
    rw [vmap_indSet hcov g hFmeas, hzero, norm_zero] at h1
    exact h1.symm
  have hsq : (μ ((fun x : X => g • x) ⁻¹' E)).toReal = 0 := by
    rw [← norm_indSet_sq μ hFmeas, hnorm]
    norm_num
  have hzero' : μ ((fun x : X => g • x) ⁻¹' E) = 0 :=
    (ENNReal.toReal_eq_zero_iff _).mp hsq |>.resolve_right (measure_ne_top μ _)
  rw [Measure.map_apply (hm g) hE]
  exact hzero'

/-- The multiplication projection depends on the set only, not on the measurability proof. -/
theorem proj_congr_set (μ : Measure X) {E F : Set X} (hE : MeasurableSet E)
    (hF : MeasurableSet F) (h : E = F) (f : Lp ℂ 2 μ) : proj μ hE f = proj μ hF f := by
  subst h
  rfl

/-! ## The Radon–Nikodym cocycle is the modulus squared of `V g 1` -/

/-- The `L²`-norm of a localized function as a set-integral. -/
theorem lintegral_enorm_sq_restrict (μ : Measure X) {F : Set X} (hF : MeasurableSet F)
    (u : Lp ℂ 2 μ) :
    ∫⁻ x in F, ‖(u : X → ℂ) x‖ₑ ^ 2 ∂μ = ENNReal.ofReal (‖proj μ hF u‖ ^ 2) := by
  have hnorm : ‖proj μ hF u‖ ^ 2 = ∫ x in F, ‖(u : X → ℂ) x‖ ^ 2 ∂μ := by
    rw [lp2_norm_sq_eq_integral μ (proj μ hF u)]
    rw [← integral_indicator hF]
    refine integral_congr_ae ?_
    filter_upwards [proj_coeFn μ hF u] with x e1
    rw [e1]
    by_cases hx : x ∈ F
    · simp [Set.indicator_of_mem hx]
    · simp [Set.indicator_of_notMem hx]
  rw [hnorm]
  have hint : Integrable (fun x => ‖(u : X → ℂ) x‖ ^ 2) (μ.restrict F) :=
    (integrable_norm_sq μ u).restrict
  rw [ofReal_integral_eq_lintegral_ofReal hint (by filter_upwards with x; positivity)]
  refine lintegral_congr fun x => ?_
  rw [← ofReal_norm_eq_enorm, ← ENNReal.ofReal_pow (norm_nonneg _)]

/-- The Radon–Nikodym cocycle of the measure is the modulus squared of `V g 1`. -/
theorem dens_eq_enorm_sq {μ : Measure X} [IsFiniteMeasure μ]
    {hm : ∀ g : G, Measurable fun x : X => g • x}
    {V : G → (Lp ℂ 2 μ ≃ₗᵢ[ℂ] Lp ℂ 2 μ)} (hcov : Covariant μ hm V) (g : G)
    {w : X → ℂ} (hwmeas : Measurable w)
    (hw : w =ᵐ[μ] ((V g (indSet μ (MeasurableSet.univ (α := X)))) : X → ℂ)) :
    dens μ g =ᵐ[μ] fun x => ‖w x‖ₑ ^ 2 := by
  have hmeasw : Measurable fun x => ‖w x‖ₑ ^ 2 := (hwmeas.enorm.pow_const 2)
  have hmap : (μ.map fun x : X => g • x) = μ.withDensity (fun x => ‖w x‖ₑ ^ 2) := by
    refine Measure.ext fun F hF => ?_
    have hEmeas : MeasurableSet ((fun x : X => g • x) ⁻¹' F) := (hm g) hF
    -- the norm identity coming from unitarity and covariance
    have hV0 := vmap_indSet hcov g hEmeas
    have hV : V g (indSet μ hEmeas)
        = proj μ hF (V g (indSet μ (MeasurableSet.univ (α := X)))) := by
      rw [hV0]
      exact proj_congr_set μ _ hF (image_preimage_smul g F) _
    have hnormV : ‖proj μ hF (V g (indSet μ (MeasurableSet.univ (α := X))))‖
        = ‖indSet μ hEmeas‖ := by
      rw [← hV]
      exact (V g).norm_map _
    have hsq : ‖proj μ hF (V g (indSet μ (MeasurableSet.univ (α := X))))‖ ^ 2
        = (μ ((fun x : X => g • x) ⁻¹' F)).toReal := by
      rw [hnormV, norm_indSet_sq μ hEmeas]
    have hlin : ∫⁻ x in F, ‖w x‖ₑ ^ 2 ∂μ
        = ∫⁻ x in F, ‖((V g (indSet μ (MeasurableSet.univ (α := X)))) : X → ℂ) x‖ₑ ^ 2 ∂μ := by
      refine lintegral_congr_ae ?_
      exact ae_restrict_of_ae (hw.mono fun x hx => by simp only [hx])
    rw [withDensity_apply _ hF, hlin,
      lintegral_enorm_sq_restrict μ hF (V g (indSet μ (MeasurableSet.univ (α := X)))), hsq,
      ENNReal.ofReal_toReal (measure_ne_top μ _), Measure.map_apply (hm g) hF]
  rw [dens, hmap]
  exact Measure.rnDeriv_withDensity μ hmeasw

/-! ## The multiplication–translation operator -/

section Operator

variable {μ : Measure X} [IsFiniteMeasure μ]

/-- The candidate for `V g`: multiply by `w` after translating by `g⁻¹`. -/
noncomputable def tfun (g : G) (w : X → ℂ) (f : X → ℂ) : X → ℂ := fun x => w x * f (g⁻¹ • x)

theorem aestronglyMeasurable_tfun (hqi : QuasiInvariant μ G) (g : G) {w : X → ℂ}
    (hwmeas : Measurable w) {f : X → ℂ} (hf : AEStronglyMeasurable f μ) :
    AEStronglyMeasurable (tfun g w f) μ :=
  hwmeas.aestronglyMeasurable.mul (hf.comp_quasiMeasurePreserving (quasiMeasurePreserving hqi g⁻¹))

/-- The translation–multiplication map preserves the `L²`-integral. -/
theorem lintegral_enorm_tfun (hqi : QuasiInvariant μ G) (g : G) {w : X → ℂ}
    (hdens : dens μ g =ᵐ[μ] fun x => ‖w x‖ₑ ^ 2)
    {f : X → ℂ} (hf : AEStronglyMeasurable f μ) :
    ∫⁻ x, ‖tfun g w f x‖ₑ ^ (2 : ℕ) ∂μ = ∫⁻ x, ‖f x‖ₑ ^ (2 : ℕ) ∂μ := by
  have hφ : AEMeasurable (fun x => ‖f x‖ₑ ^ (2 : ℕ)) μ := hf.enorm.pow_const _
  have hφ' : AEMeasurable (fun x => ‖f (g⁻¹ • x)‖ₑ ^ (2 : ℕ)) μ :=
    hφ.comp_quasiMeasurePreserving (quasiMeasurePreserving hqi g⁻¹)
  have step1 : ∫⁻ x, ‖tfun g w f x‖ₑ ^ (2 : ℕ) ∂μ
      = ∫⁻ x, dens μ g x * ‖f (g⁻¹ • x)‖ₑ ^ (2 : ℕ) ∂μ := by
    refine lintegral_congr_ae ?_
    filter_upwards [hdens] with x hx
    rw [tfun, enorm_mul, mul_pow, hx]
  rw [step1, lintegral_dens_mul₀ μ hqi g hφ']
  refine lintegral_congr fun x => ?_
  simp [smul_smul]

theorem memLp_tfun (hqi : QuasiInvariant μ G) (g : G) {w : X → ℂ} (hwmeas : Measurable w)
    (hdens : dens μ g =ᵐ[μ] fun x => ‖w x‖ₑ ^ 2) (f : Lp ℂ 2 μ) :
    MemLp (tfun g w (f : X → ℂ)) 2 μ := by
  refine ⟨aestronglyMeasurable_tfun hqi g hwmeas (Lp.aestronglyMeasurable f), ?_⟩
  have h2 := (Lp.memLp f).2
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)] at h2 ⊢
  have c1 : ∀ u : X → ℂ, ∫⁻ x, ‖u x‖ₑ ^ (2 : ENNReal).toReal ∂μ
      = ∫⁻ x, ‖u x‖ₑ ^ (2:ℕ) ∂μ := by
    intro u
    refine lintegral_congr fun x => ?_
    rw [show ((2 : ENNReal).toReal) = ((2:ℕ):ℝ) by norm_num, ENNReal.rpow_natCast]
  rw [c1] at h2 ⊢
  rw [lintegral_enorm_tfun hqi g hdens (Lp.aestronglyMeasurable f)]
  exact h2

/-- The translation–multiplication operator on `L²`. -/
noncomputable def tmap (hqi : QuasiInvariant μ G) (g : G) {w : X → ℂ} (hwmeas : Measurable w)
    (hdens : dens μ g =ᵐ[μ] fun x => ‖w x‖ₑ ^ 2) (f : Lp ℂ 2 μ) : Lp ℂ 2 μ :=
  (memLp_tfun hqi g hwmeas hdens f).toLp _

theorem tmap_coeFn (hqi : QuasiInvariant μ G) (g : G) {w : X → ℂ} (hwmeas : Measurable w)
    (hdens : dens μ g =ᵐ[μ] fun x => ‖w x‖ₑ ^ 2) (f : Lp ℂ 2 μ) :
    ((tmap hqi g hwmeas hdens f : Lp ℂ 2 μ) : X → ℂ) =ᵐ[μ] tfun g w (f : X → ℂ) :=
  MemLp.coeFn_toLp _

theorem tmap_add (hqi : QuasiInvariant μ G) (g : G) {w : X → ℂ} (hwmeas : Measurable w)
    (hdens : dens μ g =ᵐ[μ] fun x => ‖w x‖ₑ ^ 2) (f₁ f₂ : Lp ℂ 2 μ) :
    tmap hqi g hwmeas hdens (f₁ + f₂)
      = tmap hqi g hwmeas hdens f₁ + tmap hqi g hwmeas hdens f₂ := by
  refine Lp.ext ?_
  filter_upwards [tmap_coeFn hqi g hwmeas hdens (f₁ + f₂),
    tmap_coeFn hqi g hwmeas hdens f₁, tmap_coeFn hqi g hwmeas hdens f₂,
    Lp.coeFn_add (tmap hqi g hwmeas hdens f₁) (tmap hqi g hwmeas hdens f₂),
    (quasiMeasurePreserving hqi g⁻¹).ae_eq_comp (Lp.coeFn_add f₁ f₂)] with x a1 a2 a3 a4 a5
  simp only [Pi.add_apply, Function.comp_apply] at a4 a5
  rw [a1, a4, a2, a3]
  simp only [tfun, a5]
  ring

theorem tmap_smul (hqi : QuasiInvariant μ G) (g : G) {w : X → ℂ} (hwmeas : Measurable w)
    (hdens : dens μ g =ᵐ[μ] fun x => ‖w x‖ₑ ^ 2) (c : ℂ) (f : Lp ℂ 2 μ) :
    tmap hqi g hwmeas hdens (c • f) = c • tmap hqi g hwmeas hdens f := by
  refine Lp.ext ?_
  filter_upwards [tmap_coeFn hqi g hwmeas hdens (c • f), tmap_coeFn hqi g hwmeas hdens f,
    Lp.coeFn_smul c (tmap hqi g hwmeas hdens f),
    (quasiMeasurePreserving hqi g⁻¹).ae_eq_comp (Lp.coeFn_smul c f)] with x a1 a2 a3 a4
  simp only [Pi.smul_apply, Function.comp_apply] at a3 a4
  rw [a1, a3, a2]
  simp only [tfun, a4, smul_eq_mul]
  ring

theorem norm_tmap (hqi : QuasiInvariant μ G) (g : G) {w : X → ℂ} (hwmeas : Measurable w)
    (hdens : dens μ g =ᵐ[μ] fun x => ‖w x‖ₑ ^ 2) (f : Lp ℂ 2 μ) :
    ‖tmap hqi g hwmeas hdens f‖ = ‖f‖ := by
  rw [Lp.norm_def, Lp.norm_def]
  congr 1
  have hco : eLpNorm ((tmap hqi g hwmeas hdens f : Lp ℂ 2 μ) : X → ℂ) 2 μ
      = eLpNorm (tfun g w (f : X → ℂ)) 2 μ :=
    eLpNorm_congr_ae (tmap_coeFn hqi g hwmeas hdens f)
  rw [hco, eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num),
    eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)]
  congr 1
  have c1 : ∀ u : X → ℂ, ∫⁻ x, ‖u x‖ₑ ^ (2 : ENNReal).toReal ∂μ
      = ∫⁻ x, ‖u x‖ₑ ^ (2:ℕ) ∂μ := by
    intro u
    refine lintegral_congr fun x => ?_
    rw [show ((2 : ENNReal).toReal) = ((2:ℕ):ℝ) by norm_num, ENNReal.rpow_natCast]
  rw [c1, c1]
  exact lintegral_enorm_tfun hqi g hdens (Lp.aestronglyMeasurable f)

/-- The translation–multiplication operator, as a continuous linear map. -/
noncomputable def tmapL (hqi : QuasiInvariant μ G) (g : G) {w : X → ℂ} (hwmeas : Measurable w)
    (hdens : dens μ g =ᵐ[μ] fun x => ‖w x‖ₑ ^ 2) : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ :=
  LinearMap.mkContinuous
    { toFun := tmap hqi g hwmeas hdens
      map_add' := tmap_add hqi g hwmeas hdens
      map_smul' := tmap_smul hqi g hwmeas hdens } 1
    (fun f => by simpa using le_of_eq (norm_tmap hqi g hwmeas hdens f))

@[simp] theorem tmapL_apply (hqi : QuasiInvariant μ G) (g : G) {w : X → ℂ}
    (hwmeas : Measurable w) (hdens : dens μ g =ᵐ[μ] fun x => ‖w x‖ₑ ^ 2) (f : Lp ℂ 2 μ) :
    tmapL hqi g hwmeas hdens f = tmap hqi g hwmeas hdens f := rfl

end Operator

/-! ## `V g` is multiplication by `V g 1` composed with translation -/

section Identify

variable {μ : Measure X} [IsFiniteMeasure μ]

theorem mem_smul_image_iff (g : G) (E : Set X) (x : X) :
    x ∈ (fun y : X => g • y) '' E ↔ g⁻¹ • x ∈ E := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa [smul_smul] using hy
  · intro h
    exact ⟨g⁻¹ • x, h, by simp [smul_smul]⟩

/-- On indicators, `V g` is multiplication by `w = V g 1` after translation by `g⁻¹`. -/
theorem vmap_indSet_eq_tmap {hm : ∀ g : G, Measurable fun x : X => g • x}
    {V : G → (Lp ℂ 2 μ ≃ₗᵢ[ℂ] Lp ℂ 2 μ)} (hcov : Covariant μ hm V)
    (hqi : QuasiInvariant μ G) (g : G) {w : X → ℂ} (hwmeas : Measurable w)
    (hw : w =ᵐ[μ] ((V g (indSet μ (MeasurableSet.univ (α := X)))) : X → ℂ))
    (hdens : dens μ g =ᵐ[μ] fun x => ‖w x‖ₑ ^ 2)
    {E : Set X} (hE : MeasurableSet E) :
    V g (indSet μ hE) = tmap hqi g hwmeas hdens (indSet μ hE) := by
  have h1 := vmap_indSet hcov g hE
  refine Lp.ext ?_
  filter_upwards [tmap_coeFn hqi g hwmeas hdens (indSet μ hE),
    proj_coeFn μ (measurableSet_smul_image hm hE g)
      (V g (indSet μ (MeasurableSet.univ (α := X)))), hw,
    (quasiMeasurePreserving hqi g⁻¹).ae_eq_comp
      (indicatorConstLp_coeFn (μ := μ) (p := 2) (s := E) (hs := hE)
        (hμs := measure_ne_top μ E) (c := (1 : ℂ)))] with x a1 a2 a3 a4
  rw [h1, a2, a1, tfun]
  simp only [Function.comp_apply] at a4
  have ha4 : ((indSet μ hE : Lp ℂ 2 μ) : X → ℂ) (g⁻¹ • x)
      = E.indicator (fun _ => (1 : ℂ)) (g⁻¹ • x) := a4
  rw [ha4]
  by_cases hx : g⁻¹ • x ∈ E
  · have hmem : x ∈ (fun y : X => g • y) '' E := (mem_smul_image_iff g E x).mpr hx
    rw [Set.indicator_of_mem hmem, Set.indicator_of_mem hx, ← a3, mul_one]
  · have hmem : x ∉ (fun y : X => g • y) '' E := fun h => hx ((mem_smul_image_iff g E x).mp h)
    rw [Set.indicator_of_notMem hmem, Set.indicator_of_notMem hx, mul_zero]

/-- A constant multiple of an indicator, in `L²`. -/
theorem indicatorConstLp_eq_smul {E : Set X} (hE : MeasurableSet E) (hμE : μ E ≠ ⊤) (c : ℂ) :
    indicatorConstLp 2 hE hμE c = c • indSet μ hE := by
  refine Lp.ext ?_
  filter_upwards [indicatorConstLp_coeFn (μ := μ) (p := 2) (s := E) (hs := hE)
      (hμs := hμE) (c := c),
    Lp.coeFn_smul c (indSet μ hE),
    indicatorConstLp_coeFn (μ := μ) (p := 2) (s := E) (hs := hE)
      (hμs := measure_ne_top μ E) (c := (1 : ℂ))] with x e1 e2 e3
  simp only [Pi.smul_apply] at e2
  rw [e1, e2, indSet, e3]
  by_cases hx : x ∈ E <;> simp [hx]

/-- **`V g` is the multiplication–translation operator.** -/
theorem vmap_eq_tmap {hm : ∀ g : G, Measurable fun x : X => g • x}
    {V : G → (Lp ℂ 2 μ ≃ₗᵢ[ℂ] Lp ℂ 2 μ)} (hcov : Covariant μ hm V)
    (hqi : QuasiInvariant μ G) (g : G) {w : X → ℂ} (hwmeas : Measurable w)
    (hw : w =ᵐ[μ] ((V g (indSet μ (MeasurableSet.univ (α := X)))) : X → ℂ))
    (hdens : dens μ g =ᵐ[μ] fun x => ‖w x‖ₑ ^ 2) (f : Lp ℂ 2 μ) :
    V g f = tmap hqi g hwmeas hdens f := by
  refine Lp.induction (p := 2) (by simp)
    (fun f => V g f = tmap hqi g hwmeas hdens f) ?_ ?_ ?_ f
  · intro c F hF hμF
    rw [Lp.simpleFunc.coe_indicatorConst, indicatorConstLp_eq_smul hF hμF.ne c,
      map_smul, tmap_smul, vmap_indSet_eq_tmap hcov hqi g hwmeas hw hdens hF]
  · intro f₁ f₂ _ _ _ h₁ h₂
    rw [map_add, tmap_add, h₁, h₂]
  · exact isClosed_eq (V g).continuous (tmapL hqi g hwmeas hdens).continuous

end Identify

/-! ## The headline: a covariant unitary representation is induced -/

section Headline

variable {μ : Measure X} [IsFiniteMeasure μ]

/-- A measurable representative of `V g 1`. -/
noncomputable def wrep (V : G → (Lp ℂ 2 μ ≃ₗᵢ[ℂ] Lp ℂ 2 μ)) (g : G) : X → ℂ :=
  (Lp.aestronglyMeasurable (V g (indSet μ (MeasurableSet.univ (α := X))))).mk _

theorem measurable_wrep (V : G → (Lp ℂ 2 μ ≃ₗᵢ[ℂ] Lp ℂ 2 μ)) (g : G) :
    Measurable (wrep V g) :=
  (Lp.aestronglyMeasurable
    (V g (indSet μ (MeasurableSet.univ (α := X))))).stronglyMeasurable_mk.measurable

theorem wrep_ae (V : G → (Lp ℂ 2 μ ≃ₗᵢ[ℂ] Lp ℂ 2 μ)) (g : G) :
    wrep V g =ᵐ[μ] ((V g (indSet μ (MeasurableSet.univ (α := X)))) : X → ℂ) :=
  (Lp.aestronglyMeasurable _).ae_eq_mk.symm

/-- The modulus-one cocycle obtained by normalizing `V g 1`. -/
noncomputable def ucocycle (V : G → (Lp ℂ 2 μ ≃ₗᵢ[ℂ] Lp ℂ 2 μ)) (g : G) (x : X) : ℂ :=
  if wrep V g x = 0 then 1 else wrep V g x / (‖wrep V g x‖ : ℂ)

theorem norm_ucocycle (V : G → (Lp ℂ 2 μ ≃ₗᵢ[ℂ] Lp ℂ 2 μ)) (g : G) (x : X) :
    ‖ucocycle V g x‖ = 1 := by
  rw [ucocycle]
  split_ifs with h
  · simp
  · rw [norm_div, Complex.norm_real, norm_norm, div_self]
    simpa using h

theorem measurable_ucocycle (V : G → (Lp ℂ 2 μ ≃ₗᵢ[ℂ] Lp ℂ 2 μ)) (g : G) :
    Measurable (ucocycle V g) := by
  refine Measurable.ite ?_ measurable_const
    ((measurable_wrep V g).div (Complex.measurable_ofReal.comp (measurable_wrep V g).norm))
  exact measurableSet_eq_fun (measurable_wrep V g) measurable_const

/-- **A covariant unitary representation of `G` on `L²(X, μ)` is induced.**  The measure is
automatically quasi-invariant, and there is a measurable modulus-one cocycle `u` with
`(V g f)(x) = u g x · √(dens μ g x) · f(g⁻¹ x)` almost everywhere: exactly the form of the
induced representation of `BookProof.ChapterMackeyQuasiInvariant`. -/
theorem covariant_unitary_is_induced {hm : ∀ g : G, Measurable fun x : X => g • x}
    {V : G → (Lp ℂ 2 μ ≃ₗᵢ[ℂ] Lp ℂ 2 μ)} (hcov : Covariant μ hm V) :
    QuasiInvariant μ G ∧
      ∃ u : G → X → ℂ, (∀ g x, ‖u g x‖ = 1) ∧ (∀ g, Measurable (u g)) ∧
        ∀ (g : G) (f : Lp ℂ 2 μ), ((V g f : Lp ℂ 2 μ) : X → ℂ) =ᵐ[μ]
          fun x => u g x * (sqrtDens μ g x : ℂ) * (f : X → ℂ) (g⁻¹ • x) := by
  have hqi : QuasiInvariant μ G := quasiInvariant_of_covariant hcov
  refine ⟨hqi, ucocycle V, norm_ucocycle V, measurable_ucocycle V, ?_⟩
  intro g f
  have hdens : dens μ g =ᵐ[μ] fun x => ‖wrep V g x‖ₑ ^ 2 :=
    dens_eq_enorm_sq hcov g (measurable_wrep V g) (wrep_ae V g)
  have hsqrt : ∀ᵐ x ∂μ, sqrtDens μ g x = ‖wrep V g x‖ := by
    filter_upwards [hdens] with x hx
    rw [sqrtDens, hx, ← ofReal_norm_eq_enorm, ← ENNReal.ofReal_pow (norm_nonneg _),
      ENNReal.toReal_ofReal (by positivity), Real.sqrt_sq (norm_nonneg _)]
  have hV := vmap_eq_tmap hcov hqi g (measurable_wrep V g) (wrep_ae V g) hdens f
  rw [hV]
  filter_upwards [tmap_coeFn hqi g (measurable_wrep V g) hdens f, hsqrt] with x a1 a2
  rw [a1, a2, tfun]
  congr 1
  rw [ucocycle]
  split_ifs with h
  · rw [h]
    simp
  · rw [div_mul_cancel₀]
    simpa using h

end Headline

end BookProof.ChapterMackeyCocycle



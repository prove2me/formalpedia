-- Prove2me | solution 1 for AutomorphicForm.exists_isArchKFinite_invariant_nonneg_integral_maximalCompactAtHaar_mul_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/357db33f-2572-5fc1-be1b-800be029eb88

import Definitions.Def_AutomorphicForm_AdelicMaximalCompact
import Definitions.Def_AutomorphicForm_ArchKFinite
import Definitions.Def_AutomorphicForm_BorelSubgroup
import Theorems.Thm_AutomorphicForm_eq_zero_of_continuous_of_forall_isArchKFinite_integral_maximalCompactAtHaar_mul_eq_zero
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Function.LpSpace.ContinuousFunctions
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_isArchKFinite_invariant_nonneg_integral_maximalCompactAtHaar_mul_ne_zero

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel AutomorphicForm AutomorphicForm.WindowedSiegel IsDedekindDomain
open scoped Topology ENNReal

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel

noncomputable section

namespace MProjKit

theorem continuous_integral_param {P Y : Type*} [TopologicalSpace P] [TopologicalSpace Y] [CompactSpace Y]
    [MeasurableSpace Y] [BorelSpace Y] (μ : Measure Y) [IsFiniteMeasure μ] (F : P → Y → ℂ)
    (hF : Continuous (Function.uncurry F)) : Continuous fun p => ∫ y, F p y ∂μ := by
  set Φ : C(P × Y, ℂ) := ⟨Function.uncurry F, hF⟩ with hΦ
  have h1 : (fun p => ∫ y, F p y ∂μ) =
      (fun f : Y →₁[μ] ℂ => ∫ y, f y ∂μ) ∘ (ContinuousMap.toLp (E := ℂ) 1 μ ℂ) ∘ Φ.curry := by
    funext p
    simp only [Function.comp_apply]
    refine integral_congr_ae ?_
    have h := (ContinuousMap.coeFn_toLp (E := ℂ) (p := 1) μ (𝕜 := ℂ) (Φ.curry p)).symm
    refine Filter.EventuallyEq.trans (Filter.Eventually.of_forall fun y => ?_) h
    rfl
  rw [h1]
  exact continuous_integral.comp ((ContinuousMap.toLp (E := ℂ) 1 μ ℂ).continuous.comp Φ.curry.continuous)

theorem secondCountableTopology_GL (n : Type*) [Fintype n] [DecidableEq n] (L : Type*) [CommRing L]
    [TopologicalSpace L] [SecondCountableTopology L] : SecondCountableTopology (GL n L) := by
  haveI : SecondCountableTopology (Matrix n n L) := inferInstanceAs (SecondCountableTopology (n → n → L))
  haveI : SecondCountableTopology (Matrix n n L)ᵐᵒᵖ := MulOpposite.opHomeomorph.symm.secondCountableTopology
  exact Units.isEmbedding_embedProduct.secondCountableTopology

section Main

variable (K : Type) [Field K] [NumberField K]

abbrev G : Type := AdelicGL2 (𝓞 K) K

abbrev X : Type := ↥(maximalCompactAt K ∅)

omit [NumberField K] in
theorem secondCountableTopology_completion (w : InfinitePlace K) : SecondCountableTopology w.Completion :=
  (InfinitePlace.Completion.isometry_extensionEmbedding w).isEmbedding.secondCountableTopology

theorem X_ext {x y : X K}
    (h : ∀ w : InfinitePlace K, archComponent K w (glArch (𝓞 K) K (x : G K)) =
      archComponent K w (glArch (𝓞 K) K (y : G K))) : x = y := by
  apply Subtype.ext
  have hx := mem_maximalCompactAt_iff.1 x.2
  have hy := mem_maximalCompactAt_iff.1 y.2
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  apply Prod.ext
  · funext w
    have := congrArg (fun m : GL (Fin 2) w.Completion => (m : Matrix (Fin 2) (Fin 2) w.Completion) i j) (h w)
    simp only [archComponent_apply, glArch_apply] at this
    exact this
  · apply Subtype.ext
    funext v
    have hxv := hx.2 v (Finset.notMem_empty v)
    have hyv := hy.2 v (Finset.notMem_empty v)
    have ex := congrArg (fun m : GL (Fin 2) (v.adicCompletion K) => (m : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) i j) hxv
    have ey := congrArg (fun m : GL (Fin 2) (v.adicCompletion K) => (m : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) i j) hyv
    simp only [finComponent_apply, glFin_apply] at ex ey
    have h__af := ex.trans ey.symm
    simp at h__af ⊢
    exact h__af

theorem secondCountableTopology_X : SecondCountableTopology (X K) := by
  haveI : ∀ w : InfinitePlace K, SecondCountableTopology (GL (Fin 2) w.Completion) := fun w => by
    haveI := secondCountableTopology_completion K w
    exact secondCountableTopology_GL (Fin 2) w.Completion
  let Φ : X K → (∀ w : InfinitePlace K, GL (Fin 2) w.Completion) :=
    fun k w => archComponent K w (glArch (𝓞 K) K (k : G K))
  have hc : Continuous Φ := continuous_pi fun w =>
    (continuous_archComponent K w).comp ((continuous_glArch (𝓞 K) K).comp continuous_subtype_val)
  have hinj : Function.Injective Φ := fun x y hxy => X_ext K fun w => congrFun hxy w
  exact (hc.isClosedEmbedding hinj).isEmbedding.secondCountableTopology

def Msg : Subgroup (G K) := adelicBorel (𝓞 K) K ⊓ maximalCompactAt K ∅

abbrev M : Type := ↥(Msg K)

theorem isClosed_adelicBorel : IsClosed ((adelicBorel (𝓞 K) K : Set (G K))) := by
  have : ((adelicBorel (𝓞 K) K : Set (G K))) =
      {g : G K | ((g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) 1 0) = 0} := rfl
  rw [this]
  exact isClosed_eq (Units.continuous_val.matrix_elem 1 0) continuous_const

theorem isCompact_Msg : IsCompact ((Msg K : Set (G K))) :=
  (isCompact_maximalCompactAt K ∅).of_isClosed_subset
    ((isClosed_adelicBorel K).inter (isClosed_maximalCompactAt K ∅)) (fun _ h => h.2)

theorem compactSpace_M : CompactSpace (M K) := isCompact_iff_compactSpace.mp (isCompact_Msg K)

attribute [local instance] compactSpace_M

def μM : Measure (M K) := Measure.haarMeasure ⊤

theorem isHaarMeasure_μM : (μM K).IsHaarMeasure := by
  rw [μM]; infer_instance

theorem isProbabilityMeasure_μM : IsProbabilityMeasure (μM K) :=
  ⟨by rw [μM, ← TopologicalSpace.PositiveCompacts.coe_top]; exact Measure.haarMeasure_self⟩

attribute [local instance] isHaarMeasure_μM isProbabilityMeasure_μM

def toB : M K →* ↥(adelicBorel (𝓞 K) K) := Subgroup.inclusion inf_le_left

def toX : M K →* X K := Subgroup.inclusion inf_le_right

@[scoped simp] theorem coe_toX (m : M K) : ((toX K m : X K) : G K) = (m : G K) := rfl

theorem toX_apply (m : M K) : toX K m = ⟨(m : G K), m.2.2⟩ := rfl

def chr (ν : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) : M K →* ℂˣ := ν.comp (borelDiagSnd.comp (toB K))

theorem chr_apply (ν : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (m : M K) :
    chr K ν m = ν (borelDiagSnd (⟨(m : G K), m.2.1⟩ : ↥(adelicBorel (𝓞 K) K))) := rfl

theorem continuous_borelDiagSnd_toB :
    Continuous fun m : M K => (borelDiagSnd (toB K m) : (AdeleRing (𝓞 K) K)ˣ) := by
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · show Continuous fun m : M K => (((m : G K) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) 1 1)
    exact (Units.continuous_val.comp continuous_subtype_val).matrix_elem 1 1
  · show Continuous fun m : M K => ((((m⁻¹ : M K) : G K) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) 1 1)
    exact (Units.continuous_val.comp (continuous_subtype_val.comp continuous_inv)).matrix_elem 1 1

theorem continuous_chr (ν : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ)
    (hνc : Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((ν z : ℂˣ) : ℂ)) :
    Continuous fun m : M K => ((chr K ν m : ℂˣ) : ℂ) :=
  hνc.comp (continuous_borelDiagSnd_toB K)

theorem mem_X_of {g : G K} (hfin : glFin (𝓞 K) K g = 1)
    (hrow : ∀ w : InfinitePlace K, IsRowIsometry (archComponent K w (glArch (𝓞 K) K g))) :
    g ∈ maximalCompactAt K ∅ :=
  mem_maximalCompactAt_iff.2 ⟨mem_adelicMaximalCompact_iff.2
    ⟨by rw [hfin]; exact (finiteIntegralGL2 (𝓞 K) K).one_mem, hrow⟩, fun v _ => by rw [hfin, map_one]⟩

variable (ν : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ)

def avg (h : G K → ℂ) : G K → ℂ :=
  fun g => ∫ m, ((chr K ν m : ℂˣ) : ℂ) * h (((m⁻¹ : M K) : G K) * g) ∂(μM K)

variable {K ν}
variable (hνc : Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((ν z : ℂˣ) : ℂ))
include hνc

theorem continuous_integrand {h : G K → ℂ} (hh : Continuous h) :
    Continuous (Function.uncurry fun (g : G K) (m : M K) =>
      ((chr K ν m : ℂˣ) : ℂ) * h (((m⁻¹ : M K) : G K) * g)) := by
  have h1 : Continuous fun p : G K × M K => ((chr K ν p.2 : ℂˣ) : ℂ) :=
    (continuous_chr K ν hνc).comp continuous_snd
  have h2 : Continuous fun p : G K × M K => h (((p.2⁻¹ : M K) : G K) * p.1) :=
    hh.comp ((continuous_subtype_val.comp (continuous_inv.comp continuous_snd)).mul continuous_fst)
  exact h1.mul h2

theorem continuous_avg {h : G K → ℂ} (hh : Continuous h) : Continuous (avg K ν h) :=
  continuous_integral_param (μM K) _ (continuous_integrand hνc hh)

theorem integrable_slice {h : G K → ℂ} (hh : Continuous h) (g : G K) :
    Integrable (fun m : M K => ((chr K ν m : ℂˣ) : ℂ) * h (((m⁻¹ : M K) : G K) * g)) (μM K) :=
  ((continuous_integrand hνc hh).comp (Continuous.prodMk_right g)).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

theorem avg_add {h₁ h₂ : G K → ℂ} (hh₁ : Continuous h₁) (hh₂ : Continuous h₂) :
    avg K ν (h₁ + h₂) = avg K ν h₁ + avg K ν h₂ := by
  funext g
  simp only [avg, Pi.add_apply, mul_add]
  exact integral_add (integrable_slice hνc hh₁ g) (integrable_slice hνc hh₂ g)

omit hνc in
theorem avg_smul (a : ℂ) (h : G K → ℂ) : avg K ν (a • h) = a • avg K ν h := by
  funext g
  simp only [avg, Pi.smul_apply, smul_eq_mul]
  rw [← integral_const_mul]
  congr 1; funext m; ring

omit hνc in
theorem avg_zero : avg K ν (0 : G K → ℂ) = 0 := by
  funext g
  simp [avg]

omit hνc in

theorem avg_translate (h : G K → ℂ) (k : G K) :
    (fun x => avg K ν h (x * k)) = avg K ν (fun x => h (x * k)) := by
  funext x
  simp only [avg, mul_assoc]

theorem rtsf_avg {f₀ : G K → ℂ} (hc : Continuous f₀) (Kw : Subgroup (G K))
    (hK : RightTranslatesSpanFinite Kw f₀) : RightTranslatesSpanFinite Kw (avg K ν f₀) := by
  classical
  obtain ⟨s₀, hs₀⟩ := hK
  set Tset : Set (G K → ℂ) := Set.range (fun k : ↥Kw => fun x => f₀ (x * (k : G K))) with hTset
  have hTle : Submodule.span ℂ Tset ≤ Submodule.span ℂ (s₀ : Set (G K → ℂ)) :=
    Submodule.span_le.2 (by rintro _ ⟨k, rfl⟩; exact hs₀ k k.2)
  have hfg : (Submodule.span ℂ Tset).FG := by
    haveI : FiniteDimensional ℂ ↥(Submodule.span ℂ (s₀ : Set (G K → ℂ))) := FiniteDimensional.span_finset ℂ s₀
    haveI : FiniteDimensional ℂ ↥(Submodule.span ℂ Tset) := Submodule.finiteDimensional_of_le hTle
    exact Module.Finite.iff_fg.1 ‹_›
  obtain ⟨T, hTsub, hTspan⟩ := (Submodule.fg_span_iff_fg_span_finset_subset Tset).1 hfg
  refine ⟨T.image (avg K ν), fun k hk => ?_⟩
  have key : ∀ h ∈ Submodule.span ℂ (T : Set (G K → ℂ)),
      Continuous h ∧ avg K ν h ∈ Submodule.span ℂ ((T.image (avg K ν) : Finset (G K → ℂ)) : Set (G K → ℂ)) := by
    intro h hh
    induction hh using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨k', hk'⟩ := hTsub hx
      refine ⟨?_, Submodule.subset_span ?_⟩
      · rw [← hk']; exact hc.comp (continuous_mul_const _)
      · rw [Finset.coe_image]; exact ⟨x, hx, rfl⟩
    | zero => exact ⟨continuous_const, by rw [avg_zero]; exact Submodule.zero_mem _⟩
    | add x y _ _ hx hy =>
      exact ⟨hx.1.add hy.1, by rw [avg_add hνc hx.1 hy.1]; exact Submodule.add_mem _ hx.2 hy.2⟩
    | smul a x _ hx =>
      exact ⟨hx.1.const_smul a, by rw [avg_smul]; exact Submodule.smul_mem _ _ hx.2⟩
  have hmem : (fun x => f₀ (x * k)) ∈ Submodule.span ℂ (T : Set (G K → ℂ)) := by
    rw [← hTspan]; exact Submodule.subset_span ⟨⟨k, hk⟩, rfl⟩
  rw [avg_translate]
  exact (key _ hmem).2

end Main

end MProjKit
p2m_reactivate "P2MW.S_AutomorphicForm_exists_isArchKFinite_invariant_nonneg_integral_maximalCompactAtHaar_mul_ne_zero.MProjKit"

namespace MProjKit

section Closure

variable {G : Type*} [Group G]

theorem rtsf_add (K : Subgroup G) {f g : G → ℂ} (hf : RightTranslatesSpanFinite K f)
    (hg : RightTranslatesSpanFinite K g) : RightTranslatesSpanFinite K (f + g) := by
  classical
  obtain ⟨s, hs⟩ := hf
  obtain ⟨t, ht⟩ := hg
  refine ⟨s ∪ t, fun k hk => ?_⟩
  have heq : (fun x => (f + g) (x * k)) = (fun x => f (x * k)) + fun x => g (x * k) := rfl
  rw [heq, Finset.coe_union]
  exact Submodule.add_mem _ (Submodule.span_mono Set.subset_union_left (hs k hk))
    (Submodule.span_mono Set.subset_union_right (ht k hk))

open scoped Pointwise in
theorem rtsf_mul (K : Subgroup G) {f g : G → ℂ} (hf : RightTranslatesSpanFinite K f)
    (hg : RightTranslatesSpanFinite K g) : RightTranslatesSpanFinite K (f * g) := by
  classical
  obtain ⟨s, hs⟩ := hf
  obtain ⟨t, ht⟩ := hg
  refine ⟨s * t, fun k hk => ?_⟩
  have heq : (fun x => (f * g) (x * k)) = (fun x => f (x * k)) * fun x => g (x * k) := rfl
  rw [heq, Finset.coe_mul, ← Submodule.span_mul_span]
  exact Submodule.mul_mem_mul (hs k hk) (ht k hk)

theorem rtsf_star (K : Subgroup G) {f : G → ℂ} (hf : RightTranslatesSpanFinite K f) :
    RightTranslatesSpanFinite K (star f) := by
  classical
  obtain ⟨s, hs⟩ := hf
  refine ⟨s.image star, fun k hk => ?_⟩
  have heq : (fun x => (star f) (x * k)) = star (fun x => f (x * k)) := rfl
  rw [heq, Finset.coe_image]
  have key : ∀ u ∈ Submodule.span ℂ (s : Set (G → ℂ)), star u ∈ Submodule.span ℂ (star '' (s : Set (G → ℂ))) := by
    intro u hu
    induction hu using Submodule.span_induction with
    | mem x hx => exact Submodule.subset_span ⟨x, hx, rfl⟩
    | zero => rw [star_zero]; exact Submodule.zero_mem _
    | add x y _ _ hx hy => rw [star_add]; exact Submodule.add_mem _ hx hy
    | smul c x _ hx =>
      rw [star_smul]
      exact Submodule.smul_mem _ _ hx
  exact key _ (hs k hk)

end Closure
p2m_reactivate "P2MW.S_AutomorphicForm_exists_isArchKFinite_invariant_nonneg_integral_maximalCompactAtHaar_mul_ne_zero.MProjKit"

variable {F : Type} [Field F] [NumberField F]

theorem isArchKFinite_add {f g : AdelicGL2 (𝓞 F) F → ℂ} (hf : IsArchKFinite F f) (hg : IsArchKFinite F g) :
    IsArchKFinite F (f + g) := fun w => rtsf_add _ (hf w) (hg w)

theorem isArchKFinite_mul {f g : AdelicGL2 (𝓞 F) F → ℂ} (hf : IsArchKFinite F f) (hg : IsArchKFinite F g) :
    IsArchKFinite F (f * g) := fun w => rtsf_mul _ (hf w) (hg w)

theorem isArchKFinite_star {f : AdelicGL2 (𝓞 F) F → ℂ} (hf : IsArchKFinite F f) :
    IsArchKFinite F (star f) := fun w => rtsf_star _ (hf w)

theorem polarization_one (a : ℂ) :
    a = (1 / 4 : ℂ) * ((a + 1) * (starRingEnd ℂ) (a + 1) + Complex.I * ((a + Complex.I) * (starRingEnd ℂ) (a + Complex.I)) -
      (a - 1) * (starRingEnd ℂ) (a - 1) - Complex.I * ((a - Complex.I) * (starRingEnd ℂ) (a - Complex.I))) := by
  simp only [map_add, map_sub, map_one, Complex.conj_I]
  linear_combination (1 / 2 : ℂ) * (a - (starRingEnd ℂ) a) * Complex.I_sq

end MProjKit
p2m_reactivate "P2MW.S_AutomorphicForm_exists_isArchKFinite_invariant_nonneg_integral_maximalCompactAtHaar_mul_ne_zero.MProjKit"

end
p2m_reactivate "P2MW.S_AutomorphicForm_exists_isArchKFinite_invariant_nonneg_integral_maximalCompactAtHaar_mul_ne_zero.MProjKit"

open MProjKit in
theorem solution
    (K : Type) [Field K] [NumberField K]
    (β : ↥(maximalCompactAt K ∅) → ℂ) (_hβ : Continuous β)
    (_hβinv : ∀ (m : AdelicGL2 (𝓞 K) K) (_hm : m ∈ adelicBorel (𝓞 K) K) (hmK : m ∈ maximalCompactAt K ∅)
      (k : ↥(maximalCompactAt K ∅)), β (⟨m, hmK⟩ * k) = β k)
    (_hne : ∃ k₀ : ↥(maximalCompactAt K ∅), β k₀ ≠ 0) :
    ∃ f : AdelicGL2 (𝓞 K) K → ℂ, Continuous f ∧ IsArchKFinite K f ∧
      (∀ (m k : AdelicGL2 (𝓞 K) K), m ∈ adelicBorel (𝓞 K) K →
        glFin (𝓞 K) K m = 1 → glFin (𝓞 K) K k = 1 →
        (∀ w : InfinitePlace K, IsRowIsometry (archComponent K w (glArch (𝓞 K) K m))) →
        (∀ w : InfinitePlace K, IsRowIsometry (archComponent K w (glArch (𝓞 K) K k))) →
          f (m * k) = f k) ∧
      (∀ g : AdelicGL2 (𝓞 K) K, 0 ≤ (f g).re ∧ (f g).im = 0) ∧
      ∫ k, f (k : AdelicGL2 (𝓞 K) K) * β k ∂(maximalCompactAtHaar K ∅) ≠ 0 := by
  classical
  haveI := compactSpace_M K
  haveI := isHaarMeasure_μM K
  haveI := isProbabilityMeasure_μM K
  set ν : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ := 1 with hν
  have _hνc : Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((ν z : ℂˣ) : ℂ) := by
    simp only [hν, MonoidHom.one_apply, Units.val_one]; exact continuous_const
  have _hβν : ∀ (m : AdelicGL2 (𝓞 K) K) (hm : m ∈ adelicBorel (𝓞 K) K) (hmK : m ∈ maximalCompactAt K ∅)
      (k : ↥(maximalCompactAt K ∅)),
        ((ν (borelDiagSnd (⟨m, hm⟩ : ↥(adelicBorel (𝓞 K) K))) : ℂˣ) : ℂ) * β (⟨m, hmK⟩ * k) = β k := by
    intro m hm hmK k
    rw [hν, MonoidHom.one_apply, Units.val_one, one_mul]
    exact _hβinv m hm hmK k
  have hchr : ∀ m : M K, ((chr K ν m : ℂˣ) : ℂ) = 1 := fun m => by
    rw [chr_apply, hν, MonoidHom.one_apply, Units.val_one]

  have hint : ∀ F : ↥(maximalCompactAt K ∅) → ℂ, Continuous F → Integrable F (maximalCompactAtHaar K ∅) :=
    fun F hF => hF.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

  obtain ⟨f₀, hf₀c, hf₀K, hI₀⟩ : ∃ f₀ : G K → ℂ, Continuous f₀ ∧ IsArchKFinite K f₀ ∧
      ∫ k, (f₀ (k : G K) * (starRingEnd ℂ) (f₀ (k : G K))) * β k ∂(maximalCompactAtHaar K ∅) ≠ 0 := by
    by_contra hcon
    push Not at hcon
    have key : ∀ f : G K → ℂ, Continuous f → IsArchKFinite K f →
        ∫ k, f (k : G K) * β k ∂(maximalCompactAtHaar K ∅) = 0 := by
      intro f hfc hfK
      have hsq : ∀ c : ℂ, ∫ k, ((f (k : G K) + c) * (starRingEnd ℂ) (f (k : G K) + c)) * β k
          ∂(maximalCompactAtHaar K ∅) = 0 := fun c =>
        hcon (fun g => f g + c) (hfc.add continuous_const) (isArchKFinite_add hfK (isArchKFinite_const K c))
      have hi : ∀ c : ℂ, Integrable (fun k : ↥(maximalCompactAt K ∅) =>
          ((f (k : G K) + c) * (starRingEnd ℂ) (f (k : G K) + c)) * β k) (maximalCompactAtHaar K ∅) := fun c =>
        hint _ ((((hfc.comp continuous_subtype_val).add continuous_const).mul
          (Complex.continuous_conj.comp ((hfc.comp continuous_subtype_val).add continuous_const))).mul _hβ)
      have hpt : ∀ k : ↥(maximalCompactAt K ∅), f (k : G K) * β k =
          (1 / 4 : ℂ) * (((f (k : G K) + 1) * (starRingEnd ℂ) (f (k : G K) + 1)) * β k +
            Complex.I * (((f (k : G K) + Complex.I) * (starRingEnd ℂ) (f (k : G K) + Complex.I)) * β k) -
            ((f (k : G K) + (-1)) * (starRingEnd ℂ) (f (k : G K) + (-1))) * β k -
            Complex.I * (((f (k : G K) + (-Complex.I)) * (starRingEnd ℂ) (f (k : G K) + (-Complex.I))) * β k)) := by
        intro k
        conv_lhs => rw [polarization_one (f (k : G K))]
        simp only [sub_eq_add_neg]
        ring
      rw [integral_congr_ae (Filter.Eventually.of_forall hpt), integral_const_mul, integral_sub, integral_sub,
        integral_add, integral_const_mul, integral_const_mul, hsq 1, hsq Complex.I, hsq (-1), hsq (-Complex.I)]
      · simp
      · exact hi 1
      · exact (hi Complex.I).const_mul _
      · exact (hi 1).add ((hi Complex.I).const_mul _)
      · exact hi (-1)
      · exact ((hi 1).add ((hi Complex.I).const_mul _)).sub (hi (-1))
      · exact (hi (-Complex.I)).const_mul _
    obtain ⟨k₀, hk₀⟩ := _hne
    have hb := AutomorphicForm.eq_zero_of_continuous_of_forall_isArchKFinite_integral_maximalCompactAtHaar_mul_eq_zero
      K β _hβ key
    exact hk₀ (by rw [hb]; rfl)

  set F₀ : G K → ℂ := fun g => f₀ g * (starRingEnd ℂ) (f₀ g) with hF₀
  have hF₀c : Continuous F₀ := hf₀c.mul (Complex.continuous_conj.comp hf₀c)
  have hF₀K : IsArchKFinite K F₀ := isArchKFinite_mul hf₀K (isArchKFinite_star hf₀K)
  have hF₀real : ∀ g : G K, F₀ g = ((Complex.normSq (f₀ g) : ℝ) : ℂ) := fun g => Complex.mul_conj (f₀ g)
  refine ⟨avg K ν F₀, continuous_avg _hνc hF₀c, fun w => rtsf_avg _hνc hF₀c _ (hF₀K w), ?_, ?_, ?_⟩
  ·
    intro m k hm hfin _hkfin hmrow _hkrow
    have hmX : m ∈ maximalCompactAt K ∅ := mem_X_of K hfin hmrow
    set m₁ : M K := ⟨m, hm, hmX⟩ with hm₁
    have step : avg K ν F₀ (m * k) =
        ∫ m', ((chr K ν m₁ : ℂˣ) : ℂ) * (((chr K ν m' : ℂˣ) : ℂ) * F₀ (((m'⁻¹ : M K) : G K) * k)) ∂(μM K) := by
      rw [avg, ← integral_mul_left_eq_self _ m₁]
      congr 1
      funext m'
      rw [map_mul, Units.val_mul, mul_assoc]
      congr 2
      rw [mul_inv_rev, Subgroup.coe_mul, Subgroup.coe_inv, hm₁]
      show F₀ (((m'⁻¹ : M K) : G K) * m⁻¹ * (m * k)) = _
      rw [mul_assoc, inv_mul_cancel_left, Subgroup.coe_inv]
    rw [step, integral_const_mul, hchr, one_mul]
    rfl
  ·
    intro g
    have hval : avg K ν F₀ g = ((∫ m, Complex.normSq (f₀ (((m⁻¹ : M K) : G K) * g)) ∂(μM K) : ℝ) : ℂ) := by
      rw [avg, ← integral_complex_ofReal]
      congr 1
      funext m
      rw [hchr, one_mul, hF₀real]
    rw [hval, Complex.ofReal_re, Complex.ofReal_im]
    exact ⟨integral_nonneg fun m => Complex.normSq_nonneg _, rfl⟩
  ·
    haveI := secondCountableTopology_X K
    have hint2 : Integrable (Function.uncurry fun (k : X K) (m : M K) =>
        ((chr K ν m : ℂˣ) : ℂ) * F₀ (((m⁻¹ : M K) : G K) * (k : G K)) * β k)
        ((maximalCompactAtHaar K ∅).prod (μM K)) := by
      have hc : Continuous (Function.uncurry fun (k : X K) (m : M K) =>
          ((chr K ν m : ℂˣ) : ℂ) * F₀ (((m⁻¹ : M K) : G K) * (k : G K)) * β k) := by
        have h1 := (continuous_integrand _hνc hF₀c).comp
          ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd :
            Continuous fun p : X K × M K => ((p.1 : G K), p.2))
        exact h1.mul (_hβ.comp continuous_fst)
      exact hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
    have h1 : ∀ k : X K, avg K ν F₀ (k : G K) * β k =
        ∫ m, ((chr K ν m : ℂˣ) : ℂ) * F₀ (((m⁻¹ : M K) : G K) * (k : G K)) * β k ∂(μM K) := by
      intro k; rw [avg, ← integral_mul_const]
    have h2 : ∀ m : M K, ∫ k, ((chr K ν m : ℂˣ) : ℂ) * F₀ (((m⁻¹ : M K) : G K) * (k : G K)) * β k
        ∂(maximalCompactAtHaar K ∅) = ∫ k, F₀ (k : G K) * β k ∂(maximalCompactAtHaar K ∅) := by
      intro m
      have hcov : ∀ k : X K, β (toX K m * k) = β k := fun k => by
        rw [toX_apply]; exact _hβinv (m : G K) m.2.1 m.2.2 k
      calc ∫ k, ((chr K ν m : ℂˣ) : ℂ) * F₀ (((m⁻¹ : M K) : G K) * (k : G K)) * β k ∂(maximalCompactAtHaar K ∅)
          = ∫ k, ((chr K ν m : ℂˣ) : ℂ) * F₀ (((m⁻¹ : M K) : G K) * ((toX K m * k : X K) : G K)) *
              β (toX K m * k) ∂(maximalCompactAtHaar K ∅) :=
            (integral_mul_left_eq_self (fun k : X K =>
              ((chr K ν m : ℂˣ) : ℂ) * F₀ (((m⁻¹ : M K) : G K) * (k : G K)) * β k) (toX K m)).symm
        _ = ∫ k, F₀ (k : G K) * β k ∂(maximalCompactAtHaar K ∅) := by
            congr 1; funext k
            rw [hcov, Subgroup.coe_mul, coe_toX, Subgroup.coe_inv, inv_mul_cancel_left, hchr, one_mul]
    have e1 : ∫ k, avg K ν F₀ (k : G K) * β k ∂(maximalCompactAtHaar K ∅) =
        ∫ k, ∫ m, ((chr K ν m : ℂˣ) : ℂ) * F₀ (((m⁻¹ : M K) : G K) * (k : G K)) * β k ∂(μM K)
          ∂(maximalCompactAtHaar K ∅) := integral_congr_ae (Filter.Eventually.of_forall h1)
    have e2 : (fun m : M K => ∫ k, ((chr K ν m : ℂˣ) : ℂ) * F₀ (((m⁻¹ : M K) : G K) * (k : G K)) * β k
          ∂(maximalCompactAtHaar K ∅)) = fun _ => ∫ k, F₀ (k : G K) * β k ∂(maximalCompactAtHaar K ∅) :=
      funext h2
    rw [e1, integral_integral_swap hint2, e2, integral_const]
    simpa using hI₀

end S_AutomorphicForm_exists_isArchKFinite_invariant_nonneg_integral_maximalCompactAtHaar_mul_ne_zero
end P2MW
export P2MW.S_AutomorphicForm_exists_isArchKFinite_invariant_nonneg_integral_maximalCompactAtHaar_mul_ne_zero (solution)

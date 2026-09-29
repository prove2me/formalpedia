-- Prove2me | Definitions.Def_AutomorphicForm_CuspidalSpectrumCarrier
-- name    : AutomorphicForm_CuspidalSpectrumCarrier
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:26.014713+00:00
-- url     : https://prove2.me/theorems/a7670f85-52c4-5e5e-8763-7b0d7ceebe90
-- title:
--   Weighted L2 carrier for adelic GL2​ cusp forms
-- statement:
--   Throughout, $F$ is a number field. The determinant slab `detNormSlab F α β` is the set of $g \in \mathrm{GL}_2(\mathbb{A}_F)$ whose idele norm $\|\det g\|$ (the value of the module-Haar character, as in [`NumberField.TateGlobal.ideleNorm`](../def/NumberField_TateGlobalZeta.html#L19)) lies in $[\alpha,\beta]$. The structure `IsSlabFundamentalDomain F α β Φ₀` carries as fields $0 < \alpha$, $\alpha < \beta$, the inclusion $\Phi_0 \subseteq$ slab, and the assertion, in Mathlib's sense, that $\Phi_0$ is a fundamental domain for the left action of the image of $\mathrm{GL}_2(F)$ on the slab-restricted Haar measure of $\mathrm{GL}_2(\mathbb{A}_F)$; thus it is a property of a chosen set, not a construction of one. `fdPins F Φ₀` is the tuple of pins built from $\Phi_0$: Borel structures and Haar measure on $\mathrm{GL}_2(\mathbb{A}_F)$, central subgroup $\top$, level subgroups $u \mapsto$ `levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F`, Hecke generators `heckeGen`, and the additive adelic Haar measure conditioned on `adelicBox F`. `HasModulus F ξ σ` says $\|\xi(z)\| = \|z\|^{\sigma}$ for every idele $z$. The weight is $w_\sigma(x) = \|\det x\|^{-\sigma}$, the weighted measure is $w_\sigma \cdot \mu|_{\Phi_0}$ for $\mu$ the Haar measure, and the carrier is Mathlib's $L^2$ space of that measure.
--
--   `memberSubmodule F Φ₀ ξ` is the space of $\varphi : \mathrm{GL}_2(\mathbb{A}_F) \to \mathbb{C}$ automorphic at these pins, equivalently (as recorded by `isAutomorphicFnAt_fdPins_iff`) left $\mathrm{GL}_2(F)$-invariant, transforming by $\xi$ under central scalars, and square-integrable on $\Phi_0$; `contMemberSubmodule` adds continuity, and `cuspMemberSubmodule` consists of continuous $\varphi$ satisfying `IsSmoothCuspAutomorphicFnAt` — whose conditions, as used in the closure proofs, are membership above, vanishing of `constantTerm` along `unipotentGL2` against the conditioned measure, and openness of the right-translation stabiliser. Boundedness of $w_\sigma$ on the slab by $\max(\alpha^{-\sigma},\beta^{-\sigma})$ yields `memLp_weightedMeasure_of_mem` and hence the linear map `toCarrier` to the carrier; `cuspSubcarrier` and `cuspLevelSubcarrier` are the topological closures of the images of the cuspidal members, respectively of those additionally invariant under the level-$N$ subgroup, with `toCuspSubcarrier` the corestricted map. Further definitions are the explicit weighted pairing $\int_{\Phi_0} a \bar{b}\, \|\det x\|^{-\sigma} d\mu$, the predicate `IsLift` that a bounded operator on the carrier implements a given map on continuous members, and the involution $g^{\flat}(y) = \overline{g(y^{-1})}\,\|\det y\|^{-\sigma}$. Auxiliary results record continuity of the adelic unipotent embedding and integrability of the constant-term integrand.
--
--   **Relation to Mathlib.** The ambient analytic objects are Mathlib's: `IsFundamentalDomain`, `Measure.withDensity`, the $L^p$ spaces, the Haar measures on $\mathrm{GL}_2(\mathbb{A}_F)$ and on $\mathbb{A}_F$, and the module-Haar character underlying the idele norm. Mathlib has no notion of adelic automorphic or cusp form on $\mathrm{GL}_2$; the slab, the pins, the member submodules, the carrier and the lifting predicate are the project's own.
--
--   **Where it is used.** These definitions provide the Hilbert-space setting in which the cuspidal spectrum of $\mathrm{GL}_2$ over a number field is analysed (smoothing operators, discreteness, level-$N$ invariants), on the automorphic side of the modularity input to Fermat's Last Theorem. Everything is relative to the chosen fundamental domain $\Phi_0$ and the exponent $\sigma$: members do not depend on $\sigma$, their classes in the carrier do.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_AutomorphicForm_CuspidalSpectrumCarrier.lean

import Definitions.Def_AutomorphicForm_CuspidalConstituent
import Definitions.Def_NumberField_TateGlobalZeta

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox
open IsDedekindDomain
open scoped ComplexConjugate ENNReal InnerProductSpace

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel

noncomputable section

namespace AutomorphicForm

namespace CuspidalSpectrum

variable (F : Type) [Field F] [NumberField F]

def detNormSlab (α β : ℝ) : Set (AdelicGL2 (𝓞 F) F) :=
  {g | NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β}

@[simp] theorem mem_detNormSlab (α β : ℝ) (g : AdelicGL2 (𝓞 F) F) :
    g ∈ detNormSlab F α β ↔
      NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β := Iff.rfl

theorem detNormSlab_def (α β : ℝ) : detNormSlab F α β =
    {g | NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β} := rfl

structure IsSlabFundamentalDomain (α β : ℝ) (Φ₀ : Set (AdelicGL2 (𝓞 F) F)) : Prop where
  pos : 0 < α
  lt : α < β
  subset : Φ₀ ⊆ detNormSlab F α β
  isFundamentalDomain : IsFundamentalDomain (globalPoints (𝓞 F) F).range Φ₀
    ((adelicGLHaar (Fin 2) (𝓞 F) F).restrict (detNormSlab F α β))

theorem IsSlabFundamentalDomain.pos_right {α β : ℝ} {Φ₀ : Set (AdelicGL2 (𝓞 F) F)}
    (h : IsSlabFundamentalDomain F α β Φ₀) : 0 < β := h.pos.trans h.lt

abbrev fdPins (Φ₀ : Set (AdelicGL2 (𝓞 F) F)) : CarrierPins F :=
  productionPinsOf F Φ₀ (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F)
    (fun v => heckeGen (𝓞 F) F v) (adelicBox F)

@[simp] theorem fdPins_eq (Φ₀ : Set (AdelicGL2 (𝓞 F) F)) :
    fdPins F Φ₀ = productionPinsOf F Φ₀ (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F)
      (fun v => heckeGen (𝓞 F) F v) (adelicBox F) := rfl
@[simp] theorem fdPins_Z (Φ₀ : Set (AdelicGL2 (𝓞 F) F)) : (fdPins F Φ₀).Z = ⊤ := rfl
@[simp] theorem fdPins_D (Φ₀ : Set (AdelicGL2 (𝓞 F) F)) : (fdPins F Φ₀).D = Φ₀ := rfl
@[simp] theorem fdPins_mS (Φ₀ : Set (AdelicGL2 (𝓞 F) F)) : (fdPins F Φ₀).mS = glBorel (Fin 2) (𝓞 F) F := rfl
@[simp] theorem fdPins_μ (Φ₀ : Set (AdelicGL2 (𝓞 F) F)) : (fdPins F Φ₀).μ = adelicGLHaar (Fin 2) (𝓞 F) F := rfl
@[simp] theorem fdPins_U (Φ₀ : Set (AdelicGL2 (𝓞 F) F)) :
    (fdPins F Φ₀).U = fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F := rfl
@[simp] theorem fdPins_gen (Φ₀ : Set (AdelicGL2 (𝓞 F) F)) : (fdPins F Φ₀).gen = fun v => heckeGen (𝓞 F) F v := rfl
@[simp] theorem fdPins_nS (Φ₀ : Set (AdelicGL2 (𝓞 F) F)) : (fdPins F Φ₀).nS = adeleBorel (𝓞 F) F := rfl
@[simp] theorem fdPins_ν (Φ₀ : Set (AdelicGL2 (𝓞 F) F)) :
    (fdPins F Φ₀).ν = @ProbabilityTheory.cond _ (adeleBorel (𝓞 F) F) (adelicAddHaar (𝓞 F) F) (adelicBox F) := rfl

def HasModulus (ξ : (⊤ : Subgroup (AdeleRing (𝓞 F) F)ˣ) →* ℂˣ) (σ : ℝ) : Prop :=
  ∀ z : (⊤ : Subgroup (AdeleRing (𝓞 F) F)ˣ),
    ‖((ξ z : ℂˣ) : ℂ)‖ = NumberField.TateGlobal.ideleNorm F (z : (AdeleRing (𝓞 F) F)ˣ) ^ σ

theorem hasModulus_iff (ξ : (⊤ : Subgroup (AdeleRing (𝓞 F) F)ˣ) →* ℂˣ) (σ : ℝ) :
    HasModulus F ξ σ ↔ ∀ z : (⊤ : Subgroup (AdeleRing (𝓞 F) F)ˣ),
      ‖((ξ z : ℂˣ) : ℂ)‖ = NumberField.TateGlobal.ideleNorm F (z : (AdeleRing (𝓞 F) F)ˣ) ^ σ := Iff.rfl

theorem hasModulus_iff_units (ξ : (⊤ : Subgroup (AdeleRing (𝓞 F) F)ˣ) →* ℂˣ) (σ : ℝ) :
    HasModulus F ξ σ ↔ ∀ z : (AdeleRing (𝓞 F) F)ˣ,
      ‖((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ)‖ = NumberField.TateGlobal.ideleNorm F z ^ σ :=
  ⟨fun h z => h ⟨z, Subgroup.mem_top z⟩, fun h z => h z⟩

def weight (σ : ℝ) (x : AdelicGL2 (𝓞 F) F) : ℝ :=
  NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det x) ^ (-σ)

theorem weight_def (σ : ℝ) (x : AdelicGL2 (𝓞 F) F) :
    weight F σ x = NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det x) ^ (-σ) := rfl

def weightedMeasure (Φ₀ : Set (AdelicGL2 (𝓞 F) F)) (σ : ℝ) : Measure (AdelicGL2 (𝓞 F) F) :=
  ((adelicGLHaar (Fin 2) (𝓞 F) F).restrict Φ₀).withDensity fun x => ENNReal.ofReal (weight F σ x)

theorem weightedMeasure_def (Φ₀ : Set (AdelicGL2 (𝓞 F) F)) (σ : ℝ) :
    weightedMeasure F Φ₀ σ =
      ((adelicGLHaar (Fin 2) (𝓞 F) F).restrict Φ₀).withDensity fun x => ENNReal.ofReal (weight F σ x) := rfl

abbrev Carrier (Φ₀ : Set (AdelicGL2 (𝓞 F) F)) (σ : ℝ) : Type :=
  Lp ℂ 2 (weightedMeasure F Φ₀ σ)

theorem isAutomorphicFnAt_fdPins_iff (Φ₀ : Set (AdelicGL2 (𝓞 F) F)) (ξ : (⊤ : Subgroup (AdeleRing (𝓞 F) F)ˣ) →* ℂˣ)
    (φ : AdelicGL2 (𝓞 F) F → ℂ) :
    IsAutomorphicFnAt F (fdPins F Φ₀) ξ φ ↔
      IsLsXiFunction (𝓞 F) F ⊤ ξ φ ∧ MemLp φ 2 ((adelicGLHaar (Fin 2) (𝓞 F) F).restrict Φ₀) :=
  lsXiMemberAt_iff (𝓞 F) F (adelicGLHaar (Fin 2) (𝓞 F) F) ⊤ ξ Φ₀ φ

def memberSubmodule (Φ₀ : Set (AdelicGL2 (𝓞 F) F)) (ξ : (⊤ : Subgroup (AdeleRing (𝓞 F) F)ˣ) →* ℂˣ) :
    Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ) where
  carrier := {φ | IsAutomorphicFnAt F (fdPins F Φ₀) ξ φ}
  zero_mem' := (isAutomorphicFnAt_fdPins_iff F Φ₀ ξ 0).mpr
    ⟨⟨fun _ _ => rfl, fun _ _ => by simp⟩, MemLp.zero⟩
  add_mem' := fun {a b} ha hb => by
    obtain ⟨⟨hal, hac⟩, ham⟩ := (isAutomorphicFnAt_fdPins_iff F Φ₀ ξ a).mp ha
    obtain ⟨⟨hbl, hbc⟩, hbm⟩ := (isAutomorphicFnAt_fdPins_iff F Φ₀ ξ b).mp hb
    exact (isAutomorphicFnAt_fdPins_iff F Φ₀ ξ (a + b)).mpr
      ⟨⟨fun γ g => by rw [Pi.add_apply, Pi.add_apply, hal, hbl],
        fun z g => by rw [Pi.add_apply, Pi.add_apply, hac, hbc, mul_add]⟩, ham.add hbm⟩
  smul_mem' := fun c {a} ha => by
    obtain ⟨⟨hal, hac⟩, ham⟩ := (isAutomorphicFnAt_fdPins_iff F Φ₀ ξ a).mp ha
    exact (isAutomorphicFnAt_fdPins_iff F Φ₀ ξ (c • a)).mpr
      ⟨⟨fun γ g => by rw [Pi.smul_apply, Pi.smul_apply, hal],
        fun z g => by rw [Pi.smul_apply, Pi.smul_apply, hac, smul_eq_mul, smul_eq_mul, mul_left_comm]⟩,
        ham.const_smul c⟩

theorem mem_memberSubmodule_iff (Φ₀ : Set (AdelicGL2 (𝓞 F) F)) (ξ : (⊤ : Subgroup (AdeleRing (𝓞 F) F)ˣ) →* ℂˣ)
    (φ : AdelicGL2 (𝓞 F) F → ℂ) :
    φ ∈ memberSubmodule F Φ₀ ξ ↔ IsAutomorphicFnAt F (fdPins F Φ₀) ξ φ := Iff.rfl

theorem mem_memberSubmodule_iff' (Φ₀ : Set (AdelicGL2 (𝓞 F) F)) (ξ : (⊤ : Subgroup (AdeleRing (𝓞 F) F)ˣ) →* ℂˣ)
    (φ : AdelicGL2 (𝓞 F) F → ℂ) :
    φ ∈ memberSubmodule F Φ₀ ξ ↔
      IsLsXiFunction (𝓞 F) F ⊤ ξ φ ∧ MemLp φ 2 ((adelicGLHaar (Fin 2) (𝓞 F) F).restrict Φ₀) :=
  isAutomorphicFnAt_fdPins_iff F Φ₀ ξ φ

def contMemberSubmodule (Φ₀ : Set (AdelicGL2 (𝓞 F) F)) (ξ : (⊤ : Subgroup (AdeleRing (𝓞 F) F)ˣ) →* ℂˣ) :
    Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ) where
  carrier := {φ | φ ∈ memberSubmodule F Φ₀ ξ ∧ Continuous φ}
  zero_mem' := ⟨(memberSubmodule F Φ₀ ξ).zero_mem, continuous_const⟩
  add_mem' := fun {a b} ha hb => ⟨(memberSubmodule F Φ₀ ξ).add_mem ha.1 hb.1, ha.2.add hb.2⟩
  smul_mem' := fun c {a} ha => ⟨(memberSubmodule F Φ₀ ξ).smul_mem c ha.1, ha.2.const_smul c⟩

theorem continuous_unipotentGL2_adele :
    Continuous fun x : AdeleRing (𝓞 F) F => (unipotentGL2 x : AdelicGL2 (𝓞 F) F) := by
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j <;>
      simp [unipotentGL2] <;> first | exact continuous_const | exact continuous_id
  · have h : ∀ x : AdeleRing (𝓞 F) F,
        (((unipotentGL2 x)⁻¹ : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) = !![1, -x; 0, 1] :=
      fun x => rfl
    simp_rw [h]
    refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j <;>
      simp <;> first | exact continuous_const | exact continuous_id | exact continuous_neg

theorem integrable_constantTermIntegrand_fdPins (Φ₀ : Set (AdelicGL2 (𝓞 F) F))
    {φ : AdelicGL2 (𝓞 F) F → ℂ} (hφ : Continuous φ) (g : AdelicGL2 (𝓞 F) F) :
    letI : MeasurableSpace (AdeleRing (𝓞 F) F) := (fdPins F Φ₀).nS
    Integrable (constantTermIntegrand unipotentGL2 φ g) (fdPins F Φ₀).ν := by
  letI : MeasurableSpace (AdeleRing (𝓞 F) F) := adeleBorel (𝓞 F) F
  haveI : BorelSpace (AdeleRing (𝓞 F) F) := borelSpace_adeleBorel (𝓞 F) F
  haveI := isAddHaarMeasure_adelicAddHaar (𝓞 F) F
  show Integrable (constantTermIntegrand unipotentGL2 φ g)
    (@ProbabilityTheory.cond _ (adeleBorel (𝓞 F) F) (adelicAddHaar (𝓞 F) F) (adelicBox F))
  have hcont : Continuous (constantTermIntegrand (unipotentGL2 (R := AdeleRing (𝓞 F) F)) φ g) :=
    hφ.comp ((continuous_unipotentGL2_adele F).mul continuous_const)
  obtain ⟨C, hC, hsub⟩ := exists_isCompact_adelicBox_subset F
  have hint : IntegrableOn (constantTermIntegrand (unipotentGL2 (R := AdeleRing (𝓞 F) F)) φ g) (adelicBox F)
      (adelicAddHaar (𝓞 F) F) :=
    (hcont.continuousOn.integrableOn_compact hC).mono_set hsub
  rw [ProbabilityTheory.cond]
  exact hint.smul_measure (ENNReal.inv_ne_top.mpr (adelicAddHaar_adelicBox_pos F).ne')

def cuspMemberSubmodule (Φ₀ : Set (AdelicGL2 (𝓞 F) F)) (ξ : (⊤ : Subgroup (AdeleRing (𝓞 F) F)ˣ) →* ℂˣ) :
    Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ) where
  carrier := {φ | IsSmoothCuspAutomorphicFnAt F (fdPins F Φ₀) ξ φ ∧ Continuous φ}
  zero_mem' := ⟨isSmoothCuspAutomorphicFnAt_zero F (fdPins F Φ₀) ξ, continuous_const⟩
  add_mem' := fun {a b} ha hb => by
    refine ⟨⟨⟨(memberSubmodule F Φ₀ ξ).add_mem ha.1.1.1 hb.1.1.1, fun g => ?_⟩, ?_⟩, ha.2.add hb.2⟩
    ·
      letI : MeasurableSpace (AdeleRing (𝓞 F) F) := (fdPins F Φ₀).nS
      have hia := integrable_constantTermIntegrand_fdPins F Φ₀ ha.2 g
      have hib := integrable_constantTermIntegrand_fdPins F Φ₀ hb.2 g
      have h0a := ha.1.1.2 g
      have h0b := hb.1.1.2 g
      unfold constantTerm at h0a h0b ⊢
      have : constantTermIntegrand (unipotentGL2 (R := AdeleRing (𝓞 F) F)) (a + b) g
          = fun q => constantTermIntegrand unipotentGL2 a g q + constantTermIntegrand unipotentGL2 b g q := rfl
      rw [this, integral_add hia hib, h0a, h0b, add_zero]
    ·
      refine Subgroup.isOpen_mono ?_ (FLT.SmoothVectors.isOpen_coe_inf_stabilizer ha.1.2 hb.1.2)
      intro u hu
      obtain ⟨hua, hub⟩ := Subgroup.mem_inf.mp hu
      rw [MulAction.mem_stabilizer_iff] at hua hub ⊢
      refine FLT.SmoothVectors.RightTranslationFn.ext fun x => ?_
      have h1 := congrArg (fun f => FLT.SmoothVectors.RightTranslationFn.toFun f x) hua
      have h2 := congrArg (fun f => FLT.SmoothVectors.RightTranslationFn.toFun f x) hub
      simp only [Subgroup.smul_def, FLT.SmoothVectors.RightTranslationFn.toFun_smul,
        FLT.SmoothVectors.RightTranslationFn.toFun_mk] at h1 h2 ⊢
      show a (x * ↑u) + b (x * ↑u) = a x + b x
      rw [h1, h2]
  smul_mem' := fun c {a} ha => by
    refine ⟨⟨⟨(memberSubmodule F Φ₀ ξ).smul_mem c ha.1.1.1, fun g => ?_⟩, ?_⟩, ha.2.const_smul c⟩
    · letI : MeasurableSpace (AdeleRing (𝓞 F) F) := (fdPins F Φ₀).nS
      have h0a := ha.1.1.2 g
      unfold constantTerm at h0a ⊢
      have : constantTermIntegrand (unipotentGL2 (R := AdeleRing (𝓞 F) F)) (c • a) g
          = fun q => c * constantTermIntegrand unipotentGL2 a g q := rfl
      rw [this, integral_const_mul, h0a, mul_zero]
    · refine Subgroup.isOpen_mono ?_ ha.1.2
      intro u hua
      rw [MulAction.mem_stabilizer_iff] at hua ⊢
      refine FLT.SmoothVectors.RightTranslationFn.ext fun x => ?_
      have h1 := congrArg (fun f => FLT.SmoothVectors.RightTranslationFn.toFun f x) hua
      simp only [Subgroup.smul_def, FLT.SmoothVectors.RightTranslationFn.toFun_smul,
        FLT.SmoothVectors.RightTranslationFn.toFun_mk] at h1 ⊢
      show c • a (x * ↑u) = c • a x
      rw [h1]

theorem memLp_weightedMeasure_of_mem {α β : ℝ} {Φ₀ : Set (AdelicGL2 (𝓞 F) F)}
    (hΦ₀ : IsSlabFundamentalDomain F α β Φ₀) (σ : ℝ) {ξ : (⊤ : Subgroup (AdeleRing (𝓞 F) F)ˣ) →* ℂˣ}
    {φ : AdelicGL2 (𝓞 F) F → ℂ} (hφ : φ ∈ memberSubmodule F Φ₀ ξ) :
    MemLp φ 2 (weightedMeasure F Φ₀ σ) := by
  set μ := adelicGLHaar (Fin 2) (𝓞 F) F with hμ
  have hmem := ((isAutomorphicFnAt_fdPins_iff F Φ₀ ξ φ).mp hφ).2

  have hres : μ.restrict Φ₀ = (μ.restrict (detNormSlab F α β)).restrict Φ₀ := by
    rw [Measure.restrict_restrict₀ hΦ₀.isFundamentalDomain.nullMeasurableSet, Set.inter_eq_left.mpr hΦ₀.subset]
  have hae : ∀ᵐ x ∂(μ.restrict Φ₀), x ∈ Φ₀ := by
    rw [hres]; exact ae_restrict_mem₀ hΦ₀.isFundamentalDomain.nullMeasurableSet

  set C : ℝ := max (α ^ (-σ)) (β ^ (-σ)) with hC
  have hbound : ∀ x ∈ Φ₀, weight F σ x ≤ C := by
    intro x hx
    obtain ⟨h1, h2⟩ := hΦ₀.subset hx
    unfold weight
    rcases le_or_gt 0 (-σ) with hs | hs
    · exact (Real.rpow_le_rpow (hΦ₀.pos.le.trans h1) h2 hs).trans (le_max_right _ _)
    · exact (Real.rpow_le_rpow_of_nonpos hΦ₀.pos h1 hs.le).trans (le_max_left _ _)
  have hle : weightedMeasure F Φ₀ σ ≤ (ENNReal.ofReal C) • μ.restrict Φ₀ := by
    unfold weightedMeasure
    rw [← withDensity_const]
    exact withDensity_mono (hae.mono fun x hx => ENNReal.ofReal_le_ofReal (hbound x hx))
  exact (hmem.smul_measure ENNReal.ofReal_ne_top).mono_measure hle

def toCarrier {α β : ℝ} {Φ₀ : Set (AdelicGL2 (𝓞 F) F)} (hΦ₀ : IsSlabFundamentalDomain F α β Φ₀) (σ : ℝ)
    (ξ : (⊤ : Subgroup (AdeleRing (𝓞 F) F)ˣ) →* ℂˣ) : ↥(memberSubmodule F Φ₀ ξ) →ₗ[ℂ] Carrier F Φ₀ σ where
  toFun φ := (memLp_weightedMeasure_of_mem F hΦ₀ σ φ.2).toLp (φ : AdelicGL2 (𝓞 F) F → ℂ)
  map_add' φ ψ := MemLp.toLp_add (memLp_weightedMeasure_of_mem F hΦ₀ σ φ.2) (memLp_weightedMeasure_of_mem F hΦ₀ σ ψ.2)
  map_smul' c φ := MemLp.toLp_const_smul c (memLp_weightedMeasure_of_mem F hΦ₀ σ φ.2)

def pairing (Φ₀ : Set (AdelicGL2 (𝓞 F) F)) (σ : ℝ) (a b : AdelicGL2 (𝓞 F) F → ℂ) : ℂ :=
  ∫ x in Φ₀, a x * conj (b x) *
      ((NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det x) ^ (-σ) : ℝ) : ℂ)
    ∂(adelicGLHaar (Fin 2) (𝓞 F) F)

theorem pairing_def (Φ₀ : Set (AdelicGL2 (𝓞 F) F)) (σ : ℝ) (a b : AdelicGL2 (𝓞 F) F → ℂ) :
    pairing F Φ₀ σ a b = ∫ x in Φ₀, a x * conj (b x) *
      ((NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det x) ^ (-σ) : ℝ) : ℂ)
    ∂(adelicGLHaar (Fin 2) (𝓞 F) F) := rfl

def cuspSubcarrier {α β : ℝ} {Φ₀ : Set (AdelicGL2 (𝓞 F) F)} (hΦ₀ : IsSlabFundamentalDomain F α β Φ₀) (σ : ℝ)
    (ξ : (⊤ : Subgroup (AdeleRing (𝓞 F) F)ˣ) →* ℂˣ) : Submodule ℂ (Carrier F Φ₀ σ) :=
  (Submodule.map (toCarrier F hΦ₀ σ ξ)
      (Submodule.comap (memberSubmodule F Φ₀ ξ).subtype (cuspMemberSubmodule F Φ₀ ξ))).topologicalClosure

def toCuspSubcarrier {α β : ℝ} {Φ₀ : Set (AdelicGL2 (𝓞 F) F)} (hΦ₀ : IsSlabFundamentalDomain F α β Φ₀) (σ : ℝ)
    (ξ : (⊤ : Subgroup (AdeleRing (𝓞 F) F)ˣ) →* ℂˣ) :
    ↥(cuspMemberSubmodule F Φ₀ ξ) →ₗ[ℂ] ↥(cuspSubcarrier F hΦ₀ σ ξ) :=
  LinearMap.codRestrict _ ((toCarrier F hΦ₀ σ ξ).comp
      (Submodule.inclusion (show cuspMemberSubmodule F Φ₀ ξ ≤ memberSubmodule F Φ₀ ξ from fun _ h => h.1.1.1)))
    (fun φ => Submodule.le_topologicalClosure _
      ⟨Submodule.inclusion (show cuspMemberSubmodule F Φ₀ ξ ≤ memberSubmodule F Φ₀ ξ from fun _ h => h.1.1.1) φ,
        φ.2, rfl⟩)

theorem toCuspSubcarrier_apply_coe {α β : ℝ} {Φ₀ : Set (AdelicGL2 (𝓞 F) F)} (hΦ₀ : IsSlabFundamentalDomain F α β Φ₀)
    (σ : ℝ) (ξ : (⊤ : Subgroup (AdeleRing (𝓞 F) F)ˣ) →* ℂˣ) (φ : ↥(cuspMemberSubmodule F Φ₀ ξ)) :
    (toCuspSubcarrier F hΦ₀ σ ξ φ : Carrier F Φ₀ σ) = toCarrier F hΦ₀ σ ξ ⟨φ, φ.2.1.1.1⟩ := rfl

def cuspLevelSubcarrier {α β : ℝ} {Φ₀ : Set (AdelicGL2 (𝓞 F) F)} (hΦ₀ : IsSlabFundamentalDomain F α β Φ₀)
    (σ : ℝ) (ξ : (⊤ : Subgroup (AdeleRing (𝓞 F) F)ˣ) →* ℂˣ) (N : Ideal (𝓞 F)) : Submodule ℂ (Carrier F Φ₀ σ) :=
  (Submodule.map (toCarrier F hΦ₀ σ ξ)
      (Submodule.comap (memberSubmodule F Φ₀ ξ).subtype
        (cuspMemberSubmodule F Φ₀ ξ ⊓
          CuspidalConstituent.levelInvariantSubmodule F (fdPins F Φ₀) N))).topologicalClosure

structure IsLift {α β : ℝ} {Φ₀ : Set (AdelicGL2 (𝓞 F) F)} (hΦ₀ : IsSlabFundamentalDomain F α β Φ₀) (σ : ℝ)
    (ξ : (⊤ : Subgroup (AdeleRing (𝓞 F) F)ˣ) →* ℂˣ) (Tfun : (AdelicGL2 (𝓞 F) F → ℂ) → (AdelicGL2 (𝓞 F) F → ℂ))
    (T : Carrier F Φ₀ σ →L[ℂ] Carrier F Φ₀ σ) : Prop where
  mapsTo : ∀ φ, φ ∈ contMemberSubmodule F Φ₀ ξ → Tfun φ ∈ contMemberSubmodule F Φ₀ ξ
  comm : ∀ (φ : AdelicGL2 (𝓞 F) F → ℂ) (h : φ ∈ contMemberSubmodule F Φ₀ ξ),
    T (toCarrier F hΦ₀ σ ξ ⟨φ, h.1⟩) = toCarrier F hΦ₀ σ ξ ⟨Tfun φ, (mapsTo φ h).1⟩

def flat (σ : ℝ) (g : AdelicGL2 (𝓞 F) F → ℂ) : AdelicGL2 (𝓞 F) F → ℂ :=
  fun y => conj (g y⁻¹) *
    ((NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det y) ^ (-σ) : ℝ) : ℂ)

end CuspidalSpectrum

end AutomorphicForm

end



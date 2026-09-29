-- Prove2me | solution 1 for AutomorphicForm.exists_paleyWiener_oneIndex_apply_diagOne_mul_eq_of_isInducedSection_of_contDiff_of_pos
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/9bff6e44-2d63-5288-a654-9a881f307585

import Definitions.Def_AutomorphicForm_RowIsometryInvariance
import Definitions.Def_AutomorphicForm_AutomorphicFnAt
import Definitions.Def_AutomorphicForm_SlabProfile
import Definitions.Def_AutomorphicForm_ResidualSpan
import Definitions.Def_AutomorphicForm_InducedSection
import Definitions.Def_AutomorphicForm_EtaFamily
import Definitions.Def_AutomorphicForm_WeylIntertwining
import Definitions.Def_AutomorphicForm_SmoothAutomorphicFnAt
import Definitions.Def_AutomorphicForm_ArchKFinite
import Definitions.Def_AutomorphicForm_AdelicMaximalCompact
import Definitions.Def_M4aHerbrand_IdeleClassVocab
import Definitions.Def_NumberField_AdelicBox
import Definitions.Def_NumberField_IdeleProductMeasure
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_AutomorphicForm_RationalTorusUnipotentQuotient
import Definitions.Def_NumberField_AdelicHeight
import Definitions.Def_AutomorphicForm_CarrierPins
import Mathlib.Analysis.Meromorphic.NormalForm
import Theorems.Thm_AutomorphicForm_exists_flat_isInducedSection_family_eq_of_isInducedSection
import Theorems.Thm_MellinPaleyWiener_differentiable_and_forall_decay_and_inversion_of_contDiff_of_hasCompactSupport
import Theorems.Thm_NumberField_AdeleRing_distribHaarChar_algebraMap
import Theorems.Thm_AutomorphicForm_exists_mem_adelicBorel_mul_eq
import Theorems.Thm_NumberField_AdelicHeight_adelicHeight_mul_of_mem_adelicMaximalCompact
import Theorems.Thm_AutomorphicForm_isInducedSection_adelicHeight_cpow
import Definitions.Def_AutomorphicForm_ArchType
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_paleyWiener_oneIndex_apply_diagOne_mul_eq_of_isInducedSection_of_contDiff_of_pos
p2m_attr_erase "instance" "instCountableOfNumberField_definitions HeckePair.instSMulCommClassSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instAlgebraSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instOneSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instIsScalarTowerSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instRingSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instMulSubtypeForallMemSubmoduleHeckeAlgebra"
p2m_attr_erase "simp" "AutomorphicForm.fnTwist_zero AutomorphicForm.fnTwist_apply LocalGL2.coe_localRepSome LocalGL2.coe_diagPi LocalGL2.coe_localRepInf LocalGL2.coe_localRepSome_inv LocalGL2.coe_unipotentInt LocalGL2.coe_weylInt LocalGL2.coe_diagPi_inv LocalGL2.transposeGL_val LocalGL2.transposeGL_one HeckePair.convTerm_mk HeckePair.coe_apply_add HeckePair.coe_apply_smul LocalGL2.swapUnit_val"

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox
open AutomorphicForm
open scoped NNReal ENNReal Topology

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel
  NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.borelSpace_adeleBorel
  NumberField.Idele.ideleBorel NumberField.Idele.borelSpace_ideleBorel

noncomputable section

namespace EPWAx

open FLT.SmoothVectors

theorem ofReal_cpow_eq_exp (x : ℝ) (hx : 0 < x) (w : ℂ) :
    ((x : ℝ) : ℂ) ^ w = Complex.exp (w * (Real.log x : ℂ)) := by
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.2 hx.ne'), ← Complex.ofReal_log hx.le, mul_comm]

theorem rightTranslatesSpanFinite_const_mul {G : Type*} [Group G] (K : Subgroup G) (c : ℂ) {f : G → ℂ}
    (hf : RightTranslatesSpanFinite K f) : RightTranslatesSpanFinite K (fun x => c * f x) := by
  obtain ⟨s, hs⟩ := hf
  refine ⟨s, fun k hk => ?_⟩
  have h : (fun x => c * f (x * k)) = c • (fun x => f (x * k)) := by
    funext x; simp [Pi.smul_apply, smul_eq_mul]
  rw [h]
  exact Submodule.smul_mem _ c (hs k hk)

theorem isArchKFinite_const_mul (F : Type) [Field F] [NumberField F] (c : ℂ)
    {f : AdelicGL2 (𝓞 F) F → ℂ} (hf : IsArchKFinite F f) : IsArchKFinite F (fun x => c * f x) :=
  fun w => rightTranslatesSpanFinite_const_mul _ c (hf w)

theorem isKfSmooth_const_mul (F : Type) [Field F] [NumberField F] (c : ℂ)
    {f : AdelicGL2 (𝓞 F) F → ℂ} (hf : IsKfSmooth F f) : IsKfSmooth F (fun x => c * f x) := by
  unfold IsKfSmooth at hf ⊢
  rw [isSmoothVector_iff_isOpen_stabilizer] at hf ⊢
  refine Subgroup.isOpen_mono ?_ hf
  intro u hu
  rw [MulAction.mem_stabilizer_iff] at hu ⊢
  apply RightTranslationFn.ext
  intro x
  have h1 := congrArg (fun φ => RightTranslationFn.toFun φ x) hu
  simp only [Subgroup.smul_def, RightTranslationFn.toFun_smul] at h1 ⊢
  show c * f (x * (u : AdelicGL2 (𝓞 F) F)) = c * f x
  have h2 : f (x * (u : AdelicGL2 (𝓞 F) F)) = f x := h1
  rw [h2]

theorem diagOne_mem_adelicBorel (F : Type) [Field F] [NumberField F] (y : (AdeleRing (𝓞 F) F)ˣ) :
    NumberField.AdelicLevel.diagOne y ∈ adelicBorel (𝓞 F) F := by
  show ((NumberField.AdelicLevel.diagOne y : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) 1 0 = 0
  rw [NumberField.AdelicLevel.diagOne_coe_apply]
  simp

theorem borelDiagFst_diagOne (F : Type) [Field F] [NumberField F] (y : (AdeleRing (𝓞 F) F)ˣ) :
    borelDiagFst (⟨NumberField.AdelicLevel.diagOne y, diagOne_mem_adelicBorel F y⟩ : ↥(adelicBorel (𝓞 F) F)) = y := by
  apply Units.ext
  show ((NumberField.AdelicLevel.diagOne y : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) 0 0 = (y : AdeleRing (𝓞 F) F)
  rw [NumberField.AdelicLevel.diagOne_coe_apply]
  simp

theorem borelDiagSnd_diagOne (F : Type) [Field F] [NumberField F] (y : (AdeleRing (𝓞 F) F)ˣ) :
    borelDiagSnd (⟨NumberField.AdelicLevel.diagOne y, diagOne_mem_adelicBorel F y⟩ : ↥(adelicBorel (𝓞 F) F)) = 1 := by
  apply Units.ext
  show ((NumberField.AdelicLevel.diagOne y : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) 1 1 = ((1 : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F)
  rw [NumberField.AdelicLevel.diagOne_coe_apply]
  simp

end EPWAx

section FlatInherit
open AutomorphicForm AutomorphicForm.WindowedSiegel in
theorem EPWAx.flatInherit
    (F : Type) [Field F] [NumberField F] :
    let α : (AdeleRing (𝓞 F) F)ˣ →* ℝˣ :=
      ((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp
        (distribHaarChar (AdeleRing (𝓞 F) F))).toHomUnits
    ∀ (hα : ∀ x, 0 < ((α x : ℝˣ) : ℝ))
      (μ ν : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ)
      (ψ : ℂ → AdelicGL2 (𝓞 F) F → ℂ)
      (_hψ : ∀ s, IsInducedSection (𝓞 F) F (etaFst μ α hα s) (etaSnd ν α hα s) (ψ s))
      (_hψK : ∀ s, IsArchKFinite F (ψ s))
      (_hψf : ∀ s, IsKfSmooth F (ψ s))
      (_hψjc : Continuous (fun p : ℂ × AdelicGL2 (𝓞 F) F => ψ p.1 p.2))
      (_hψhol : ∀ g, Differentiable ℂ (fun s => ψ s g))
      (_hψflat : ∀ (s s' : ℂ) (k : AdelicGL2 (𝓞 F) F),
          glFin (𝓞 F) F k ∈ finiteIntegralGL2 (𝓞 F) F →
          (∀ w : InfinitePlace F, IsRowIsometry (archComponent F w (glArch (𝓞 F) F k))) →
          ψ s k = ψ s' k),
    (∀ w : InfinitePlace F, ∃ W : Submodule ℂ (↥(archRowIsometrySubgroup F w) → ℂ),
        FiniteDimensional ℂ W ∧ ∀ (s : ℂ) (g : AdelicGL2 (𝓞 F) F),
          (fun k : ↥(archRowIsometrySubgroup F w) => ψ s (g * (k : AdelicGL2 (𝓞 F) F))) ∈ W) ∧
    (∀ (σ₀ : ℝ) (C : Set (AdelicGL2 (𝓞 F) F)), IsCompact C →
        ∃ M : ℝ, ∀ σ' : ℝ, |σ'| ≤ σ₀ →
          ∀ (t : ℝ), ∀ g ∈ C, ‖ψ ((σ' : ℂ) + (t : ℂ) * Complex.I) g‖ ≤ M) := by
  intro α hα μ ν ψ hψ hψK hψf hψjc hψhol hψflat

  have hKw : ∀ (w : InfinitePlace F) (k' : ↥(archRowIsometrySubgroup F w)),
      glFin (𝓞 F) F (k' : AdelicGL2 (𝓞 F) F) = 1 ∧
      ∀ v : InfinitePlace F, IsRowIsometry (archComponent F v (glArch (𝓞 F) F (k' : AdelicGL2 (𝓞 F) F))) := by
    intro w k'
    obtain ⟨k, hk, hkeq⟩ := Subgroup.mem_map.1 k'.2
    rw [← hkeq]
    refine ⟨?_, fun v => ?_⟩
    · show glFin (𝓞 F) F (adelicArchGLIncl F (archGLIncl F w k)) = 1
      exact glFin_adelicArchGLIncl F _
    · show IsRowIsometry (archComponent F v (glArch (𝓞 F) F (adelicArchGLIncl F (archGLIncl F w k))))
      rw [glArch_adelicArchGLIncl]
      by_cases hvw : v = w
      · subst hvw; rw [archComponent_archGLIncl_self]; exact mem_rowIsometrySubgroup_iff.1 hk
      · rw [archComponent_archGLIncl_of_ne F hvw]; exact isRowIsometry_one
  have hprod : ∀ (w : InfinitePlace F) (k₀ : AdelicGL2 (𝓞 F) F),
      glFin (𝓞 F) F k₀ ∈ finiteIntegralGL2 (𝓞 F) F →
      (∀ v : InfinitePlace F, IsRowIsometry (archComponent F v (glArch (𝓞 F) F k₀))) →
      ∀ k' : ↥(archRowIsometrySubgroup F w),
        glFin (𝓞 F) F (k₀ * (k' : AdelicGL2 (𝓞 F) F)) ∈ finiteIntegralGL2 (𝓞 F) F ∧
        ∀ v : InfinitePlace F, IsRowIsometry (archComponent F v (glArch (𝓞 F) F (k₀ * (k' : AdelicGL2 (𝓞 F) F)))) := by
    intro w k₀ hk1 hk2 k'
    obtain ⟨h1, h2⟩ := hKw w k'
    refine ⟨by rw [map_mul, h1, mul_one]; exact hk1, fun v => by rw [map_mul, map_mul]; exact (hk2 v).mul (h2 v)⟩
  constructor
  ·
    intro w
    classical
    obtain ⟨S, hS⟩ := hψK 0 w
    haveI hVfd : FiniteDimensional ℂ (Submodule.span ℂ (S : Set (AdelicGL2 (𝓞 F) F → ℂ))) :=
      FiniteDimensional.span_of_finite ℂ S.finite_toSet
    let bV := Module.finBasis ℂ (Submodule.span ℂ (S : Set (AdelicGL2 (𝓞 F) F → ℂ)))
    let vec : ↥(archRowIsometrySubgroup F w) → Submodule.span ℂ (S : Set (AdelicGL2 (𝓞 F) F → ℂ)) :=
      fun k' => ⟨fun x => ψ 0 (x * (k' : AdelicGL2 (𝓞 F) F)), hS _ k'.2⟩
    let c : Fin (Module.finrank ℂ (Submodule.span ℂ (S : Set (AdelicGL2 (𝓞 F) F → ℂ)))) →
        (↥(archRowIsometrySubgroup F w) → ℂ) := fun i k' => bV.repr (vec k') i
    refine ⟨Submodule.span ℂ (Set.range c), FiniteDimensional.span_of_finite ℂ (Set.finite_range c), fun s g => ?_⟩
    obtain ⟨b, k₀, hb, hk1, hk2, rfl⟩ := AutomorphicForm.exists_mem_adelicBorel_mul_eq F g
    set η : ℂ := ((etaFst μ α hα s (borelDiagFst (⟨b, hb⟩ : ↥(adelicBorel (𝓞 F) F))) : ℂˣ) : ℂ) *
        ((etaSnd ν α hα s (borelDiagSnd (⟨b, hb⟩ : ↥(adelicBorel (𝓞 F) F))) : ℂˣ) : ℂ) with hηdef

    have hrepr : ∀ k' : ↥(archRowIsometrySubgroup F w),
        ψ 0 (k₀ * (k' : AdelicGL2 (𝓞 F) F)) =
          ∑ i, c i k' * ((bV i : Submodule.span ℂ (S : Set (AdelicGL2 (𝓞 F) F → ℂ))) : AdelicGL2 (𝓞 F) F → ℂ) k₀ := by
      intro k'
      have hsum := bV.sum_repr (vec k')
      have hval := congrArg (fun f : Submodule.span ℂ (S : Set (AdelicGL2 (𝓞 F) F → ℂ)) => (f : AdelicGL2 (𝓞 F) F → ℂ) k₀) hsum
      simp only [Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at hval
      exact hval.symm
    have hexp : ∀ k' : ↥(archRowIsometrySubgroup F w),
        ψ s (b * k₀ * (k' : AdelicGL2 (𝓞 F) F)) =
          η * ∑ i, c i k' * ((bV i : Submodule.span ℂ (S : Set (AdelicGL2 (𝓞 F) F → ℂ))) : AdelicGL2 (𝓞 F) F → ℂ) k₀ := by
      intro k'
      obtain ⟨hp1, hp2⟩ := hprod w k₀ hk1 hk2 k'
      rw [mul_assoc, hψ s b hb, hψflat s 0 (k₀ * (k' : AdelicGL2 (𝓞 F) F)) hp1 hp2, hrepr k']
    have hfun : (fun k' : ↥(archRowIsometrySubgroup F w) => ψ s (b * k₀ * (k' : AdelicGL2 (𝓞 F) F))) =
        η • ∑ i, (((bV i : Submodule.span ℂ (S : Set (AdelicGL2 (𝓞 F) F → ℂ))) : AdelicGL2 (𝓞 F) F → ℂ) k₀) • c i := by
      funext k'
      rw [hexp k']
      simp only [Pi.smul_apply, Finset.sum_apply, smul_eq_mul]
      congr 1
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [hfun]
    exact Submodule.smul_mem _ _ (Submodule.sum_mem _ fun i _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩))
  ·
    intro σ₀ C hC
    have key : ∀ (σ' t : ℝ) (g : AdelicGL2 (𝓞 F) F),
        ‖ψ ((σ' : ℂ) + (t : ℂ) * Complex.I) g‖ = ‖ψ (σ' : ℂ) g‖ := by
      intro σ' t g
      obtain ⟨b, k, hb, hk1, hk2, rfl⟩ := AutomorphicForm.exists_mem_adelicBorel_mul_eq F g
      rw [hψ _ b hb k, hψ (σ' : ℂ) b hb k, hψflat ((σ' : ℂ) + (t : ℂ) * Complex.I) (σ' : ℂ) k hk1 hk2]
      simp only [norm_mul, etaFst_apply, etaSnd_apply, Units.val_mul, cpowChar_apply_val,
        Complex.norm_cpow_eq_rpow_re_of_pos (hα _)]
      have r1 : (((σ' : ℂ) + (t : ℂ) * Complex.I) + 1 / 2).re = ((σ' : ℂ) + 1 / 2).re := by simp
      have r2 : (-(((σ' : ℂ) + (t : ℂ) * Complex.I) + 1 / 2)).re = (-((σ' : ℂ) + 1 / 2)).re := by simp
      rw [r1, r2]
    have hcont : Continuous fun p : ℝ × AdelicGL2 (𝓞 F) F => ψ (p.1 : ℂ) p.2 :=
      hψjc.comp ((Complex.continuous_ofReal.comp continuous_fst).prodMk continuous_snd)
    obtain ⟨M, hM⟩ := (isCompact_Icc.prod hC).exists_bound_of_continuousOn
      (f := fun p : ℝ × AdelicGL2 (𝓞 F) F => ψ (p.1 : ℂ) p.2) (s := Set.Icc (-σ₀) σ₀ ×ˢ C) hcont.continuousOn
    refine ⟨M, fun σ' hσ' t g hg => ?_⟩
    rw [key]
    exact hM (σ', g) ⟨abs_le.1 hσ', hg⟩

end FlatInherit

theorem solution
    (F : Type) [Field F] [NumberField F] :
    let α : (AdeleRing (𝓞 F) F)ˣ →* ℝˣ :=
      ((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp
        (distribHaarChar (AdeleRing (𝓞 F) F))).toHomUnits
    ∀ (hα : ∀ x, 0 < ((α x : ℝˣ) : ℝ))
      (Φ : Set (AdelicGL2 (𝓞 F) F))
      (ξ : (productionPinsOf F Φ (fun N => levelOne (𝓞 F) F N) (fun v => heckeGen (𝓞 F) F v) (adelicBox F)).Z →* ℂˣ)
      (μ ν : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ)
      (_hμ : IsUnitaryChar (𝓞 F) F μ) (_hν : IsUnitaryChar (𝓞 F) F ν)
      (_hμic : IsIdeleClassChar (𝓞 F) F μ) (_hνic : IsIdeleClassChar (𝓞 F) F ν)
      (_hμc : Continuous fun x : (AdeleRing (𝓞 F) F)ˣ => ((μ x : ℂˣ) : ℂ))
      (_hνc : Continuous fun x : (AdeleRing (𝓞 F) F)ˣ => ((ν x : ℂˣ) : ℂ))
      (_hμν : ∀ z : (productionPinsOf F Φ (fun N => levelOne (𝓞 F) F N) (fun v => heckeGen (𝓞 F) F v) (adelicBox F)).Z, μ (z : (AdeleRing (𝓞 F) F)ˣ) * ν (z : (AdeleRing (𝓞 F) F)ˣ) = ξ z)
      (φ₀ : AdelicGL2 (𝓞 F) F → ℂ)
      (_hφ₀ : IsInducedSection (𝓞 F) F (etaFst μ α hα 0) (etaSnd ν α hα 0) φ₀)
      (_hφ₀K : IsArchKFinite F φ₀) (_hφ₀f : IsKfSmooth F φ₀) (_hφ₀c : Continuous φ₀)
      (a b : ℝ) (_ha : 0 < a) (_hb : 0 < b)
      (h₁ : ℝ → ℂ) (_hh₁ : ContDiff ℝ (⊤ : ℕ∞) h₁) (_hh₁c : HasCompactSupport h₁)
      (_hh₁b : ∀ u : ℝ, h₁ u ≠ 0 → u ∈ Set.Icc (Real.log a) (Real.log b)),
    ∃ (ψf₀ : ℂ → AdelicGL2 (𝓞 F) F → ℂ) (ψ₀ : AdelicGL2 (𝓞 F) F → ℂ),
      (∀ s, IsInducedSection (𝓞 F) F (etaFst μ α hα s) (etaSnd ν α hα s) (ψf₀ s)) ∧
      Continuous (fun p : ℂ × AdelicGL2 (𝓞 F) F => ψf₀ p.1 p.2) ∧
      (∀ g, Differentiable ℂ (fun s => ψf₀ s g)) ∧
      (∀ s, IsArchKFinite F (ψf₀ s)) ∧ (∀ s, IsKfSmooth F (ψf₀ s)) ∧
      (∀ w : InfinitePlace F, ∃ W : Submodule ℂ (↥(archRowIsometrySubgroup F w) → ℂ),
        FiniteDimensional ℂ W ∧ ∀ (s : ℂ) (g : AdelicGL2 (𝓞 F) F),
          (fun k : ↥(archRowIsometrySubgroup F w) => ψf₀ s (g * (k : AdelicGL2 (𝓞 F) F))) ∈ W) ∧
      (∀ (m₀ : ℕ) (σ₀ : ℝ) (C : Set (AdelicGL2 (𝓞 F) F)), IsCompact C →
        ∃ m : ℝ → ℝ, Integrable m ∧ (∃ B : ℝ, ∀ t, m t ≤ B) ∧ ∀ σ' : ℝ, |σ'| ≤ σ₀ →
          ∀ (t : ℝ), ∀ g ∈ C, (1 + |t|) ^ m₀ * ‖ψf₀ ((σ' : ℂ) + (t : ℂ) * Complex.I) g‖ ≤ m t) ∧
      AutomorphicForm.IsSlabProfile F (productionPinsOf F Φ (fun N => levelOne (𝓞 F) F N) (fun v => heckeGen (𝓞 F) F v) (adelicBox F)).Z ξ ψ₀ ∧
      (∀ (σ' : ℝ) (g : AdelicGL2 (𝓞 F) F),
        ψ₀ g = (((4 * Real.pi)⁻¹ : ℝ) : ℂ) * ∫ t : ℝ, ψf₀ ((σ' : ℂ) + (t : ℂ) * Complex.I) g) ∧
      (∀ g : AdelicGL2 (𝓞 F) F, ψ₀ g ≠ 0 → NumberField.AdelicHeight.adelicHeight F g ∈ Set.Icc a b) ∧
      (∀ (y : (AdeleRing (𝓞 F) F)ˣ) (k : AdelicGL2 (𝓞 F) F),
        glFin (𝓞 F) F k ∈ finiteIntegralGL2 (𝓞 F) F →
        (∀ w : InfinitePlace F, AutomorphicForm.WindowedSiegel.IsRowIsometry (archComponent F w (glArch (𝓞 F) F k))) →
          ψ₀ (NumberField.AdelicLevel.diagOne y * k) =
            ((μ y : ℂˣ) : ℂ) * h₁ (Real.log (NumberField.TateGlobal.ideleNorm F y)) * φ₀ k) := by
  intro α hα Φ ξ μ ν hμ hν hμic hνic hμc hνc hμν φ₀ hφ₀ hφ₀K hφ₀f hφ₀c a b ha hbpos h₁ hh₁ hh₁c hh₁b
  have hαnorm : ∀ y : (AdeleRing (𝓞 F) F)ˣ, NumberField.TateGlobal.ideleNorm F y = ((α y : ℝˣ) : ℝ) := fun y => rfl

  obtain ⟨Ψ, hΨ0, hΨsec, hΨK, hΨf, hΨjc, hΨhol, hΨflat⟩ :=
    AutomorphicForm.exists_flat_isInducedSection_family_eq_of_isInducedSection F hα μ ν 0 φ₀ hφ₀ hφ₀K hφ₀f hφ₀c
  obtain ⟨hΨW, hΨbd⟩ :=
    EPWAx.flatInherit F hα μ ν Ψ
      hΨsec hΨK hΨf hΨjc hΨhol hΨflat
  have hΨk : ∀ (s : ℂ) (k : AdelicGL2 (𝓞 F) F), glFin (𝓞 F) F k ∈ finiteIntegralGL2 (𝓞 F) F →
      (∀ w : InfinitePlace F, AutomorphicForm.WindowedSiegel.IsRowIsometry (archComponent F w (glArch (𝓞 F) F k))) →
      Ψ s k = φ₀ k := by
    intro s k hk1 hk2; rw [hΨflat s 0 k hk1 hk2, hΨ0]

  set h : ℝ → ℂ := fun v => 2 * Complex.exp ((v : ℂ) / 2) * h₁ (-v) with hhdef
  have hh : ContDiff ℝ (⊤ : ℕ∞) h := by
    have e1 : ContDiff ℝ (⊤ : ℕ∞) (fun v : ℝ => Complex.exp ((v : ℂ) / 2)) :=
      Complex.contDiff_exp.comp ((Complex.ofRealCLM.contDiff).div_const _)
    have e2 : ContDiff ℝ (⊤ : ℕ∞) (fun v : ℝ => h₁ (-v)) := hh₁.comp contDiff_neg
    exact (contDiff_const.mul e1).mul e2
  have hhc : HasCompactSupport h := by
    have : HasCompactSupport (fun v : ℝ => h₁ (-v)) := by
      have e : (fun v : ℝ => h₁ (-v)) = h₁ ∘ (Homeomorph.neg ℝ) := by funext v; rfl
      rw [e]; exact hh₁c.comp_homeomorph _
    exact this.mul_left
  obtain ⟨hMdiff, hMdec, hMinv⟩ :=
    MellinPaleyWiener.differentiable_and_forall_decay_and_inversion_of_contDiff_of_hasCompactSupport h hh hhc
  set M : ℂ → ℂ := fun s => ∫ u : ℝ, h u * Complex.exp (s * (u : ℂ)) with hMdef
  have hMcont : Continuous M := hMdiff.continuous
  set ψf₀ : ℂ → AdelicGL2 (𝓞 F) F → ℂ := fun s g => M s * Ψ s g with hψf₀def
  set ψ₀ : AdelicGL2 (𝓞 F) F → ℂ := fun g =>
    (((4 * Real.pi)⁻¹ : ℝ) : ℂ) * ∫ t : ℝ, ψf₀ (((0 : ℝ) : ℂ) + (t : ℂ) * Complex.I) g with hψ₀def

  have hval : ∀ (σ' : ℝ) (bb : AdelicGL2 (𝓞 F) F) (hb : bb ∈ adelicBorel (𝓞 F) F) (k : AdelicGL2 (𝓞 F) F),
      glFin (𝓞 F) F k ∈ finiteIntegralGL2 (𝓞 F) F →
      (∀ w : InfinitePlace F, AutomorphicForm.WindowedSiegel.IsRowIsometry (archComponent F w (glArch (𝓞 F) F k))) →
      ∫ t : ℝ, ψf₀ ((σ' : ℂ) + (t : ℂ) * Complex.I) (bb * k) =
        (((4 * Real.pi) : ℝ) : ℂ) *
          (((μ (borelDiagFst (⟨bb, hb⟩ : ↥(adelicBorel (𝓞 F) F))) : ℂˣ) : ℂ) *
           ((ν (borelDiagSnd (⟨bb, hb⟩ : ↥(adelicBorel (𝓞 F) F))) : ℂˣ) : ℂ) *
           h₁ (Real.log (((α (borelDiagFst (⟨bb, hb⟩ : ↥(adelicBorel (𝓞 F) F))) : ℝˣ) : ℝ) /
                          ((α (borelDiagSnd (⟨bb, hb⟩ : ↥(adelicBorel (𝓞 F) F))) : ℝˣ) : ℝ))) *
           φ₀ k) := by
    intro σ' bb hb k hk1 hk2
    set y₁ := borelDiagFst (⟨bb, hb⟩ : ↥(adelicBorel (𝓞 F) F)) with hy₁
    set y₂ := borelDiagSnd (⟨bb, hb⟩ : ↥(adelicBorel (𝓞 F) F)) with hy₂
    set r₁ : ℝ := ((α y₁ : ℝˣ) : ℝ) with hr₁def
    set r₂ : ℝ := ((α y₂ : ℝˣ) : ℝ) with hr₂def
    have hr₁ : 0 < r₁ := hα y₁
    have hr₂ : 0 < r₂ := hα y₂
    set L : ℝ := Real.log r₁ - Real.log r₂ with hLdef
    have hL : Real.log (r₁ / r₂) = L := Real.log_div hr₁.ne' hr₂.ne'
    set c₀ : ℂ := ((μ y₁ : ℂˣ) : ℂ) * ((ν y₂ : ℂˣ) : ℂ) * φ₀ k with hc₀def

    have hpt : ∀ s : ℂ, ψf₀ s (bb * k) =
        (c₀ * Complex.exp ((L : ℂ) / 2)) * (M s * Complex.exp (s * (L : ℂ))) := by
      intro s
      have e : Complex.exp ((s + 1 / 2) * (Real.log r₁ : ℂ)) * Complex.exp (-(s + 1 / 2) * (Real.log r₂ : ℂ)) =
          Complex.exp ((L : ℂ) / 2) * Complex.exp (s * (L : ℂ)) := by
        rw [← Complex.exp_add, ← Complex.exp_add, hLdef]; congr 1; push_cast; ring
      have step : ψf₀ s (bb * k) = M s * ((((μ y₁ : ℂˣ) : ℂ) * Complex.exp ((s + 1 / 2) * (Real.log r₁ : ℂ))) *
          ((((ν y₂ : ℂˣ) : ℂ) * Complex.exp (-(s + 1 / 2) * (Real.log r₂ : ℂ)))) * φ₀ k) := by
        simp only [hψf₀def]
        rw [hΨsec s bb hb k, hΨk s k hk1 hk2, etaFst_apply, etaSnd_apply, Units.val_mul, Units.val_mul,
          cpowChar_apply_val, cpowChar_apply_val, EPWAx.ofReal_cpow_eq_exp _ hr₁, EPWAx.ofReal_cpow_eq_exp _ hr₂]
      rw [step, hc₀def]
      linear_combination (M s * ((μ y₁ : ℂˣ) : ℂ) * ((ν y₂ : ℂˣ) : ℂ) * φ₀ k) * e

    have hI : ∫ t : ℝ, M ((σ' : ℂ) + (t : ℂ) * Complex.I) * Complex.exp (((σ' : ℂ) + (t : ℂ) * Complex.I) * (L : ℂ)) =
        (((2 * Real.pi) : ℝ) : ℂ) * h (-L) := by
      have h' := hMinv σ' (-L)
      have e : (fun t : ℝ => (∫ v : ℝ, h v * Complex.exp (((σ' : ℂ) + (t : ℂ) * Complex.I) * (v : ℂ))) *
          Complex.exp (-(((σ' : ℂ) + (t : ℂ) * Complex.I) * ((-L : ℝ) : ℂ)))) =
          fun t : ℝ => M ((σ' : ℂ) + (t : ℂ) * Complex.I) * Complex.exp (((σ' : ℂ) + (t : ℂ) * Complex.I) * (L : ℂ)) := by
        funext t
        have : Complex.exp (-(((σ' : ℂ) + (t : ℂ) * Complex.I) * ((-L : ℝ) : ℂ))) =
            Complex.exp (((σ' : ℂ) + (t : ℂ) * Complex.I) * (L : ℂ)) := by
          congr 1; push_cast; ring
        rw [this]
      rw [e] at h'
      rw [h']
      have hπ : ((2 : ℂ) * (Real.pi : ℂ)) ≠ 0 :=
        mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.2 Real.pi_ne_zero)
      push_cast
      rw [← mul_assoc, mul_inv_cancel₀ hπ, one_mul]
    have e2 : Complex.exp ((L : ℂ) / 2) * Complex.exp (-(L : ℂ) / 2) = 1 := by
      rw [← Complex.exp_add]; ring_nf; exact Complex.exp_zero
    calc ∫ t : ℝ, ψf₀ ((σ' : ℂ) + (t : ℂ) * Complex.I) (bb * k)
        = ∫ t : ℝ, (c₀ * Complex.exp ((L : ℂ) / 2)) *
            (M ((σ' : ℂ) + (t : ℂ) * Complex.I) * Complex.exp (((σ' : ℂ) + (t : ℂ) * Complex.I) * (L : ℂ))) := by
          congr 1; funext t; exact hpt _
      _ = (c₀ * Complex.exp ((L : ℂ) / 2)) * ((((2 * Real.pi) : ℝ) : ℂ) * h (-L)) := by
          rw [integral_const_mul, hI]
      _ = _ := by
          rw [hL]
          simp only [hhdef, hc₀def]
          push_cast
          simp only [neg_neg]
          linear_combination (4 * (Real.pi : ℂ) * ((μ y₁ : ℂˣ) : ℂ) * ((ν y₂ : ℂˣ) : ℂ) * h₁ L * φ₀ k) * e2

  have hαprin : ∀ u : Fˣ, ((α (Units.map (algebraMap F (AdeleRing (𝓞 F) F) : F →* AdeleRing (𝓞 F) F) u) : ℝˣ) : ℝ) = 1 := by
    intro u
    have h2 := NumberField.AdeleRing.distribHaarChar_algebraMap F u
    show ((NNReal.toRealHom (distribHaarChar (AdeleRing (𝓞 F) F)
      (Units.map (algebraMap F (AdeleRing (𝓞 F) F) : F →* AdeleRing (𝓞 F) F) u))) : ℝ) = 1
    rw [show (Units.map (algebraMap F (AdeleRing (𝓞 F) F) : F →* AdeleRing (𝓞 F) F) u) =
      Units.map (algebraMap F (AdeleRing (𝓞 F) F)).toMonoidHom u from rfl, h2]
    simp

  have hglob : ∀ (s : ℂ) (γ : Matrix.GeneralLinearGroup (Fin 2) F) (hγ : γ ∈ borelSubgroup F) (g : AdelicGL2 (𝓞 F) F),
      Ψ s (globalPoints (𝓞 F) F γ * g) = Ψ s g := by
    intro s γ hγ g
    have hmem := globalPoints_mem_adelicBorel (𝓞 F) F hγ
    rw [hΨsec s _ hmem g, borelDiagFst_globalPoints (𝓞 F) F hγ hmem, borelDiagSnd_globalPoints (𝓞 F) F hγ hmem,
      etaFst_apply, etaSnd_apply, Units.val_mul, Units.val_mul, cpowChar_apply_val, cpowChar_apply_val,
      hμic, hνic, hαprin, hαprin]
    simp

  have hcent : ∀ (s : ℂ) (z : (productionPinsOf F Φ (fun N => levelOne (𝓞 F) F N) (fun v => heckeGen (𝓞 F) F v) (adelicBox F)).Z)
      (g : AdelicGL2 (𝓞 F) F),
      Ψ s (centralScalar (𝓞 F) F (z : (AdeleRing (𝓞 F) F)ˣ) * g) = ((ξ z : ℂˣ) : ℂ) * Ψ s g := by
    intro s z g
    rw [isInducedSection_centralScalar_mul (hΨsec s), ← Units.val_mul, etaFst_mul_etaSnd, hμν z]

  obtain ⟨Bh, hBh⟩ : ∃ Bh : ℝ, ∀ u : ℝ, ‖h₁ u‖ ≤ Bh := hh₁.continuous.bounded_above_of_compact_support hh₁c
  obtain ⟨Bφ, hBφ⟩ : ∃ Bφ : ℝ, ∀ k ∈ (adelicMaximalCompact F : Set (AdelicGL2 (𝓞 F) F)), ‖φ₀ k‖ ≤ Bφ :=
    (isCompact_adelicMaximalCompact F).exists_bound_of_continuousOn hφ₀c.continuousOn

  have hψ₀val : ∀ (bb : AdelicGL2 (𝓞 F) F) (hb : bb ∈ adelicBorel (𝓞 F) F) (k : AdelicGL2 (𝓞 F) F),
      glFin (𝓞 F) F k ∈ finiteIntegralGL2 (𝓞 F) F →
      (∀ w : InfinitePlace F, AutomorphicForm.WindowedSiegel.IsRowIsometry (archComponent F w (glArch (𝓞 F) F k))) →
      ψ₀ (bb * k) =
          ((μ (borelDiagFst (⟨bb, hb⟩ : ↥(adelicBorel (𝓞 F) F))) : ℂˣ) : ℂ) *
           ((ν (borelDiagSnd (⟨bb, hb⟩ : ↥(adelicBorel (𝓞 F) F))) : ℂˣ) : ℂ) *
           h₁ (Real.log (((α (borelDiagFst (⟨bb, hb⟩ : ↥(adelicBorel (𝓞 F) F))) : ℝˣ) : ℝ) /
                          ((α (borelDiagSnd (⟨bb, hb⟩ : ↥(adelicBorel (𝓞 F) F))) : ℝˣ) : ℝ))) *
           φ₀ k := by
    intro bb hb k hk1 hk2
    simp only [hψ₀def]
    rw [hval 0 bb hb k hk1 hk2]
    have hπ : ((4 : ℂ) * (Real.pi : ℂ)) ≠ 0 :=
      mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.2 Real.pi_ne_zero)
    push_cast
    rw [← mul_assoc, inv_mul_cancel₀ hπ, one_mul]

  obtain ⟨-, h1u, hHsec⟩ := AutomorphicForm.isInducedSection_adelicHeight_cpow F
  have hHratio : ∀ (bb : AdelicGL2 (𝓞 F) F) (hb : bb ∈ adelicBorel (𝓞 F) F) (k : AdelicGL2 (𝓞 F) F),
      k ∈ adelicMaximalCompact F →
      NumberField.AdelicHeight.adelicHeight F (bb * k) =
        ((α (borelDiagFst (⟨bb, hb⟩ : ↥(adelicBorel (𝓞 F) F))) : ℝˣ) : ℝ) /
        ((α (borelDiagSnd (⟨bb, hb⟩ : ↥(adelicBorel (𝓞 F) F))) : ℝˣ) : ℝ) := by
    intro bb hb k hk
    have hHk : NumberField.AdelicHeight.adelicHeight F k = 1 := by
      have h := NumberField.AdelicHeight.adelicHeight_mul_of_mem_adelicMaximalCompact F 1 k hk
      rw [one_mul] at h
      rw [h]
      unfold NumberField.AdelicHeight.adelicHeight
      rw [map_one, map_one, AutomorphicForm.WindowedSiegel.archHeight_one,
        NumberField.AdelicHeight.finHeight_eq_one_of_mem (Subgroup.one_mem _), mul_one]
    have hsec := hHsec hα ((1 / 2 : ℝ) : ℂ) bb hb k
    have hn := congrArg norm hsec
    dsimp only at hn
    rw [norm_mul, norm_mul, hHk, Complex.ofReal_one, Complex.one_cpow, norm_one, mul_one,
      Complex.norm_cpow_eq_rpow_re_of_pos (NumberField.AdelicHeight.adelicHeight_pos _),
      norm_etaFst_apply_of_unitary h1u, etaSnd_apply, Units.val_mul, norm_mul, h1u, one_mul,
      norm_cpowChar_apply] at hn
    have e1 : (((1 / 2 : ℝ) : ℂ) + 1 / 2).re = 1 := by simp; norm_num
    have e2 : ((1 / 2 : ℝ) : ℂ).re + 1 / 2 = 1 := by simp; norm_num
    have e3 : (-(((1 / 2 : ℝ) : ℂ) + 1 / 2)).re = -1 := by simp; norm_num
    rw [e1, e2, e3, Real.rpow_one, Real.rpow_one, Real.rpow_neg_one] at hn
    rw [hn, div_eq_mul_inv]

  have hband : ∀ g : AdelicGL2 (𝓞 F) F, ψ₀ g ≠ 0 →
      NumberField.AdelicHeight.adelicHeight F g ∈ Set.Icc a b := by
    intro g hg0
    obtain ⟨bb, k, hbm, hk1, hk2, rfl⟩ := AutomorphicForm.exists_mem_adelicBorel_mul_eq F g
    have hk : k ∈ adelicMaximalCompact F := (mem_adelicMaximalCompact_iff).2 ⟨hk1, hk2⟩
    rw [hψ₀val bb hbm k hk1 hk2] at hg0
    set r : ℝ := ((α (borelDiagFst (⟨bb, hbm⟩ : ↥(adelicBorel (𝓞 F) F))) : ℝˣ) : ℝ) /
        ((α (borelDiagSnd (⟨bb, hbm⟩ : ↥(adelicBorel (𝓞 F) F))) : ℝˣ) : ℝ) with hrdef
    have hr : 0 < r := div_pos (hα _) (hα _)
    have hh0 : h₁ (Real.log r) ≠ 0 := by
      intro h0; apply hg0; rw [h0]; simp
    have hu := hh₁b _ hh0
    rw [hHratio bb hbm k hk]
    exact ⟨(Real.log_le_log_iff ha hr).1 hu.1, (Real.log_le_log_iff hr hbpos).1 hu.2⟩

  refine ⟨ψf₀, ψ₀, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  ·
    intro s bb hb g
    simp only [hψf₀def]
    rw [hΨsec s bb hb g]; ring
  ·
    show Continuous fun p : ℂ × AdelicGL2 (𝓞 F) F => M p.1 * Ψ p.1 p.2
    exact (hMcont.comp continuous_fst).mul hΨjc
  ·
    intro g
    show Differentiable ℂ fun s => M s * Ψ s g
    exact hMdiff.mul (hΨhol g)
  ·
    intro s
    exact EPWAx.isArchKFinite_const_mul F (M s) (hΨK s)
  ·
    intro s
    exact EPWAx.isKfSmooth_const_mul F (M s) (hΨf s)
  ·
    intro w
    obtain ⟨W, hWfd, hW⟩ := hΨW w
    refine ⟨W, hWfd, fun s g => ?_⟩
    have hmem := W.smul_mem (M s) (hW s g)
    have e : (fun k : ↥(archRowIsometrySubgroup F w) => ψf₀ s (g * (k : AdelicGL2 (𝓞 F) F))) =
        (M s) • (fun k : ↥(archRowIsometrySubgroup F w) => Ψ s (g * (k : AdelicGL2 (𝓞 F) F))) := by
      funext k; simp [hψf₀def, Pi.smul_apply, smul_eq_mul]
    rw [e]; exact hmem
  ·
    intro m₀ σ₀ C hC
    obtain ⟨CM, hCM0, hCM⟩ := hMdec (m₀ + 2) σ₀
    obtain ⟨MΨ, hMΨ⟩ := hΨbd σ₀ C hC
    refine ⟨fun t => CM * max MΨ 0 * (1 + ‖t‖) ^ (-(2 : ℝ)), ?_, ⟨CM * max MΨ 0, fun t => ?_⟩, ?_⟩
    · exact (integrable_one_add_norm (by simp)).const_mul _
    · have h1 : (1 + ‖t‖) ^ (-(2 : ℝ)) ≤ 1 :=
        Real.rpow_le_one_of_one_le_of_nonpos (by simp) (by norm_num)
      have h0 : 0 ≤ CM * max MΨ 0 := mul_nonneg hCM0 (le_max_right _ _)
      calc CM * max MΨ 0 * (1 + ‖t‖) ^ (-(2 : ℝ)) ≤ CM * max MΨ 0 * 1 :=
            mul_le_mul_of_nonneg_left h1 h0
        _ = CM * max MΨ 0 := mul_one _
    · intro σ' hσ' t g hg
      have h1 := hCM σ' hσ' t
      have h2 : ‖Ψ ((σ' : ℂ) + (t : ℂ) * Complex.I) g‖ ≤ max MΨ 0 := (hMΨ σ' hσ' t g hg).trans (le_max_left _ _)
      simp only [hψf₀def, norm_mul]
      have hpos : 0 < 1 + |t| := by positivity
      have hpow : (1 + |t|) ^ m₀ = (1 + |t|) ^ (m₀ + 2) * (1 + ‖t‖) ^ (-(2 : ℝ)) := by
        rw [Real.norm_eq_abs, Real.rpow_neg hpos.le, Real.rpow_two, pow_add]
        field_simp
      rw [hpow]
      calc (1 + |t|) ^ (m₀ + 2) * (1 + ‖t‖) ^ (-(2 : ℝ)) *
            (‖M ((σ' : ℂ) + (t : ℂ) * Complex.I)‖ * ‖Ψ ((σ' : ℂ) + (t : ℂ) * Complex.I) g‖)
          = ((1 + |t|) ^ (m₀ + 2) * ‖M ((σ' : ℂ) + (t : ℂ) * Complex.I)‖) *
              ‖Ψ ((σ' : ℂ) + (t : ℂ) * Complex.I) g‖ * (1 + ‖t‖) ^ (-(2 : ℝ)) := by ring
        _ ≤ CM * max MΨ 0 * (1 + ‖t‖) ^ (-(2 : ℝ)) := by
            exact mul_le_mul_of_nonneg_right (mul_le_mul h1 h2 (norm_nonneg _) hCM0)
              (Real.rpow_nonneg (by positivity) _)
  ·
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    ·
      have hs : Continuous fun p : AdelicGL2 (𝓞 F) F × ℝ => (((0 : ℝ) : ℂ) + ((p.2 : ℝ) : ℂ) * Complex.I) := by
        fun_prop
      have hcont2 : Continuous (fun p : AdelicGL2 (𝓞 F) F × ℝ =>
          ψf₀ (((0 : ℝ) : ℂ) + ((p.2 : ℝ) : ℂ) * Complex.I) p.1) := by
        show Continuous fun p : AdelicGL2 (𝓞 F) F × ℝ =>
          M (((0 : ℝ) : ℂ) + ((p.2 : ℝ) : ℂ) * Complex.I) * Ψ (((0 : ℝ) : ℂ) + ((p.2 : ℝ) : ℂ) * Complex.I) p.1
        refine (hMcont.comp hs).mul ?_
        exact hΨjc.comp (hs.prodMk continuous_fst)
      have hsm : StronglyMeasurable (Function.uncurry fun (g : AdelicGL2 (𝓞 F) F) (t : ℝ) =>
          ψf₀ (((0 : ℝ) : ℂ) + ((t : ℝ) : ℂ) * Complex.I) g) := hcont2.stronglyMeasurable
      have hm : StronglyMeasurable fun g : AdelicGL2 (𝓞 F) F =>
          ∫ t : ℝ, ψf₀ (((0 : ℝ) : ℂ) + ((t : ℝ) : ℂ) * Complex.I) g := hsm.integral_prod_right
      show Measurable fun g : AdelicGL2 (𝓞 F) F =>
        (((4 * Real.pi)⁻¹ : ℝ) : ℂ) * ∫ t : ℝ, ψf₀ (((0 : ℝ) : ℂ) + (t : ℂ) * Complex.I) g
      exact hm.measurable.const_mul _
    ·
      intro x g
      have hu : ∀ s, Ψ s (unipotentGL2 x * g) = Ψ s g := fun s => isInducedSection_unipotent_mul (hΨsec s) x g
      simp only [hψ₀def, hψf₀def, hu]
    ·
      intro γ hγ g
      have hu : ∀ s, Ψ s (globalPoints (𝓞 F) F γ * g) = Ψ s g := fun s => hglob s γ hγ g
      simp only [hψ₀def, hψf₀def, hu]
    ·
      intro z g
      have hu : ∀ s, Ψ s (centralScalar (𝓞 F) F (z : (AdeleRing (𝓞 F) F)ˣ) * g) = ((ξ z : ℂˣ) : ℂ) * Ψ s g :=
        fun s => hcent s z g
      simp only [hψ₀def, hψf₀def, hu]
      have e : (fun t : ℝ => M (((0 : ℝ) : ℂ) + (t : ℂ) * Complex.I) *
          (((ξ z : ℂˣ) : ℂ) * Ψ (((0 : ℝ) : ℂ) + (t : ℂ) * Complex.I) g)) =
          fun t : ℝ => ((ξ z : ℂˣ) : ℂ) * (M (((0 : ℝ) : ℂ) + (t : ℂ) * Complex.I) * Ψ (((0 : ℝ) : ℂ) + (t : ℂ) * Complex.I) g) := by
        funext t; ring
      rw [e, integral_const_mul]; ring
    ·
      intro d₁ d₂ hd₁
      refine ⟨Bh * Bφ, fun g _ => ?_⟩
      obtain ⟨bb, k, hbm, hk1, hk2, rfl⟩ := AutomorphicForm.exists_mem_adelicBorel_mul_eq F g
      have hk : k ∈ adelicMaximalCompact F := (mem_adelicMaximalCompact_iff).2 ⟨hk1, hk2⟩
      rw [hψ₀val bb hbm k hk1 hk2, norm_mul, norm_mul, norm_mul, hμ, hν, one_mul, one_mul]
      exact mul_le_mul (hBh _) (hBφ k hk) (norm_nonneg _) ((norm_nonneg _).trans (hBh 0))
    ·
      exact ⟨a, b, ha, hband⟩
  ·
    intro σ' g
    obtain ⟨bb, k, hb, hk1, hk2, rfl⟩ := AutomorphicForm.exists_mem_adelicBorel_mul_eq F g
    simp only [hψ₀def]
    rw [hval 0 bb hb k hk1 hk2, hval σ' bb hb k hk1 hk2]
  ·
    exact hband
  ·
    intro y k hk1 hk2
    have hb := EPWAx.diagOne_mem_adelicBorel F y
    rw [hψ₀val _ hb k hk1 hk2, EPWAx.borelDiagFst_diagOne, EPWAx.borelDiagSnd_diagOne, map_one, map_one,
      Units.val_one, Units.val_one, mul_one, div_one, ← hαnorm]

end
end S_AutomorphicForm_exists_paleyWiener_oneIndex_apply_diagOne_mul_eq_of_isInducedSection_of_contDiff_of_pos
end P2MW
export P2MW.S_AutomorphicForm_exists_paleyWiener_oneIndex_apply_diagOne_mul_eq_of_isInducedSection_of_contDiff_of_pos (solution)

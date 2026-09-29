-- Prove2me | solution 1 for AutomorphicForm.exists_isInducedSection_one_etaSnd_eq_on_maximalCompact_of_equivariant
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/617ca3ba-f6c2-59ec-aebf-df8e5bb949d4

import Definitions.Def_AutomorphicForm_InducedSection
import Definitions.Def_AutomorphicForm_EtaFamily
import Definitions.Def_AutomorphicForm_SmoothAutomorphicFnAt
import Definitions.Def_AutomorphicForm_ArchKFinite
import Definitions.Def_AutomorphicForm_RowIsometryInvariance
import Definitions.Def_NumberField_AdelicLevel
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_UnramifiedWhittaker_HeckeRecursion
import Mathlib.MeasureTheory.Measure.Haar.DistribChar

import Definitions.Def_AdelicDock_LocalEmbedding
import Theorems.Thm_AutomorphicForm_exists_continuous_isArchKFinite_eq_of_borel_arch_of_equivariant
import Theorems.Thm_AutomorphicForm_exists_isKfSmooth_eq_prod_localChar_of_borel_fin_of_level
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_isInducedSection_one_etaSnd_eq_on_maximalCompact_of_equivariant
p2m_attr_erase "instance" "HeckePair.instSMulCommClassSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instAlgebraSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instOneSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instIsScalarTowerSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instRingSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instMulSubtypeForallMemSubmoduleHeckeAlgebra FixedPoints.instMulActionElemFixedPointsOfSMulCommClass_definitions FixedPoints.module FixedPoints.instSMulElemFixedPointsOfSMulCommClass_definitions FixedPoints.instAddCommMonoidElemFixedPoints_definitions AutomorphicForm.compactSpace_maximalCompactAway AutomorphicForm.compactSpace_adelicMaximalCompact AutomorphicForm.isProbabilityMeasure_maximalCompactHaar AutomorphicForm.isHaarMeasure_maximalCompactHaar AutomorphicForm.compactSpace_maximalCompactAt AutomorphicForm.isProbabilityMeasure_maximalCompactAwayHaar AutomorphicForm.isHaarMeasure_maximalCompactAwayHaar AutomorphicForm.isProbabilityMeasure_maximalCompactAtHaar AutomorphicForm.isHaarMeasure_maximalCompactAtHaar instCountableOfNumberField_definitions"
p2m_attr_erase "simp" "LocalGL2.coe_localRepSome LocalGL2.coe_diagPi LocalGL2.coe_localRepInf LocalGL2.coe_localRepSome_inv LocalGL2.coe_unipotentInt LocalGL2.coe_weylInt LocalGL2.coe_diagPi_inv LocalGL2.transposeGL_val LocalGL2.transposeGL_one HeckePair.convTerm_mk HeckePair.coe_apply_add HeckePair.coe_apply_smul FixedPoints.coe_zero FixedPoints.coe_smul FixedPoints.coe_add LocalGL2.swapUnit_val AutomorphicForm.SiegelCoordinates.upperUnit_apply_zero_zero AutomorphicForm.SiegelCoordinates.upperUnit_apply_one_zero AutomorphicForm.SiegelCoordinates.upperUnit_apply_one_one AutomorphicForm.SiegelCoordinates.upperUnit_apply_zero_one NumberField.AdeleRing.val_finiteUnitsComponent IsDedekindDomain.FiniteAdeleRing.val_unitsComponent NumberField.AdeleRing.val_finitePartUnits NumberField.AdeleRing.val_infiniteUnitsComponent"

set_option autoImplicit false

p2m_open "MeasureTheory NumberField NumberField.AdelicLevel NumberField.TateGlobal AutomorphicForm P2MW.S_AutomorphicForm_exists_isInducedSection_one_etaSnd_eq_on_maximalCompact_of_equivariant.AutomorphicForm"
open AutomorphicForm.WindowedSiegel IsDedekindDomain
open scoped NNReal

noncomputable section

namespace AutomorphicForm
p2m_export "AutomorphicForm" "IsInducedSection mem_borelSubgroup_iff borelDiagFst borelDiagSnd adelicBorel AdelicGL2 IsIdeleClassChar IsUnitaryChar etaFst etaSnd finiteAdelicGL2Subgroup IsKfSmooth isKfSmooth_iff RightTranslatesSpanFinite archRowIsometrySubgroup IsArchKFinite adelicArchGLIncl glArch_adelicArchGLIncl glFin_adelicArchGLIncl exists_continuous_isArchKFinite_eq_of_borel_arch_of_equivariant exists_isKfSmooth_eq_prod_localChar_of_borel_fin_of_level"
p2m_open "AutomorphicForm"

namespace SectConAssembly

variable (K : Type) [Field K] [NumberField K]

theorem gl_eq_of_parts {g g' : AdelicGL2 (𝓞 K) K} (h1 : glArch (𝓞 K) K g = glArch (𝓞 K) K g')
    (h2 : glFin (𝓞 K) K g = glFin (𝓞 K) K g') : g = g' := by
  apply Units.ext
  ext i j
  refine Prod.ext ?_ ?_
  · have := congrArg (fun u : GL (Fin 2) (InfiniteAdeleRing K) => (u : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K)) i j) h1
    simpa [glArch_apply] using this
  · have := congrArg (fun u : GL (Fin 2) (FiniteAdeleRing (𝓞 K) K) => (u : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 K) K)) i j) h2
    simpa [glFin_apply] using this

theorem adele_fst_mul (x y : AdeleRing (𝓞 K) K) : (x * y).1 = x.1 * y.1 := rfl
theorem adele_snd_mul (x y : AdeleRing (𝓞 K) K) : (x * y).2 = x.2 * y.2 := rfl

def archP (g : AdelicGL2 (𝓞 K) K) : AdelicGL2 (𝓞 K) K := adelicArchGLIncl K (glArch (𝓞 K) K g)

def finP (g : AdelicGL2 (𝓞 K) K) : AdelicGL2 (𝓞 K) K := AdelicDock.finEmbed (𝓞 K) K (glFin (𝓞 K) K g)

theorem glArch_archP (g : AdelicGL2 (𝓞 K) K) : glArch (𝓞 K) K (archP K g) = glArch (𝓞 K) K g :=
  glArch_adelicArchGLIncl K _
theorem glFin_archP (g : AdelicGL2 (𝓞 K) K) : glFin (𝓞 K) K (archP K g) = 1 := glFin_adelicArchGLIncl K _
theorem glArch_finP (g : AdelicGL2 (𝓞 K) K) : glArch (𝓞 K) K (finP K g) = 1 := AdelicDock.glArch_finEmbed (𝓞 K) K _
theorem glFin_finP (g : AdelicGL2 (𝓞 K) K) : glFin (𝓞 K) K (finP K g) = glFin (𝓞 K) K g := AdelicDock.glFin_finEmbed (𝓞 K) K _

theorem archP_mul_finP (g : AdelicGL2 (𝓞 K) K) : archP K g * finP K g = g :=
  gl_eq_of_parts K (by rw [map_mul, glArch_archP, glArch_finP, mul_one]) (by rw [map_mul, glFin_archP, glFin_finP, one_mul])

theorem finP_mul_archP (g : AdelicGL2 (𝓞 K) K) : finP K g * archP K g = g :=
  gl_eq_of_parts K (by rw [map_mul, glArch_archP, glArch_finP, one_mul]) (by rw [map_mul, glFin_archP, glFin_finP, mul_one])

theorem archP_apply_fst (g : AdelicGL2 (𝓞 K) K) (i j : Fin 2) :
    (((archP K g : AdelicGL2 (𝓞 K) K) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) i j).1 =
      (((g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) i j)).1 := by
  have := glArch_archP K g
  exact congrArg (fun u : GL (Fin 2) (InfiniteAdeleRing K) => (u : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K)) i j) this
theorem archP_apply_snd (g : AdelicGL2 (𝓞 K) K) (i j : Fin 2) :
    (((archP K g : AdelicGL2 (𝓞 K) K) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) i j).2 =
      ((1 : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 K) K)) i j) := by
  have := glFin_archP K g
  exact congrArg (fun u : GL (Fin 2) (FiniteAdeleRing (𝓞 K) K) => (u : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 K) K)) i j) this
theorem finP_apply_fst (g : AdelicGL2 (𝓞 K) K) (i j : Fin 2) :
    (((finP K g : AdelicGL2 (𝓞 K) K) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) i j).1 =
      ((1 : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K)) i j) := by
  have := glArch_finP K g
  exact congrArg (fun u : GL (Fin 2) (InfiniteAdeleRing K) => (u : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K)) i j) this
theorem finP_apply_snd (g : AdelicGL2 (𝓞 K) K) (i j : Fin 2) :
    (((finP K g : AdelicGL2 (𝓞 K) K) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) i j).2 =
      (((g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) i j)).2 := by
  have := glFin_finP K g
  exact congrArg (fun u : GL (Fin 2) (FiniteAdeleRing (𝓞 K) K) => (u : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 K) K)) i j) this

theorem archP_mem_borel {b : AdelicGL2 (𝓞 K) K} (hb : b ∈ adelicBorel (𝓞 K) K) : archP K b ∈ adelicBorel (𝓞 K) K := by
  rw [mem_borelSubgroup_iff] at hb ⊢
  refine Prod.ext ?_ ?_
  · rw [archP_apply_fst, hb]
  · rw [archP_apply_snd, Matrix.one_apply_ne (by decide)]; rfl

theorem finP_mem_borel {b : AdelicGL2 (𝓞 K) K} (hb : b ∈ adelicBorel (𝓞 K) K) : finP K b ∈ adelicBorel (𝓞 K) K := by
  rw [mem_borelSubgroup_iff] at hb ⊢
  refine Prod.ext ?_ ?_
  · rw [finP_apply_fst, Matrix.one_apply_ne (by decide)]; rfl
  · rw [finP_apply_snd, hb]

theorem borelDiagFst_split {b : AdelicGL2 (𝓞 K) K} (hb : b ∈ adelicBorel (𝓞 K) K) :
    borelDiagFst (⟨b, hb⟩ : ↥(adelicBorel (𝓞 K) K)) =
      borelDiagFst (⟨archP K b, archP_mem_borel K hb⟩ : ↥(adelicBorel (𝓞 K) K)) *
        borelDiagFst (⟨finP K b, finP_mem_borel K hb⟩ : ↥(adelicBorel (𝓞 K) K)) := by
  apply Units.ext
  rw [Units.val_mul]
  change ((b : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) 0 0) =
    ((archP K b : AdelicGL2 (𝓞 K) K) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) 0 0 *
      ((finP K b : AdelicGL2 (𝓞 K) K) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) 0 0
  refine Prod.ext ?_ ?_
  · rw [adele_fst_mul, archP_apply_fst, finP_apply_fst, Matrix.one_apply_eq, mul_one]
  · rw [adele_snd_mul, archP_apply_snd, finP_apply_snd, Matrix.one_apply_eq, one_mul]

theorem borelDiagSnd_split {b : AdelicGL2 (𝓞 K) K} (hb : b ∈ adelicBorel (𝓞 K) K) :
    borelDiagSnd (⟨b, hb⟩ : ↥(adelicBorel (𝓞 K) K)) =
      borelDiagSnd (⟨archP K b, archP_mem_borel K hb⟩ : ↥(adelicBorel (𝓞 K) K)) *
        borelDiagSnd (⟨finP K b, finP_mem_borel K hb⟩ : ↥(adelicBorel (𝓞 K) K)) := by
  apply Units.ext
  rw [Units.val_mul]
  change ((b : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) 1 1) =
    ((archP K b : AdelicGL2 (𝓞 K) K) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) 1 1 *
      ((finP K b : AdelicGL2 (𝓞 K) K) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) 1 1
  refine Prod.ext ?_ ?_
  · rw [adele_fst_mul, archP_apply_fst, finP_apply_fst, Matrix.one_apply_eq, mul_one]
  · rw [adele_snd_mul, archP_apply_snd, finP_apply_snd, Matrix.one_apply_eq, one_mul]

theorem glArch_placeEmbed (v : HeightOneSpectrum (𝓞 K)) (k : GL (Fin 2) (v.adicCompletion K)) :
    glArch (𝓞 K) K (UnramifiedWhittaker.placeEmbed K v k) = 1 :=
  AdelicDock.glArch_finEmbed (𝓞 K) K _

theorem one_entry_snd (i j : Fin 2) (v : HeightOneSpectrum (𝓞 K)) :
    ((((1 : AdelicGL2 (𝓞 K) K) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) i j).2 v) =
      ((1 : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) i j) := by
  rw [Matrix.GeneralLinearGroup.coe_one]
  by_cases h : i = j
  · subst h; rw [Matrix.one_apply_eq, Matrix.one_apply_eq]; rfl
  · rw [Matrix.one_apply_ne h, Matrix.one_apply_ne h]; rfl

theorem glFin_eq_one_of_mem_archRowIsometrySubgroup (w : InfinitePlace K) {k : AdelicGL2 (𝓞 K) K}
    (hk : k ∈ archRowIsometrySubgroup K w) : glFin (𝓞 K) K k = 1 := by
  obtain ⟨r, -, rfl⟩ := hk
  exact glFin_adelicArchGLIncl K _

theorem rightTranslatesSpanFinite_mul {G : Type*} [Group G] (H : Subgroup G) (ψ φ : G → ℂ)
    (hψ : ∀ k ∈ H, ∀ x, ψ (x * k) = ψ x) (hφ : RightTranslatesSpanFinite H φ) :
    RightTranslatesSpanFinite H (fun x => ψ x * φ x) := by
  classical
  obtain ⟨s, hs⟩ := hφ
  let L : (G → ℂ) →ₗ[ℂ] (G → ℂ) :=
    { toFun := fun f x => ψ x * f x
      map_add' := fun f g => by funext x; simp [mul_add]
      map_smul' := fun c f => by funext x; simp; ring }
  refine ⟨s.image L, fun k hk => ?_⟩
  have h1 : (fun x => ψ (x * k) * φ (x * k)) = L (fun x => φ (x * k)) := by
    funext x; simp [L, hψ k hk x]
  rw [h1, Finset.coe_image, ← Submodule.map_span]
  exact Submodule.mem_map_of_mem (hs k hk)

end SectConAssembly

end AutomorphicForm

end

open _root_.AutomorphicForm _root_.P2MW.S_AutomorphicForm_exists_isInducedSection_one_etaSnd_eq_on_maximalCompact_of_equivariant.AutomorphicForm in
theorem solution
    (K : Type) [Field K] [NumberField K] :
    let α : (AdeleRing (𝓞 K) K)ˣ →* ℝˣ :=
      ((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp
        (distribHaarChar (AdeleRing (𝓞 K) K))).toHomUnits
    ∀ (hα : ∀ x, 0 < ((α x : ℝˣ) : ℝ)) (s : ℂ)
      (ν : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ)
      (_hνu : IsUnitaryChar (𝓞 K) K ν) (_hνF : IsIdeleClassChar (𝓞 K) K ν)
      (_hνc : Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((ν z : ℂˣ) : ℂ))
      (S : Finset (HeightOneSpectrum (𝓞 K))) (n : HeightOneSpectrum (𝓞 K) → ℕ)
      (_hn : ∀ v ∈ S, 0 < n v)
      (_hνS : ∀ v ∈ S, ∀ t : (v.adicCompletion K)ˣ,
        Valued.v ((t : v.adicCompletion K) - 1) ≤
            ((Multiplicative.ofAdd (-(n v : ℤ)) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) →
          localChar ν v t = 1)
      (_hνout : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S → IsUnramifiedCharAt ν v)
      (finf : AdelicGL2 (𝓞 K) K → ℂ) (_hfc : Continuous finf) (_hfK : IsArchKFinite K finf)
      (_hfeq : ∀ (m k : AdelicGL2 (𝓞 K) K) (hm : m ∈ adelicBorel (𝓞 K) K),
        glFin (𝓞 K) K m = 1 → glFin (𝓞 K) K k = 1 →
        (∀ w : InfinitePlace K, IsRowIsometry (archComponent K w (glArch (𝓞 K) K m))) →
        (∀ w : InfinitePlace K, IsRowIsometry (archComponent K w (glArch (𝓞 K) K k))) →
          finf (m * k) = ((ν (borelDiagSnd (⟨m, hm⟩ : ↥(adelicBorel (𝓞 K) K))) : ℂˣ) : ℂ) * finf k),
    ∃ φ₀ : AdelicGL2 (𝓞 K) K → ℂ,
      IsInducedSection (𝓞 K) K (etaFst 1 α hα s) (etaSnd ν α hα s) φ₀ ∧
      Continuous φ₀ ∧ IsArchKFinite K φ₀ ∧ IsKfSmooth K φ₀ ∧

      (∀ (g k : AdelicGL2 (𝓞 K) K), k ∈ finiteAdelicGL2Subgroup K →
        glFin (𝓞 K) K k ∈ finiteIntegralGL2 (𝓞 K) K →
        (∀ v ∈ S, ∀ i j : Fin 2,
          Valued.v ((((k : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) i j -
              (1 : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) i j)).2 v) ≤
            ((Multiplicative.ofAdd (-(n v : ℤ)) : Multiplicative ℤ) : WithZero (Multiplicative ℤ))) →
        φ₀ (g * k) = φ₀ g) ∧

      (∀ v : HeightOneSpectrum (𝓞 K), v ∉ S →
        ∀ (kv : GL (Fin 2) (v.adicCompletionIntegers K)) (g : AdelicGL2 (𝓞 K) K),
          φ₀ (g * UnramifiedWhittaker.placeEmbed K v
            (Matrix.GeneralLinearGroup.map
              (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K)) kv)) = φ₀ g) ∧

      (∀ g : AdelicGL2 (𝓞 K) K,
        (∃ v ∈ S, ¬ Valued.v (((g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) 1 0).2 v) ≤
            Valued.v (((g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) 1 1).2 v) *
              ((Multiplicative.ofAdd (-(n v : ℤ)) : Multiplicative ℤ) : WithZero (Multiplicative ℤ))) →
        φ₀ g = 0) ∧

      (∀ k : AdelicGL2 (𝓞 K) K, glFin (𝓞 K) K k = 1 →
        (∀ w : InfinitePlace K, IsRowIsometry (archComponent K w (glArch (𝓞 K) K k))) →
          φ₀ k = finf k) ∧

      (∀ (k kinf : AdelicGL2 (𝓞 K) K) (d : (v : HeightOneSpectrum (𝓞 K)) → (v.adicCompletion K)ˣ),
        glFin (𝓞 K) K k ∈ finiteIntegralGL2 (𝓞 K) K →
        (∀ w : InfinitePlace K, IsRowIsometry (archComponent K w (glArch (𝓞 K) K k))) →
        glFin (𝓞 K) K kinf = 1 → glArch (𝓞 K) K kinf = glArch (𝓞 K) K k →
        (∀ v ∈ S, (((k : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) 1 1).2 v) = (d v : v.adicCompletion K)) →
        (∀ v ∈ S, Valued.v (((k : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) 1 0).2 v) ≤
            Valued.v (((k : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) 1 1).2 v) *
              ((Multiplicative.ofAdd (-(n v : ℤ)) : Multiplicative ℤ) : WithZero (Multiplicative ℤ))) →
          φ₀ k = (∏ v ∈ S, ((localChar ν v (d v) : ℂˣ) : ℂ)) * finf kinf) := by
  intro α hα s ν hνu hνF hνc S n hn hνS hνout finf hfc hfK hfeq
  obtain ⟨Φ, hΦdep, hΦB, hΦc, hΦK, hΦeq⟩ :=
    AutomorphicForm.exists_continuous_isArchKFinite_eq_of_borel_arch_of_equivariant K hα s ν hνc finf hfc hfK hfeq
  obtain ⟨Ψ, hΨdep, hΨB, hΨc, hΨsm, hΨcong, hΨsph, hΨsupp, hΨval⟩ :=
    AutomorphicForm.exists_isKfSmooth_eq_prod_localChar_of_borel_fin_of_level K hα s ν hνc S n hn hνS hνout

  have hΦfin : ∀ (g k : AdelicGL2 (𝓞 K) K), glArch (𝓞 K) K k = 1 → Φ (g * k) = Φ g := fun g k hk =>
    hΦdep _ _ (by rw [map_mul, hk, mul_one])
  have hΨarch : ∀ (g k : AdelicGL2 (𝓞 K) K), glFin (𝓞 K) K k = 1 → Ψ (g * k) = Ψ g := fun g k hk =>
    hΨdep _ _ (by rw [map_mul, hk, mul_one])
  have hΨone : Ψ 1 = 1 := by
    have h := hΨval 1 (fun _ => 1) (by rw [map_one]; exact Subgroup.one_mem _)
      (fun v _ => by rw [SectConAssembly.one_entry_snd, Matrix.one_apply_eq, Units.val_one])
      (fun v _ => by
        rw [SectConAssembly.one_entry_snd, SectConAssembly.one_entry_snd, Matrix.one_apply_ne (by decide), Valuation.map_zero]
        exact zero_le')
    rw [h]
    exact Finset.prod_eq_one fun v _ => by rw [map_one, Units.val_one]
  refine ⟨fun g => Ψ g * Φ g, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  ·
    intro b hb g
    have hsplit : b * g = SectConAssembly.finP K b * (SectConAssembly.archP K b * g) := by
      rw [← mul_assoc, SectConAssembly.finP_mul_archP]
    have hsplit' : b * g = SectConAssembly.archP K b * (SectConAssembly.finP K b * g) := by
      rw [← mul_assoc, SectConAssembly.archP_mul_finP]
    have h3 : Ψ (SectConAssembly.archP K b * g) = Ψ g :=
      hΨdep _ _ (by rw [map_mul, SectConAssembly.glFin_archP, one_mul])
    have h4 : Φ (SectConAssembly.finP K b * g) = Φ g :=
      hΦdep _ _ (by rw [map_mul, SectConAssembly.glArch_finP, one_mul])
    have h1 : Ψ (b * g) = Ψ (SectConAssembly.finP K b * (SectConAssembly.archP K b * g)) := by rw [hsplit]
    have h2 : Φ (b * g) = Φ (SectConAssembly.archP K b * (SectConAssembly.finP K b * g)) := by rw [hsplit']
    simp only
    rw [h1, hΨB _ (SectConAssembly.finP_mem_borel K hb) _ (SectConAssembly.glArch_finP K b), h3,
      h2, hΦB _ (SectConAssembly.archP_mem_borel K hb) _ (SectConAssembly.glFin_archP K b), h4,
      SectConAssembly.borelDiagFst_split K hb, SectConAssembly.borelDiagSnd_split K hb, map_mul, map_mul,
      Units.val_mul, Units.val_mul]
    ring
  · exact hΨc.mul hΦc
  · intro w
    exact SectConAssembly.rightTranslatesSpanFinite_mul _ Ψ Φ
      (fun k hk x => hΨarch x k (SectConAssembly.glFin_eq_one_of_mem_archRowIsometrySubgroup K w hk)) (hΦK w)
  ·
    rw [isKfSmooth_iff, FLT.SmoothVectors.isSmoothVector_iff_isOpen_stabilizer] at hΨsm ⊢
    refine Subgroup.isOpen_mono ?_ hΨsm
    intro k hk
    rw [MulAction.mem_stabilizer_iff] at hk ⊢
    refine FLT.SmoothVectors.RightTranslationFn.ext fun x => ?_
    have hk' := congrArg (fun F => FLT.SmoothVectors.RightTranslationFn.toFun F x) hk
    simp only [Subgroup.smul_def, FLT.SmoothVectors.RightTranslationFn.toFun_smul, FLT.SmoothVectors.RightTranslationFn.toFun_mk] at hk' ⊢
    rw [hk', hΦfin x k k.2]
  · intro g k hkf hki hkc
    simp only
    rw [hΨcong g k hkf hki hkc, hΦfin g k hkf]
  · intro v hv kv g
    simp only
    rw [hΨsph v hv kv g, hΦfin g _ (SectConAssembly.glArch_placeEmbed K v _)]
  · intro g hg
    simp only
    rw [hΨsupp g hg, zero_mul]
  · intro k hkf hka
    simp only
    rw [hΦeq k hkf hka, hΨdep k 1 (by rw [hkf, map_one]), hΨone, one_mul]
  · intro k kinf d hki hka hkinf harch hd hsupp
    simp only
    rw [hΨval k d hki hd hsupp, hΦdep k kinf harch.symm, hΦeq kinf hkinf (fun w => by rw [harch]; exact hka w)]

end S_AutomorphicForm_exists_isInducedSection_one_etaSnd_eq_on_maximalCompact_of_equivariant
end P2MW
export P2MW.S_AutomorphicForm_exists_isInducedSection_one_etaSnd_eq_on_maximalCompact_of_equivariant (solution)

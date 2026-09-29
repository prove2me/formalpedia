-- Prove2me | solution 1 for AutomorphicForm.exists_haar_localGL2_eq_smul_map_unipotentGL2_mul_diagUnits2_mul_lowerUnipotentGL2
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/6d2b24dc-b3fa-54ad-9a35-7b3a285835a3

import Mathlib
import Definitions.Def_AutomorphicForm_ArchDerivCasimir
import Definitions.Def_AutomorphicForm_LocalOrbitalBase
import Definitions.Def_LanglandsTunnell_CubicInduction_TorusValues
import Definitions.Def_LanglandsTunnell_StandardLocalConstantsAt
import Theorems.Thm_AutomorphicForm_exists_haar_localGL2_eq_smul_map_lowerUnipotentGL2_mul_diagUnits2_mul_unipotentGL2
import Theorems.Thm_Matrix_GeneralLinearGroup_isMulRightInvariant_and_isInvInvariant_of_isHaarMeasure_fin_two
import Theorems.Thm_LanglandsTunnell_TateLocal_modulus_adicCompletion_eq_nnnorm
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_haar_localGL2_eq_smul_map_unipotentGL2_mul_diagUnits2_mul_lowerUnipotentGL2
p2m_attr_erase "instance" "instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions instCountableOfNumberField_definitions"

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

open MeasureTheory IsDedekindDomain NumberField AutomorphicForm LanglandsTunnell.TateLocal LanglandsTunnell.CubicInduction Topology

open scoped ENNReal NNReal Pointwise

noncomputable section

namespace LeftBruhatCellHaar

variable {K : Type} [Field K] [NumberField K] {v : HeightOneSpectrum (𝓞 K)}

local notation "F" => (HeightOneSpectrum.adicCompletion K v)
local notation "G" => (GL (Fin 2) (HeightOneSpectrum.adicCompletion K v))
local notation "Mat" => (Matrix (Fin 2) (Fin 2) (HeightOneSpectrum.adicCompletion K v))
local notation "Fˣ" => ((HeightOneSpectrum.adicCompletion K v)ˣ)

theorem modulus_eq_nnnorm (x : F) : modulus x = ‖x‖₊ :=
  LanglandsTunnell.TateLocal.modulus_adicCompletion_eq_nnnorm K v x

scoped instance secondCountable_units : SecondCountableTopology Fˣ :=
  Units.isEmbedding_val₀.secondCountableTopology

theorem borelSpace_units {G₀ : Type*} [GroupWithZero G₀] [TopologicalSpace G₀] [ContinuousInv₀ G₀]
    [MeasurableSpace G₀] [BorelSpace G₀] : BorelSpace G₀ˣ := by
  refine ⟨?_⟩
  have hind : (inferInstance : TopologicalSpace G₀ˣ) = TopologicalSpace.induced Units.val inferInstance :=
    (Units.isEmbedding_val₀ (G₀ := G₀)).eq_induced
  show MeasurableSpace.comap Units.val (inferInstance : MeasurableSpace G₀) = borel G₀ˣ
  rw [BorelSpace.measurable_eq (α := G₀), ← borel_comap, ← hind]

scoped instance : SecondCountableTopology (Matrix (Fin 2) (Fin 2) (HeightOneSpectrum.adicCompletion K v)) :=
  inferInstanceAs (SecondCountableTopology (Fin 2 → Fin 2 → HeightOneSpectrum.adicCompletion K v))

scoped instance : SecondCountableTopology (Matrix (Fin 2) (Fin 2) (HeightOneSpectrum.adicCompletion K v))ᵐᵒᵖ :=
  MulOpposite.opHomeomorph.symm.secondCountableTopology

scoped instance secondCountableTopology_localGL : SecondCountableTopology G :=
  Units.isEmbedding_embedProduct.isInducing.secondCountableTopology

scoped instance locallyCompactSpace_localGL' : LocallyCompactSpace G := locallyCompactSpace_localGL K v

theorem continuous_unipotentGL2 : Continuous fun y : F => (unipotentGL2 y : G) := by
  rw [Units.continuous_iff]
  constructor
  · have h : (Units.val ∘ fun y : F => (unipotentGL2 y : G)) = fun y => !![1, y; 0, 1] := funext fun y => rfl
    rw [h]
    refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j <;> simp <;> first | exact continuous_const | exact continuous_id
  · have h : (fun y : F => (((unipotentGL2 y : G)⁻¹ : G) : Mat)) = fun y => !![1, -y; 0, 1] :=
      funext fun y => rfl
    show Continuous fun y : F => (((unipotentGL2 y : G)⁻¹ : G) : Mat)
    rw [h]
    refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j <;> simp <;> first | exact continuous_const | exact continuous_neg

theorem continuous_lowerUnipotentGL2 : Continuous fun x : F => (lowerUnipotentGL2 x : G) := by
  rw [Units.continuous_iff]
  constructor
  · have h : (Units.val ∘ fun x : F => (lowerUnipotentGL2 x : G)) = fun x => !![1, 0; x, 1] := funext fun x => rfl
    rw [h]
    refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j <;> simp <;> first | exact continuous_const | exact continuous_id
  · have h : (fun x : F => (((lowerUnipotentGL2 x : G)⁻¹ : G) : Mat)) = fun x => !![1, 0; -x, 1] :=
      funext fun x => rfl
    show Continuous fun x : F => (((lowerUnipotentGL2 x : G)⁻¹ : G) : Mat)
    rw [h]
    refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j <;> simp <;> first | exact continuous_const | exact continuous_neg

theorem continuous_diagUnits2 : Continuous fun da : Fˣ × Fˣ => (diagUnits2 da.1 da.2 : G) := by
  rw [Units.continuous_iff]
  have h1 : Continuous fun da : Fˣ × Fˣ => ((da.1 : F)) := Units.continuous_val.comp continuous_fst
  have h2 : Continuous fun da : Fˣ × Fˣ => ((da.2 : F)) := Units.continuous_val.comp continuous_snd
  have h1' : Continuous fun da : Fˣ × Fˣ => ((da.1 : F))⁻¹ := by
    have := (Units.continuous_coe_inv (M := F)).comp (continuous_fst : Continuous fun da : Fˣ × Fˣ => da.1)
    refine this.congr fun da => ?_
    simp [Function.comp_apply, Units.val_inv_eq_inv_val]
  have h2' : Continuous fun da : Fˣ × Fˣ => ((da.2 : F))⁻¹ := by
    have := (Units.continuous_coe_inv (M := F)).comp (continuous_snd : Continuous fun da : Fˣ × Fˣ => da.2)
    refine this.congr fun da => ?_
    simp [Function.comp_apply, Units.val_inv_eq_inv_val]
  constructor
  · have h : (Units.val ∘ fun da : Fˣ × Fˣ => (diagUnits2 da.1 da.2 : G)) = fun da => !![(da.1 : F), 0; 0, (da.2 : F)] :=
      funext fun da => rfl
    rw [h]
    refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j <;> simp <;> first | exact continuous_const | exact h1 | exact h2
  · have h : (fun da : Fˣ × Fˣ => (((diagUnits2 da.1 da.2 : G)⁻¹ : G) : Mat)) =
        fun da => !![((da.1 : F))⁻¹, 0; 0, ((da.2 : F))⁻¹] := by
      funext da
      change !![(((da.1)⁻¹ : Fˣ) : F), 0; 0, (((da.2)⁻¹ : Fˣ) : F)] = _
      simp [Units.val_inv_eq_inv_val]
    show Continuous fun da : Fˣ × Fˣ => (((diagUnits2 da.1 da.2 : G)⁻¹ : G) : Mat)
    rw [h]
    refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j <;> simp <;> first | exact continuous_const | exact h1' | exact h2'

abbrev Coord (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K)) : Type :=
  HeightOneSpectrum.adicCompletion K v × (HeightOneSpectrum.adicCompletion K v)ˣ ×
    (HeightOneSpectrum.adicCompletion K v)ˣ × HeightOneSpectrum.adicCompletion K v

local notation "Q" => (Coord K v)

def cellMap (q : Q) : G := lowerUnipotentGL2 q.2.2.2 * diagUnits2 q.2.2.1 q.2.1 * unipotentGL2 q.1

def cellMap' (q : Q) : G := unipotentGL2 q.1 * diagUnits2 q.2.2.1 q.2.1 * lowerUnipotentGL2 q.2.2.2

theorem cellMap_eq :
    (cellMap : Q → G) = fun q => lowerUnipotentGL2 q.2.2.2 * diagUnits2 q.2.2.1 q.2.1 * unipotentGL2 q.1 := rfl

theorem cellMap'_eq :
    (cellMap' : Q → G) = fun q => unipotentGL2 q.1 * diagUnits2 q.2.2.1 q.2.1 * lowerUnipotentGL2 q.2.2.2 := rfl

def sig (q : Q) : Q := (-q.1, (q.2.1)⁻¹, (q.2.2.1)⁻¹, -q.2.2.2)

theorem sig_eq : (sig : Q → Q) = Prod.map Neg.neg (Prod.map Inv.inv (Prod.map Inv.inv Neg.neg)) := by
  funext q
  rfl

theorem continuous_cellMap : Continuous (cellMap : Q → G) := by
  unfold cellMap
  refine ((continuous_lowerUnipotentGL2.comp (continuous_snd.comp (continuous_snd.comp continuous_snd))).mul
    (continuous_diagUnits2.comp ((continuous_fst.comp (continuous_snd.comp continuous_snd)).prodMk
      (continuous_fst.comp continuous_snd)))).mul (continuous_unipotentGL2.comp continuous_fst)

theorem continuous_cellMap' : Continuous (cellMap' : Q → G) := by
  unfold cellMap'
  refine ((continuous_unipotentGL2.comp continuous_fst).mul
    (continuous_diagUnits2.comp ((continuous_fst.comp (continuous_snd.comp continuous_snd)).prodMk
      (continuous_fst.comp continuous_snd)))).mul
    (continuous_lowerUnipotentGL2.comp (continuous_snd.comp (continuous_snd.comp continuous_snd)))

theorem inv_unipotentGL2 (y : F) : (unipotentGL2 y : G)⁻¹ = unipotentGL2 (-y) :=
  Units.ext rfl

theorem inv_lowerUnipotentGL2 (x : F) : (lowerUnipotentGL2 x : G)⁻¹ = lowerUnipotentGL2 (-x) :=
  Units.ext rfl

theorem inv_diagUnits2 (d a : Fˣ) : (diagUnits2 d a : G)⁻¹ = diagUnits2 d⁻¹ a⁻¹ :=
  Units.ext rfl

theorem inv_cellMap (q : Q) : (cellMap q)⁻¹ = cellMap' (sig q) := by
  simp only [cellMap, cellMap', sig, mul_inv_rev, inv_unipotentGL2, inv_lowerUnipotentGL2, inv_diagUnits2, mul_assoc]

theorem inv_comp_cellMap : ((fun g : G => g⁻¹) ∘ (cellMap : Q → G)) = cellMap' ∘ sig := by
  funext q
  exact inv_cellMap q

section Measures

attribute [local instance] LanglandsTunnell.TateLocal.localBorel LanglandsTunnell.TateLocal.borelSpace_localBorel
  AutomorphicForm.localGLBorel AutomorphicForm.borelSpace_localGLBorel

scoped instance borelSpace_units_local : BorelSpace Fˣ := borelSpace_units

theorem measurable_cellMap : Measurable (cellMap : Q → G) := continuous_cellMap.measurable

theorem measurable_cellMap' : Measurable (cellMap' : Q → G) := continuous_cellMap'.measurable

theorem measurable_sig : Measurable (sig : Q → Q) := by
  rw [sig_eq]
  exact measurable_neg.prodMap (measurable_inv.prodMap (measurable_inv.prodMap measurable_neg))

def wt (q : Q) : ℝ≥0∞ := (modulus (((q.2.2.1 * (q.2.1)⁻¹ : Fˣ)) : F) : ℝ≥0∞)

def wt' (q : Q) : ℝ≥0∞ := (modulus (((q.2.1 * (q.2.2.1)⁻¹ : Fˣ)) : F) : ℝ≥0∞)

theorem wt_eq : (wt : Q → ℝ≥0∞) = fun q => (modulus (((q.2.2.1 * (q.2.1)⁻¹ : Fˣ)) : F) : ℝ≥0∞) := rfl

theorem wt'_eq : (wt' : Q → ℝ≥0∞) = fun q => (modulus (((q.2.1 * (q.2.2.1)⁻¹ : Fˣ)) : F) : ℝ≥0∞) := rfl

theorem wt_comp_sig : (wt ∘ sig : Q → ℝ≥0∞) = wt' := by
  funext q
  simp only [Function.comp_apply, wt, wt', sig, inv_inv]
  rw [mul_comm]

theorem continuous_wt'_nnreal : Continuous fun q : Q => (modulus (((q.2.1 * (q.2.2.1)⁻¹ : Fˣ)) : F) : ℝ≥0) := by
  have h : (fun q : Q => (modulus (((q.2.1 * (q.2.2.1)⁻¹ : Fˣ)) : F) : ℝ≥0)) =
      fun q => ‖(((q.2.1 * (q.2.2.1)⁻¹ : Fˣ)) : F)‖₊ := funext fun q => modulus_eq_nnnorm _
  rw [h]
  refine continuous_nnnorm.comp (Units.continuous_val.comp ?_)
  exact (continuous_fst.comp continuous_snd).mul (continuous_fst.comp (continuous_snd.comp continuous_snd)).inv

theorem measurable_wt' : Measurable (wt' : Q → ℝ≥0∞) :=
  ENNReal.continuous_coe.measurable.comp continuous_wt'_nnreal.measurable

theorem withDensity_map_eq {α β : Type*} [MeasurableSpace α] [MeasurableSpace β] (μ : Measure α) {A : α → β}
    (hA : Measurable A) {g : β → ℝ≥0∞} (hg : Measurable g) :
    (Measure.map A μ).withDensity g = Measure.map A (μ.withDensity (g ∘ A)) := by
  refine Measure.ext fun s hs => ?_
  rw [withDensity_apply _ hs, Measure.map_apply hA hs, withDensity_apply _ (hA hs), Measure.restrict_map hA hs,
    lintegral_map hg hA]
  rfl

variable (ν : Measure (HeightOneSpectrum.adicCompletion K v)) [ν.IsAddHaarMeasure]
  (τ : Measure (HeightOneSpectrum.adicCompletion K v)ˣ) [τ.IsHaarMeasure]

def rho : Measure Q := ν.prod (τ.prod (τ.prod ν))

theorem map_sig_rho : Measure.map sig (rho ν τ) = rho ν τ := by
  have h1 : Measure.map (Neg.neg : F → F) ν = ν := Measure.map_neg_eq_self ν
  have h2 : Measure.map (Inv.inv : Fˣ → Fˣ) τ = τ := Measure.map_inv_eq_self τ
  unfold rho
  rw [sig_eq, ← Measure.map_prod_map _ _ measurable_neg (measurable_inv.prodMap (measurable_inv.prodMap measurable_neg)),
    ← Measure.map_prod_map _ _ measurable_inv (measurable_inv.prodMap measurable_neg),
    ← Measure.map_prod_map _ _ measurable_inv measurable_neg, h1, h2]

theorem map_sig_rhoW : Measure.map sig ((rho ν τ).withDensity wt) = (rho ν τ).withDensity wt' := by
  have h := withDensity_map_eq (rho ν τ) measurable_sig measurable_wt'
  rw [map_sig_rho] at h
  rw [h]
  congr 1
  rw [← wt_comp_sig]
  rfl

end Measures

section Assembly

attribute [local instance] LanglandsTunnell.TateLocal.localBorel LanglandsTunnell.TateLocal.borelSpace_localBorel
  AutomorphicForm.localGLBorel AutomorphicForm.borelSpace_localGLBorel

theorem main (μ : Measure G) [μ.IsHaarMeasure] (τ : Measure Fˣ) [τ.IsHaarMeasure]
    (ν : Measure F) [ν.IsAddHaarMeasure] :
    ∃ c : ℝ≥0∞, c ≠ 0 ∧ c ≠ ⊤ ∧ μ = c • Measure.map cellMap' ((rho ν τ).withDensity wt') := by
  obtain ⟨c, hc0, hctop, hμ⟩ :=
    AutomorphicForm.exists_haar_localGL2_eq_smul_map_lowerUnipotentGL2_mul_diagUnits2_mul_unipotentGL2 K v μ τ ν
  haveI : μ.IsInvInvariant :=
    (Matrix.GeneralLinearGroup.isMulRightInvariant_and_isInvInvariant_of_isHaarMeasure_fin_two μ).2
  refine ⟨c, hc0, hctop, ?_⟩
  have hρ : Measure.map cellMap' ((rho ν τ).withDensity wt') =
      Measure.map (fun g : G => g⁻¹) (Measure.map cellMap ((rho ν τ).withDensity wt)) := by
    rw [Measure.map_map measurable_inv measurable_cellMap, inv_comp_cellMap,
      ← Measure.map_map measurable_cellMap' measurable_sig, map_sig_rhoW]
  have hcell : (fun q : Q => lowerUnipotentGL2 q.2.2.2 * diagUnits2 q.2.2.1 q.2.1 * unipotentGL2 q.1) = cellMap := rfl
  have hwt : (fun q : Q => (modulus (((q.2.2.1 * (q.2.1)⁻¹ : Fˣ)) : F) : ℝ≥0∞)) = wt := rfl
  rw [hcell, hwt] at hμ
  change μ = c • Measure.map cellMap (((rho ν τ)).withDensity wt) at hμ
  calc μ = Measure.map (fun g : G => g⁻¹) μ := (Measure.map_inv_eq_self μ).symm
    _ = Measure.map (fun g : G => g⁻¹) (c • Measure.map cellMap ((rho ν τ).withDensity wt)) := by rw [← hμ]
    _ = c • Measure.map cellMap' ((rho ν τ).withDensity wt') := by rw [Measure.map_smul, hρ]

end Assembly

end LeftBruhatCellHaar
p2m_reactivate "P2MW.S_AutomorphicForm_exists_haar_localGL2_eq_smul_map_unipotentGL2_mul_diagUnits2_mul_lowerUnipotentGL2.LeftBruhatCellHaar"

theorem solution
    (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K)) :
    letI := localBorel K v
    letI := localGLBorel K v
    haveI := borelSpace_localGLBorel K v
    ∀ (μ : Measure (GL (Fin 2) (v.adicCompletion K))) [μ.IsHaarMeasure]
      (τ : Measure (v.adicCompletion K)ˣ) [τ.IsHaarMeasure]
      (ν : Measure (v.adicCompletion K)) [ν.IsAddHaarMeasure],
    ∃ c : ℝ≥0∞, c ≠ 0 ∧ c ≠ ⊤ ∧
      μ = c • Measure.map
        (fun q : v.adicCompletion K × (v.adicCompletion K)ˣ × (v.adicCompletion K)ˣ × v.adicCompletion K =>
          unipotentGL2 q.1 * diagUnits2 q.2.2.1 q.2.1 * lowerUnipotentGL2 q.2.2.2)
        ((ν.prod (τ.prod (τ.prod ν))).withDensity fun q =>
          (modulus (((q.2.1 * (q.2.2.1)⁻¹ : (v.adicCompletion K)ˣ)) : v.adicCompletion K) : ℝ≥0∞)) := by
  intro μ _ τ _ ν _
  exact LeftBruhatCellHaar.main μ τ ν

end
p2m_reactivate "P2MW.S_AutomorphicForm_exists_haar_localGL2_eq_smul_map_unipotentGL2_mul_diagUnits2_mul_lowerUnipotentGL2.LeftBruhatCellHaar"

end S_AutomorphicForm_exists_haar_localGL2_eq_smul_map_unipotentGL2_mul_diagUnits2_mul_lowerUnipotentGL2
end P2MW
export P2MW.S_AutomorphicForm_exists_haar_localGL2_eq_smul_map_unipotentGL2_mul_diagUnits2_mul_lowerUnipotentGL2 (solution)

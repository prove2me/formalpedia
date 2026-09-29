-- Prove2me | solution 1 for AutomorphicForm.exists_haar_localGL2_eq_smul_map_lowerUnipotentGL2_mul_diagUnits2_mul_unipotentGL2
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/b3fa3f08-5bf8-5766-b68c-d7afad17e30e

import Mathlib
import Definitions.Def_AutomorphicForm_ArchDerivCasimir
import Definitions.Def_AutomorphicForm_LocalOrbitalBase
import Definitions.Def_LanglandsTunnell_CubicInduction_TorusValues
import Definitions.Def_LanglandsTunnell_StandardLocalConstantsAt
import Theorems.Thm_Matrix_GeneralLinearGroup_isMulRightInvariant_and_isInvInvariant_of_isHaarMeasure_fin_two
import Theorems.Thm_LanglandsTunnell_TateLocal_modulus_adicCompletion_eq_nnnorm
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

p2m_attr_erase "ext" "IsDedekindDomain.HeightOneSpectrum.adicCompletion.ext"
namespace P2MW.S_AutomorphicForm_exists_haar_localGL2_eq_smul_map_lowerUnipotentGL2_mul_diagUnits2_mul_unipotentGL2
p2m_attr_erase "instance" "instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions instCountableOfNumberField_definitions"

set_option autoImplicit false

open MeasureTheory IsDedekindDomain NumberField AutomorphicForm LanglandsTunnell.TateLocal LanglandsTunnell.CubicInduction Topology

open scoped ENNReal NNReal Pointwise

noncomputable section

namespace BruhatCellHaar

variable {K : Type} [Field K] [NumberField K] {v : HeightOneSpectrum (𝓞 K)}

local notation "F" => (HeightOneSpectrum.adicCompletion K v)
local notation "G" => (GL (Fin 2) (HeightOneSpectrum.adicCompletion K v))
local notation "Mat" => (Matrix (Fin 2) (Fin 2) (HeightOneSpectrum.adicCompletion K v))
local notation "Fˣ" => ((HeightOneSpectrum.adicCompletion K v)ˣ)

theorem coe_modulus_eq_norm (x : F) : ((modulus x : ℝ≥0) : ℝ) = ‖x‖ := by
  rw [LanglandsTunnell.TateLocal.modulus_adicCompletion_eq_nnnorm K v x, coe_nnnorm]

theorem modulus_eq_nnnorm (x : F) : modulus x = ‖x‖₊ :=
  LanglandsTunnell.TateLocal.modulus_adicCompletion_eq_nnnorm K v x

theorem modulus_units_ne_zero (u : Fˣ) : modulus (u : F) ≠ 0 := modulus_ne_zero u.ne_zero

theorem modulus_units_ne_zero' (u : Fˣ) : (modulus (u : F) : ℝ≥0∞) ≠ 0 :=
  ENNReal.coe_ne_zero.mpr (modulus_units_ne_zero u)

scoped instance secondCountable_units : SecondCountableTopology Fˣ :=
  Units.isEmbedding_val₀.secondCountableTopology

theorem borelSpace_units {G₀ : Type*} [GroupWithZero G₀] [TopologicalSpace G₀] [ContinuousInv₀ G₀]
    [MeasurableSpace G₀] [BorelSpace G₀] : BorelSpace G₀ˣ := by
  refine ⟨?_⟩
  have hind : (inferInstance : TopologicalSpace G₀ˣ) = TopologicalSpace.induced Units.val inferInstance :=
    (Units.isEmbedding_val₀ (G₀ := G₀)).eq_induced
  show MeasurableSpace.comap Units.val (inferInstance : MeasurableSpace G₀) = borel G₀ˣ
  rw [BorelSpace.measurable_eq (α := G₀), ← borel_comap, ← hind]

theorem continuous_units_of_val {X : Type*} [TopologicalSpace X] {f : X → Fˣ} (hf : Continuous fun x => (f x : F)) :
    Continuous f :=
  Units.isEmbedding_val₀.continuous_iff.mpr hf

theorem smul_set_eq_preimage {c : F} (hc : c ≠ 0) (T : Set F) :
    c • T = (fun y => c⁻¹ * y) ⁻¹' T := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa [smul_eq_mul, inv_mul_cancel_left₀ hc] using hy
  · intro hx
    exact ⟨c⁻¹ * x, hx, by simp [smul_eq_mul, mul_inv_cancel_left₀ hc]⟩

section Scaling

variable [MeasurableSpace (HeightOneSpectrum.adicCompletion K v)] [BorelSpace (HeightOneSpectrum.adicCompletion K v)]

theorem map_mul_left_eq_smul (ν : Measure F) [ν.IsAddHaarMeasure] (u : Fˣ) :
    ν.map (fun x : F => (u : F) * x) = ((modulus (u : F) : ℝ≥0∞))⁻¹ • ν := by
  refine Measure.ext fun s hs => ?_
  rw [Measure.map_apply (measurable_const_mul _) hs, Measure.smul_apply, smul_eq_mul]
  have hpre : (fun x : F => (u : F) * x) ⁻¹' s = ((u⁻¹ : Fˣ) : F) • s := by
    rw [smul_set_eq_preimage (u⁻¹).ne_zero, Units.val_inv_eq_inv_val, inv_inv]
  rw [hpre]
  have h := distribHaarChar_mul ν (u⁻¹) s
  rw [show ((u⁻¹ : Fˣ) • s : Set F) = ((u⁻¹ : Fˣ) : F) • s from rfl] at h
  rw [← h, map_inv, modulus_coe_units, ENNReal.coe_inv (distribHaarChar_pos).ne']

theorem map_affine_eq_smul (ν : Measure F) [ν.IsAddHaarMeasure] (x₀ : F) (u : Fˣ) :
    ν.map (fun x : F => x₀ + (u : F) * x) = ((modulus (u : F) : ℝ≥0∞))⁻¹ • ν := by
  have h : (fun x : F => x₀ + (u : F) * x) = (fun x : F => x₀ + x) ∘ fun x : F => (u : F) * x := rfl
  rw [h, ← Measure.map_map (measurable_const_add x₀) (measurable_const_mul _), map_mul_left_eq_smul,
    Measure.map_smul, map_add_left_eq_self]

end Scaling

scoped instance : SecondCountableTopology (Matrix (Fin 2) (Fin 2) (HeightOneSpectrum.adicCompletion K v)) :=
  inferInstanceAs (SecondCountableTopology (Fin 2 → Fin 2 → HeightOneSpectrum.adicCompletion K v))

scoped instance : SecondCountableTopology (Matrix (Fin 2) (Fin 2) (HeightOneSpectrum.adicCompletion K v))ᵐᵒᵖ :=
  MulOpposite.opHomeomorph.symm.secondCountableTopology

scoped instance secondCountableTopology_localGL : SecondCountableTopology G :=
  Units.isEmbedding_embedProduct.isInducing.secondCountableTopology

scoped instance locallyCompactSpace_localGL' : LocallyCompactSpace G := locallyCompactSpace_localGL K v

def ent (g : G) (i j : Fin 2) : F := (g : Mat) i j

theorem continuous_ent (i j : Fin 2) : Continuous fun g : G => ent g i j :=
  (Units.continuous_val).matrix_elem i j

theorem det_eq (g : G) : (g : Mat).det = ent g 0 0 * ent g 1 1 - ent g 0 1 * ent g 1 0 :=
  Matrix.det_fin_two _

theorem det_ne_zero (g : G) : (g : Mat).det ≠ 0 := by
  rw [← Matrix.GeneralLinearGroup.val_det_apply]
  exact (Matrix.GeneralLinearGroup.det g).ne_zero

theorem ext_ent {g h : G} (h00 : ent g 0 0 = ent h 0 0) (h01 : ent g 0 1 = ent h 0 1) (h10 : ent g 1 0 = ent h 1 0)
    (h11 : ent g 1 1 = ent h 1 1) : g = h := by
  refine Units.ext ?_
  ext i j
  fin_cases i <;> fin_cases j
  · exact h00
  · exact h01
  · exact h10
  · exact h11

abbrev unip : Subgroup G := (unipotentGL2Hom (R := HeightOneSpectrum.adicCompletion K v)).range

theorem mem_unip_iff (g : G) : g ∈ unip ↔ ent g 0 0 = 1 ∧ ent g 1 0 = 0 ∧ ent g 1 1 = 1 := by
  simp only [MonoidHom.mem_range]
  constructor
  · rintro ⟨x, rfl⟩
    simp [ent, unipotentGL2Hom, unipotentGL2_coe]
  · rintro ⟨h00, h10, h11⟩
    refine ⟨Multiplicative.ofAdd (ent g 0 1), Units.ext ?_⟩
    change ((unipotentGL2 (ent g 0 1) : G) : Mat) = (g : Mat)
    rw [unipotentGL2_coe]
    ext i j; fin_cases i <;> fin_cases j
    · exact h00.symm
    · rfl
    · exact h10.symm
    · exact h11.symm

theorem isClosed_unip : IsClosed ((unip : Subgroup G) : Set G) := by
  have h : ((unip : Subgroup G) : Set G) = {g : G | ent g 0 0 = 1 ∧ ent g 1 0 = 0 ∧ ent g 1 1 = 1} := by
    ext g; exact mem_unip_iff g
  rw [h]
  exact ((isClosed_singleton.preimage (continuous_ent 0 0)).inter
    ((isClosed_singleton.preimage (continuous_ent 1 0)).inter
      (isClosed_singleton.preimage (continuous_ent 1 1))))

theorem unip_eq_unipotentGL2 (n : (unip : Subgroup G)) : (n : G) = unipotentGL2 (ent (n : G) 0 1) := by
  obtain ⟨z, hz⟩ := n.2
  rw [← hz]
  change (unipotentGL2 z.toAdd : G) = unipotentGL2 (ent (unipotentGL2 z.toAdd : G) 0 1)
  have h01 : ent (unipotentGL2 z.toAdd : G) 0 1 = z.toAdd := by simp [ent, unipotentGL2_coe]
  rw [h01]

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

def lowerTri : Subgroup G where
  carrier := {g : G | ent g 0 1 = 0}
  mul_mem' := by
    intro g h hg hh
    simp only [Set.mem_setOf_eq, ent] at hg hh ⊢
    rw [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two, hg, hh]
    ring
  one_mem' := by simp [ent]
  inv_mem' := by
    intro g hg
    simp only [Set.mem_setOf_eq, ent] at hg ⊢
    rw [Matrix.coe_units_inv, Matrix.inv_def, Matrix.adjugate_fin_two]
    simp [hg]

theorem mem_lowerTri_iff (g : G) : g ∈ lowerTri ↔ ent g 0 1 = 0 := Iff.rfl

theorem isClosed_lowerTri : IsClosed ((lowerTri : Subgroup G) : Set G) :=
  isClosed_singleton.preimage (continuous_ent 0 1)

theorem ent00_mul_ent11_of_mem {b : G} (hb : b ∈ lowerTri) : ent b 0 0 * ent b 1 1 = (b : Mat).det := by
  rw [det_eq, (mem_lowerTri_iff b).mp hb, zero_mul, sub_zero]

theorem ent00_ne_zero_of_mem {b : G} (hb : b ∈ lowerTri) : ent b 0 0 ≠ 0 := fun h => by
  have := ent00_mul_ent11_of_mem hb
  rw [h, zero_mul] at this
  exact det_ne_zero b this.symm

theorem ent11_ne_zero_of_mem {b : G} (hb : b ∈ lowerTri) : ent b 1 1 ≠ 0 := fun h => by
  have := ent00_mul_ent11_of_mem hb
  rw [h, mul_zero] at this
  exact det_ne_zero b this.symm

theorem lowerUnipotentGL2_mul_diagUnits2_mem (x : F) (d a : Fˣ) : lowerUnipotentGL2 x * diagUnits2 d a ∈ lowerTri := by
  rw [mem_lowerTri_iff]
  simp [ent, Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two, lowerUnipotentGL2_coe]

theorem ent_lowerUnipotentGL2_mul_diagUnits2 (x : F) (d a : Fˣ) :
    ent (lowerUnipotentGL2 x * diagUnits2 d a) 0 0 = d ∧ ent (lowerUnipotentGL2 x * diagUnits2 d a) 1 0 = x * d ∧
      ent (lowerUnipotentGL2 x * diagUnits2 d a) 1 1 = a := by
  simp [ent, Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two, lowerUnipotentGL2_coe]

theorem unipotentGL2_mem_unip (y : F) : (unipotentGL2 y : G) ∈ unip := ⟨Multiplicative.ofAdd y, rfl⟩

theorem eq_one_of_mem_lowerTri_of_mem_unip {g : G} (hb : g ∈ lowerTri) (hn : g ∈ unip) : g = 1 := by
  obtain ⟨h00, h10, h11⟩ := (mem_unip_iff g).mp hn
  refine ext_ent ?_ ?_ ?_ ?_
  · simpa [ent] using h00
  · simpa [ent] using (mem_lowerTri_iff g).mp hb
  · simpa [ent] using h10
  · simpa [ent] using h11

section Chart

attribute [local instance] LanglandsTunnell.TateLocal.localBorel LanglandsTunnell.TateLocal.borelSpace_localBorel
  AutomorphicForm.localGLBorel AutomorphicForm.borelSpace_localGLBorel

scoped instance borelSpace_units_local : BorelSpace Fˣ := borelSpace_units

theorem measurable_units_of_val {X : Type*} [MeasurableSpace X] {f : X → Fˣ} (hf : Measurable fun x => (f x : F)) :
    Measurable f := by
  rw [measurable_iff_comap_le] at hf ⊢
  have h : MeasurableSpace.comap f (Units.instMeasurableSpace : MeasurableSpace Fˣ) =
      MeasurableSpace.comap (fun x => (f x : F)) (inferInstance : MeasurableSpace F) := by
    show MeasurableSpace.comap f (MeasurableSpace.comap Units.val _) = _
    rw [MeasurableSpace.comap_comp]
    rfl
  rw [h]
  exact hf

abbrev Coord (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K)) : Type :=
  HeightOneSpectrum.adicCompletion K v × (HeightOneSpectrum.adicCompletion K v)ˣ ×
    (HeightOneSpectrum.adicCompletion K v)ˣ × HeightOneSpectrum.adicCompletion K v

abbrev Pgrp (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K)) : Type :=
  ↥(lowerTri : Subgroup (GL (Fin 2) (HeightOneSpectrum.adicCompletion K v))) ×
    ↥(unip : Subgroup (GL (Fin 2) (HeightOneSpectrum.adicCompletion K v)))

local notation "Q" => (Coord K v)
local notation "P" => (Pgrp K v)

scoped instance secondCountable_lowerTri : SecondCountableTopology ↥(lowerTri : Subgroup G) :=
  TopologicalSpace.Subtype.secondCountableTopology ((lowerTri : Subgroup G) : Set G)

scoped instance secondCountable_unip : SecondCountableTopology ↥(unip : Subgroup G) :=
  TopologicalSpace.Subtype.secondCountableTopology ((unip : Subgroup G) : Set G)

scoped instance borelSpace_lowerTri : BorelSpace ↥(lowerTri : Subgroup G) := Subtype.borelSpace _

scoped instance borelSpace_unip : BorelSpace ↥(unip : Subgroup G) := Subtype.borelSpace _

scoped instance borelSpace_P : BorelSpace P := Prod.borelSpace

scoped instance locallyCompactSpace_lowerTri : LocallyCompactSpace ↥(lowerTri : Subgroup G) :=
  isClosed_lowerTri.locallyCompactSpace

scoped instance locallyCompactSpace_unip : LocallyCompactSpace ↥(unip : Subgroup G) := isClosed_unip.locallyCompactSpace

def cellMap (q : Q) : G := lowerUnipotentGL2 q.2.2.2 * diagUnits2 q.2.2.1 q.2.1 * unipotentGL2 q.1

theorem cellMap_eq :
    (cellMap : Q → G) = fun q => lowerUnipotentGL2 q.2.2.2 * diagUnits2 q.2.2.1 q.2.1 * unipotentGL2 q.1 := rfl

theorem ent_cellMap (q : Q) :
    ent (cellMap q) 0 0 = q.2.2.1 ∧ ent (cellMap q) 0 1 = q.2.2.1 * q.1 ∧
      ent (cellMap q) 1 0 = q.2.2.2 * q.2.2.1 ∧ ent (cellMap q) 1 1 = q.2.2.2 * q.2.2.1 * q.1 + q.2.1 := by
  simp [cellMap, ent, Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two, lowerUnipotentGL2_coe, unipotentGL2_coe]

theorem continuous_cellMap : Continuous (cellMap : Q → G) := by
  have hL : Continuous fun q : Q => (lowerUnipotentGL2 q.2.2.2 : G) :=
    continuous_lowerUnipotentGL2.comp (continuous_snd.comp (continuous_snd.comp continuous_snd))
  have hD : Continuous fun q : Q => (diagUnits2 q.2.2.1 q.2.1 : G) :=
    continuous_diagUnits2.comp ((continuous_fst.comp (continuous_snd.comp continuous_snd)).prodMk
      (continuous_fst.comp continuous_snd))
  have hU : Continuous fun q : Q => (unipotentGL2 q.1 : G) := continuous_unipotentGL2.comp continuous_fst
  exact (hL.mul hD).mul hU

def bPart (q : Q) : ↥(lowerTri : Subgroup G) :=
  ⟨lowerUnipotentGL2 q.2.2.2 * diagUnits2 q.2.2.1 q.2.1, lowerUnipotentGL2_mul_diagUnits2_mem _ _ _⟩

def nPart (q : Q) : ↥(unip : Subgroup G) := ⟨unipotentGL2 q.1, unipotentGL2_mem_unip _⟩

def Xi (q : Q) : P := (bPart q, nPart q)

def mulMap (bn : P) : G := (bn.1 : G) * (bn.2 : G)

theorem mulMap_Xi (q : Q) : mulMap (Xi q) = cellMap q := rfl

theorem continuous_mulMap : Continuous (mulMap : P → G) :=
  (continuous_subtype_val.comp continuous_fst).mul (continuous_subtype_val.comp continuous_snd)

theorem continuous_Xi : Continuous (Xi : Q → P) := by
  have hL : Continuous fun q : Q => (lowerUnipotentGL2 q.2.2.2 : G) :=
    continuous_lowerUnipotentGL2.comp (continuous_snd.comp (continuous_snd.comp continuous_snd))
  have hD : Continuous fun q : Q => (diagUnits2 q.2.2.1 q.2.1 : G) :=
    continuous_diagUnits2.comp ((continuous_fst.comp (continuous_snd.comp continuous_snd)).prodMk
      (continuous_fst.comp continuous_snd))
  have hU : Continuous fun q : Q => (unipotentGL2 q.1 : G) := continuous_unipotentGL2.comp continuous_fst
  exact ((hL.mul hD).subtype_mk _).prodMk (hU.subtype_mk _)

theorem mulMap_injective : Function.Injective (mulMap : P → G) := by
  rintro ⟨b, n⟩ ⟨b', n'⟩ h
  simp only [mulMap] at h

  have hq : ((b'⁻¹ * b : ↥(lowerTri : Subgroup G)) : G) = ((n' * n⁻¹ : ↥(unip : Subgroup G)) : G) := by
    change ((b' : G))⁻¹ * (b : G) = (n' : G) * ((n : G))⁻¹
    rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, ← h, mul_assoc, mul_inv_cancel, mul_one]
  have h1 : ((b'⁻¹ * b : ↥(lowerTri : Subgroup G)) : G) = 1 :=
    eq_one_of_mem_lowerTri_of_mem_unip (b'⁻¹ * b).2 (hq ▸ (n' * n⁻¹).2)
  have hb : b = b' := by
    have : b'⁻¹ * b = 1 := Subtype.ext h1
    rw [inv_mul_eq_one] at this
    exact this.symm
  subst hb
  have hn : (n : G) = n' := mul_left_cancel h
  exact Prod.ext rfl (Subtype.ext hn)

def unit00 (b : ↥(lowerTri : Subgroup G)) : Fˣ := Units.mk0 (ent (b : G) 0 0) (ent00_ne_zero_of_mem b.2)

def unit11 (b : ↥(lowerTri : Subgroup G)) : Fˣ := Units.mk0 (ent (b : G) 1 1) (ent11_ne_zero_of_mem b.2)

def XiInv (bn : P) : Q :=
  (ent (bn.2 : G) 0 1, unit11 bn.1, unit00 bn.1, ent (bn.1 : G) 1 0 * (ent (bn.1 : G) 0 0)⁻¹)

theorem continuous_XiInv : Continuous (XiInv : P → Q) := by
  have hb : ∀ i j : Fin 2, Continuous fun bn : P => ent (bn.1 : G) i j := fun i j =>
    (continuous_ent i j).comp (continuous_subtype_val.comp continuous_fst)
  have hn : ∀ i j : Fin 2, Continuous fun bn : P => ent (bn.2 : G) i j := fun i j =>
    (continuous_ent i j).comp (continuous_subtype_val.comp continuous_snd)
  refine (hn 0 1).prodMk ((continuous_units_of_val (hb 1 1)).prodMk
    ((continuous_units_of_val (hb 0 0)).prodMk ((hb 1 0).mul ((hb 0 0).inv₀ fun bn => ?_))))
  exact ent00_ne_zero_of_mem bn.1.2

theorem XiInv_Xi (q : Q) : XiInv (Xi q) = q := by
  obtain ⟨y, a, d, x⟩ := q
  obtain ⟨h00, h10, h11⟩ := ent_lowerUnipotentGL2_mul_diagUnits2 (K := K) (v := v) x d a
  simp only [XiInv, Xi, bPart, nPart, unit00, unit11]
  refine Prod.ext ?_ (Prod.ext (Units.ext ?_) (Prod.ext (Units.ext ?_) ?_))
  · simp [ent, unipotentGL2_coe]
  · exact h11
  · exact h00
  · change ent (lowerUnipotentGL2 x * diagUnits2 d a) 1 0 * (ent (lowerUnipotentGL2 x * diagUnits2 d a) 0 0)⁻¹ = x
    rw [h10, h00, mul_inv_cancel_right₀ d.ne_zero]

theorem Xi_XiInv (bn : P) : Xi (XiInv bn) = bn := by
  obtain ⟨b, n⟩ := bn
  simp only [XiInv, Xi, bPart, nPart]
  refine Prod.ext (Subtype.ext ?_) (Subtype.ext ?_)
  · change lowerUnipotentGL2 (ent (b : G) 1 0 * (ent (b : G) 0 0)⁻¹) * diagUnits2 (unit00 b) (unit11 b) = (b : G)
    have h0 := ent00_ne_zero_of_mem b.2
    obtain ⟨h00, h10, h11⟩ := ent_lowerUnipotentGL2_mul_diagUnits2 (K := K) (v := v)
      (ent (b : G) 1 0 * (ent (b : G) 0 0)⁻¹) (unit00 b) (unit11 b)
    refine ext_ent ?_ ?_ ?_ ?_
    · rw [h00]; rfl
    · rw [(mem_lowerTri_iff _).mp (lowerUnipotentGL2_mul_diagUnits2_mem _ _ _), (mem_lowerTri_iff _).mp b.2]
    · rw [h10]
      change ent (b : G) 1 0 * (ent (b : G) 0 0)⁻¹ * ent (b : G) 0 0 = _
      rw [inv_mul_cancel_right₀ h0]
    · rw [h11]; rfl
  · change (unipotentGL2 (ent (n : G) 0 1) : G) = n
    exact (unip_eq_unipotentGL2 n).symm

def XiHomeo : Q ≃ₜ P where
  toFun := Xi
  invFun := XiInv
  left_inv := XiInv_Xi
  right_inv := Xi_XiInv
  continuous_toFun := continuous_Xi
  continuous_invFun := continuous_XiInv

theorem XiHomeo_apply (q : Q) : XiHomeo q = Xi q := rfl

theorem Xi_surjective : Function.Surjective (Xi : Q → P) := (XiHomeo (K := K) (v := v)).surjective

theorem Xi_mul_Xi (q₀ q : Q) :
    Xi q₀ * Xi q =
      Xi (q₀.1 + q.1, q₀.2.1 * q.2.1, q₀.2.2.1 * q.2.2.1,
        q₀.2.2.2 + ((q₀.2.1 * (q₀.2.2.1)⁻¹ : Fˣ) : F) * q.2.2.2) := by
  obtain ⟨y₀, a₀, d₀, x₀⟩ := q₀
  obtain ⟨y, a, d, x⟩ := q
  simp only [Xi, bPart, nPart, Prod.mk_mul_mk]
  refine Prod.ext (Subtype.ext ?_) (Subtype.ext ?_)
  · change lowerUnipotentGL2 x₀ * diagUnits2 d₀ a₀ * (lowerUnipotentGL2 x * diagUnits2 d a) =
      lowerUnipotentGL2 (x₀ + ((a₀ * d₀⁻¹ : Fˣ) : F) * x) * diagUnits2 (d₀ * d) (a₀ * a)
    refine Units.ext ?_
    simp only [Units.val_mul, lowerUnipotentGL2_coe, coe_diagUnits2, Units.val_inv_eq_inv_val]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
    field_simp
  · change (unipotentGL2 y₀ : G) * unipotentGL2 y = unipotentGL2 (y₀ + y)
    rw [unipotentGL2_add]

def cell : Set G := {g : G | ent g 0 0 ≠ 0}

theorem isOpen_cell : IsOpen (cell : Set G) := isOpen_ne_fun (continuous_ent 0 0) continuous_const

theorem measurableSet_cell : MeasurableSet (cell : Set G) := isOpen_cell.measurableSet

theorem mulMap_mem_cell (bn : P) : mulMap bn ∈ cell := by
  obtain ⟨q, rfl⟩ := Xi_surjective bn
  rw [mulMap_Xi]
  show ent (cellMap q) 0 0 ≠ 0
  rw [(ent_cellMap q).1]
  exact q.2.2.1.ne_zero

open scoped Classical in

def d0 (g : G) : F := if ent g 0 0 = 0 then 1 else ent g 0 0

theorem d0_ne_zero (g : G) : d0 g ≠ 0 := by
  unfold d0
  split_ifs with h
  · exact one_ne_zero
  · exact h

theorem d0_of_mem {g : G} (hg : g ∈ cell) : d0 g = ent g 0 0 := by
  unfold d0
  rw [if_neg hg]

theorem measurable_d0 : Measurable (d0 : G → F) := by
  unfold d0
  exact Measurable.ite (measurableSet_eq_fun (continuous_ent 0 0).measurable measurable_const) measurable_const
    (continuous_ent 0 0).measurable

def crd (g : G) : Q :=
  (ent g 0 1 * (d0 g)⁻¹, Units.mk0 ((g : Mat).det * (d0 g)⁻¹) (mul_ne_zero (det_ne_zero g) (inv_ne_zero (d0_ne_zero g))),
    Units.mk0 (d0 g) (d0_ne_zero g), ent g 1 0 * (d0 g)⁻¹)

theorem measurable_crd : Measurable (crd : G → Q) := by
  have he : ∀ i j : Fin 2, Measurable fun g : G => ent g i j := fun i j => (continuous_ent i j).measurable
  have hdet : Measurable fun g : G => (g : Mat).det := (Units.continuous_val.matrix_det).measurable
  have hinv : Measurable fun g : G => (d0 g)⁻¹ := measurable_d0.inv
  refine ((he 0 1).mul hinv).prodMk ((measurable_units_of_val (hdet.mul hinv)).prodMk
    ((measurable_units_of_val measurable_d0).prodMk ((he 1 0).mul hinv)))

def sect (g : G) : P := Xi (crd g)

theorem measurable_sect : Measurable (sect : G → P) := continuous_Xi.measurable.comp measurable_crd

theorem mulMap_sect {g : G} (hg : g ∈ cell) : mulMap (sect g) = g := by
  have h0 : ent g 0 0 ≠ 0 := hg
  have hd0 : d0 g = ent g 0 0 := d0_of_mem hg
  rw [sect, mulMap_Xi]
  obtain ⟨h00, h01, h10, h11⟩ := ent_cellMap (crd g)
  have hdet := det_eq g
  refine ext_ent ?_ ?_ ?_ ?_
  · rw [h00]; exact hd0
  · rw [h01]
    change d0 g * (ent g 0 1 * (d0 g)⁻¹) = ent g 0 1
    rw [hd0, mul_comm, inv_mul_cancel_right₀ h0]
  · rw [h10]
    change ent g 1 0 * (d0 g)⁻¹ * d0 g = ent g 1 0
    rw [hd0, inv_mul_cancel_right₀ h0]
  · rw [h11]
    change ent g 1 0 * (d0 g)⁻¹ * d0 g * (ent g 0 1 * (d0 g)⁻¹) + (g : Mat).det * (d0 g)⁻¹ = ent g 1 1
    rw [hd0, hdet]
    field_simp
    ring

theorem sect_mulMap (bn : P) : sect (mulMap bn) = bn :=
  mulMap_injective (mulMap_sect (mulMap_mem_cell bn))

theorem mem_cell_iff (g : G) : g ∈ cell ↔ ∃ bn : P, mulMap bn = g :=
  ⟨fun hg => ⟨sect g, mulMap_sect hg⟩, fun ⟨bn, hbn⟩ => hbn ▸ mulMap_mem_cell bn⟩

end Chart

section NullComplement

attribute [local instance] LanglandsTunnell.TateLocal.localBorel LanglandsTunnell.TateLocal.borelSpace_localBorel
  AutomorphicForm.localGLBorel AutomorphicForm.borelSpace_localGLBorel

theorem ent00_unipotentGL2_mul (t : F) (g : G) : ent (unipotentGL2 t * g) 0 0 = ent g 0 0 + t * ent g 1 0 := by
  simp [ent, Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two, unipotentGL2_coe]

theorem ent10_ne_zero_of_not_mem {g : G} (hg : g ∉ cell) : ent g 1 0 ≠ 0 := by
  have h0 : ent g 0 0 = 0 := by
    by_contra h
    exact hg h
  intro h10
  apply det_ne_zero g
  rw [det_eq, h0, h10, zero_mul, mul_zero, sub_zero]

theorem isClosed_compl_cell : IsClosed ((cell : Set G)ᶜ) := isOpen_cell.isClosed_compl

theorem valued_natCast_le_one (k : ℕ) : Valued.v ((k : F)) ≤ 1 := by
  have : ((k : HeightOneSpectrum.adicCompletionIntegers K v) : F) = (k : F) := by simp
  rw [← this]
  exact (HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 K) K v).mp (SetLike.coe_mem _)

scoped instance charZero_adicCompletion : CharZero F := charZero_of_injective_algebraMap (algebraMap K F).injective

theorem measure_compl_cell_inter_eq_zero (μ : Measure G) [μ.IsHaarMeasure] {L : Set G} (hL : IsCompact L) :
    μ ((cell : Set G)ᶜ ∩ L) = 0 := by
  set S : Set G := (cell : Set G)ᶜ ∩ L with hS
  have hSmeas : MeasurableSet S := (isClosed_compl_cell.inter hL.isClosed).measurableSet

  set T : Set F := {t : F | Valued.v t ≤ 1} with hT
  have hTc : IsCompact T := by
    have : T = (HeightOneSpectrum.adicCompletionIntegers K v : Set F) := by
      ext t; simp [hT, HeightOneSpectrum.mem_adicCompletionIntegers]
    rw [this]
    exact isCompact_iff_compactSpace.mpr (show CompactSpace (HeightOneSpectrum.adicCompletionIntegers K v) from
      inferInstance)
  set M : Set G := (fun p : F × G => (unipotentGL2 p.1 : G) * p.2) '' (T ×ˢ L) with hM
  have hMc : IsCompact M :=
    (hTc.prod hL).image ((continuous_unipotentGL2.comp continuous_fst).mul continuous_snd)
  have hMfin : μ M < ⊤ := hMc.measure_lt_top
  set Sk : ℕ → Set G := fun k => ((unipotentGL2 ((k : F)) : G)) • S with hSk
  have hSk_sub : ∀ k, Sk k ⊆ M := by
    intro k g hg
    obtain ⟨s, hs, rfl⟩ := hg
    exact ⟨((k : F), s), ⟨valued_natCast_le_one k, hs.2⟩, rfl⟩
  have hSk_meas : ∀ k, MeasurableSet (Sk k) := fun k => hSmeas.const_smul _
  have hSk_measure : ∀ k, μ (Sk k) = μ S := fun k => measure_smul μ _ _
  have hSk_disj : Pairwise (Function.onFun Disjoint Sk) := by
    intro k k' hkk'
    rw [Function.onFun, Set.disjoint_left]
    rintro g ⟨s, hs, rfl⟩ ⟨s', hs', hg⟩
    have h1 : ent ((unipotentGL2 ((k : F)) : G) * s) 0 0 = (k : F) * ent s 1 0 := by
      rw [ent00_unipotentGL2_mul, show ent s 0 0 = 0 from not_not.mp hs.1, zero_add]
    have h2 : ent ((unipotentGL2 ((k' : F)) : G) * s') 0 0 = (k' : F) * ent s' 1 0 := by
      rw [ent00_unipotentGL2_mul, show ent s' 0 0 = 0 from not_not.mp hs'.1, zero_add]
    have h10 : ent ((unipotentGL2 ((k : F)) : G) * s) 1 0 = ent s 1 0 := by
      simp [ent, Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two, unipotentGL2_coe]
    have h10' : ent ((unipotentGL2 ((k' : F)) : G) * s') 1 0 = ent s' 1 0 := by
      simp [ent, Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two, unipotentGL2_coe]
    have hg' : (unipotentGL2 ((k' : F)) : G) * s' = (unipotentGL2 ((k : F)) : G) * s := hg
    have hrow : ent s' 1 0 = ent s 1 0 := by rw [← h10, ← h10', hg']
    have h00 : (k' : F) * ent s' 1 0 = (k : F) * ent s 1 0 := by rw [← h1, ← h2, hg']
    rw [hrow] at h00
    have hne : ent s 1 0 ≠ 0 := ent10_ne_zero_of_not_mem hs.1
    have : (k' : F) = (k : F) := mul_right_cancel₀ hne h00
    exact hkk' (Nat.cast_injective this).symm

  by_contra hne
  have htop : μ (⋃ k, Sk k) = ⊤ := by
    rw [measure_iUnion hSk_disj hSk_meas]
    simp_rw [hSk_measure]
    exact ENNReal.tsum_const_eq_top_of_ne_zero hne
  have hle : μ (⋃ k, Sk k) ≤ μ M := measure_mono (Set.iUnion_subset hSk_sub)
  rw [htop, top_le_iff] at hle
  exact hMfin.ne hle

theorem measure_compl_cell_eq_zero (μ : Measure G) [μ.IsHaarMeasure] : μ ((cell : Set G)ᶜ) = 0 := by
  have hcov : (cell : Set G)ᶜ = ⋃ n, (cell : Set G)ᶜ ∩ compactCovering G n := by
    rw [← Set.inter_iUnion, iUnion_compactCovering, Set.inter_univ]
  rw [hcov]
  exact measure_iUnion_null fun n => measure_compl_cell_inter_eq_zero μ (isCompact_compactCovering G n)

end NullComplement

section CoordinateHaar

attribute [local instance] LanglandsTunnell.TateLocal.localBorel LanglandsTunnell.TateLocal.borelSpace_localBorel
  AutomorphicForm.localGLBorel AutomorphicForm.borelSpace_localGLBorel

local notation "Q" => (Coord K v)
local notation "P" => (Pgrp K v)

def wt (q : Q) : ℝ≥0∞ := (modulus (((q.2.2.1 * (q.2.1)⁻¹ : Fˣ)) : F) : ℝ≥0∞)

theorem wt_eq : (wt : Q → ℝ≥0∞) = fun q => (modulus (((q.2.2.1 * (q.2.1)⁻¹ : Fˣ)) : F) : ℝ≥0∞) := rfl

theorem continuous_wt_nnreal : Continuous fun q : Q => (modulus (((q.2.2.1 * (q.2.1)⁻¹ : Fˣ)) : F) : ℝ≥0) := by
  have h : (fun q : Q => (modulus (((q.2.2.1 * (q.2.1)⁻¹ : Fˣ)) : F) : ℝ≥0)) =
      fun q => ‖(((q.2.2.1 * (q.2.1)⁻¹ : Fˣ)) : F)‖₊ := funext fun q => modulus_eq_nnnorm _
  rw [h]
  refine continuous_nnnorm.comp (Units.continuous_val.comp ?_)
  exact (continuous_fst.comp (continuous_snd.comp continuous_snd)).mul (continuous_fst.comp continuous_snd).inv

theorem measurable_wt : Measurable (wt : Q → ℝ≥0∞) :=
  ENNReal.continuous_coe.measurable.comp continuous_wt_nnreal.measurable

theorem wt_ne_zero (q : Q) : wt q ≠ 0 := modulus_units_ne_zero' _

theorem modulus_units_mul (u w : Fˣ) : modulus (((u * w : Fˣ)) : F) = modulus (u : F) * modulus (w : F) := by
  rw [Units.val_mul, modulus_mul]

theorem modulus_units_inv (u : Fˣ) : modulus (((u⁻¹ : Fˣ)) : F) = (modulus (u : F))⁻¹ := by
  have h : modulus (((u⁻¹ : Fˣ)) : F) * modulus (u : F) = 1 := by
    rw [← modulus_units_mul, inv_mul_cancel, Units.val_one, modulus_one]
  exact eq_inv_of_mul_eq_one_left h

def transl (q₀ : Q) : Q → Q :=
  Prod.map (fun y => q₀.1 + y) (Prod.map (fun a => q₀.2.1 * a)
    (Prod.map (fun d => q₀.2.2.1 * d) (fun x => q₀.2.2.2 + ((q₀.2.1 * (q₀.2.2.1)⁻¹ : Fˣ) : F) * x)))

theorem Xi_mul_Xi' (q₀ q : Q) : Xi q₀ * Xi q = Xi (transl q₀ q) := Xi_mul_Xi q₀ q

theorem measurable_transl (q₀ : Q) : Measurable (transl q₀) :=
  (measurable_const_add _).prodMap ((measurable_const_mul _).prodMap ((measurable_const_mul _).prodMap
    ((measurable_const_add _).comp (measurable_const_mul _))))

theorem wt_transl (q₀ q : Q) :
    wt (transl q₀ q) = (modulus (((q₀.2.2.1 * (q₀.2.1)⁻¹ : Fˣ)) : F) : ℝ≥0∞) * wt q := by
  obtain ⟨y₀, a₀, d₀, x₀⟩ := q₀
  obtain ⟨y, a, d, x⟩ := q
  show (modulus ((((d₀ * d) * (a₀ * a)⁻¹ : Fˣ)) : F) : ℝ≥0∞) =
    (modulus (((d₀ * a₀⁻¹ : Fˣ)) : F) : ℝ≥0∞) * (modulus (((d * a⁻¹ : Fˣ)) : F) : ℝ≥0∞)
  rw [← ENNReal.coe_mul, ← modulus_units_mul, mul_inv, mul_mul_mul_comm]

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

def rhoW : Measure Q := (rho ν τ).withDensity wt

def eta : Measure P := Measure.map Xi (rhoW ν τ)

theorem map_transl_rho (q₀ : Q) :
    Measure.map (transl q₀) (rho ν τ) = ((modulus (((q₀.2.1 * (q₀.2.2.1)⁻¹ : Fˣ)) : F) : ℝ≥0∞))⁻¹ • rho ν τ := by
  have hf1 : Measurable fun y : F => q₀.1 + y := measurable_const_add _
  have hf2 : Measurable fun a : Fˣ => q₀.2.1 * a := measurable_const_mul _
  have hf3 : Measurable fun d : Fˣ => q₀.2.2.1 * d := measurable_const_mul _
  have hf4 : Measurable fun x : F => q₀.2.2.2 + ((q₀.2.1 * (q₀.2.2.1)⁻¹ : Fˣ) : F) * x :=
    (measurable_const_add _).comp (measurable_const_mul _)
  have h1 : Measure.map (fun y : F => q₀.1 + y) ν = ν := map_add_left_eq_self ν _
  have h2 : Measure.map (fun a : Fˣ => q₀.2.1 * a) τ = τ := map_mul_left_eq_self τ _
  have h3 : Measure.map (fun d : Fˣ => q₀.2.2.1 * d) τ = τ := map_mul_left_eq_self τ _
  have h4 : Measure.map (fun x : F => q₀.2.2.2 + ((q₀.2.1 * (q₀.2.2.1)⁻¹ : Fˣ) : F) * x) ν =
      ((modulus (((q₀.2.1 * (q₀.2.2.1)⁻¹ : Fˣ)) : F) : ℝ≥0∞))⁻¹ • ν := map_affine_eq_smul ν _ _
  unfold rho transl
  rw [← Measure.map_prod_map _ _ hf1 (hf2.prodMap (hf3.prodMap hf4)), ← Measure.map_prod_map _ _ hf2 (hf3.prodMap hf4),
    ← Measure.map_prod_map _ _ hf3 hf4, h1, h2, h3, h4, Measure.prod_smul_right, Measure.prod_smul_right,
    Measure.prod_smul_right]

theorem map_transl_rhoW (q₀ : Q) : Measure.map (transl q₀) (rhoW ν τ) = rhoW ν τ := by
  set κ : ℝ≥0∞ := (modulus (((q₀.2.2.1 * (q₀.2.1)⁻¹ : Fˣ)) : F) : ℝ≥0∞) with hκ
  set c : ℝ≥0∞ := (modulus (((q₀.2.1 * (q₀.2.2.1)⁻¹ : Fˣ)) : F) : ℝ≥0∞) with hc
  have hκ0 : κ ≠ 0 := modulus_units_ne_zero' _
  have hκtop : κ ≠ ⊤ := ENNReal.coe_ne_top
  have hcκ : c = κ⁻¹ := by
    rw [hc, hκ, ← ENNReal.coe_inv (modulus_units_ne_zero _), ← modulus_units_inv, mul_inv_rev, inv_inv]

  have hfun : (wt : Q → ℝ≥0∞) = ((κ⁻¹ • wt) ∘ transl q₀) := by
    funext q
    simp only [Function.comp_apply, Pi.smul_apply, smul_eq_mul]
    rw [wt_transl, ← hκ, ← mul_assoc, ENNReal.inv_mul_cancel hκ0 hκtop, one_mul]
  unfold rhoW
  conv_lhs => rw [hfun]
  rw [← withDensity_map_eq _ (measurable_transl q₀) (measurable_wt.const_smul _), map_transl_rho,
    withDensity_smul_measure, withDensity_smul _ measurable_wt, ← hc, hcκ, smul_smul, inv_inv,
    ENNReal.mul_inv_cancel hκ0 hκtop, one_smul]

scoped instance sFinite_rhoW : SFinite (rhoW ν τ) := by unfold rhoW rho; infer_instance

scoped instance isOpenPosMeasure_rho : (rho ν τ).IsOpenPosMeasure := by
  haveI : (τ.prod ν).IsOpenPosMeasure := Measure.prod.instIsOpenPosMeasure
  haveI : (τ.prod (τ.prod ν)).IsOpenPosMeasure := Measure.prod.instIsOpenPosMeasure
  unfold rho
  exact Measure.prod.instIsOpenPosMeasure

theorem measurable_Xi : Measurable (Xi : Q → P) := continuous_Xi.measurable

scoped instance isMulLeftInvariant_eta : (eta ν τ).IsMulLeftInvariant := by
  refine ⟨fun p₀ => ?_⟩
  obtain ⟨q₀, rfl⟩ := Xi_surjective p₀
  unfold eta
  rw [Measure.map_map (measurable_const_mul _) measurable_Xi]
  have hcomp : ((fun p : P => Xi q₀ * p) ∘ Xi) = Xi ∘ transl q₀ := funext fun q => Xi_mul_Xi' q₀ q
  rw [hcomp, ← Measure.map_map measurable_Xi (measurable_transl q₀), map_transl_rhoW]

scoped instance isFiniteMeasureOnCompacts_eta : IsFiniteMeasureOnCompacts (eta ν τ) := by
  refine ⟨fun L hL => ?_⟩
  unfold eta
  rw [Measure.map_apply measurable_Xi hL.measurableSet]
  have hLc : IsCompact ((Xi : Q → P) ⁻¹' L) := (XiHomeo (K := K) (v := v)).isCompact_preimage.mpr hL

  obtain ⟨M, hM⟩ := (hLc.image continuous_wt_nnreal).bddAbove
  unfold rhoW
  rw [withDensity_apply _ hLc.measurableSet]
  have hbound : ∀ q ∈ (Xi : Q → P) ⁻¹' L, wt q ≤ (M : ℝ≥0∞) := fun q hq =>
    ENNReal.coe_le_coe.mpr (hM ⟨q, hq, rfl⟩)
  calc ∫⁻ q in (Xi : Q → P) ⁻¹' L, wt q ∂rho ν τ
      ≤ ∫⁻ _ in (Xi : Q → P) ⁻¹' L, (M : ℝ≥0∞) ∂rho ν τ := setLIntegral_mono' hLc.measurableSet hbound
    _ = (M : ℝ≥0∞) * rho ν τ ((Xi : Q → P) ⁻¹' L) := setLIntegral_const _ _
    _ < ⊤ := by
        refine ENNReal.mul_lt_top ENNReal.coe_lt_top ?_
        unfold rho
        exact hLc.measure_lt_top

scoped instance isOpenPosMeasure_eta : (eta ν τ).IsOpenPosMeasure := by
  refine ⟨fun U hU hne => ?_⟩
  unfold eta
  rw [Measure.map_apply measurable_Xi hU.measurableSet]
  have hO : IsOpen ((Xi : Q → P) ⁻¹' U) := hU.preimage continuous_Xi
  have hOne : ((Xi : Q → P) ⁻¹' U).Nonempty := hne.preimage Xi_surjective
  unfold rhoW
  rw [withDensity_apply _ hO.measurableSet]
  intro h0
  rw [lintegral_eq_zero_iff measurable_wt] at h0
  have h1 : ∀ᵐ q ∂(rho ν τ).restrict ((Xi : Q → P) ⁻¹' U), False := by
    filter_upwards [h0] with q hq
    exact wt_ne_zero q hq
  rw [Filter.eventually_false_iff_eq_bot, ae_eq_bot] at h1
  have h2 : rho ν τ ((Xi : Q → P) ⁻¹' U) = 0 := by
    rw [← Measure.restrict_apply_univ, h1]
    rfl
  exact (hO.measure_ne_zero _ hOne) h2

scoped instance isHaarMeasure_eta : (eta ν τ).IsHaarMeasure where

end CoordinateHaar

section PullBack

attribute [local instance] LanglandsTunnell.TateLocal.localBorel LanglandsTunnell.TateLocal.borelSpace_localBorel
  AutomorphicForm.localGLBorel AutomorphicForm.borelSpace_localGLBorel

local notation "Q" => (Coord K v)
local notation "P" => (Pgrp K v)

theorem unip_comm (m n : ↥(unip : Subgroup G)) : m * n = n * m := by
  refine Subtype.ext ?_
  change (m : G) * (n : G) = (n : G) * (m : G)
  rw [unip_eq_unipotentGL2 m, unip_eq_unipotentGL2 n, ← unipotentGL2_add, ← unipotentGL2_add, add_comm]

theorem measurable_mulMap : Measurable (mulMap : P → G) := continuous_mulMap.measurable

variable (μ : Measure (GL (Fin 2) (HeightOneSpectrum.adicCompletion K v))) [μ.IsHaarMeasure]

def lam : Measure P := Measure.map sect (μ.restrict cell)

theorem sect_preimage_inter_cell (S : Set P) : sect ⁻¹' S ∩ (cell : Set G) = mulMap '' S := by
  ext g
  constructor
  · rintro ⟨hgS, hgC⟩
    exact ⟨sect g, hgS, mulMap_sect hgC⟩
  · rintro ⟨bn, hbn, rfl⟩
    exact ⟨by rw [Set.mem_preimage, sect_mulMap]; exact hbn, mulMap_mem_cell bn⟩

omit [μ.IsHaarMeasure] in
theorem lam_apply {S : Set P} (hS : MeasurableSet S) : lam μ S = μ (mulMap '' S) := by
  unfold lam
  rw [Measure.map_apply measurable_sect hS, Measure.restrict_apply (measurable_sect hS), sect_preimage_inter_cell]

scoped instance isFiniteMeasureOnCompacts_lam : IsFiniteMeasureOnCompacts (lam μ) := by
  refine ⟨fun L hL => ?_⟩
  rw [lam_apply μ hL.measurableSet]
  exact (hL.image continuous_mulMap).measure_lt_top

def twoSided (p₀ : P) (g : G) : G := (p₀.1 : G) * g * (p₀.2 : G)

theorem measurable_twoSided (p₀ : P) : Measurable (twoSided p₀) :=
  ((continuous_const.mul continuous_id).mul continuous_const).measurable

theorem twoSided_mulMap (p₀ bn : P) : twoSided p₀ (mulMap bn) = mulMap (p₀ * bn) := by
  obtain ⟨b₀, n₀⟩ := p₀
  obtain ⟨b, n⟩ := bn
  simp only [twoSided, mulMap, Prod.mk_mul_mk, Subgroup.coe_mul]
  have h := congrArg Subtype.val (unip_comm n₀ n)
  simp only [Subgroup.coe_mul] at h
  rw [h]
  simp only [mul_assoc]

theorem twoSided_preimage_cell (p₀ : P) : twoSided p₀ ⁻¹' (cell : Set G) = cell := by
  ext g
  simp only [Set.mem_preimage, mem_cell_iff]
  constructor
  · rintro ⟨bn, hbn⟩
    refine ⟨p₀⁻¹ * bn, ?_⟩
    have h := twoSided_mulMap p₀ (p₀⁻¹ * bn)
    rw [mul_inv_cancel_left, hbn] at h

    have hinj : Function.Injective (twoSided p₀) := fun x y hxy => by
      simpa [twoSided, mul_assoc] using hxy
    exact hinj h
  · rintro ⟨bn, rfl⟩
    exact ⟨p₀ * bn, (twoSided_mulMap p₀ bn).symm⟩

theorem map_twoSided [μ.IsMulRightInvariant] (p₀ : P) : Measure.map (twoSided p₀) μ = μ := by
  have h : twoSided p₀ = (fun g : G => g * (p₀.2 : G)) ∘ fun g : G => (p₀.1 : G) * g := rfl
  rw [h, ← Measure.map_map (measurable_mul_const _) (measurable_const_mul _), map_mul_left_eq_self,
    map_mul_right_eq_self]

theorem map_twoSided_restrict [μ.IsMulRightInvariant] (p₀ : P) :
    Measure.map (twoSided p₀) (μ.restrict cell) = μ.restrict cell := by
  refine Measure.ext fun s hs => ?_
  rw [Measure.map_apply (measurable_twoSided p₀) hs, Measure.restrict_apply (measurable_twoSided p₀ hs),
    Measure.restrict_apply hs]
  conv_lhs => rw [← twoSided_preimage_cell p₀, ← Set.preimage_inter, ← Measure.map_apply (measurable_twoSided p₀)
    (hs.inter measurableSet_cell), map_twoSided]

theorem isMulLeftInvariant_lam [μ.IsMulRightInvariant] : (lam μ).IsMulLeftInvariant := by
  refine ⟨fun p₀ => ?_⟩
  unfold lam
  rw [Measure.map_map (measurable_const_mul _) measurable_sect]
  have hae : ((fun p : P => p₀ * p) ∘ sect) =ᵐ[μ.restrict cell] (sect ∘ twoSided p₀) := by
    refine (ae_restrict_mem measurableSet_cell).mono fun g hg => ?_
    simp only [Function.comp_apply]
    apply mulMap_injective
    rw [← twoSided_mulMap, mulMap_sect hg, mulMap_sect]
    rw [← twoSided_preimage_cell p₀] at hg
    exact hg
  rw [Measure.map_congr hae, ← Measure.map_map measurable_sect (measurable_twoSided p₀), map_twoSided_restrict]

theorem lam_univ_ne_zero : lam μ Set.univ ≠ 0 := by
  rw [lam_apply μ MeasurableSet.univ]
  have h : mulMap '' (Set.univ : Set P) = cell := by
    ext g
    simp only [Set.mem_image, Set.mem_univ, true_and]
    exact (mem_cell_iff g).symm
  rw [h]
  exact isOpen_cell.measure_ne_zero μ ⟨1, show ent (1 : G) 0 0 ≠ 0 by simp [ent]⟩

theorem map_mulMap_lam : Measure.map mulMap (lam μ) = μ := by
  unfold lam
  rw [Measure.map_map measurable_mulMap measurable_sect]
  have hae : (mulMap ∘ sect) =ᵐ[μ.restrict cell] id :=
    (ae_restrict_mem measurableSet_cell).mono fun g hg => mulMap_sect hg
  rw [Measure.map_congr hae, Measure.map_id]
  exact Measure.restrict_eq_self_of_ae_mem (mem_ae_iff.mpr (measure_compl_cell_eq_zero μ))

end PullBack

section Assembly

attribute [local instance] LanglandsTunnell.TateLocal.localBorel LanglandsTunnell.TateLocal.borelSpace_localBorel
  AutomorphicForm.localGLBorel AutomorphicForm.borelSpace_localGLBorel

local notation "Q" => (Coord K v)
local notation "P" => (Pgrp K v)

theorem mulMap_comp_Xi : (mulMap ∘ Xi : Q → G) = cellMap := funext mulMap_Xi

theorem main (μ : Measure G) [μ.IsHaarMeasure] (τ : Measure Fˣ) [τ.IsHaarMeasure]
    (ν : Measure F) [ν.IsAddHaarMeasure] :
    ∃ c : ℝ≥0∞, c ≠ 0 ∧ c ≠ ⊤ ∧ μ = c • Measure.map cellMap (rhoW ν τ) := by
  haveI : μ.IsMulRightInvariant :=
    (Matrix.GeneralLinearGroup.isMulRightInvariant_and_isInvInvariant_of_isHaarMeasure_fin_two μ).1
  haveI : (lam μ).IsMulLeftInvariant := isMulLeftInvariant_lam μ
  set c : ℝ≥0 := (lam μ).haarScalarFactor (eta ν τ) with hc
  have hlam : lam μ = c • eta ν τ := Measure.isMulLeftInvariant_eq_smul _ _
  have hc0 : (c : ℝ≥0∞) ≠ 0 := by
    intro h
    have hc' : c = 0 := ENNReal.coe_eq_zero.mp h
    apply lam_univ_ne_zero μ
    rw [hlam, hc', zero_smul]
    rfl
  refine ⟨c, hc0, ENNReal.coe_ne_top, ?_⟩
  calc μ = Measure.map mulMap (lam μ) := (map_mulMap_lam μ).symm
    _ = Measure.map mulMap (c • eta ν τ) := by rw [hlam]
    _ = (c : ℝ≥0∞) • Measure.map cellMap (rhoW ν τ) := by
        unfold eta
        rw [Measure.map_smul, Measure.map_map measurable_mulMap measurable_Xi, mulMap_comp_Xi]
        rfl

end Assembly

end BruhatCellHaar
p2m_reactivate "P2MW.S_AutomorphicForm_exists_haar_localGL2_eq_smul_map_lowerUnipotentGL2_mul_diagUnits2_mul_unipotentGL2.BruhatCellHaar"

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
          lowerUnipotentGL2 q.2.2.2 * diagUnits2 q.2.2.1 q.2.1 * unipotentGL2 q.1)
        ((ν.prod (τ.prod (τ.prod ν))).withDensity fun q =>
          (modulus (((q.2.2.1 * (q.2.1)⁻¹ : (v.adicCompletion K)ˣ)) : v.adicCompletion K) : ℝ≥0∞)) := by
  intro μ _ τ _ ν _
  exact BruhatCellHaar.main μ τ ν

end
p2m_reactivate "P2MW.S_AutomorphicForm_exists_haar_localGL2_eq_smul_map_lowerUnipotentGL2_mul_diagUnits2_mul_unipotentGL2.BruhatCellHaar"

end S_AutomorphicForm_exists_haar_localGL2_eq_smul_map_lowerUnipotentGL2_mul_diagUnits2_mul_unipotentGL2
end P2MW
export P2MW.S_AutomorphicForm_exists_haar_localGL2_eq_smul_map_lowerUnipotentGL2_mul_diagUnits2_mul_unipotentGL2 (solution)

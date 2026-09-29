-- Prove2me | solution 1 for AutomorphicForm.exists_continuous_hasCompactSupport_eq_of_isWeightedOrbitalIntegralOn_scalar_mul_diagUnits2
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/6dcadaa8-6272-5bba-a0b6-5fa03c7cc0f1

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_NumberField_AdelicHaar
import Definitions.Def_NumberField_AdelicLevel
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_NumberField_IdeleProductMeasure
import Definitions.Def_LocalLanglands_HeckeCosetLocal
import Definitions.Def_LocalLanglands_HeckeCosetSystem
import Definitions.Def_AutomorphicForm_LocalOrbitalBase
import Definitions.Def_AutomorphicForm_SatakeCombinationCoeff
import Definitions.Def_AutomorphicForm_WindingDatum
import Definitions.Def_LanglandsTunnell_CubicInduction_TorusValues
import Definitions.Def_AutomorphicForm_WeightedOrbitalRelation
import Definitions.Def_AutomorphicForm_BaseChangePlaces
import Definitions.Def_NumberField_AdelicHeight
import Definitions.Def_AutomorphicForm_WeylIntertwining
import Definitions.Def_UnramifiedWhittaker_ZetaIntegrand
import Definitions.Def_M4aHerbrand_GenuineDescent
import Definitions.Def_NumberField_IdeleBox
import Definitions.Def_AutomorphicForm_RowIsometryInvariance
import Definitions.Def_AutomorphicForm_ConstantTerm
import Definitions.Def_AutomorphicForm_FactorizableTestFn
import Definitions.Def_NumberField_AdelicBox
import Theorems.Thm_AutomorphicForm_exists_pos_forall_prod_norm_sub_one_pow_mul_eq_and_weighted_eq_mul_prod_norm_pow_mul_integral_integral_of_scalar_mul_diagUnits2
import Theorems.Thm_AutomorphicForm_WindowedSiegel_sum_mult_mul_log_topNormSq_mul_rowNormSq_div_eq_neg_log_archHeight_sub_log_archHeight_weyl_mul
import Theorems.Thm_MeasureTheory_contDiff_integral_smul_comp_of_contDiff_of_hasCompactSupport
import Theorems.Thm_NumberField_InfiniteAdeleRing_exists_mem_borelSubgroup_mul_eq_and_isCompact_iInf_rowIsometrySubgroup
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_continuous_hasCompactSupport_eq_of_isWeightedOrbitalIntegralOn_scalar_mul_diagUnits2
p2m_attr_erase "instance" "instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions"
p2m_attr_erase "simp" "ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply"

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option synthInstance.maxSize 8192

open MeasureTheory NumberField NumberField.AdelicLevel IsDedekindDomain
open scoped ENNReal

attribute [local instance] AutomorphicForm.centralizerBorel

open LanglandsTunnell.CubicInduction (diagUnits2)

noncomputable section

namespace SmoothWindow

open AutomorphicForm
open scoped Classical

variable (K : Type) [Field K] [NumberField K]

local notation "MS" => mixedEmbedding.mixedSpace K
local notation "Kinf" => InfiniteAdeleRing K
local notation "GA" => GL (Fin 2) (InfiniteAdeleRing K)

section Coords

variable {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X]

theorem contDiff_ms {f : X → MS}
    (h1 : ∀ i, ContDiff ℝ (⊤ : ℕ∞) fun x => (f x).1 i)
    (h2 : ∀ i, ContDiff ℝ (⊤ : ℕ∞) fun x => (f x).2 i) : ContDiff ℝ (⊤ : ℕ∞) f := by
  have hf : f = fun x => ((fun i => (f x).1 i), (fun i => (f x).2 i)) := rfl
  rw [hf]
  exact (contDiff_pi.mpr h1).prodMk (contDiff_pi.mpr h2)

theorem contDiff_fst_apply (i : {w : InfinitePlace K // w.IsReal}) :
    ContDiff ℝ (⊤ : ℕ∞) fun q : MS => q.1 i :=
  (contDiff_apply ℝ ℝ i).comp contDiff_fst

theorem contDiff_snd_apply (i : {w : InfinitePlace K // w.IsComplex}) :
    ContDiff ℝ (⊤ : ℕ∞) fun q : MS => q.2 i :=
  (contDiff_apply ℝ ℂ i).comp contDiff_snd

theorem contDiff_ms_mul {f g : X → MS} (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hg : ContDiff ℝ (⊤ : ℕ∞) g) :
    ContDiff ℝ (⊤ : ℕ∞) fun x => f x * g x := by
  refine contDiff_ms K (fun i => ?_) (fun i => ?_)
  · show ContDiff ℝ (⊤ : ℕ∞) fun x => (f x).1 i * (g x).1 i
    exact ((contDiff_fst_apply K i).comp hf).mul ((contDiff_fst_apply K i).comp hg)
  · show ContDiff ℝ (⊤ : ℕ∞) fun x => (f x).2 i * (g x).2 i
    exact ((contDiff_snd_apply K i).comp hf).mul ((contDiff_snd_apply K i).comp hg)

end Coords

def Mmat (p : Fin 2 → MS) (xm : MS) : Fin 2 → Fin 2 → MS :=
  ![![p 1 * p 0, p 1 * p 0 * xm], ![0, p 1]]

def conjM (A B M : Fin 2 → Fin 2 → MS) : Fin 2 → Fin 2 → MS :=
  fun i j => ∑ l, ∑ r, B i l * M l r * A r j

theorem contDiff_conjM_Mmat :
    ContDiff ℝ (⊤ : ℕ∞) fun q : (MS × (Fin 2 → Fin 2 → MS) × (Fin 2 → Fin 2 → MS)) × (Fin 2 → MS) =>
      conjM K q.1.2.1 q.1.2.2 (Mmat K q.2 q.1.1) := by
  refine contDiff_pi.mpr fun i => contDiff_pi.mpr fun j => ?_
  show ContDiff ℝ (⊤ : ℕ∞) fun q : (MS × (Fin 2 → Fin 2 → MS) × (Fin 2 → Fin 2 → MS)) × (Fin 2 → MS) =>
    ∑ l, ∑ r, q.1.2.2 i l * Mmat K q.2 q.1.1 l r * q.1.2.1 r j
  refine ContDiff.sum fun l _ => ContDiff.sum fun r _ => ?_
  have hA : ContDiff ℝ (⊤ : ℕ∞) fun q : (MS × (Fin 2 → Fin 2 → MS) × (Fin 2 → Fin 2 → MS)) × (Fin 2 → MS) =>
      q.1.2.1 r j :=
    (contDiff_apply_apply ℝ _ r j).comp (contDiff_fst.comp (contDiff_snd.comp contDiff_fst))
  have hB : ContDiff ℝ (⊤ : ℕ∞) fun q : (MS × (Fin 2 → Fin 2 → MS) × (Fin 2 → Fin 2 → MS)) × (Fin 2 → MS) =>
      q.1.2.2 i l :=
    (contDiff_apply_apply ℝ _ i l).comp (contDiff_snd.comp (contDiff_snd.comp contDiff_fst))
  have hx : ContDiff ℝ (⊤ : ℕ∞) fun q : (MS × (Fin 2 → Fin 2 → MS) × (Fin 2 → Fin 2 → MS)) × (Fin 2 → MS) =>
      q.1.1 := contDiff_fst.comp contDiff_fst
  have hp : ∀ a : Fin 2, ContDiff ℝ (⊤ : ℕ∞)
      fun q : (MS × (Fin 2 → Fin 2 → MS) × (Fin 2 → Fin 2 → MS)) × (Fin 2 → MS) => q.2 a :=
    fun a => (contDiff_apply ℝ _ a).comp contDiff_snd
  have hM : ContDiff ℝ (⊤ : ℕ∞)
      fun q : (MS × (Fin 2 → Fin 2 → MS) × (Fin 2 → Fin 2 → MS)) × (Fin 2 → MS) => Mmat K q.2 q.1.1 l r := by
    fin_cases l <;> fin_cases r
    · show ContDiff ℝ (⊤ : ℕ∞) fun q : (MS × (Fin 2 → Fin 2 → MS) × (Fin 2 → Fin 2 → MS)) × (Fin 2 → MS) =>
        q.2 1 * q.2 0
      exact contDiff_ms_mul K (hp 1) (hp 0)
    · show ContDiff ℝ (⊤ : ℕ∞) fun q : (MS × (Fin 2 → Fin 2 → MS) × (Fin 2 → Fin 2 → MS)) × (Fin 2 → MS) =>
        q.2 1 * q.2 0 * q.1.1
      exact contDiff_ms_mul K (contDiff_ms_mul K (hp 1) (hp 0)) hx
    · show ContDiff ℝ (⊤ : ℕ∞) fun q : (MS × (Fin 2 → Fin 2 → MS) × (Fin 2 → Fin 2 → MS)) × (Fin 2 → MS) =>
        (0 : MS)
      exact contDiff_const
    · show ContDiff ℝ (⊤ : ℕ∞) fun q : (MS × (Fin 2 → Fin 2 → MS) × (Fin 2 → Fin 2 → MS)) × (Fin 2 → MS) =>
        q.2 1
      exact hp 1
  exact contDiff_ms_mul K (contDiff_ms_mul K hB hM) hA

theorem conjM_archEntries (k : GA) (u z : (Kinf)ˣ) (x : Kinf) :
    conjM K (archEntries K k) (archEntries K k⁻¹)
        (Mmat K ![InfiniteAdeleRing.ringEquiv_mixedSpace K (u : Kinf), InfiniteAdeleRing.ringEquiv_mixedSpace K (z : Kinf)]
          (InfiniteAdeleRing.ringEquiv_mixedSpace K x)) =
      archEntries K (k⁻¹ * (Matrix.GeneralLinearGroup.scalar (Fin 2) z * diagUnits2 u 1 * unipotentGL2 x) * k) := by
  have hM : ((Matrix.GeneralLinearGroup.scalar (Fin 2) z * diagUnits2 u 1 * unipotentGL2 x : GA) :
      Matrix (Fin 2) (Fin 2) Kinf) = !![(z : Kinf) * u, (z : Kinf) * u * x; 0, (z : Kinf)] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [diagUnits2, unipotentGL2, Matrix.GeneralLinearGroup.scalar, Matrix.mul_apply, Fin.sum_univ_two]
  have hMm : ∀ l r, Mmat K ![InfiniteAdeleRing.ringEquiv_mixedSpace K (u : Kinf),
        InfiniteAdeleRing.ringEquiv_mixedSpace K (z : Kinf)] (InfiniteAdeleRing.ringEquiv_mixedSpace K x) l r =
      InfiniteAdeleRing.ringEquiv_mixedSpace K
        (((Matrix.GeneralLinearGroup.scalar (Fin 2) z * diagUnits2 u 1 * unipotentGL2 x : GA) :
          Matrix (Fin 2) (Fin 2) Kinf) l r) := by
    intro l r
    rw [hM]
    fin_cases l <;> fin_cases r <;>
      simp only [Fin.zero_eta, Fin.mk_one, Mmat, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.head_cons, Matrix.head_fin_const, map_mul, map_zero]
  funext i j
  simp only [conjM, archEntries_apply, hMm, ← map_mul, ← map_sum]
  congr 1
  rw [Finset.sum_comm]
  simp only [Units.val_mul, Matrix.mul_apply, Finset.sum_mul]

section Topology

theorem secondCountableTopology_infiniteAdeleRing : SecondCountableTopology Kinf := by
  haveI : ∀ w : InfinitePlace K, SecondCountableTopology w.Completion := fun w =>
    (InfinitePlace.Completion.isometry_extensionEmbedding w).isEmbedding.secondCountableTopology
  exact inferInstanceAs (SecondCountableTopology ((w : InfinitePlace K) → w.Completion))

theorem secondCountableTopology_gl : SecondCountableTopology GA := by
  haveI := secondCountableTopology_infiniteAdeleRing K
  haveI : SecondCountableTopology (Matrix (Fin 2) (Fin 2) Kinf) :=
    inferInstanceAs (SecondCountableTopology (Fin 2 → Fin 2 → Kinf))
  haveI : SecondCountableTopology (Matrix (Fin 2) (Fin 2) Kinf)ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.isInducing.secondCountableTopology
  exact Units.isInducing_embedProduct.secondCountableTopology

theorem t2Space_gl : T2Space GA := by
  haveI : T2Space (Matrix (Fin 2) (Fin 2) Kinf) := inferInstanceAs (T2Space (Fin 2 → Fin 2 → Kinf))
  exact Units.isEmbedding_embedProduct.t2Space

def iotaHomeo : Kinf ≃ₜ MS := by
  haveI := secondCountableTopology_infiniteAdeleRing K
  exact (InfiniteAdeleRing.ringEquiv_mixedSpace K).toEquiv.toHomeomorphOfContinuousOpen
    (AdelicBox.continuous_ringEquiv_mixedSpace K)
    ((InfiniteAdeleRing.ringEquiv_mixedSpace K).toAddMonoidHom.isOpenMap_of_sigmaCompact
      (InfiniteAdeleRing.ringEquiv_mixedSpace K).surjective (AdelicBox.continuous_ringEquiv_mixedSpace K))

theorem iotaHomeo_apply (x : Kinf) : iotaHomeo K x = InfiniteAdeleRing.ringEquiv_mixedSpace K x := rfl

theorem continuous_iota_symm : Continuous (InfiniteAdeleRing.ringEquiv_mixedSpace K).symm := by
  have h : ⇑(InfiniteAdeleRing.ringEquiv_mixedSpace K).symm = ⇑(iotaHomeo K).symm := by
    funext y
    apply (InfiniteAdeleRing.ringEquiv_mixedSpace K).injective
    rw [RingEquiv.apply_symm_apply]
    exact ((iotaHomeo K).apply_symm_apply y).symm
  rw [h]
  exact (iotaHomeo K).symm.continuous

omit [NumberField K] in
theorem isUnit_iff_forall_ne_zero (y : Kinf) : IsUnit y ↔ ∀ w : InfinitePlace K, y w ≠ 0 := by
  have h := @Pi.isUnit_iff (InfinitePlace K) (fun w => w.Completion) _ y
  exact h.trans (forall_congr' fun w => isUnit_iff_ne_zero)

theorem isOpen_setOf_isUnit : IsOpen {y : Kinf | IsUnit y} := by
  have h : {y : Kinf | IsUnit y} = ⋂ w : InfinitePlace K, {y | y w ≠ 0} := by
    ext y; simp [isUnit_iff_forall_ne_zero]
  rw [h]
  exact isOpen_iInter_of_finite fun w => isOpen_ne_fun (continuous_apply w) continuous_const

def Uunits : Set (Fin 2 → MS) :=
  {p | IsUnit ((InfiniteAdeleRing.ringEquiv_mixedSpace K).symm (p 0)) ∧
    IsUnit ((InfiniteAdeleRing.ringEquiv_mixedSpace K).symm (p 1))}

theorem isOpen_Uunits : IsOpen (Uunits K) :=
  ((isOpen_setOf_isUnit K).preimage ((continuous_iota_symm K).comp (continuous_apply 0))).inter
    ((isOpen_setOf_isUnit K).preimage ((continuous_iota_symm K).comp (continuous_apply 1)))

end Topology

section Bump

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

omit K in
theorem exists_smooth_bump {S U : Set E} (hS : IsCompact S) (hU : IsOpen U) (hSU : S ⊆ U) :
    ∃ χ : E → ℝ, ContDiff ℝ (⊤ : ℕ∞) χ ∧ HasCompactSupport χ ∧ (∀ x ∈ S, χ x = 1) ∧ tsupport χ ⊆ U := by
  obtain ⟨R, hR⟩ := hS.isBounded.subset_ball 0
  set U' : Set E := U ∩ Metric.ball 0 R with hU'
  have hU'o : IsOpen U' := hU.inter Metric.isOpen_ball
  have hd : Disjoint U'ᶜ S := by
    rw [Set.disjoint_left]
    intro x hx hxS
    exact hx ⟨hSU hxS, hR hxS⟩
  obtain ⟨f, hf0, hf1, -⟩ := exists_contMDiffMap_zero_one_nhds_of_isClosed
    (modelWithCornersSelf ℝ E) (n := (⊤ : ℕ∞)) hU'o.isClosed_compl hS.isClosed hd
  obtain ⟨V, hVo, hsV, hV⟩ := eventually_nhdsSet_iff_exists.mp hf0
  have hts : tsupport (⇑f) ⊆ U' := by
    refine (closure_minimal (fun x hx => ?_) hVo.isClosed_compl).trans (Set.compl_subset_comm.mp hsV)
    exact fun hxV => hx (hV x hxV)
  refine ⟨f, contMDiff_iff_contDiff.mp f.contMDiff, ?_, fun x hx => hf1.self_of_nhdsSet x hx,
    hts.trans Set.inter_subset_left⟩
  exact IsCompact.of_isClosed_subset (isCompact_closedBall 0 R) (isClosed_tsupport _)
    (hts.trans (Set.inter_subset_right.trans Metric.ball_subset_closedBall))

end Bump

section Theta

def theta (u z : (Kinf)ˣ) (x : Kinf) : GA :=
  Matrix.GeneralLinearGroup.scalar (Fin 2) z * diagUnits2 u 1 * unipotentGL2 x

omit [NumberField K] in
theorem coe_theta (u z : (Kinf)ˣ) (x : Kinf) :
    ((theta K u z x : GA) : Matrix (Fin 2) (Fin 2) Kinf) = !![(z : Kinf) * u, (z : Kinf) * u * x; 0, (z : Kinf)] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [theta, diagUnits2, unipotentGL2, Matrix.GeneralLinearGroup.scalar, Matrix.mul_apply, Fin.sum_univ_two]

omit [NumberField K] in

theorem inv_entries_of_upper {g : GA} (hg : (g : Matrix (Fin 2) (Fin 2) Kinf) 1 0 = 0) :
    ((g⁻¹ : GA) : Matrix (Fin 2) (Fin 2) Kinf) 0 0 * (g : Matrix (Fin 2) (Fin 2) Kinf) 0 0 = 1 ∧
    ((g⁻¹ : GA) : Matrix (Fin 2) (Fin 2) Kinf) 1 1 * (g : Matrix (Fin 2) (Fin 2) Kinf) 1 1 = 1 := by
  have h1 : ((g⁻¹ * g : GA) : Matrix (Fin 2) (Fin 2) Kinf) = 1 := by rw [inv_mul_cancel]; rfl
  have hdet : IsUnit ((g : Matrix (Fin 2) (Fin 2) Kinf) 0 0 * (g : Matrix (Fin 2) (Fin 2) Kinf) 1 1) := by
    have hd : IsUnit ((g : Matrix (Fin 2) (Fin 2) Kinf).det) := (g : GA).isUnit.map Matrix.detMonoidHom
    rw [Matrix.det_fin_two, hg, mul_zero, sub_zero] at hd
    exact hd
  obtain ⟨h00u, h11u⟩ := IsUnit.mul_iff.mp hdet
  have e10 : ((g⁻¹ : GA) : Matrix (Fin 2) (Fin 2) Kinf) 1 0 * (g : Matrix (Fin 2) (Fin 2) Kinf) 0 0 = 0 := by
    have h := congrFun (congrFun h1 1) 0
    rw [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two, hg, mul_zero, add_zero, Matrix.one_apply_ne (by decide)] at h
    exact h
  have e10' : ((g⁻¹ : GA) : Matrix (Fin 2) (Fin 2) Kinf) 1 0 = 0 := by
    obtain ⟨a, ha⟩ := h00u
    rw [← ha] at e10
    have := congrArg (· * (a⁻¹ : (Kinf)ˣ).val) e10
    simpa [mul_assoc] using this
  refine ⟨?_, ?_⟩
  · have h := congrFun (congrFun h1 0) 0
    rw [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two, hg, mul_zero, add_zero, Matrix.one_apply_eq] at h
    exact h
  · have h := congrFun (congrFun h1 1) 1
    rw [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two, e10', zero_mul, zero_add, Matrix.one_apply_eq] at h
    exact h

def Lam (g : GA) : Fin 2 → MS :=
  ![InfiniteAdeleRing.ringEquiv_mixedSpace K ((g : Matrix (Fin 2) (Fin 2) Kinf) 0 0 *
      ((g⁻¹ : GA) : Matrix (Fin 2) (Fin 2) Kinf) 1 1),
    InfiniteAdeleRing.ringEquiv_mixedSpace K ((g : Matrix (Fin 2) (Fin 2) Kinf) 1 1)]

def LamX (g : GA) : MS :=
  InfiniteAdeleRing.ringEquiv_mixedSpace K ((g : Matrix (Fin 2) (Fin 2) Kinf) 0 1 *
      ((g⁻¹ : GA) : Matrix (Fin 2) (Fin 2) Kinf) 0 0)

theorem continuous_Lam : Continuous (Lam K) := by
  refine continuous_pi fun i => ?_
  fin_cases i
  · show Continuous fun g : GA => InfiniteAdeleRing.ringEquiv_mixedSpace K
      ((g : Matrix (Fin 2) (Fin 2) Kinf) 0 0 * ((g⁻¹ : GA) : Matrix (Fin 2) (Fin 2) Kinf) 1 1)
    exact (AdelicBox.continuous_ringEquiv_mixedSpace K).comp
      ((Units.continuous_val.matrix_elem 0 0).mul (Units.continuous_coe_inv.matrix_elem 1 1))
  · show Continuous fun g : GA => InfiniteAdeleRing.ringEquiv_mixedSpace K ((g : Matrix (Fin 2) (Fin 2) Kinf) 1 1)
    exact (AdelicBox.continuous_ringEquiv_mixedSpace K).comp (Units.continuous_val.matrix_elem 1 1)

theorem continuous_LamX : Continuous (LamX K) :=
  (AdelicBox.continuous_ringEquiv_mixedSpace K).comp
    ((Units.continuous_val.matrix_elem 0 1).mul (Units.continuous_coe_inv.matrix_elem 0 0))

omit [NumberField K] in
theorem theta_one_zero (u z : (Kinf)ˣ) (x : Kinf) :
    ((theta K u z x : GA) : Matrix (Fin 2) (Fin 2) Kinf) 1 0 = 0 := by
  rw [coe_theta]; rfl

theorem Lam_theta (u z : (Kinf)ˣ) (x : Kinf) :
    Lam K (theta K u z x) =
      ![InfiniteAdeleRing.ringEquiv_mixedSpace K (u : Kinf), InfiniteAdeleRing.ringEquiv_mixedSpace K (z : Kinf)] := by
  obtain ⟨-, h11⟩ := inv_entries_of_upper K (theta_one_zero K u z x)
  have e00 : ((theta K u z x : GA) : Matrix (Fin 2) (Fin 2) Kinf) 0 0 = (z : Kinf) * u := by rw [coe_theta]; rfl
  have e11 : ((theta K u z x : GA) : Matrix (Fin 2) (Fin 2) Kinf) 1 1 = (z : Kinf) := by rw [coe_theta]; rfl
  rw [e11] at h11
  have hinv : (((theta K u z x)⁻¹ : GA) : Matrix (Fin 2) (Fin 2) Kinf) 1 1 = ((z⁻¹ : (Kinf)ˣ) : Kinf) := by
    calc (((theta K u z x)⁻¹ : GA) : Matrix (Fin 2) (Fin 2) Kinf) 1 1
        = (((theta K u z x)⁻¹ : GA) : Matrix (Fin 2) (Fin 2) Kinf) 1 1 * ((z : Kinf) * ((z⁻¹ : (Kinf)ˣ) : Kinf)) := by
          rw [Units.mul_inv, mul_one]
      _ = ((z⁻¹ : (Kinf)ˣ) : Kinf) := by rw [← mul_assoc, h11, one_mul]
  unfold Lam
  rw [e00, e11, hinv]
  congr 1
  · congr 1
    rw [mul_comm ((z : Kinf)) (u : Kinf), mul_assoc, Units.mul_inv, mul_one]

theorem LamX_theta (u z : (Kinf)ˣ) (x : Kinf) :
    LamX K (theta K u z x) = InfiniteAdeleRing.ringEquiv_mixedSpace K x := by
  obtain ⟨h00, -⟩ := inv_entries_of_upper K (theta_one_zero K u z x)
  have e00 : ((theta K u z x : GA) : Matrix (Fin 2) (Fin 2) Kinf) 0 0 = (z : Kinf) * u := by rw [coe_theta]; rfl
  have e01 : ((theta K u z x : GA) : Matrix (Fin 2) (Fin 2) Kinf) 0 1 = (z : Kinf) * u * x := by rw [coe_theta]; rfl
  unfold LamX
  rw [e01]
  congr 1
  calc (z : Kinf) * u * x * (((theta K u z x)⁻¹ : GA) : Matrix (Fin 2) (Fin 2) Kinf) 0 0
      = x * ((((theta K u z x)⁻¹ : GA) : Matrix (Fin 2) (Fin 2) Kinf) 0 0 *
          ((theta K u z x : GA) : Matrix (Fin 2) (Fin 2) Kinf) 0 0) := by rw [e00]; ring
    _ = x := by rw [h00, mul_one]

theorem Lam_mem_Uunits {g : GA} (hg : (g : Matrix (Fin 2) (Fin 2) Kinf) 1 0 = 0) : Lam K g ∈ Uunits K := by
  obtain ⟨h00, h11⟩ := inv_entries_of_upper K hg
  have hdet : IsUnit ((g : Matrix (Fin 2) (Fin 2) Kinf) 0 0 * (g : Matrix (Fin 2) (Fin 2) Kinf) 1 1) := by
    have hd : IsUnit ((g : Matrix (Fin 2) (Fin 2) Kinf).det) := (g : GA).isUnit.map Matrix.detMonoidHom
    rw [Matrix.det_fin_two, hg, mul_zero, sub_zero] at hd
    exact hd
  obtain ⟨h00u, h11u⟩ := IsUnit.mul_iff.mp hdet
  have hi11 : IsUnit (((g⁻¹ : GA) : Matrix (Fin 2) (Fin 2) Kinf) 1 1) :=
    isUnit_iff_exists_inv.mpr ⟨_, h11⟩
  refine ⟨?_, ?_⟩
  · show IsUnit ((InfiniteAdeleRing.ringEquiv_mixedSpace K).symm (Lam K g 0))
    simp only [Lam, Matrix.cons_val_zero, RingEquiv.symm_apply_apply]
    exact h00u.mul hi11
  · show IsUnit ((InfiniteAdeleRing.ringEquiv_mixedSpace K).symm (Lam K g 1))
    simp only [Lam, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_zero, Matrix.cons_val_fin_one,
      RingEquiv.symm_apply_apply]
    exact h11u

theorem continuous_archEntries' : Continuous (archEntries K : GA → Fin 2 → Fin 2 → MS) :=
  continuous_pi fun i => continuous_pi fun j =>
    (AdelicBox.continuous_ringEquiv_mixedSpace K).comp (Units.continuous_val.matrix_elem i j)

end Theta

section NormFactor

def sqw (w : InfinitePlace K) (q : MS) : ℝ :=
  if hw : w.IsReal then (q.1 ⟨w, hw⟩) ^ 2
  else ‖q.2 ⟨w, NumberField.InfinitePlace.not_isReal_iff_isComplex.mp hw⟩‖ ^ 2

theorem contDiff_sqw (w : InfinitePlace K) : ContDiff ℝ (⊤ : ℕ∞) (sqw K w) := by
  by_cases hw : w.IsReal
  · have : sqw K w = fun q => (q.1 ⟨w, hw⟩) ^ 2 := funext fun q => dif_pos hw
    rw [this]
    exact (contDiff_fst_apply K ⟨w, hw⟩).pow 2
  · have : sqw K w = fun q => ‖q.2 ⟨w, NumberField.InfinitePlace.not_isReal_iff_isComplex.mp hw⟩‖ ^ 2 :=
      funext fun q => dif_neg hw
    rw [this]
    exact (contDiff_norm_sq ℝ).comp (contDiff_snd_apply K _)

theorem sqw_iota (w : InfinitePlace K) (y : Kinf) :
    sqw K w (InfiniteAdeleRing.ringEquiv_mixedSpace K y) = ‖y w‖ ^ 2 := by
  rw [InfiniteAdeleRing.ringEquiv_mixedSpace_apply]
  by_cases hw : w.IsReal
  · rw [sqw, dif_pos hw]
    show (InfinitePlace.Completion.extensionEmbeddingOfIsReal hw (y w)) ^ 2 = ‖y w‖ ^ 2
    rw [← sq_abs, ← Real.norm_eq_abs,
      (InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal hw).norm_map_of_map_zero (map_zero _)]
  · rw [sqw, dif_neg hw]
    show ‖InfinitePlace.Completion.extensionEmbedding w (y w)‖ ^ 2 = ‖y w‖ ^ 2
    rw [(InfinitePlace.Completion.isometry_extensionEmbedding w).norm_map_of_map_zero (map_zero _)]

def Nfun (p : Fin 2 → MS) : ℝ := ∏ w : InfinitePlace K, (sqw K w (p 0)) ^ ((w.mult : ℝ) / 2)

theorem Nfun_iota (u : Kinf) (q : MS) :
    Nfun K ![InfiniteAdeleRing.ringEquiv_mixedSpace K u, q] = ∏ w : InfinitePlace K, ‖u w‖ ^ w.mult := by
  unfold Nfun
  refine Finset.prod_congr rfl fun w _ => ?_
  rw [Matrix.cons_val_zero, sqw_iota]
  rw [← Real.rpow_natCast ‖u w‖ 2, ← Real.rpow_mul (norm_nonneg _), ← Real.rpow_natCast]
  congr 1
  push_cast
  ring

theorem contDiffAt_Nfun {p : Fin 2 → MS} (hp : p ∈ Uunits K) : ContDiffAt ℝ (⊤ : ℕ∞) (Nfun K) p := by
  have hne : ∀ w, sqw K w (p 0) ≠ 0 := by
    intro w
    have hu := (isUnit_iff_forall_ne_zero K _).mp hp.1 w
    have h := sqw_iota K w ((InfiniteAdeleRing.ringEquiv_mixedSpace K).symm (p 0))
    rw [RingEquiv.apply_symm_apply] at h
    rw [h]
    exact pow_ne_zero 2 (norm_ne_zero_iff.mpr hu)
  unfold Nfun
  exact contDiffAt_prod fun w _ =>
    (((contDiff_sqw K w).comp (contDiff_apply ℝ _ 0)).contDiffAt).rpow_const_of_ne (hne w)

end NormFactor

section UnitsTop

def invK (x : Kinf) : Kinf :=
  show ((w : InfinitePlace K) → w.Completion) from fun w => (x w)⁻¹

omit [NumberField K] in
theorem invK_apply (x : Kinf) (w : InfinitePlace K) : invK K x w = (x w)⁻¹ := rfl

omit [NumberField K] in
theorem continuousOn_invK : ContinuousOn (invK K) {x : Kinf | ∀ w : InfinitePlace K, x w ≠ 0} := by
  intro x hx
  have h : ∀ w : InfinitePlace K, ContinuousWithinAt (fun y : Kinf => invK K y w) {x : Kinf | ∀ w, x w ≠ 0} x := by
    intro w
    have h1 : ContinuousAt (fun y : Kinf => (y w)⁻¹) x :=
      (continuousAt_inv₀ (hx w)).comp (f := fun y : Kinf => y w) (continuous_apply w).continuousAt
    exact h1.continuousWithinAt
  exact continuousWithinAt_pi.mpr h

def unitOf (x : Kinf) (hx : ∀ w : InfinitePlace K, x w ≠ 0) : (Kinf)ˣ :=
  ⟨x, invK K x, funext fun w => mul_inv_cancel₀ (hx w), funext fun w => inv_mul_cancel₀ (hx w)⟩

omit [NumberField K] in
theorem val_unitOf (x : Kinf) (hx : ∀ w : InfinitePlace K, x w ≠ 0) : (unitOf K x hx : Kinf) = x := rfl

theorem ne_zero_of_mem_Uunits₀ (q : ↥(Uunits K)) (w : InfinitePlace K) :
    (InfiniteAdeleRing.ringEquiv_mixedSpace K).symm (q.1 0) w ≠ 0 :=
  (isUnit_iff_forall_ne_zero K _).mp q.2.1 w

theorem ne_zero_of_mem_Uunits₁ (q : ↥(Uunits K)) (w : InfinitePlace K) :
    (InfiniteAdeleRing.ringEquiv_mixedSpace K).symm (q.1 1) w ≠ 0 :=
  (isUnit_iff_forall_ne_zero K _).mp q.2.2 w

def Theta (q : ↥(Uunits K)) : (Kinf)ˣ × (Kinf)ˣ :=
  (unitOf K _ (ne_zero_of_mem_Uunits₀ K q), unitOf K _ (ne_zero_of_mem_Uunits₁ K q))

theorem continuous_unitOf_comp {X : Type} [TopologicalSpace X] (g : X → Kinf) (hg : Continuous g)
    (hne : ∀ x (w : InfinitePlace K), g x w ≠ 0) :
    Continuous fun x => unitOf K (g x) (hne x) := by
  refine Units.isInducing_embedProduct.continuous_iff.mpr ?_
  show Continuous fun x => ((g x : Kinf), MulOpposite.op (invK K (g x)))
  refine hg.prodMk (MulOpposite.continuous_op.comp ?_)
  exact (continuousOn_invK K).comp_continuous hg fun x => hne x

theorem continuous_Theta : Continuous (Theta K) := by
  refine Continuous.prodMk ?_ ?_
  · exact continuous_unitOf_comp K _
      ((continuous_iota_symm K).comp ((continuous_apply 0).comp continuous_subtype_val)) _
  · exact continuous_unitOf_comp K _
      ((continuous_iota_symm K).comp ((continuous_apply 1).comp continuous_subtype_val)) _

theorem exists_isCompact_units_of_subset_Uunits {T : Set (Fin 2 → MS)} (hT : IsCompact T) (hTU : T ⊆ Uunits K) :
    ∃ Ca : Set ((Kinf)ˣ × (Kinf)ˣ), IsCompact Ca ∧ ∀ p ∈ T, ∃ q ∈ Ca,
      p = ![InfiniteAdeleRing.ringEquiv_mixedSpace K ((q.1 : (Kinf)ˣ) : Kinf),
            InfiniteAdeleRing.ringEquiv_mixedSpace K ((q.2 : (Kinf)ˣ) : Kinf)] := by
  have hT' : IsCompact (Subtype.val ⁻¹' T : Set ↥(Uunits K)) := by
    refine Topology.IsEmbedding.subtypeVal.isCompact_iff.mpr ?_
    rw [Subtype.image_preimage_coe, Set.inter_eq_right.mpr hTU]
    exact hT
  refine ⟨Theta K '' (Subtype.val ⁻¹' T), hT'.image (continuous_Theta K), fun p hp => ?_⟩
  refine ⟨Theta K ⟨p, hTU hp⟩, ⟨⟨p, hTU hp⟩, hp, rfl⟩, ?_⟩
  show p = ![InfiniteAdeleRing.ringEquiv_mixedSpace K ((InfiniteAdeleRing.ringEquiv_mixedSpace K).symm (p 0)),
    InfiniteAdeleRing.ringEquiv_mixedSpace K ((InfiniteAdeleRing.ringEquiv_mixedSpace K).symm (p 1))]
  rw [RingEquiv.apply_symm_apply, RingEquiv.apply_symm_apply]
  funext i
  fin_cases i <;> rfl

end UnitsTop

section Main

set_option maxHeartbeats 3200000 in
theorem main_aux
    [MeasurableSpace Kinf] [BorelSpace Kinf]
    (lam : Measure Kinf) [lam.IsAddHaarMeasure]
    (Kc : Subgroup GA) (hKc_cpt : IsCompact (Kc : Set GA))
    (κ : @Measure Kc (borel _)) (hκ : @Measure.IsHaarMeasure _ _ _ (borel _) κ)
    (fa : GA → ℂ) (hfa : IsArchTestFactor K fa) (η : Kinf → ℝ) (hη : Continuous η) :
    ∃ Φ : (Fin 2 → MS) → ℂ,
      ContDiff ℝ (⊤ : ℕ∞) Φ ∧ HasCompactSupport Φ ∧
      (∀ p : Fin 2 → MS, Φ p ≠ 0 →
        IsUnit ((InfiniteAdeleRing.ringEquiv_mixedSpace K).symm (p 0)) ∧
          IsUnit ((InfiniteAdeleRing.ringEquiv_mixedSpace K).symm (p 1))) ∧
      (∃ Ca : Set ((Kinf)ˣ × (Kinf)ˣ), IsCompact Ca ∧
        ∀ p ∈ tsupport Φ, ∃ q ∈ Ca,
          p = ![InfiniteAdeleRing.ringEquiv_mixedSpace K ((q.1 : (Kinf)ˣ) : Kinf),
                InfiniteAdeleRing.ringEquiv_mixedSpace K ((q.2 : (Kinf)ˣ) : Kinf)]) ∧
      ∀ (u z : (Kinf)ˣ),
        ((∏ w : InfinitePlace K, ‖(u : Kinf) w‖ ^ w.mult : ℝ) : ℂ) *
            ∫ x, @integral _ ℂ _ _ (borel _) κ (fun k =>
                fa ((k : GA)⁻¹ *
                  (Matrix.GeneralLinearGroup.scalar (Fin 2) z * diagUnits2 u 1 * unipotentGL2 x) *
                  (k : GA))) * ((η x : ℝ) : ℂ) ∂lam =
          Φ ![InfiniteAdeleRing.ringEquiv_mixedSpace K (u : Kinf),
              InfiniteAdeleRing.ringEquiv_mixedSpace K (z : Kinf)] := by
  obtain ⟨⟨Φ₀, hΦ₀, hrepr⟩, hsupp⟩ := hfa
  letI mK : MeasurableSpace Kc := borel _
  haveI : BorelSpace Kc := ⟨rfl⟩
  haveI : Measure.IsHaarMeasure κ := hκ
  haveI := secondCountableTopology_infiniteAdeleRing K
  haveI := secondCountableTopology_gl K
  haveI := t2Space_gl K
  haveI : CompactSpace Kc := isCompact_iff_compactSpace.mp hKc_cpt
  haveI : SecondCountableTopology Kc := TopologicalSpace.Subtype.secondCountableTopology _

  obtain ⟨T₂, hT₂⟩ : ∃ T₂ : Set GA, T₂ = (fun q : Kc × GA × Kc => (q.1 : GA) * q.2.1 * ((q.2.2 : GA))⁻¹) ''
      (Set.univ ×ˢ (tsupport fa ×ˢ Set.univ)) := ⟨_, rfl⟩
  have hT2c : IsCompact T₂ := by
    rw [hT₂]
    refine (isCompact_univ.prod (hsupp.prod isCompact_univ)).image ?_
    exact ((continuous_subtype_val.comp continuous_fst).mul (continuous_fst.comp continuous_snd)).mul
      ((continuous_subtype_val.comp (continuous_snd.comp continuous_snd)).inv)
  obtain ⟨B₀, hB₀⟩ : ∃ B₀ : Set GA, B₀ = {g : GA | ((g : GA) : Matrix (Fin 2) (Fin 2) Kinf) 1 0 = 0} := ⟨_, rfl⟩
  have hB0c : IsClosed B₀ := by
    rw [hB₀]; exact isClosed_eq (Units.continuous_val.matrix_elem 1 0) continuous_const
  have hT3c : IsCompact (T₂ ∩ B₀) := hT2c.inter_right hB0c
  have hSc : IsCompact (Lam K '' (T₂ ∩ B₀)) := hT3c.image (continuous_Lam K)
  have hSU : Lam K '' (T₂ ∩ B₀) ⊆ Uunits K := by
    rintro _ ⟨g, hg, rfl⟩
    have hg2 : (g : Matrix (Fin 2) (Fin 2) Kinf) 1 0 = 0 := by
      have h := hg.2; rw [hB₀] at h; exact h
    exact Lam_mem_Uunits K hg2
  have hX0c : IsCompact (LamX K '' (T₂ ∩ B₀)) := hT3c.image (continuous_LamX K)
  have hA0c : IsCompact (archEntries K '' (Kc : Set GA)) := hKc_cpt.image (continuous_archEntries' K)
  have hmem : ∀ (u z : (Kinf)ˣ) (x : Kinf) (k : Kc),
      fa ((k : GA)⁻¹ * theta K u z x * k) ≠ 0 → theta K u z x ∈ T₂ ∩ B₀ := by
    intro u z x k h
    refine ⟨?_, ?_⟩
    · rw [hT₂]
      refine ⟨(k, (k : GA)⁻¹ * theta K u z x * k, k), ?_, ?_⟩
      · exact Set.mk_mem_prod (Set.mem_univ _) (Set.mk_mem_prod (subset_tsupport _ h) (Set.mem_univ _))
      · show (k : GA) * ((k : GA)⁻¹ * theta K u z x * k) * (k : GA)⁻¹ = theta K u z x
        group
    · rw [hB₀]; exact theta_one_zero K u z x

  obtain ⟨χp, hχp, hχpc, hχp1, hχpU⟩ :=
    exists_smooth_bump (E := Fin 2 → MS) hSc (isOpen_Uunits K) hSU
  obtain ⟨χx, hχx, hχxc, hχx1, -⟩ := exists_smooth_bump (E := MS) hX0c isOpen_univ (Set.subset_univ _)
  obtain ⟨χA, hχA, hχAc, hχA1, -⟩ :=
    exists_smooth_bump (E := Fin 2 → Fin 2 → MS) hA0c isOpen_univ (Set.subset_univ _)

  obtain ⟨Ψ, hΨ⟩ : ∃ Ψ : (MS × (Fin 2 → Fin 2 → MS) × (Fin 2 → Fin 2 → MS)) × (Fin 2 → MS) → ℂ,
      Ψ = fun q => ((χp q.2 * χx q.1.1 * χA q.1.2.1 * χA q.1.2.2 : ℝ) : ℂ) *
        Φ₀ (conjM K q.1.2.1 q.1.2.2 (Mmat K q.2 q.1.1)) := ⟨_, rfl⟩
  have hΨs : ContDiff ℝ (⊤ : ℕ∞) Ψ := by
    rw [hΨ]
    refine ContDiff.mul ?_ (hΦ₀.comp (contDiff_conjM_Mmat K))
    refine Complex.ofRealCLM.contDiff.comp ?_
    exact (((hχp.comp contDiff_snd).mul (hχx.comp (contDiff_fst.comp contDiff_fst))).mul
      (hχA.comp (contDiff_fst.comp (contDiff_snd.comp contDiff_fst)))).mul
      (hχA.comp (contDiff_snd.comp (contDiff_snd.comp contDiff_fst)))
  have hΨapply : ∀ q, Ψ q = ((χp q.2 * χx q.1.1 * χA q.1.2.1 * χA q.1.2.2 : ℝ) : ℂ) *
        Φ₀ (conjM K q.1.2.1 q.1.2.2 (Mmat K q.2 q.1.1)) := fun q => by rw [hΨ]
  have hΨz : ∀ q : (MS × (Fin 2 → Fin 2 → MS) × (Fin 2 → Fin 2 → MS)) × (Fin 2 → MS),
      χp q.2 * χx q.1.1 * χA q.1.2.1 * χA q.1.2.2 = 0 → Ψ q = 0 := by
    intro q hq
    rw [hΨapply, hq, Complex.ofReal_zero, zero_mul]
  have hΨc : HasCompactSupport Ψ := by
    refine HasCompactSupport.intro ((hχxc.prod (hχAc.prod hχAc)).prod hχpc) fun q hq => hΨz q ?_
    simp only [Set.mem_prod, not_and_or] at hq
    rcases hq with (hx | hA | hB) | hp
    · rw [image_eq_zero_of_notMem_tsupport hx]; ring
    · rw [image_eq_zero_of_notMem_tsupport hA]; ring
    · rw [image_eq_zero_of_notMem_tsupport hB]; ring
    · rw [image_eq_zero_of_notMem_tsupport hp]; ring
  obtain ⟨c, hc⟩ : ∃ c : Kinf × Kc → MS × (Fin 2 → Fin 2 → MS) × (Fin 2 → Fin 2 → MS),
      c = fun q => (InfiniteAdeleRing.ringEquiv_mixedSpace K q.1, archEntries K (q.2 : GA),
        archEntries K ((q.2 : GA)⁻¹)) := ⟨_, rfl⟩
  have hcc : Continuous c := by
    rw [hc]
    exact ((AdelicBox.continuous_ringEquiv_mixedSpace K).comp continuous_fst).prodMk
      (((continuous_archEntries' K).comp (continuous_subtype_val.comp continuous_snd)).prodMk
        ((continuous_archEntries' K).comp ((continuous_subtype_val.comp continuous_snd).inv)))
  obtain ⟨w, hw⟩ : ∃ w : Kinf × Kc → ℝ, w = fun q => χx (InfiniteAdeleRing.ringEquiv_mixedSpace K q.1) * η q.1 :=
    ⟨_, rfl⟩
  have hwc : Continuous w := by
    rw [hw]
    exact (hχx.continuous.comp ((AdelicBox.continuous_ringEquiv_mixedSpace K).comp continuous_fst)).mul
      (hη.comp continuous_fst)
  have hws : HasCompactSupport w := by
    refine HasCompactSupport.intro (((iotaHomeo K).isCompact_preimage.mpr hχxc).prod isCompact_univ)
      fun q hq => ?_
    simp only [Set.mem_prod, Set.mem_univ, and_true, Set.mem_preimage, iotaHomeo_apply] at hq
    rw [hw]
    show χx _ * η _ = 0
    rw [image_eq_zero_of_notMem_tsupport hq, zero_mul]

  obtain ⟨G, hG⟩ : ∃ G : (Fin 2 → MS) → ℂ, G = fun p => ∫ q, w q • Ψ (c q, p) ∂(lam.prod κ) := ⟨_, rfl⟩
  have hGs : ContDiff ℝ (⊤ : ℕ∞) G := by
    rw [hG]
    exact MeasureTheory.contDiff_integral_smul_comp_of_contDiff_of_hasCompactSupport (lam.prod κ) c hcc w hwc hws
      Ψ hΨs hΨc
  have hG0 : ∀ p, χp p = 0 → G p = 0 := by
    intro p hp
    have hz : (fun q : Kinf × Kc => w q • Ψ (c q, p)) = fun _ => 0 := by
      funext q
      rw [hΨz (c q, p) (by simp only [hp, zero_mul]), smul_zero]
    rw [hG]
    show (∫ q, w q • Ψ (c q, p) ∂(lam.prod κ)) = 0
    rw [hz, integral_zero]

  have key : ∀ (u z : (Kinf)ˣ) (x : Kinf) (k : Kc),
      w (x, k) • Ψ (c (x, k), ![InfiniteAdeleRing.ringEquiv_mixedSpace K (u : Kinf),
        InfiniteAdeleRing.ringEquiv_mixedSpace K (z : Kinf)]) =
        ((η x : ℝ) : ℂ) * fa ((k : GA)⁻¹ * theta K u z x * k) := by
    intro u z x k
    have hk' : archEntries K ((k : GA)⁻¹) ∈ archEntries K '' (Kc : Set GA) :=
      ⟨((k⁻¹ : Kc) : GA), (k⁻¹).2, by rw [Subgroup.coe_inv]⟩
    have hk : archEntries K (k : GA) ∈ archEntries K '' (Kc : Set GA) := ⟨k, k.2, rfl⟩
    rw [hΨapply, hw, hc]
    simp only []
    rw [conjM_archEntries K, ← hrepr, hχA1 _ hk, hχA1 _ hk']
    by_cases h0 : fa ((k : GA)⁻¹ * theta K u z x * k) = 0
    · have h0' : fa ((k : GA)⁻¹ *
          (Matrix.GeneralLinearGroup.scalar (Fin 2) z * diagUnits2 u 1 * unipotentGL2 x) * k) = 0 := h0
      rw [h0', h0, mul_zero, smul_zero, mul_zero]
    · obtain hT := hmem u z x k h0
      have h1 : χp ![InfiniteAdeleRing.ringEquiv_mixedSpace K (u : Kinf),
          InfiniteAdeleRing.ringEquiv_mixedSpace K (z : Kinf)] = 1 :=
        hχp1 _ ⟨_, hT, Lam_theta K u z x⟩
      have h2 : χx (InfiniteAdeleRing.ringEquiv_mixedSpace K x) = 1 := hχx1 _ ⟨_, hT, LamX_theta K u z x⟩
      rw [h1, h2]
      simp only [mul_one, Complex.ofReal_one, one_mul]
      rw [Complex.real_smul]
      rfl
  have hGu : ∀ (u z : (Kinf)ˣ), G ![InfiniteAdeleRing.ringEquiv_mixedSpace K (u : Kinf),
        InfiniteAdeleRing.ringEquiv_mixedSpace K (z : Kinf)] =
      ∫ x, (∫ k : Kc, fa ((k : GA)⁻¹ *
        (Matrix.GeneralLinearGroup.scalar (Fin 2) z * diagUnits2 u 1 * unipotentGL2 x) * (k : GA)) ∂κ) *
        ((η x : ℝ) : ℂ) ∂lam := by
    intro u z
    have hint : Integrable (fun q : Kinf × Kc => w q • Ψ (c q,
        ![InfiniteAdeleRing.ringEquiv_mixedSpace K (u : Kinf), InfiniteAdeleRing.ringEquiv_mixedSpace K (z : Kinf)]))
        (lam.prod κ) := by
      refine Continuous.integrable_of_hasCompactSupport ?_ hws.smul_right
      exact hwc.smul (hΨs.continuous.comp (hcc.prodMk continuous_const))
    rw [hG]
    show (∫ q, w q • Ψ (c q, _) ∂(lam.prod κ)) = _
    rw [MeasureTheory.integral_prod _ hint]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    show (∫ k, w (x, k) • Ψ (c (x, k), _) ∂κ) = (∫ k : Kc, fa ((k : GA)⁻¹ * theta K u z x * k) ∂κ) * _
    rw [integral_congr_ae (Filter.Eventually.of_forall fun k => key u z x k), integral_const_mul, mul_comm]
  have hGc : HasCompactSupport G :=
    HasCompactSupport.intro hχpc fun p hp => hG0 p (image_eq_zero_of_notMem_tsupport hp)

  have hGts : tsupport G ⊆ tsupport χp :=
    closure_minimal (fun p hp => by_contra fun h => hp (hG0 p (image_eq_zero_of_notMem_tsupport h)))
      (isClosed_tsupport χp)
  refine ⟨fun p => ((Nfun K p : ℝ) : ℂ) * G p, ?_, hGc.mul_left, ?_, ?_, ?_⟩
  · rw [contDiff_iff_contDiffAt]
    intro p
    by_cases hp : p ∈ tsupport χp
    · have hN : ContDiffAt ℝ (⊤ : ℕ∞) (fun p => ((Nfun K p : ℝ) : ℂ)) p :=
        Complex.ofRealCLM.contDiff.contDiffAt.comp p (contDiffAt_Nfun K (hχpU hp))
      exact hN.mul hGs.contDiffAt
    · have hev : (fun p => ((Nfun K p : ℝ) : ℂ) * G p) =ᶠ[nhds p] fun _ => 0 := by
        filter_upwards [(isClosed_tsupport χp).isOpen_compl.mem_nhds hp] with p' hp'
        rw [hG0 p' (image_eq_zero_of_notMem_tsupport hp'), mul_zero]
      exact (contDiffAt_const (c := (0 : ℂ))).congr_of_eventuallyEq hev
  · intro p hp
    have hGp : χp p ≠ 0 := fun h => hp (show ((Nfun K p : ℝ) : ℂ) * G p = 0 by rw [hG0 p h, mul_zero])
    exact hχpU (subset_tsupport _ hGp)
  · obtain ⟨Ca, hCa, hmemCa⟩ := exists_isCompact_units_of_subset_Uunits K hχpc hχpU
    refine ⟨Ca, hCa, fun p hp => hmemCa p ?_⟩
    exact hGts ((tsupport_mul_subset_right (f := fun p => ((Nfun K p : ℝ) : ℂ)) (g := G)) hp)
  · intro u z
    show _ = ((Nfun K ![InfiniteAdeleRing.ringEquiv_mixedSpace K (u : Kinf),
        InfiniteAdeleRing.ringEquiv_mixedSpace K (z : Kinf)] : ℝ) : ℂ) *
      G ![InfiniteAdeleRing.ringEquiv_mixedSpace K (u : Kinf), InfiniteAdeleRing.ringEquiv_mixedSpace K (z : Kinf)]
    rw [Nfun_iota, hGu]

end Main

end SmoothWindow

end

namespace WR2aux

open AutomorphicForm AutomorphicForm.WindowedSiegel
open scoped Classical

variable (K : Type) [Field K] [NumberField K]

local notation "Kinf" => InfiniteAdeleRing K
local notation "GA" => GL (Fin 2) (InfiniteAdeleRing K)

noncomputable def lamK : GA → ℝ := fun y : GA =>
  -Real.log (AutomorphicForm.WindowedSiegel.archHeight K y)
    - Real.log (AutomorphicForm.WindowedSiegel.archHeight K
        (AdelicLevel.glArch (𝓞 K) K (AutomorphicForm.adelicWeyl (𝓞 K) K) * y))

noncomputable def omegaK : Kinf → ℝ := fun y => ∑ w : InfinitePlace K, (w.mult : ℝ) * Real.log (1 + ‖y w‖ ^ 2)

theorem continuous_omegaK : Continuous (omegaK K) := by
  unfold omegaK
  refine continuous_finsetSum _ fun w _ => continuous_const.mul ?_
  refine Continuous.log (continuous_const.add (((continuous_apply w).norm).pow 2)) fun y => ?_
  positivity

theorem lamK_eq : lamK K = fun x : GA =>
    ∑ w : InfinitePlace K, (w.mult : ℝ) *
      Real.log (topNormSq ((archComponent K w x : GL (Fin 2) w.Completion) : Matrix (Fin 2) (Fin 2) w.Completion) *
        rowNormSq ((archComponent K w x : GL (Fin 2) w.Completion) : Matrix (Fin 2) (Fin 2) w.Completion) /
        ‖((archComponent K w x : GL (Fin 2) w.Completion) : Matrix (Fin 2) (Fin 2) w.Completion).det‖ ^ 2) :=
  (AutomorphicForm.WindowedSiegel.sum_mult_mul_log_topNormSq_mul_rowNormSq_div_eq_neg_log_archHeight_sub_log_archHeight_weyl_mul K).symm

theorem topNormSq_pos {F : Type*} [NormedField F] (g : GL (Fin 2) F) :
    0 < topNormSq (g : Matrix (Fin 2) (Fin 2) F) := by
  unfold topNormSq
  by_contra h
  have h0 : ‖(g : Matrix (Fin 2) (Fin 2) F) 0 0‖ ^ 2 + ‖(g : Matrix (Fin 2) (Fin 2) F) 0 1‖ ^ 2 = 0 :=
    le_antisymm (not_lt.mp h) (by positivity)
  have h00 : (g : Matrix (Fin 2) (Fin 2) F) 0 0 = 0 := by
    have : ‖(g : Matrix (Fin 2) (Fin 2) F) 0 0‖ ^ 2 = 0 := by nlinarith [sq_nonneg ‖(g : Matrix (Fin 2) (Fin 2) F) 0 0‖, sq_nonneg ‖(g : Matrix (Fin 2) (Fin 2) F) 0 1‖]
    exact norm_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp this)
  have h01 : (g : Matrix (Fin 2) (Fin 2) F) 0 1 = 0 := by
    have : ‖(g : Matrix (Fin 2) (Fin 2) F) 0 1‖ ^ 2 = 0 := by nlinarith [sq_nonneg ‖(g : Matrix (Fin 2) (Fin 2) F) 0 0‖, sq_nonneg ‖(g : Matrix (Fin 2) (Fin 2) F) 0 1‖]
    exact norm_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp this)
  apply Matrix.GeneralLinearGroup.det_ne_zero g
  rw [Matrix.det_fin_two, h00, h01]
  ring

theorem continuous_lamK : Continuous (lamK K) := by
  rw [lamK_eq]
  refine continuous_finsetSum _ fun w _ => continuous_const.mul ?_
  have hc : Continuous fun x : GA =>
      ((archComponent K w x : GL (Fin 2) w.Completion) : Matrix (Fin 2) (Fin 2) w.Completion) :=
    Units.continuous_val.comp (AdelicLevel.continuous_archComponent K w)
  have ht : Continuous fun x : GA =>
      topNormSq ((archComponent K w x : GL (Fin 2) w.Completion) : Matrix (Fin 2) (Fin 2) w.Completion) := by
    unfold topNormSq
    exact ((hc.matrix_elem 0 0).norm.pow 2).add ((hc.matrix_elem 0 1).norm.pow 2)
  have hr : Continuous fun x : GA =>
      rowNormSq ((archComponent K w x : GL (Fin 2) w.Completion) : Matrix (Fin 2) (Fin 2) w.Completion) := by
    unfold rowNormSq
    exact ((hc.matrix_elem 1 0).norm.pow 2).add ((hc.matrix_elem 1 1).norm.pow 2)
  have hd : Continuous fun x : GA =>
      ‖((archComponent K w x : GL (Fin 2) w.Completion) : Matrix (Fin 2) (Fin 2) w.Completion).det‖ ^ 2 :=
    (hc.matrix_det.norm).pow 2
  refine ((ht.mul hr).div hd fun x => ?_).log fun x => ?_
  · exact pow_ne_zero 2 (norm_ne_zero_iff.mpr (Matrix.GeneralLinearGroup.det_ne_zero _))
  · exact (div_pos (mul_pos (topNormSq_pos _) (rowNormSq_pos _))
      (pow_pos (norm_pos_iff.mpr (Matrix.GeneralLinearGroup.det_ne_zero _)) 2)).ne'

theorem lamK_bnk (u' t' : (Kinf)ˣ) (y : Kinf) (k : GA)
    (hk : k ∈ (⨅ w : InfinitePlace K,
      (rowIsometrySubgroup w.Completion).comap (archComponent K w) : Subgroup GA)) :
    lamK K (Matrix.GeneralLinearGroup.scalar (Fin 2) u' * diagUnits2 t' 1 * unipotentGL2 y * k) = omegaK K y := by
  rw [lamK_eq]
  unfold omegaK
  refine Finset.sum_congr rfl fun w _ => ?_
  congr 1
  congr 1
  have hkw : IsRowIsometry (archComponent K w k) := by
    have h1 := (Subgroup.mem_iInf.mp hk) w
    exact (mem_rowIsometrySubgroup_iff).mp (Subgroup.mem_comap.mp h1)
  set B : GA := Matrix.GeneralLinearGroup.scalar (Fin 2) u' * diagUnits2 t' 1 * unipotentGL2 y with hB
  rw [map_mul, topNormSq_mul_rowIsometry _ hkw, rowNormSq_mul_rowIsometry _ hkw, Units.val_mul, Matrix.det_mul,
    norm_mul, hkw.1, mul_one]
  have ha : (u' : Kinf) w ≠ 0 := (SmoothWindow.isUnit_iff_forall_ne_zero K (u' : Kinf)).mp u'.isUnit w
  have hb : (t' : Kinf) w ≠ 0 := (SmoothWindow.isUnit_iff_forall_ne_zero K (t' : Kinf)).mp t'.isUnit w
  have hBw : ((archComponent K w B : GL (Fin 2) w.Completion) : Matrix (Fin 2) (Fin 2) w.Completion) =
      !![(u' : Kinf) w * (t' : Kinf) w, (u' : Kinf) w * (t' : Kinf) w * y w; 0, (u' : Kinf) w] := by
    have hmul : ∀ a b : Kinf, (a * b) w = a w * b w := fun a b => rfl
    have hzero : (0 : Kinf) w = 0 := rfl
    ext i j
    rw [AdelicLevel.archComponent_apply, hB]
    fin_cases i <;> fin_cases j <;>
      simp [diagUnits2, unipotentGL2, Matrix.GeneralLinearGroup.scalar, Matrix.mul_apply, Fin.sum_univ_two,
        hmul, hzero] <;> ring
  rw [hBw]
  simp only [topNormSq, rowNormSq, Matrix.det_fin_two_of, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_cons, Matrix.head_fin_const,
    norm_zero, norm_mul, mul_zero, sub_zero]
  have ha' : ‖(u' : Kinf) w‖ ≠ 0 := norm_ne_zero_iff.mpr ha
  have hb' : ‖(t' : Kinf) w‖ ≠ 0 := norm_ne_zero_iff.mpr hb
  field_simp
  ring

end WR2aux

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicHaar IsDedekindDomain AutomorphicForm in
open scoped TensorProduct TensorProduct.RightActions Classical in
theorem solution
    (K : Type) [Field K] [NumberField K]
    (fa : GL (Fin 2) (InfiniteAdeleRing K) → ℂ) (hfa : AutomorphicForm.IsArchTestFactor K fa)
    (ν : @Measure (GL (Fin 2) (InfiniteAdeleRing K)) (AutomorphicForm.glBorelOf (InfiniteAdeleRing K)))
    (hν : @Measure.IsHaarMeasure _ _ _ (AutomorphicForm.glBorelOf (InfiniteAdeleRing K)) ν)
    [MeasurableSpace (InfiniteAdeleRing K)ˣ] [BorelSpace (InfiniteAdeleRing K)ˣ]
    (ρ : Measure (InfiniteAdeleRing K)ˣ) [ρ.IsHaarMeasure]
    (u : (InfiniteAdeleRing K)ˣ) (hu : ∀ w : InfinitePlace K, (u : InfiniteAdeleRing K) w ≠ 1) :
    ∃ Ψ : (Fin 2 → mixedEmbedding.mixedSpace K) → ℂ,
      Continuous Ψ ∧ HasCompactSupport Ψ ∧
      (∀ p : Fin 2 → mixedEmbedding.mixedSpace K, Ψ p ≠ 0 →
        IsUnit ((InfiniteAdeleRing.ringEquiv_mixedSpace K).symm (p 0)) ∧
          IsUnit ((InfiniteAdeleRing.ringEquiv_mixedSpace K).symm (p 1))) ∧
      (∃ Ca : Set ((InfiniteAdeleRing K)ˣ × (InfiniteAdeleRing K)ˣ), IsCompact Ca ∧
        ∀ p ∈ tsupport Ψ, ∃ q ∈ Ca,
          p = ![InfiniteAdeleRing.ringEquiv_mixedSpace K ((q.1 : (InfiniteAdeleRing K)ˣ) : InfiniteAdeleRing K),
                InfiniteAdeleRing.ringEquiv_mixedSpace K ((q.2 : (InfiniteAdeleRing K)ˣ) : InfiniteAdeleRing K)]) ∧
      ∀ (z : (InfiniteAdeleRing K)ˣ)
          (τ : Measure (Subgroup.centralizer
              ({Matrix.GeneralLinearGroup.scalar (Fin 2) z * diagUnits2 u 1} : Set (GL (Fin 2) (InfiniteAdeleRing K))))),
          (∀ g : GL (Fin 2) (InfiniteAdeleRing K) → ℂ,
              ∫ t, g (t : GL (Fin 2) (InfiniteAdeleRing K)) ∂τ =
                ∫ p : (InfiniteAdeleRing K)ˣ × (InfiniteAdeleRing K)ˣ, g (diagUnits2 p.1 p.2) ∂(ρ.prod ρ)) →
          ∀ J : ℂ, AutomorphicForm.IsWeightedOrbitalIntegralOn (InfiniteAdeleRing K) ν
              (fun y : GL (Fin 2) (InfiniteAdeleRing K) =>
        -Real.log (AutomorphicForm.WindowedSiegel.archHeight K y)
          - Real.log (AutomorphicForm.WindowedSiegel.archHeight K
              (AdelicLevel.glArch (𝓞 K) K (AutomorphicForm.adelicWeyl (𝓞 K) K) * y)))
              (Matrix.GeneralLinearGroup.scalar (Fin 2) z * diagUnits2 u 1) τ fa J →
            J = Ψ ![InfiniteAdeleRing.ringEquiv_mixedSpace K (u : InfiniteAdeleRing K),
                InfiniteAdeleRing.ringEquiv_mixedSpace K (z : InfiniteAdeleRing K)] := by
  classical
  letI mA : MeasurableSpace (InfiniteAdeleRing K) := borel _
  haveI : BorelSpace (InfiniteAdeleRing K) := ⟨rfl⟩
  let lam : Measure (InfiniteAdeleRing K) := Measure.addHaar
  let Kc : Subgroup (GL (Fin 2) (InfiniteAdeleRing K)) :=
    ⨅ w : InfinitePlace K, (AutomorphicForm.WindowedSiegel.rowIsometrySubgroup w.Completion).comap (archComponent K w)
  letI mK : MeasurableSpace Kc := borel _
  haveI : BorelSpace Kc := ⟨rfl⟩
  have hKc : IsCompact (Kc : Set (GL (Fin 2) (InfiniteAdeleRing K))) :=
    (NumberField.InfiniteAdeleRing.exists_mem_borelSubgroup_mul_eq_and_isCompact_iInf_rowIsometrySubgroup K).2
  haveI : CompactSpace Kc := isCompact_iff_compactSpace.mp hKc
  let K₀ : TopologicalSpace.PositiveCompacts Kc := ⟨⟨Set.univ, isCompact_univ⟩, by simp [interior_univ]⟩
  let κ : Measure Kc := Measure.haarMeasure K₀
  obtain ⟨c, hc, hdesc⟩ :=
    AutomorphicForm.exists_pos_forall_prod_norm_sub_one_pow_mul_eq_and_weighted_eq_mul_prod_norm_pow_mul_integral_integral_of_scalar_mul_diagUnits2
      K ν hν lam ρ κ inferInstance

  have huinv : ∀ w : InfinitePlace K, ((u⁻¹ : (InfiniteAdeleRing K)ˣ) : (InfiniteAdeleRing K)) w = ((u : (InfiniteAdeleRing K)) w)⁻¹ := by
    intro w
    have h := congr_fun (congr_arg (fun a : (InfiniteAdeleRing K)ˣ => (a : (InfiniteAdeleRing K))) (inv_mul_cancel u)) w
    simp only [Units.val_mul, Pi.mul_apply, Units.val_one, Pi.one_apply] at h
    exact eq_inv_of_mul_eq_one_left h
  have hvne : ∀ w : InfinitePlace K, ((1 : (InfiniteAdeleRing K)) - ((u⁻¹ : (InfiniteAdeleRing K)ˣ) : (InfiniteAdeleRing K))) w ≠ 0 := by
    intro w
    have e : ((1 : (InfiniteAdeleRing K)) - ((u⁻¹ : (InfiniteAdeleRing K)ˣ) : (InfiniteAdeleRing K))) w = 1 - ((u⁻¹ : (InfiniteAdeleRing K)ˣ) : (InfiniteAdeleRing K)) w := rfl
    rw [e, huinv, sub_ne_zero]
    intro h
    have hu0 : (u : (InfiniteAdeleRing K)) w ≠ 0 := (SmoothWindow.isUnit_iff_forall_ne_zero K (u : (InfiniteAdeleRing K))).mp u.isUnit w
    exact hu w (by rw [← inv_inv ((u : (InfiniteAdeleRing K)) w), ← h, inv_one])
  let v : (InfiniteAdeleRing K)ˣ := SmoothWindow.unitOf K (1 - ((u⁻¹ : (InfiniteAdeleRing K)ˣ) : (InfiniteAdeleRing K))) hvne
  have hv : (v : (InfiniteAdeleRing K)) = 1 - ((u⁻¹ : (InfiniteAdeleRing K)ˣ) : (InfiniteAdeleRing K)) := rfl

  have hη : Continuous fun x : (InfiniteAdeleRing K) => WR2aux.omegaK K (((v⁻¹ : (InfiniteAdeleRing K)ˣ) : (InfiniteAdeleRing K)) * x) :=
    (WR2aux.continuous_omegaK K).comp (continuous_const.mul continuous_id)
  obtain ⟨Φ, hΦs, hΦc, hΦu, ⟨Ca, hCa, hCamem⟩, hΦwin⟩ :=
    SmoothWindow.main_aux K lam Kc hKc κ inferInstance fa hfa
      (fun x : (InfiniteAdeleRing K) => WR2aux.omegaK K (((v⁻¹ : (InfiniteAdeleRing K)ˣ) : (InfiniteAdeleRing K)) * x)) hη

  set N : ℝ := ∏ w : InfinitePlace K, ‖(u : (InfiniteAdeleRing K)) w - 1‖ ^ w.mult with hN
  have hN0 : N ≠ 0 := by
    rw [hN]
    refine Finset.prod_ne_zero_iff.mpr fun w _ => pow_ne_zero _ (norm_ne_zero_iff.mpr ?_)
    exact sub_ne_zero.mpr (hu w)
  have hNc : (N : ℂ) ≠ 0 := by exact_mod_cast hN0
  refine ⟨fun p => ((N : ℝ) : ℂ)⁻¹ * (c : ℂ) * Φ p, ?_, ?_, ?_, ?_, ?_⟩
  · exact continuous_const.mul hΦs.continuous
  · exact hΦc.mul_left
  · intro p hp
    refine hΦu p fun h => hp ?_
    show ((N : ℝ) : ℂ)⁻¹ * (c : ℂ) * Φ p = 0
    rw [h, mul_zero]
  · exact ⟨Ca, hCa, fun p hp => hCamem p
      ((tsupport_mul_subset_right (f := fun _ : Fin 2 → mixedEmbedding.mixedSpace K => ((N : ℝ) : ℂ)⁻¹ * (c : ℂ)) (g := Φ)) hp)⟩
  · intro z τ hτ J hJ
    have h := (hdesc fa hfa (WR2aux.omegaK K) (WR2aux.continuous_omegaK K) (WR2aux.lamK K) (WR2aux.continuous_lamK K)
      (fun u' t' y k hk => WR2aux.lamK_bnk K u' t' y k hk) u z hu v hv τ hτ).2 J hJ

    rw [← hN] at h
    have hw := hΦwin u z
    show J = ((N : ℝ) : ℂ)⁻¹ * (c : ℂ) * Φ _
    rw [← hw]
    have hJ' : J = ((N : ℝ) : ℂ)⁻¹ * (((N : ℝ) : ℂ) * J) := by
      rw [← mul_assoc, inv_mul_cancel₀ hNc, one_mul]
    rw [hJ', h]
    ring

end S_AutomorphicForm_exists_continuous_hasCompactSupport_eq_of_isWeightedOrbitalIntegralOn_scalar_mul_diagUnits2
end P2MW
export P2MW.S_AutomorphicForm_exists_continuous_hasCompactSupport_eq_of_isWeightedOrbitalIntegralOn_scalar_mul_diagUnits2 (solution)

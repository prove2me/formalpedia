-- Prove2me | solution 1 for AutomorphicForm.exists_contDiff_hasCompactSupport_forall_integral_twistedConj_diagUnits2_mul_unipotentGL2_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/3a48dc7b-16bf-515d-bcc2-3e9289d0e3bc

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_NumberField_AdelicLevel
import Definitions.Def_LanglandsTunnell_CubicInduction_TorusValues
import Definitions.Def_AutomorphicForm_RowIsometryInvariance
import Definitions.Def_AutomorphicForm_ConstantTerm
import Definitions.Def_AutomorphicForm_FactorizableTestFn
import Definitions.Def_NumberField_AdelicBox
import Theorems.Thm_MeasureTheory_contDiff_integral_smul_comp_of_contDiff_of_hasCompactSupport
import Theorems.Thm_NumberField_InfiniteAdeleRing_exists_mem_borelSubgroup_mul_eq_and_isCompact_iInf_rowIsometrySubgroup
import Theorems.Thm_NumberField_InfiniteAdeleRing_isEmbedding_units_val
import Definitions.Def_AutomorphicForm_BaseChangePlaces
import Definitions.Def_AutomorphicForm_WeightedOrbitalRelation
import Definitions.Def_AutomorphicForm_WeylIntertwining
import Definitions.Def_NumberField_AdelicHeight
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_contDiff_hasCompactSupport_forall_integral_twistedConj_diagUnits2_mul_unipotentGL2_eq
p2m_attr_erase "simp" "LocalGL2.coe_localRepSome LocalGL2.coe_diagPi LocalGL2.coe_localRepInf LocalGL2.coe_localRepSome_inv LocalGL2.coe_unipotentInt LocalGL2.coe_weylInt LocalGL2.coe_diagPi_inv LocalGL2.transposeGL_val LocalGL2.transposeGL_one LocalGL2.swapUnit_val"

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option synthInstance.maxSize 8192

open MeasureTheory NumberField NumberField.AdelicLevel IsDedekindDomain
open scoped ENNReal

attribute [local instance] AutomorphicForm.centralizerBorel

open LanglandsTunnell.CubicInduction (diagUnits2)

noncomputable section

namespace TwKAvg

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

def Mmat3 (p : Fin 3 → MS) : Fin 2 → Fin 2 → MS :=
  ![![p 0, p 0 * p 2], ![0, p 1]]

def conjM (A B M : Fin 2 → Fin 2 → MS) : Fin 2 → Fin 2 → MS :=
  fun i j => ∑ l, ∑ r, B i l * M l r * A r j

theorem contDiff_conjM_Mmat3 :
    ContDiff ℝ (⊤ : ℕ∞) fun q : ((Fin 2 → Fin 2 → MS) × (Fin 2 → Fin 2 → MS)) × (Fin 3 → MS) =>
      conjM K q.1.1 q.1.2 (Mmat3 K q.2) := by
  refine contDiff_pi.mpr fun i => contDiff_pi.mpr fun j => ?_
  show ContDiff ℝ (⊤ : ℕ∞) fun q : ((Fin 2 → Fin 2 → MS) × (Fin 2 → Fin 2 → MS)) × (Fin 3 → MS) =>
    ∑ l, ∑ r, q.1.2 i l * Mmat3 K q.2 l r * q.1.1 r j
  refine ContDiff.sum fun l _ => ContDiff.sum fun r _ => ?_
  have hA : ContDiff ℝ (⊤ : ℕ∞) fun q : ((Fin 2 → Fin 2 → MS) × (Fin 2 → Fin 2 → MS)) × (Fin 3 → MS) => q.1.1 r j :=
    (contDiff_apply_apply ℝ _ r j).comp (contDiff_fst.comp contDiff_fst)
  have hB : ContDiff ℝ (⊤ : ℕ∞) fun q : ((Fin 2 → Fin 2 → MS) × (Fin 2 → Fin 2 → MS)) × (Fin 3 → MS) => q.1.2 i l :=
    (contDiff_apply_apply ℝ _ i l).comp (contDiff_snd.comp contDiff_fst)
  have hp : ∀ a : Fin 3, ContDiff ℝ (⊤ : ℕ∞)
      fun q : ((Fin 2 → Fin 2 → MS) × (Fin 2 → Fin 2 → MS)) × (Fin 3 → MS) => q.2 a :=
    fun a => (contDiff_apply ℝ _ a).comp contDiff_snd
  have hM : ContDiff ℝ (⊤ : ℕ∞)
      fun q : ((Fin 2 → Fin 2 → MS) × (Fin 2 → Fin 2 → MS)) × (Fin 3 → MS) => Mmat3 K q.2 l r := by
    fin_cases l <;> fin_cases r
    · show ContDiff ℝ (⊤ : ℕ∞) fun q : ((Fin 2 → Fin 2 → MS) × (Fin 2 → Fin 2 → MS)) × (Fin 3 → MS) => q.2 0
      exact hp 0
    · show ContDiff ℝ (⊤ : ℕ∞) fun q : ((Fin 2 → Fin 2 → MS) × (Fin 2 → Fin 2 → MS)) × (Fin 3 → MS) => q.2 0 * q.2 2
      exact contDiff_ms_mul K (hp 0) (hp 2)
    · show ContDiff ℝ (⊤ : ℕ∞) fun q : ((Fin 2 → Fin 2 → MS) × (Fin 2 → Fin 2 → MS)) × (Fin 3 → MS) => (0 : MS)
      exact contDiff_const
    · show ContDiff ℝ (⊤ : ℕ∞) fun q : ((Fin 2 → Fin 2 → MS) × (Fin 2 → Fin 2 → MS)) × (Fin 3 → MS) => q.2 1
      exact hp 1
  exact contDiff_ms_mul K (contDiff_ms_mul K hB hM) hA

def theta3 (a t : (Kinf)ˣ) (x : Kinf) : GA := diagUnits2 a t * unipotentGL2 x

omit [NumberField K] in
theorem coe_theta3 (a t : (Kinf)ˣ) (x : Kinf) :
    ((theta3 K a t x : GA) : Matrix (Fin 2) (Fin 2) Kinf) = !![(a : Kinf), (a : Kinf) * x; 0, (t : Kinf)] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [theta3, diagUnits2, unipotentGL2, Matrix.mul_apply, Fin.sum_univ_two]

theorem conjM_archEntries3 (g₁ g₂ : GA) (a t : (Kinf)ˣ) (x : Kinf) :
    conjM K (archEntries K g₁) (archEntries K g₂)
        (Mmat3 K ![InfiniteAdeleRing.ringEquiv_mixedSpace K (a : Kinf), InfiniteAdeleRing.ringEquiv_mixedSpace K (t : Kinf), InfiniteAdeleRing.ringEquiv_mixedSpace K x]) =
      archEntries K (g₂ * theta3 K a t x * g₁) := by
  have hM := coe_theta3 K a t x
  have hMm : ∀ l r, Mmat3 K ![InfiniteAdeleRing.ringEquiv_mixedSpace K (a : Kinf), InfiniteAdeleRing.ringEquiv_mixedSpace K (t : Kinf), InfiniteAdeleRing.ringEquiv_mixedSpace K x] l r =
      InfiniteAdeleRing.ringEquiv_mixedSpace K (((theta3 K a t x : GA) : Matrix (Fin 2) (Fin 2) Kinf) l r) := by
    intro l r
    rw [hM]
    fin_cases l <;> fin_cases r <;>
      simp only [Fin.zero_eta, Fin.mk_one, Mmat3, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons, Matrix.head_fin_const, map_mul, map_zero]
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

def Lam3 (g : GA) : Fin 3 → MS :=
  ![InfiniteAdeleRing.ringEquiv_mixedSpace K ((g : Matrix (Fin 2) (Fin 2) Kinf) 0 0),
    InfiniteAdeleRing.ringEquiv_mixedSpace K ((g : Matrix (Fin 2) (Fin 2) Kinf) 1 1),
    InfiniteAdeleRing.ringEquiv_mixedSpace K ((g : Matrix (Fin 2) (Fin 2) Kinf) 0 1 * ((g⁻¹ : GA) : Matrix (Fin 2) (Fin 2) Kinf) 0 0)]

theorem continuous_Lam3 : Continuous (Lam3 K) := by
  refine continuous_pi fun i => ?_
  fin_cases i
  · show Continuous fun g : GA => InfiniteAdeleRing.ringEquiv_mixedSpace K ((g : Matrix (Fin 2) (Fin 2) Kinf) 0 0)
    exact (AdelicBox.continuous_ringEquiv_mixedSpace K).comp (Units.continuous_val.matrix_elem 0 0)
  · show Continuous fun g : GA => InfiniteAdeleRing.ringEquiv_mixedSpace K ((g : Matrix (Fin 2) (Fin 2) Kinf) 1 1)
    exact (AdelicBox.continuous_ringEquiv_mixedSpace K).comp (Units.continuous_val.matrix_elem 1 1)
  · show Continuous fun g : GA => InfiniteAdeleRing.ringEquiv_mixedSpace K
      ((g : Matrix (Fin 2) (Fin 2) Kinf) 0 1 * ((g⁻¹ : GA) : Matrix (Fin 2) (Fin 2) Kinf) 0 0)
    exact (AdelicBox.continuous_ringEquiv_mixedSpace K).comp
      ((Units.continuous_val.matrix_elem 0 1).mul (Units.continuous_coe_inv.matrix_elem 0 0))

omit [NumberField K] in
theorem theta3_one_zero (a t : (Kinf)ˣ) (x : Kinf) :
    ((theta3 K a t x : GA) : Matrix (Fin 2) (Fin 2) Kinf) 1 0 = 0 := by
  rw [coe_theta3]; rfl

theorem Lam3_theta3 (a t : (Kinf)ˣ) (x : Kinf) :
    Lam3 K (theta3 K a t x) = ![InfiniteAdeleRing.ringEquiv_mixedSpace K (a : Kinf), InfiniteAdeleRing.ringEquiv_mixedSpace K (t : Kinf), InfiniteAdeleRing.ringEquiv_mixedSpace K x] := by
  obtain ⟨h00, -⟩ := inv_entries_of_upper K (theta3_one_zero K a t x)
  have e00 : ((theta3 K a t x : GA) : Matrix (Fin 2) (Fin 2) Kinf) 0 0 = (a : Kinf) := by rw [coe_theta3]; rfl
  have e01 : ((theta3 K a t x : GA) : Matrix (Fin 2) (Fin 2) Kinf) 0 1 = (a : Kinf) * x := by rw [coe_theta3]; rfl
  have e11 : ((theta3 K a t x : GA) : Matrix (Fin 2) (Fin 2) Kinf) 1 1 = (t : Kinf) := by rw [coe_theta3]; rfl
  rw [e00] at h00
  have hinv : (((theta3 K a t x)⁻¹ : GA) : Matrix (Fin 2) (Fin 2) Kinf) 0 0 = ((a⁻¹ : (Kinf)ˣ) : Kinf) := by
    calc (((theta3 K a t x)⁻¹ : GA) : Matrix (Fin 2) (Fin 2) Kinf) 0 0
        = (((theta3 K a t x)⁻¹ : GA) : Matrix (Fin 2) (Fin 2) Kinf) 0 0 * ((a : Kinf) * ((a⁻¹ : (Kinf)ˣ) : Kinf)) := by
          rw [Units.mul_inv, mul_one]
      _ = ((a⁻¹ : (Kinf)ˣ) : Kinf) := by rw [← mul_assoc, h00, one_mul]
  unfold Lam3
  rw [e00, e01, e11, hinv]
  congr 1; congr 1; congr 1; congr 1
  rw [mul_comm ((a : Kinf)) x, mul_assoc, Units.mul_inv, mul_one]

def U3 : Set (Fin 3 → MS) :=
  {p | IsUnit ((InfiniteAdeleRing.ringEquiv_mixedSpace K).symm (p 0)) ∧ IsUnit ((InfiniteAdeleRing.ringEquiv_mixedSpace K).symm (p 1))}

theorem isOpen_U3 : IsOpen (U3 K) :=
  ((isOpen_setOf_isUnit K).preimage ((continuous_iota_symm K).comp (continuous_apply 0))).inter
    ((isOpen_setOf_isUnit K).preimage ((continuous_iota_symm K).comp (continuous_apply 1)))

theorem Lam3_mem_U3 {g : GA} (hg : (g : Matrix (Fin 2) (Fin 2) Kinf) 1 0 = 0) : Lam3 K g ∈ U3 K := by
  obtain ⟨h00, h11⟩ := inv_entries_of_upper K hg
  have hdet : IsUnit ((g : Matrix (Fin 2) (Fin 2) Kinf) 0 0 * (g : Matrix (Fin 2) (Fin 2) Kinf) 1 1) := by
    have hd : IsUnit ((g : Matrix (Fin 2) (Fin 2) Kinf).det) := (g : GA).isUnit.map Matrix.detMonoidHom
    rw [Matrix.det_fin_two, hg, mul_zero, sub_zero] at hd
    exact hd
  obtain ⟨h00u, h11u⟩ := IsUnit.mul_iff.mp hdet
  have hi00 : IsUnit (((g⁻¹ : GA) : Matrix (Fin 2) (Fin 2) Kinf) 0 0) :=
    isUnit_iff_exists_inv.mpr ⟨_, h00⟩
  refine ⟨?_, ?_⟩
  · show IsUnit ((InfiniteAdeleRing.ringEquiv_mixedSpace K).symm (Lam3 K g 0))
    simp only [Lam3, Matrix.cons_val_zero, RingEquiv.symm_apply_apply]
    exact h00u
  · show IsUnit ((InfiniteAdeleRing.ringEquiv_mixedSpace K).symm (Lam3 K g 1))
    simp only [Lam3, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_zero, RingEquiv.symm_apply_apply]
    exact h11u

theorem continuous_archEntries' : Continuous (archEntries K : GA → Fin 2 → Fin 2 → MS) :=
  continuous_pi fun i => continuous_pi fun j =>
    (AdelicBox.continuous_ringEquiv_mixedSpace K).comp (Units.continuous_val.matrix_elem i j)

end Theta

section Main

set_option maxHeartbeats 6400000 in
theorem main_auxT
    {X : Type} [TopologicalSpace X] [CompactSpace X] [T2Space X] [SecondCountableTopology X]
    [MeasurableSpace X] [BorelSpace X]
    (κ : Measure X) [IsFiniteMeasureOnCompacts κ]
    (A B : X → GA) (hAc : Continuous A) (hBc : Continuous B)
    (fa : GA → ℂ) (hfa : IsArchTestFactor K fa) :
    ∃ Ψ : (Fin 3 → MS) → ℂ,
      ContDiff ℝ (⊤ : ℕ∞) Ψ ∧ HasCompactSupport Ψ ∧
      (∃ Ca : Set ((Kinf)ˣ × (Kinf)ˣ), IsCompact Ca ∧
        ∀ p ∈ tsupport Ψ, ∃ q ∈ Ca,
          p 0 = InfiniteAdeleRing.ringEquiv_mixedSpace K ((q.1 : (Kinf)ˣ) : Kinf) ∧ p 1 = InfiniteAdeleRing.ringEquiv_mixedSpace K ((q.2 : (Kinf)ˣ) : Kinf)) ∧
      ∀ (a t : (Kinf)ˣ) (x : Kinf),
        ∫ k, fa (B k * (diagUnits2 a t * unipotentGL2 x) * A k) ∂κ = Ψ ![InfiniteAdeleRing.ringEquiv_mixedSpace K (a : Kinf), InfiniteAdeleRing.ringEquiv_mixedSpace K (t : Kinf), InfiniteAdeleRing.ringEquiv_mixedSpace K x] := by
  obtain ⟨⟨Φ₀, hΦ₀, hrepr⟩, hsupp⟩ := hfa
  haveI := secondCountableTopology_infiniteAdeleRing K
  haveI := secondCountableTopology_gl K
  haveI := t2Space_gl K

  obtain ⟨T₂, hT₂⟩ : ∃ T₂ : Set GA, T₂ = (fun q : X × GA × X => (B q.1)⁻¹ * q.2.1 * (A q.2.2)⁻¹) ''
      (Set.univ ×ˢ (tsupport fa ×ˢ Set.univ)) := ⟨_, rfl⟩
  have hT2c : IsCompact T₂ := by
    rw [hT₂]
    refine (isCompact_univ.prod (hsupp.prod isCompact_univ)).image ?_
    exact ((hBc.comp continuous_fst).inv.mul (continuous_fst.comp continuous_snd)).mul
      ((hAc.comp (continuous_snd.comp continuous_snd)).inv)
  obtain ⟨B₀, hB₀⟩ : ∃ B₀ : Set GA, B₀ = {g : GA | ((g : GA) : Matrix (Fin 2) (Fin 2) Kinf) 1 0 = 0} := ⟨_, rfl⟩
  have hB0c : IsClosed B₀ := by
    rw [hB₀]; exact isClosed_eq (Units.continuous_val.matrix_elem 1 0) continuous_const
  have hT3c : IsCompact (T₂ ∩ B₀) := hT2c.inter_right hB0c
  have hSc : IsCompact (Lam3 K '' (T₂ ∩ B₀)) := hT3c.image (continuous_Lam3 K)
  have hSU : Lam3 K '' (T₂ ∩ B₀) ⊆ U3 K := by
    rintro _ ⟨g, hg, rfl⟩
    have hg2 : (g : Matrix (Fin 2) (Fin 2) Kinf) 1 0 = 0 := by
      have h := hg.2; rw [hB₀] at h; exact h
    exact Lam3_mem_U3 K hg2
  have hA0c : IsCompact (archEntries K '' (Set.range A ∪ Set.range B)) :=
    ((isCompact_range hAc).union (isCompact_range hBc)).image (continuous_archEntries' K)
  have hmem : ∀ (a t : (Kinf)ˣ) (x : Kinf) (k : X),
      fa (B k * theta3 K a t x * A k) ≠ 0 → theta3 K a t x ∈ T₂ ∩ B₀ := by
    intro a t x k h
    refine ⟨?_, ?_⟩
    · rw [hT₂]
      refine ⟨(k, B k * theta3 K a t x * A k, k), ?_, ?_⟩
      · exact Set.mk_mem_prod (Set.mem_univ _) (Set.mk_mem_prod (subset_tsupport _ h) (Set.mem_univ _))
      · show (B k)⁻¹ * (B k * theta3 K a t x * A k) * (A k)⁻¹ = theta3 K a t x
        group
    · rw [hB₀]; exact theta3_one_zero K a t x

  obtain ⟨χp, hχp, hχpc, hχp1, hχpU⟩ :=
    exists_smooth_bump (E := Fin 3 → MS) hSc (isOpen_U3 K) hSU
  obtain ⟨χA, hχA, hχAc, hχA1, -⟩ :=
    exists_smooth_bump (E := Fin 2 → Fin 2 → MS) hA0c isOpen_univ (Set.subset_univ _)

  obtain ⟨Ψ, hΨ⟩ : ∃ Ψ : ((Fin 2 → Fin 2 → MS) × (Fin 2 → Fin 2 → MS)) × (Fin 3 → MS) → ℂ,
      Ψ = fun q => ((χp q.2 * χA q.1.1 * χA q.1.2 : ℝ) : ℂ) *
        Φ₀ (conjM K q.1.1 q.1.2 (Mmat3 K q.2)) := ⟨_, rfl⟩
  have hΨs : ContDiff ℝ (⊤ : ℕ∞) Ψ := by
    rw [hΨ]
    refine ContDiff.mul ?_ (hΦ₀.comp (contDiff_conjM_Mmat3 K))
    refine Complex.ofRealCLM.contDiff.comp ?_
    exact ((hχp.comp contDiff_snd).mul (hχA.comp (contDiff_fst.comp contDiff_fst))).mul
      (hχA.comp (contDiff_snd.comp contDiff_fst))
  have hΨapply : ∀ q, Ψ q = ((χp q.2 * χA q.1.1 * χA q.1.2 : ℝ) : ℂ) *
        Φ₀ (conjM K q.1.1 q.1.2 (Mmat3 K q.2)) := fun q => by rw [hΨ]
  have hΨz : ∀ q : ((Fin 2 → Fin 2 → MS) × (Fin 2 → Fin 2 → MS)) × (Fin 3 → MS),
      χp q.2 * χA q.1.1 * χA q.1.2 = 0 → Ψ q = 0 := by
    intro q hq
    rw [hΨapply, hq, Complex.ofReal_zero, zero_mul]
  have hΨc : HasCompactSupport Ψ := by
    refine HasCompactSupport.intro ((hχAc.prod hχAc).prod hχpc) fun q hq => hΨz q ?_
    simp only [Set.mem_prod, not_and_or] at hq
    rcases hq with (hA | hB) | hp
    · rw [image_eq_zero_of_notMem_tsupport hA]; ring
    · rw [image_eq_zero_of_notMem_tsupport hB]; ring
    · rw [image_eq_zero_of_notMem_tsupport hp]; ring
  obtain ⟨c, hc⟩ : ∃ c : X → (Fin 2 → Fin 2 → MS) × (Fin 2 → Fin 2 → MS),
      c = fun k : X => (archEntries K (A k), archEntries K (B k)) := ⟨_, rfl⟩
  have hcc : Continuous c := by
    rw [hc]
    exact ((continuous_archEntries' K).comp hAc).prodMk ((continuous_archEntries' K).comp hBc)
  obtain ⟨w, hw⟩ : ∃ w : X → ℝ, w = fun _ => 1 := ⟨_, rfl⟩
  have hwc : Continuous w := by rw [hw]; exact continuous_const
  have hws : HasCompactSupport w :=
    IsCompact.of_isClosed_subset isCompact_univ (isClosed_tsupport _) (Set.subset_univ _)

  obtain ⟨G, hG⟩ : ∃ G : (Fin 3 → MS) → ℂ, G = fun p => ∫ k, w k • Ψ (c k, p) ∂κ := ⟨_, rfl⟩
  have hGs : ContDiff ℝ (⊤ : ℕ∞) G := by
    rw [hG]
    exact MeasureTheory.contDiff_integral_smul_comp_of_contDiff_of_hasCompactSupport κ c hcc w hwc hws Ψ hΨs hΨc
  have hG0 : ∀ p, χp p = 0 → G p = 0 := by
    intro p hp
    have hz : (fun k : X => w k • Ψ (c k, p)) = fun _ => 0 := by
      funext k
      rw [hΨz (c k, p) (by simp only [hp, zero_mul]), smul_zero]
    rw [hG]
    show (∫ k, w k • Ψ (c k, p) ∂κ) = 0
    rw [hz, integral_zero]

  have key : ∀ (a t : (Kinf)ˣ) (x : Kinf) (k : X),
      w k • Ψ (c k, ![InfiniteAdeleRing.ringEquiv_mixedSpace K (a : Kinf), InfiniteAdeleRing.ringEquiv_mixedSpace K (t : Kinf), InfiniteAdeleRing.ringEquiv_mixedSpace K x]) = fa (B k * theta3 K a t x * A k) := by
    intro a t x k
    have hk' : archEntries K (B k) ∈ archEntries K '' (Set.range A ∪ Set.range B) :=
      ⟨B k, Or.inr ⟨k, rfl⟩, rfl⟩
    have hk : archEntries K (A k) ∈ archEntries K '' (Set.range A ∪ Set.range B) :=
      ⟨A k, Or.inl ⟨k, rfl⟩, rfl⟩
    rw [hΨapply, hw, hc]
    simp only []
    rw [conjM_archEntries3 K, ← hrepr, hχA1 _ hk, hχA1 _ hk', one_smul]
    by_cases h0 : fa (B k * theta3 K a t x * A k) = 0
    · rw [h0, mul_zero]
    · obtain hT := hmem a t x k h0
      have h1 : χp ![InfiniteAdeleRing.ringEquiv_mixedSpace K (a : Kinf), InfiniteAdeleRing.ringEquiv_mixedSpace K (t : Kinf), InfiniteAdeleRing.ringEquiv_mixedSpace K x] = 1 :=
        hχp1 _ ⟨_, hT, Lam3_theta3 K a t x⟩
      rw [h1]
      simp only [mul_one, Complex.ofReal_one, one_mul]
  have hGval : ∀ (a t : (Kinf)ˣ) (x : Kinf),
      G ![InfiniteAdeleRing.ringEquiv_mixedSpace K (a : Kinf), InfiniteAdeleRing.ringEquiv_mixedSpace K (t : Kinf), InfiniteAdeleRing.ringEquiv_mixedSpace K x] =
        ∫ k : X, fa (B k * (diagUnits2 a t * unipotentGL2 x) * A k) ∂κ := by
    intro a t x
    rw [hG]
    show (∫ k, w k • Ψ (c k, _) ∂κ) = _
    refine integral_congr_ae (Filter.Eventually.of_forall fun k => ?_)
    exact key a t x k
  have hGc : HasCompactSupport G :=
    HasCompactSupport.intro hχpc fun p hp => hG0 p (image_eq_zero_of_notMem_tsupport hp)
  have hGt : tsupport G ⊆ tsupport χp := by
    intro p hp
    by_contra h
    have hev : G =ᶠ[nhds p] 0 := by
      filter_upwards [(isClosed_tsupport χp).isOpen_compl.mem_nhds h] with p' hp'
      exact hG0 p' (image_eq_zero_of_notMem_tsupport hp')
    exact (notMem_tsupport_iff_eventuallyEq.mpr hev) hp

  have hUE := NumberField.InfiniteAdeleRing.isEmbedding_units_val K
  obtain ⟨C, hC⟩ : ∃ C : Fin 3 → Set ((Kinf)ˣ), C = fun i =>
      Units.val ⁻¹' ((fun p : Fin 3 → MS => (InfiniteAdeleRing.ringEquiv_mixedSpace K).symm (p i)) '' tsupport χp) := ⟨_, rfl⟩
  have hCc : ∀ i : Fin 3, (i = 0 ∨ i = 1) → IsCompact (C i) := by
    intro i hi
    rw [hC]
    refine hUE.isInducing.isCompact_iff.mpr ?_
    have hsub : (fun p : Fin 3 → MS => (InfiniteAdeleRing.ringEquiv_mixedSpace K).symm (p i)) '' tsupport χp ⊆ Set.range (Units.val : (Kinf)ˣ → Kinf) := by
      rintro _ ⟨p, hp, rfl⟩
      have hpU := hχpU hp
      rcases hi with rfl | rfl
      · obtain ⟨u, hu⟩ := hpU.1; exact ⟨u, hu⟩
      · obtain ⟨u, hu⟩ := hpU.2; exact ⟨u, hu⟩
    rw [Set.image_preimage_eq_of_subset hsub]
    exact hχpc.image ((continuous_iota_symm K).comp (continuous_apply i))
  refine ⟨G, hGs, hGc, ⟨C 0 ×ˢ C 1, (hCc 0 (Or.inl rfl)).prod (hCc 1 (Or.inr rfl)), fun p hp => ?_⟩,
    fun a t x => (hGval a t x).symm⟩
  have hp' := hGt hp
  have hpU := hχpU hp'
  obtain ⟨u₀, hu₀⟩ := hpU.1
  obtain ⟨u₁, hu₁⟩ := hpU.2
  refine ⟨(u₀, u₁), ⟨?_, ?_⟩, ?_, ?_⟩
  · show u₀ ∈ C 0
    rw [hC]; exact ⟨p, hp', hu₀.symm⟩
  · show u₁ ∈ C 1
    rw [hC]; exact ⟨p, hp', hu₁.symm⟩
  · show p 0 = InfiniteAdeleRing.ringEquiv_mixedSpace K (u₀ : Kinf)
    rw [hu₀, RingEquiv.apply_symm_apply]
  · show p 1 = InfiniteAdeleRing.ringEquiv_mixedSpace K (u₁ : Kinf)
    rw [hu₁, RingEquiv.apply_symm_apply]

end Main

end TwKAvg

namespace TwKAvgE

open AutomorphicForm
open scoped TensorProduct TensorProduct.RightActions Classical

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

theorem continuous_sigmaTensor (σ : L ≃ₐ[K] L) :
    Continuous (AutomorphicForm.sigmaTensor K L (InfiniteAdeleRing K) σ) := by
  let f : (L ⊗[K] InfiniteAdeleRing K) →ₗ[InfiniteAdeleRing K] (L ⊗[K] InfiniteAdeleRing K) :=
    { toFun := AutomorphicForm.sigmaTensor K L (InfiniteAdeleRing K) σ
      map_add' := map_add _
      map_smul' := fun r y => by
        have h1 : AutomorphicForm.sigmaTensor K L (InfiniteAdeleRing K) σ ((1 : L) ⊗ₜ[K] r) = (1 : L) ⊗ₜ[K] r := by
          show (Algebra.TensorProduct.map (σ : L →ₐ[K] L) (AlgHom.id K (InfiniteAdeleRing K))) ((1 : L) ⊗ₜ[K] r) = _
          rw [Algebra.TensorProduct.map_tmul, map_one]; rfl
        rw [rightActions_smul_eq, map_mul, h1, rightActions_smul_eq, RingHom.id_apply] }
  haveI : ContinuousAdd (L ⊗[K] InfiniteAdeleRing K) :=
    (isTopologicalRing_tensor K L (InfiniteAdeleRing K)).toContinuousAdd
  exact IsModuleTopology.continuous_of_linearMap f

theorem archIdentGL_theta (d₁ d₂ : (L ⊗[K] InfiniteAdeleRing K)ˣ) (y : L ⊗[K] InfiniteAdeleRing K) :
    archIdentGL K L (diagUnits2 d₁ d₂ * unipotentGL2 y) =
      TwKAvg.theta3 L (Units.map (archIdent K L : (L ⊗[K] InfiniteAdeleRing K) →* InfiniteAdeleRing L) d₁)
        (Units.map (archIdent K L : (L ⊗[K] InfiniteAdeleRing K) →* InfiniteAdeleRing L) d₂) (archIdent K L y) := by
  apply Units.ext
  rw [TwKAvg.coe_theta3]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [archIdentGL, Matrix.GeneralLinearGroup.map, diagUnits2, unipotentGL2, Matrix.mul_apply, Fin.sum_univ_two]

end TwKAvgE

end

open MeasureTheory NumberField NumberField.AdelicLevel IsDedekindDomain AutomorphicForm in
attribute [local instance] AutomorphicForm.twistedCentralizerBorel in
open scoped TensorProduct TensorProduct.RightActions in
open scoped Classical in
theorem solution
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (σ : L ≃ₐ[K] L) (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ) (hdeg : (Module.finrank K L).Prime)
    (φa : GL (Fin 2) (InfiniteAdeleRing L) → ℂ) (hφa : AutomorphicForm.IsArchTestFactor L φa)
    (κ : @Measure (↥(⨅ w : InfinitePlace L,
        (AutomorphicForm.WindowedSiegel.rowIsometrySubgroup w.Completion).comap
          ((archComponent L w).comp (AutomorphicForm.archIdentGL K L)) :
          Subgroup (GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K)))) (borel _))
    (hκ : @Measure.IsHaarMeasure _ _ _ (borel _) κ) :
    ∃ Φ : (Fin 3 → NumberField.mixedEmbedding.mixedSpace L) → ℂ,
      ContDiff ℝ (⊤ : ℕ∞) Φ ∧ HasCompactSupport Φ ∧
      (∃ C : Set ((L ⊗[K] InfiniteAdeleRing K)ˣ × (L ⊗[K] InfiniteAdeleRing K)ˣ), IsCompact C ∧
        ∀ p ∈ tsupport Φ, ∃ q ∈ C,
          p 0 = NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace L (AutomorphicForm.archIdent K L ((q.1 : (L ⊗[K] InfiniteAdeleRing K)ˣ) : (L ⊗[K] InfiniteAdeleRing K))) ∧
          p 1 = NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace L (AutomorphicForm.archIdent K L ((q.2 : (L ⊗[K] InfiniteAdeleRing K)ˣ) : (L ⊗[K] InfiniteAdeleRing K)))) ∧
      ∀ (d₁ d₂ : (L ⊗[K] InfiniteAdeleRing K)ˣ) (y : (L ⊗[K] InfiniteAdeleRing K)),
        @integral _ ℂ _ _ (borel _) κ (fun k =>
            φa (AutomorphicForm.archIdentGL K L
              ((k : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K))⁻¹ * (diagUnits2 d₁ d₂ * AutomorphicForm.unipotentGL2 y) *
                AutomorphicForm.sigmaGL K L (InfiniteAdeleRing K) σ (k : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K))))) =
          Φ ![NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace L (AutomorphicForm.archIdent K L (d₁ : (L ⊗[K] InfiniteAdeleRing K))), NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace L (AutomorphicForm.archIdent K L (d₂ : (L ⊗[K] InfiniteAdeleRing K))), NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace L (AutomorphicForm.archIdent K L y)] := by
  classical

  letI mK : MeasurableSpace ↥(⨅ w : InfinitePlace L,
        (AutomorphicForm.WindowedSiegel.rowIsometrySubgroup w.Completion).comap
          ((archComponent L w).comp (AutomorphicForm.archIdentGL K L)) :
          Subgroup (GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K))) := borel _
  haveI : BorelSpace ↥(⨅ w : InfinitePlace L,
        (AutomorphicForm.WindowedSiegel.rowIsometrySubgroup w.Completion).comap
          ((archComponent L w).comp (AutomorphicForm.archIdentGL K L)) :
          Subgroup (GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K))) := ⟨rfl⟩
  haveI := hκ

  haveI := TwKAvg.secondCountableTopology_gl L
  haveI := TwKAvg.t2Space_gl L
  let eG := AutomorphicForm.archIdentGLEquiv K L
  haveI : SecondCountableTopology (GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) :=
    eG.toHomeomorph.isEmbedding.secondCountableTopology
  haveI : T2Space (GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) := eG.toHomeomorph.isEmbedding.t2Space
  have hKcL := (NumberField.InfiniteAdeleRing.exists_mem_borelSubgroup_mul_eq_and_isCompact_iInf_rowIsometrySubgroup L).2
  have hset : ((⨅ w : InfinitePlace L,
        (AutomorphicForm.WindowedSiegel.rowIsometrySubgroup w.Completion).comap
          ((archComponent L w).comp (AutomorphicForm.archIdentGL K L)) :
          Subgroup (GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K))) : Set (GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K))) =
      eG ⁻¹' ((⨅ w : InfinitePlace L,
        (AutomorphicForm.WindowedSiegel.rowIsometrySubgroup w.Completion).comap (archComponent L w) :
          Subgroup (GL (Fin 2) (InfiniteAdeleRing L))) : Set (GL (Fin 2) (InfiniteAdeleRing L))) := by
    ext k
    simp only [Set.mem_preimage, SetLike.mem_coe, Subgroup.mem_iInf, Subgroup.mem_comap, MonoidHom.coe_comp,
      Function.comp_apply]
    rfl
  have hKcEc : IsCompact ((⨅ w : InfinitePlace L,
        (AutomorphicForm.WindowedSiegel.rowIsometrySubgroup w.Completion).comap
          ((archComponent L w).comp (AutomorphicForm.archIdentGL K L)) :
          Subgroup (GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K))) : Set (GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K))) := by
    rw [hset]; exact eG.toHomeomorph.isCompact_preimage.mpr hKcL
  haveI : CompactSpace ↥(⨅ w : InfinitePlace L,
        (AutomorphicForm.WindowedSiegel.rowIsometrySubgroup w.Completion).comap
          ((archComponent L w).comp (AutomorphicForm.archIdentGL K L)) :
          Subgroup (GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K))) := isCompact_iff_compactSpace.mp hKcEc
  haveI : SecondCountableTopology ↥(⨅ w : InfinitePlace L,
        (AutomorphicForm.WindowedSiegel.rowIsometrySubgroup w.Completion).comap
          ((archComponent L w).comp (AutomorphicForm.archIdentGL K L)) :
          Subgroup (GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K))) := TopologicalSpace.Subtype.secondCountableTopology _

  haveI := AutomorphicForm.isTopologicalRing_tensor K L (InfiniteAdeleRing K)
  have hσc : Continuous (AutomorphicForm.sigmaGL K L (InfiniteAdeleRing K) σ) :=
    AutomorphicForm.continuous_glMap _ (TwKAvgE.continuous_sigmaTensor K L σ)
  have heGc : Continuous (AutomorphicForm.archIdentGL K L) := eG.continuous
  obtain ⟨Ψ, hΨs, hΨc, ⟨Ca, hCac, hCa⟩, hΨ⟩ := TwKAvg.main_auxT L (X := ↥(⨅ w : InfinitePlace L,
        (AutomorphicForm.WindowedSiegel.rowIsometrySubgroup w.Completion).comap
          ((archComponent L w).comp (AutomorphicForm.archIdentGL K L)) :
          Subgroup (GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K)))) κ
    (fun k => AutomorphicForm.archIdentGL K L (AutomorphicForm.sigmaGL K L (InfiniteAdeleRing K) σ (k : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K))))
    (fun k => AutomorphicForm.archIdentGL K L ((k : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K))⁻¹))
    (heGc.comp (hσc.comp continuous_subtype_val)) (heGc.comp continuous_subtype_val.inv) φa hφa

  let u : (InfiniteAdeleRing L)ˣ → (L ⊗[K] InfiniteAdeleRing K)ˣ :=
    Units.map ((AutomorphicForm.archIdentEquiv K L).symm : InfiniteAdeleRing L →* (L ⊗[K] InfiniteAdeleRing K))
  have huc : Continuous u :=
    Continuous.units_map _ (AutomorphicForm.archIdentHomeomorph K L).symm.continuous
  have hu : ∀ v : (InfiniteAdeleRing L)ˣ, AutomorphicForm.archIdent K L ((u v : (L ⊗[K] InfiniteAdeleRing K)ˣ) : L ⊗[K] InfiniteAdeleRing K) = (v : InfiniteAdeleRing L) :=
    fun v => (AutomorphicForm.archIdentEquiv K L).apply_symm_apply v
  refine ⟨Ψ, hΨs, hΨc, ⟨(fun q => (u q.1, u q.2)) '' Ca,
    hCac.image ((huc.comp continuous_fst).prodMk (huc.comp continuous_snd)), fun p hp => ?_⟩, fun d₁ d₂ y => ?_⟩
  · obtain ⟨q, hq, h0, h1⟩ := hCa p hp
    exact ⟨(u q.1, u q.2), ⟨q, hq, rfl⟩, by rw [hu]; exact h0, by rw [hu]; exact h1⟩
  · have := hΨ (Units.map (AutomorphicForm.archIdent K L : (L ⊗[K] InfiniteAdeleRing K) →* InfiniteAdeleRing L) d₁)
      (Units.map (AutomorphicForm.archIdent K L : (L ⊗[K] InfiniteAdeleRing K) →* InfiniteAdeleRing L) d₂) (AutomorphicForm.archIdent K L y)
    have hint : (∫ k, φa (AutomorphicForm.archIdentGL K L
          ((k : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K))⁻¹ * (diagUnits2 d₁ d₂ * AutomorphicForm.unipotentGL2 y) *
            AutomorphicForm.sigmaGL K L (InfiniteAdeleRing K) σ (k : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K)))) ∂κ) =
        ∫ k, φa (AutomorphicForm.archIdentGL K L ((k : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K))⁻¹) *
          (diagUnits2 (Units.map (AutomorphicForm.archIdent K L : (L ⊗[K] InfiniteAdeleRing K) →* InfiniteAdeleRing L) d₁)
            (Units.map (AutomorphicForm.archIdent K L : (L ⊗[K] InfiniteAdeleRing K) →* InfiniteAdeleRing L) d₂) *
            AutomorphicForm.unipotentGL2 (AutomorphicForm.archIdent K L y)) *
          AutomorphicForm.archIdentGL K L (AutomorphicForm.sigmaGL K L (InfiniteAdeleRing K) σ (k : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K)))) ∂κ := by
      refine integral_congr_ae (Filter.Eventually.of_forall fun k => ?_)
      have hθ := TwKAvgE.archIdentGL_theta K L d₁ d₂ y
      simp only [TwKAvg.theta3] at hθ
      beta_reduce
      rw [map_mul, map_mul, hθ]
    rw [hint, this]
    rfl

end S_AutomorphicForm_exists_contDiff_hasCompactSupport_forall_integral_twistedConj_diagUnits2_mul_unipotentGL2_eq
end P2MW
export P2MW.S_AutomorphicForm_exists_contDiff_hasCompactSupport_forall_integral_twistedConj_diagUnits2_mul_unipotentGL2_eq (solution)

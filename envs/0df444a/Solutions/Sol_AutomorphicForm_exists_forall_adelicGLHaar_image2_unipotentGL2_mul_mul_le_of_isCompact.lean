-- Prove2me | solution 1 for AutomorphicForm.exists_forall_adelicGLHaar_image2_unipotentGL2_mul_mul_le_of_isCompact
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/032dcfbe-bd77-5ac1-a3d4-f49104511bc9

import Definitions.Def_AutomorphicForm_CentreCutSiegelSet
import Definitions.Def_AutomorphicForm_ConstantTerm
import Definitions.Def_NumberField_AdelicBox
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_forall_adelicGLHaar_image2_unipotentGL2_mul_mul_le_of_isCompact

set_option autoImplicit false

open NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar AutomorphicForm AutomorphicForm.WindowedSiegel MeasureTheory

open scoped ProbabilityTheory ENNReal NNReal

attribute [local instance] NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.borelSpace_adeleBorel
  NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel

noncomputable section

namespace HighCuspEnds

private theorem r1_loc_unipotentGL2_apply {L : Type*} [NormedField L] (t : L) :
    ((unipotentGL2 t : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) 0 0 = 1 ∧
    ((unipotentGL2 t : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) 0 1 = t ∧
    ((unipotentGL2 t : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧
    ((unipotentGL2 t : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) 1 1 = 1 :=
  ⟨by rw [unipotentGL2_coe]; rfl, by rw [unipotentGL2_coe]; rfl,
    by rw [unipotentGL2_coe]; rfl, by rw [unipotentGL2_coe]; rfl⟩

private theorem r1_loc_conj_sub_one_apply {L : Type*} [NormedField L] (g : GL (Fin 2) L) (t : L)
    (i j : Fin 2) :
    ((g⁻¹ * unipotentGL2 t * g : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) i j
        - (1 : Matrix (Fin 2) (Fin 2) L) i j
      = t * ((g⁻¹ : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) i 0
          * (g : Matrix (Fin 2) (Fin 2) L) 1 j := by
  obtain ⟨hN00, hN01, hN10, hN11⟩ := r1_loc_unipotentGL2_apply (L := L) t
  have hval : ((g⁻¹ * unipotentGL2 t * g : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L)
      = ((g⁻¹ : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L)
          * ((unipotentGL2 t : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L)
          * (g : Matrix (Fin 2) (Fin 2) L) := by
    rw [Units.val_mul, Units.val_mul]
  have hone : (1 : Matrix (Fin 2) (Fin 2) L)
      = ((g⁻¹ : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) * (g : Matrix (Fin 2) (Fin 2) L) :=
    (Units.inv_mul g).symm
  rw [hval, hone]
  simp only [Matrix.mul_apply, Fin.sum_univ_two, hN00, hN01, hN10, hN11]
  ring

private theorem r1_loc_norm_inv_apply_zero {L : Type*} [NormedField L] (g : GL (Fin 2) L)
    (i : Fin 2) :
    ‖((g⁻¹ : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) i 0‖
      = ‖(g : Matrix (Fin 2) (Fin 2) L).det‖⁻¹ * ‖(g : Matrix (Fin 2) (Fin 2) L).adjugate i 0‖ := by
  have hcoe : ((g⁻¹ : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L)
      = ((g : Matrix (Fin 2) (Fin 2) L))⁻¹ := Matrix.coe_units_inv g
  rw [hcoe, Matrix.inv_def, Ring.inverse_eq_inv, Matrix.smul_apply, norm_smul, norm_inv]

private theorem r1_loc_real_bound {T D x y R : ℝ} (hT : 0 ≤ T) (hD : 0 < D) (hxy : x * y ≤ R) :
    T * (D⁻¹ * x) * y ≤ T / (D / R) := by
  rw [div_div_eq_mul_div, le_div_iff₀ hD]
  calc T * (D⁻¹ * x) * y * D = T * (x * y) * (D⁻¹ * D) := by ring
    _ = T * (x * y) := by rw [inv_mul_cancel₀ hD.ne', mul_one]
    _ ≤ T * R := mul_le_mul_of_nonneg_left hxy hT

private theorem r1_norm_conj_unipotentGL2_sub_one_apply_le {L : Type*} [NormedField L]
    (g : GL (Fin 2) L) (t : L) (i j : Fin 2) :
    ‖((g⁻¹ * unipotentGL2 t * g : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) i j
        - (1 : Matrix (Fin 2) (Fin 2) L) i j‖ ≤ ‖t‖ / localHeight g := by
  have hdet0 : (g : Matrix (Fin 2) (Fin 2) L).det ≠ 0 := Matrix.GeneralLinearGroup.det_ne_zero g
  have hdetpos : 0 < ‖(g : Matrix (Fin 2) (Fin 2) L).det‖ := by
    rw [norm_pos_iff]
    exact hdet0
  have hA := sq_nonneg (‖(g : Matrix (Fin 2) (Fin 2) L) 1 0‖ - ‖(g : Matrix (Fin 2) (Fin 2) L) 1 1‖)
  have hB := sq_nonneg ‖(g : Matrix (Fin 2) (Fin 2) L) 1 0‖
  have hC := sq_nonneg ‖(g : Matrix (Fin 2) (Fin 2) L) 1 1‖
  rw [r1_loc_conj_sub_one_apply g t i j, norm_mul, norm_mul, r1_loc_norm_inv_apply_zero g i]
  refine r1_loc_real_bound (norm_nonneg t) hdetpos ?_
  rw [Matrix.adjugate_fin_two]
  fin_cases i <;> fin_cases j
  · show ‖(g : Matrix (Fin 2) (Fin 2) L) 1 1‖ * ‖(g : Matrix (Fin 2) (Fin 2) L) 1 0‖
      ≤ ‖(g : Matrix (Fin 2) (Fin 2) L) 1 0‖ ^ 2 + ‖(g : Matrix (Fin 2) (Fin 2) L) 1 1‖ ^ 2
    nlinarith [hA, hB, hC]
  · show ‖(g : Matrix (Fin 2) (Fin 2) L) 1 1‖ * ‖(g : Matrix (Fin 2) (Fin 2) L) 1 1‖
      ≤ ‖(g : Matrix (Fin 2) (Fin 2) L) 1 0‖ ^ 2 + ‖(g : Matrix (Fin 2) (Fin 2) L) 1 1‖ ^ 2
    nlinarith [hA, hB, hC]
  · show ‖-(g : Matrix (Fin 2) (Fin 2) L) 1 0‖ * ‖(g : Matrix (Fin 2) (Fin 2) L) 1 0‖
      ≤ ‖(g : Matrix (Fin 2) (Fin 2) L) 1 0‖ ^ 2 + ‖(g : Matrix (Fin 2) (Fin 2) L) 1 1‖ ^ 2
    rw [norm_neg]
    nlinarith [hA, hB, hC]
  · show ‖-(g : Matrix (Fin 2) (Fin 2) L) 1 0‖ * ‖(g : Matrix (Fin 2) (Fin 2) L) 1 1‖
      ≤ ‖(g : Matrix (Fin 2) (Fin 2) L) 1 0‖ ^ 2 + ‖(g : Matrix (Fin 2) (Fin 2) L) 1 1‖ ^ 2
    rw [norm_neg]
    nlinarith [hA, hB, hC]

private theorem r1_norm_conj_unipotentGL2_apply_le {L : Type*} [NormedField L]
    (g : GL (Fin 2) L) (t : L) {c r : ℝ} (hc : 0 < c) (hr : 0 ≤ r) (hcg : c ≤ localHeight g) (ht : ‖t‖ ≤ r) (i j : Fin 2) :
    ‖((g⁻¹ * unipotentGL2 t * g : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) i j‖ ≤ 1 + r / c := by
  have hsub := r1_norm_conj_unipotentGL2_sub_one_apply_le g t i j
  have hone : ‖(1 : Matrix (Fin 2) (Fin 2) L) i j‖ ≤ 1 := by
    rw [Matrix.one_apply]
    split_ifs
    · exact norm_one.le
    · exact norm_zero.trans_le zero_le_one
  have hdiv : ‖t‖ / localHeight g ≤ r / c := div_le_div₀ hr ht hc hcg
  calc ‖((g⁻¹ * unipotentGL2 t * g : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) i j‖
      = ‖(((g⁻¹ * unipotentGL2 t * g : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) i j
          - (1 : Matrix (Fin 2) (Fin 2) L) i j) + (1 : Matrix (Fin 2) (Fin 2) L) i j‖ := by
        rw [sub_add_cancel]
    _ ≤ ‖((g⁻¹ * unipotentGL2 t * g : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) i j
          - (1 : Matrix (Fin 2) (Fin 2) L) i j‖ + ‖(1 : Matrix (Fin 2) (Fin 2) L) i j‖ :=
        norm_add_le _ _
    _ ≤ r / c + 1 := add_le_add (hsub.trans hdiv) hone
    _ = 1 + r / c := add_comm _ _

private theorem r1_unipotentGL2_inv {R : Type*} [CommRing R] (x : R) :
    (unipotentGL2 x)⁻¹ = unipotentGL2 (-x) :=
  inv_eq_of_mul_eq_one_right (by rw [← unipotentGL2_add, add_neg_cancel, unipotentGL2_zero])

section Adelic

variable (K : Type) [Field K] [NumberField K]

private theorem r1_archComponent_glArch_unipotentGL2 (w : InfinitePlace K) (b : AdeleRing (𝓞 K) K) :
    archComponent K w (glArch (𝓞 K) K (unipotentGL2 b)) = unipotentGL2 (b.1 w) := by
  ext i j
  rw [archComponent_apply, glArch_apply, unipotentGL2_coe, unipotentGL2_coe]
  fin_cases i <;> fin_cases j <;> rfl

private theorem r1_arch_entry_norm_le {c' u' d₁' d₂' rB : ℝ} (hc' : 0 < c') (hrB : 0 ≤ rB)
    {s : GL (Fin 2) (AdeleRing (𝓞 K) K)} (hs : s ∈ centreCutSiegelSet K c' u' d₁' d₂')
    {b : AdeleRing (𝓞 K) K} (hb : ∀ w : InfinitePlace K, ‖b.1 w‖ ≤ rB)
    (w : InfinitePlace K) (i j : Fin 2) :
    ‖(((s⁻¹ * unipotentGL2 b * s : GL (Fin 2) (AdeleRing (𝓞 K) K)) :
        Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) i j).1 w‖ ≤ 1 + rB / c' := by
  have hlh : c' ≤ localHeight (archComponent K w (glArch (𝓞 K) K s)) :=
    (mem_centreCutSiegelSet_iff.mp hs).2.1 w
  have hconj : archComponent K w (glArch (𝓞 K) K (s⁻¹ * unipotentGL2 b * s))
      = (archComponent K w (glArch (𝓞 K) K s))⁻¹ * unipotentGL2 (b.1 w)
          * archComponent K w (glArch (𝓞 K) K s) := by
    simp only [map_mul, map_inv, r1_archComponent_glArch_unipotentGL2]
  have hentry : (((s⁻¹ * unipotentGL2 b * s : GL (Fin 2) (AdeleRing (𝓞 K) K)) :
        Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) i j).1 w
      = (archComponent K w (glArch (𝓞 K) K (s⁻¹ * unipotentGL2 b * s)) :
          Matrix (Fin 2) (Fin 2) w.Completion) i j := rfl
  rw [hentry, hconj]
  exact r1_norm_conj_unipotentGL2_apply_le _ _ hc' hrB hlh (hb w) i j

private theorem r1_glFin_unipotentGL2_mem {b : AdeleRing (𝓞 K) K}
    (hb : b.2 ∈ AdelicLevel.integralFiniteAdeles (𝓞 K) K) :
    glFin (𝓞 K) K (unipotentGL2 b) ∈ finiteIntegralGL2 (𝓞 K) K := by
  have hneg : (-b).2 ∈ AdelicLevel.integralFiniteAdeles (𝓞 K) K := by
    rw [show (-b).2 = -b.2 from rfl, neg_eq_zero_sub]
    exact AdelicLevel.sub_mem_integralFiniteAdeles AdelicLevel.zero_mem_integralFiniteAdeles hb
  rw [mem_finiteIntegralGL2_iff, ← map_inv, r1_unipotentGL2_inv]
  refine ⟨fun i j => ?_, fun i j => ?_⟩
  · rw [glFin_apply, unipotentGL2_coe]
    fin_cases i <;> fin_cases j
    · exact AdelicLevel.one_mem_integralFiniteAdeles
    · exact hb
    · exact AdelicLevel.zero_mem_integralFiniteAdeles
    · exact AdelicLevel.one_mem_integralFiniteAdeles
  · rw [glFin_apply, unipotentGL2_coe]
    fin_cases i <;> fin_cases j
    · exact AdelicLevel.one_mem_integralFiniteAdeles
    · exact hneg
    · exact AdelicLevel.zero_mem_integralFiniteAdeles
    · exact AdelicLevel.one_mem_integralFiniteAdeles

private theorem r1_fin_entry_mem {s : GL (Fin 2) (AdeleRing (𝓞 K) K)}
    (hs : glFin (𝓞 K) K s ∈ finiteIntegralGL2 (𝓞 K) K) {b : AdeleRing (𝓞 K) K}
    (hb : b.2 ∈ AdelicLevel.integralFiniteAdeles (𝓞 K) K) (i j : Fin 2) :
    (((s⁻¹ * unipotentGL2 b * s : GL (Fin 2) (AdeleRing (𝓞 K) K)) :
        Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) i j).2
      ∈ AdelicLevel.integralFiniteAdeles (𝓞 K) K := by
  have hm : glFin (𝓞 K) K (s⁻¹ * unipotentGL2 b * s) ∈ finiteIntegralGL2 (𝓞 K) K := by
    rw [map_mul, map_mul, map_inv]
    exact mul_mem (mul_mem (inv_mem hs) (r1_glFin_unipotentGL2_mem K hb)) hs
  have h := (mem_finiteIntegralGL2_iff.mp hm).1 i j
  rwa [glFin_apply] at h

private theorem r1_isCompact_closure_box : IsCompact (closure (adelicBox K)) := by
  obtain ⟨C, hC, hsub⟩ := exists_isCompact_adelicBox_subset K
  exact hC.closure_of_subset hsub

private theorem r1_exists_box_bound :
    ∃ rB : ℝ, 0 ≤ rB ∧ ∀ b ∈ closure (adelicBox K), ∀ w : InfinitePlace K, ‖b.1 w‖ ≤ rB := by
  have hcont : Continuous fun b : AdeleRing (𝓞 K) K => ∑ w : InfinitePlace K, ‖b.1 w‖ :=
    continuous_finsetSum _ fun w _ => ((continuous_archEval K w).comp continuous_fst).norm
  obtain ⟨r, hr⟩ := (r1_isCompact_closure_box K).exists_bound_of_continuousOn hcont.continuousOn
  refine ⟨max r 0, le_max_right _ _, fun b hb w => ?_⟩
  refine le_trans (Finset.single_le_sum (f := fun v : InfinitePlace K => ‖b.1 v‖)
    (fun v _ => norm_nonneg _) (Finset.mem_univ w)) ?_
  exact ((le_abs_self _).trans ((Real.norm_eq_abs _).symm.le.trans (hr b hb))).trans (le_max_left _ _)

private theorem r1_snd_mem_of_mem_closure_box {b : AdeleRing (𝓞 K) K}
    (hb : b ∈ closure (adelicBox K)) : b.2 ∈ AdelicLevel.integralFiniteAdeles (𝓞 K) K := by
  have hcl : IsClosed {y : AdeleRing (𝓞 K) K | y.2 ∈ AdelicBox.integralFiniteAdeles (𝓞 K) K} :=
    (AdelicBox.isClosed_integralFiniteAdeles K).preimage continuous_snd
  exact closure_minimal (fun y hy => hy.2) hcl hb

private def r1_adeleBall (r : ℝ) : Set (AdeleRing (𝓞 K) K) :=
  {y | (∀ w : InfinitePlace K, ‖y.1 w‖ ≤ r) ∧ y.2 ∈ AdelicLevel.integralFiniteAdeles (𝓞 K) K}

private theorem r1_mem_adeleBall {r : ℝ} {y : AdeleRing (𝓞 K) K} :
    y ∈ r1_adeleBall K r ↔
      (∀ w : InfinitePlace K, ‖y.1 w‖ ≤ r) ∧ y.2 ∈ AdelicLevel.integralFiniteAdeles (𝓞 K) K :=
  Iff.rfl

private theorem r1_isCompact_adeleBall (r : ℝ) : IsCompact (r1_adeleBall K r) := by
  haveI : ∀ v : InfinitePlace K, ProperSpace v.Completion := fun v =>
    NumberField.AdelicBox.properSpace_completion K v
  have hS : IsCompact {x : InfiniteAdeleRing K | ∀ v, ‖x v‖ ≤ r} := by
    have : {x : InfiniteAdeleRing K | ∀ v, ‖x v‖ ≤ r} =
        Set.pi Set.univ fun v : InfinitePlace K => Metric.closedBall (0 : v.Completion) r := by
      ext x
      exact ⟨fun h v _ => mem_closedBall_zero_iff.mpr (h v),
        fun h v => mem_closedBall_zero_iff.mp (h v (Set.mem_univ v))⟩
    rw [this]
    exact isCompact_univ_pi fun v => isCompact_closedBall (0 : v.Completion) r
  have : IsCompact ({x : InfiniteAdeleRing K | ∀ v, ‖x v‖ ≤ r} ×ˢ
      AdelicLevel.integralFiniteAdeles (𝓞 K) K) :=
    hS.prod (AdelicLevel.isCompact_integralFiniteAdeles (𝓞 K) K)
  exact this

private def r1_matBall (r : ℝ) : Set (Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) :=
  Set.pi Set.univ fun _ : Fin 2 => Set.pi Set.univ fun _ : Fin 2 => r1_adeleBall K r

private def r1_Omega (r : ℝ) : Set (GL (Fin 2) (AdeleRing (𝓞 K) K)) :=
  Units.embedProduct (Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) ⁻¹'
    (r1_matBall K r ×ˢ (MulOpposite.op '' r1_matBall K r))

private theorem r1_isCompact_Omega (r : ℝ) : IsCompact (r1_Omega K r) := by
  have hM : IsCompact (r1_matBall K r) :=
    isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => r1_isCompact_adeleBall K r
  exact Units.isClosedEmbedding_embedProduct.isCompact_preimage
    (hM.prod (hM.image MulOpposite.continuous_op))

private theorem r1_mem_Omega {r : ℝ} {m : GL (Fin 2) (AdeleRing (𝓞 K) K)}
    (h₁ : ∀ i j, (m : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) i j ∈ r1_adeleBall K r)
    (h₂ : ∀ i j, ((m⁻¹ : GL (Fin 2) (AdeleRing (𝓞 K) K)) :
      Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) i j ∈ r1_adeleBall K r) :
    m ∈ r1_Omega K r := by
  rw [r1_Omega, Set.mem_preimage, Units.embedProduct_apply, Set.mem_prod]
  exact ⟨Set.mem_univ_pi.mpr fun i => Set.mem_univ_pi.mpr fun j => h₁ i j,
    ⟨((m⁻¹ : GL (Fin 2) (AdeleRing (𝓞 K) K)) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)),
      Set.mem_univ_pi.mpr fun i => Set.mem_univ_pi.mpr fun j => h₂ i j, rfl⟩⟩

private theorem r1_conj_mem_Omega {c' u' d₁' d₂' rB : ℝ} (hc' : 0 < c') (hrB : 0 ≤ rB)
    {s : GL (Fin 2) (AdeleRing (𝓞 K) K)} (hs : s ∈ centreCutSiegelSet K c' u' d₁' d₂')
    {b : AdeleRing (𝓞 K) K} (hb₁ : ∀ w : InfinitePlace K, ‖b.1 w‖ ≤ rB)
    (hb₂ : b.2 ∈ AdelicLevel.integralFiniteAdeles (𝓞 K) K) :
    s⁻¹ * unipotentGL2 b * s ∈ r1_Omega K (1 + rB / c') := by
  have hs₁ : glFin (𝓞 K) K s ∈ finiteIntegralGL2 (𝓞 K) K := (mem_centreCutSiegelSet_iff.mp hs).1
  have hnb₁ : ∀ w : InfinitePlace K, ‖(-b).1 w‖ ≤ rB := fun w => by
    rw [show (-b).1 w = -(b.1 w) from rfl, norm_neg]
    exact hb₁ w
  have hnb₂ : (-b).2 ∈ AdelicLevel.integralFiniteAdeles (𝓞 K) K := by
    rw [show (-b).2 = -b.2 from rfl, neg_eq_zero_sub]
    exact AdelicLevel.sub_mem_integralFiniteAdeles AdelicLevel.zero_mem_integralFiniteAdeles hb₂
  have hinv : (s⁻¹ * unipotentGL2 b * s)⁻¹ = s⁻¹ * unipotentGL2 (-b) * s := by
    simp only [mul_inv_rev, inv_inv, r1_unipotentGL2_inv, mul_assoc]
  refine r1_mem_Omega K (fun i j => (r1_mem_adeleBall K).mpr ⟨fun w => ?_, ?_⟩)
    (fun i j => (r1_mem_adeleBall K).mpr ?_)
  · exact r1_arch_entry_norm_le K hc' hrB hs hb₁ w i j
  · exact r1_fin_entry_mem K hs₁ hb₂ i j
  · rw [hinv]
    exact ⟨fun w => r1_arch_entry_norm_le K hc' hrB hs hnb₁ w i j, r1_fin_entry_mem K hs₁ hnb₂ i j⟩

private theorem r1_exists_absorbing {c' u' d₁' d₂' : ℝ} (hc' : 0 < c')
    {C : Set (GL (Fin 2) (AdeleRing (𝓞 K) K))} (hC : IsCompact C) :
    ∃ E : Set (GL (Fin 2) (AdeleRing (𝓞 K) K)), IsCompact E ∧
      ∀ s ∈ centreCutSiegelSet K c' u' d₁' d₂',
        Set.image2 (fun (t : AdeleRing (𝓞 K) K) (c : GL (Fin 2) (AdeleRing (𝓞 K) K)) =>
            unipotentGL2 t * s * c) (closure (adelicBox K)) C
          ⊆ (fun y => s * y) '' E := by
  obtain ⟨rB, hrB, hbox⟩ := r1_exists_box_bound K
  refine ⟨Set.image2 (fun m c => m * c) (r1_Omega K (1 + rB / c')) C, ?_, fun s hs x hx => ?_⟩
  · rw [← Set.image_prod]
    exact ((r1_isCompact_Omega K _).prod hC).image (continuous_fst.mul continuous_snd)
  · obtain ⟨b, hb, c, hc, rfl⟩ := Set.mem_image2.mp hx
    refine ⟨s⁻¹ * unipotentGL2 b * s * c, Set.mem_image2_of_mem
      (r1_conj_mem_Omega K hc' hrB hs (hbox b hb) (r1_snd_mem_of_mem_closure_box K hb)) hc, ?_⟩
    show s * (s⁻¹ * unipotentGL2 b * s * c) = unipotentGL2 b * s * c
    simp only [← mul_assoc, mul_inv_cancel, one_mul]

end Adelic

private theorem r1_bound (K : Type) [Field K] [NumberField K]
    (c' u' d₁' d₂' : ℝ) (hc' : 0 < c')
    {C : Set (GL (Fin 2) (AdeleRing (𝓞 K) K))} (hC : IsCompact C) :
    ∃ M₀ : ℝ, 0 ≤ M₀ ∧ ∀ s ∈ centreCutSiegelSet K c' u' d₁' d₂',
      adelicGLHaar (Fin 2) (𝓞 K) K
          (Set.image2 (fun (t : AdeleRing (𝓞 K) K) (c : GL (Fin 2) (AdeleRing (𝓞 K) K)) =>
            unipotentGL2 t * s * c) (closure (adelicBox K)) C)
        ≤ ENNReal.ofReal M₀ := by
  haveI := isHaarMeasure_adelicGLHaar (Fin 2) (𝓞 K) K
  obtain ⟨E, hE, hsub⟩ := r1_exists_absorbing K (u' := u') (d₁' := d₁') (d₂' := d₂') hc' hC
  have hEtop : adelicGLHaar (Fin 2) (𝓞 K) K E ≠ ⊤ := hE.measure_lt_top.ne
  refine ⟨(adelicGLHaar (Fin 2) (𝓞 K) K E).toReal, ENNReal.toReal_nonneg, fun s hs => ?_⟩
  rw [ENNReal.ofReal_toReal hEtop]
  calc adelicGLHaar (Fin 2) (𝓞 K) K
        (Set.image2 (fun (t : AdeleRing (𝓞 K) K) (c : GL (Fin 2) (AdeleRing (𝓞 K) K)) =>
          unipotentGL2 t * s * c) (closure (adelicBox K)) C)
      ≤ adelicGLHaar (Fin 2) (𝓞 K) K ((fun y => s * y) '' E) := measure_mono (hsub s hs)
    _ = adelicGLHaar (Fin 2) (𝓞 K) K E := by
        rw [Set.image_mul_left, measure_preimage_mul]

end HighCuspEnds

theorem solution (K : Type) [Field K] [NumberField K]
    (c' u' d₁' d₂' : ℝ) (hc' : 0 < c')
    {C : Set (GL (Fin 2) (AdeleRing (𝓞 K) K))} (hC : IsCompact C) :
    ∃ M₀ : ℝ, 0 ≤ M₀ ∧ ∀ s ∈ centreCutSiegelSet K c' u' d₁' d₂',
      adelicGLHaar (Fin 2) (𝓞 K) K
          (Set.image2 (fun (t : AdeleRing (𝓞 K) K) (c : GL (Fin 2) (AdeleRing (𝓞 K) K)) =>
            unipotentGL2 t * s * c) (closure (adelicBox K)) C)
        ≤ ENNReal.ofReal M₀ :=
  HighCuspEnds.r1_bound K c' u' d₁' d₂' hc' hC

end

end S_AutomorphicForm_exists_forall_adelicGLHaar_image2_unipotentGL2_mul_mul_le_of_isCompact
end P2MW
export P2MW.S_AutomorphicForm_exists_forall_adelicGLHaar_image2_unipotentGL2_mul_mul_le_of_isCompact (solution)

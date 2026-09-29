-- Prove2me | solution 1 for AutomorphicForm.exists_conjInvariant_forall_exists_eq_sum_integral_comp_mul_archEntries
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/ddf75696-a92f-5e83-83ae-e68c486c31c1

import Theorems.Thm_LocalParametrix_exists_continuous_hasCompactSupport_apply_eq_integral_iterate_sum_iteratedFDeriv_add_integral_of_span_eq_top
import Theorems.Thm_LocalParametrix_exists_continuous_hasCompactSupport_invariant_apply_eq_integral_add_integral_of_compactSpace
import Theorems.Thm_NumberField_mixedEmbedding_sum_iteratedFDeriv_two_comp_conj_eq_of_mul_conjTranspose_eq_one
import Definitions.Def_AutomorphicForm_UnitFactorizableOfType
import Definitions.Def_AutomorphicForm_AdelicMaximalCompact
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_conjInvariant_forall_exists_eq_sum_integral_comp_mul_archEntries

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

open NumberField AutomorphicForm MeasureTheory Topology
open scoped Classical Matrix

namespace R4ArchParam

section EntrySpace

variable (K : Type) [Field K] [NumberField K]

abbrev Ent : Type := Fin 2 → Fin 2 → mixedEmbedding.mixedSpace K

def mulRight (Y : Matrix (Fin 2) (Fin 2) (mixedEmbedding.mixedSpace K)) : Ent K →L[ℝ] Ent K :=
  LinearMap.toContinuousLinearMap
    { toFun := fun E => Matrix.of.symm (Matrix.of E * Y)
      map_add' := fun E E' => by
        change Matrix.of.symm ((Matrix.of E + Matrix.of E') * Y) = _
        rw [Matrix.add_mul]; rfl
      map_smul' := fun c E => by
        change Matrix.of.symm ((c • Matrix.of E) * Y) = _
        rw [Matrix.smul_mul]; rfl }

@[scoped simp] theorem mulRight_apply (Y : Matrix (Fin 2) (Fin 2) (mixedEmbedding.mixedSpace K)) (E : Ent K) :
    mulRight K Y E = Matrix.of.symm (Matrix.of E * Y) := rfl

def mulLeft (X : Matrix (Fin 2) (Fin 2) (mixedEmbedding.mixedSpace K)) : Ent K →L[ℝ] Ent K :=
  LinearMap.toContinuousLinearMap
    { toFun := fun E => Matrix.of.symm (X * Matrix.of E)
      map_add' := fun E E' => by
        change Matrix.of.symm (X * (Matrix.of E + Matrix.of E')) = _
        rw [Matrix.mul_add]; rfl
      map_smul' := fun c E => by
        change Matrix.of.symm (X * (c • Matrix.of E)) = _
        rw [Matrix.mul_smul]; rfl }

@[scoped simp] theorem mulLeft_apply (X : Matrix (Fin 2) (Fin 2) (mixedEmbedding.mixedSpace K)) (E : Ent K) :
    mulLeft K X E = Matrix.of.symm (X * Matrix.of E) := rfl

abbrev Idx : Type := Fin 2 × Fin 2 × mixedEmbedding.index K

def Yb (p : Idx K) : Matrix (Fin 2) (Fin 2) (mixedEmbedding.mixedSpace K) :=
  Matrix.single p.1 p.2.1 (mixedEmbedding.stdBasis K p.2.2)

def Avf (p : Idx K) : Ent K →L[ℝ] Ent K := mulRight K (Yb K p)

theorem Avf_apply (p : Idx K) (E : Ent K) :
    Avf K p E = Matrix.of.symm (Matrix.of E * Matrix.single p.1 p.2.1 (mixedEmbedding.stdBasis K p.2.2)) :=
  rfl

def one : Ent K := Matrix.of.symm 1

theorem archEntries_one : archEntries K 1 = one K := by
  funext i j
  rw [archEntries_apply]
  change InfiniteAdeleRing.ringEquiv_mixedSpace K ((1 : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K)) i j) =
    (1 : Matrix (Fin 2) (Fin 2) (mixedEmbedding.mixedSpace K)) i j
  by_cases h : i = j
  · subst h; rw [Matrix.one_apply_eq, Matrix.one_apply_eq, map_one]
  · rw [Matrix.one_apply_ne h, Matrix.one_apply_ne h, map_zero]

theorem Avf_one (p : Idx K) : Avf K p (one K) = (mixedEmbedding.stdBasis K).matrix (Fin 2) (Fin 2) p := by
  obtain ⟨a, b, j⟩ := p
  rw [Avf_apply, one, Module.Basis.matrix_apply]
  change Matrix.of.symm (1 * _) = _
  rw [Matrix.one_mul]
  rfl

theorem span_Avf_one : Submodule.span ℝ (Set.range fun p : Idx K => Avf K p (one K)) = ⊤ := by
  have hfun : (fun p : Idx K => Avf K p (one K)) = ⇑((mixedEmbedding.stdBasis K).matrix (Fin 2) (Fin 2)) :=
    funext (Avf_one K)
  rw [hfun]
  exact ((mixedEmbedding.stdBasis K).matrix (Fin 2) (Fin 2)).span_eq

end EntrySpace

section Operator

variable (K : Type) [Field K] [NumberField K]

def Lap (G : Ent K → ℂ) (y : Ent K) : ℂ := ∑ p : Idx K, iteratedFDeriv ℝ 2 G y (fun _ => Avf K p y)

theorem Lap_def : Lap K = fun (G : Ent K → ℂ) (y : Ent K) =>
    ∑ p : Idx K, iteratedFDeriv ℝ 2 G y (fun _ => Avf K p y) := rfl

theorem Lap_eq_fderiv (G : Ent K → ℂ) :
    Lap K G = fun y => ∑ p : Idx K, fderiv ℝ (fderiv ℝ G) y (Avf K p y) (Avf K p y) := by
  funext y
  simp only [Lap, iteratedFDeriv_two_apply]

theorem contDiff_Lap {G : Ent K → ℂ} (hG : ContDiff ℝ (⊤ : ℕ∞) G) : ContDiff ℝ (⊤ : ℕ∞) (Lap K G) := by
  rw [Lap_eq_fderiv]
  have h1 : ContDiff ℝ (⊤ : ℕ∞) (fderiv ℝ G) := (contDiff_infty_iff_fderiv.mp hG).2
  have h2 : ContDiff ℝ (⊤ : ℕ∞) (fderiv ℝ (fderiv ℝ G)) := (contDiff_infty_iff_fderiv.mp h1).2
  refine ContDiff.sum fun p _ => ?_
  exact (h2.clm_apply (Avf K p).contDiff).clm_apply (Avf K p).contDiff

theorem continuous_Lap {G : Ent K → ℂ} (hG : ContDiff ℝ (⊤ : ℕ∞) G) : Continuous (Lap K G) :=
  (contDiff_Lap K hG).continuous

theorem tsupport_Lap_subset (G : Ent K → ℂ) : tsupport (Lap K G) ⊆ tsupport G := by
  refine closure_minimal ?_ (isClosed_tsupport G)
  intro y hy
  have hne : iteratedFDeriv ℝ 2 G y ≠ 0 := by
    intro h0
    apply hy
    change ∑ p : Idx K, iteratedFDeriv ℝ 2 G y (fun _ => Avf K p y) = 0
    simp only [h0, ContinuousMultilinearMap.zero_apply, Finset.sum_const_zero]
  exact support_iteratedFDeriv_subset 2 hne

theorem Lap_comp_mulLeft {G : Ent K → ℂ} (hG : ContDiff ℝ (⊤ : ℕ∞) G)
    (X : Matrix (Fin 2) (Fin 2) (mixedEmbedding.mixedSpace K)) :
    Lap K (fun E => G (mulLeft K X E)) = fun E => Lap K G (mulLeft K X E) := by
  funext E
  change ∑ p : Idx K, iteratedFDeriv ℝ 2 (G ∘ ⇑(mulLeft K X)) E (fun _ => Avf K p E) =
    ∑ p : Idx K, iteratedFDeriv ℝ 2 G (mulLeft K X E) (fun _ => Avf K p (mulLeft K X E))
  have h2 : ((2 : ℕ) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) := WithTop.coe_le_coe.mpr le_top
  rw [ContinuousLinearMap.iteratedFDeriv_comp_right (mulLeft K X) hG E h2]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [ContinuousMultilinearMap.compContinuousLinearMap_apply]
  congr 1
  funext i
  rw [mulLeft_apply, Avf_apply, Avf_apply, mulLeft_apply, Equiv.apply_symm_apply, Equiv.apply_symm_apply,
    Matrix.mul_assoc]

def LapIt (m : ℕ) : (Ent K → ℂ) → (Ent K → ℂ) := (Lap K)^[m]

theorem LapIt_succ (m : ℕ) (G : Ent K → ℂ) : LapIt K (m + 1) G = Lap K (LapIt K m G) := by
  rw [LapIt, LapIt, Function.iterate_succ_apply']

theorem contDiff_LapIt (m : ℕ) {G : Ent K → ℂ} (hG : ContDiff ℝ (⊤ : ℕ∞) G) :
    ContDiff ℝ (⊤ : ℕ∞) (LapIt K m G) := by
  induction m with
  | zero => exact hG
  | succ m ih => rw [LapIt_succ]; exact contDiff_Lap K ih

theorem tsupport_LapIt_subset (m : ℕ) (G : Ent K → ℂ) : tsupport (LapIt K m G) ⊆ tsupport G := by
  induction m with
  | zero => exact subset_rfl
  | succ m ih => rw [LapIt_succ]; exact (tsupport_Lap_subset K _).trans ih

theorem LapIt_comp_mulLeft (m : ℕ) {G : Ent K → ℂ} (hG : ContDiff ℝ (⊤ : ℕ∞) G)
    (X : Matrix (Fin 2) (Fin 2) (mixedEmbedding.mixedSpace K)) :
    LapIt K m (fun E => G (mulLeft K X E)) = fun E => LapIt K m G (mulLeft K X E) := by
  induction m with
  | zero => rfl
  | succ m ih => rw [LapIt_succ, LapIt_succ, ih, Lap_comp_mulLeft K (contDiff_LapIt K m hG)]

end Operator

section CompactGroup

variable (K : Type) [Field K] [NumberField K]

theorem isCompact_rowIsometrySubgroup₀ (w : InfinitePlace K) :
    IsCompact (rowIsometrySubgroup₀ w.Completion : Set (GL (Fin 2) w.Completion)) := by
  set C : Set (Matrix (Fin 2) (Fin 2) w.Completion) := {m | ∀ i j, ‖m i j‖ ≤ 1} with hC_def
  have hC : IsCompact C := by
    have hpi : C = Set.pi Set.univ fun _ : Fin 2 => Set.pi Set.univ fun _ : Fin 2 =>
        {x : w.Completion | ‖x‖ ≤ 1} := by
      ext m
      exact ⟨fun h i _ j _ => h i j, fun h i j => h i (Set.mem_univ _) j (Set.mem_univ _)⟩
    rw [hpi]
    exact isCompact_univ_pi fun _ => isCompact_univ_pi fun _ =>
      isCompact_setOf_norm_le_one_completion K w
  have hK : IsCompact ((Units.embedProduct (Matrix (Fin 2) (Fin 2) w.Completion)) ⁻¹'
      (C ×ˢ (MulOpposite.op '' C))) :=
    Units.isClosedEmbedding_embedProduct.isCompact_preimage (hC.prod (hC.image MulOpposite.continuous_op))
  have hcl : IsClosed (rowIsometrySubgroup₀ w.Completion : Set (GL (Fin 2) w.Completion)) := by
    have heq : (rowIsometrySubgroup₀ w.Completion : Set (GL (Fin 2) w.Completion)) =
        {k : GL (Fin 2) w.Completion | (k : Matrix (Fin 2) (Fin 2) w.Completion).det = 1} ∩
          {k : GL (Fin 2) w.Completion | WindowedSiegel.IsRowIsometry k} := by
      ext k
      simp only [SetLike.mem_coe, Set.mem_inter_iff, Set.mem_setOf_eq]
      exact mem_rowIsometrySubgroup₀_iff w.Completion
    rw [heq]
    refine IsClosed.inter ?_ (isClosed_setOf_isRowIsometry w.Completion)
    exact isClosed_eq ((continuous_id.matrix_det).comp Units.continuous_val) continuous_const
  refine hK.of_isClosed_subset hcl ?_
  intro k hk
  have hk' : WindowedSiegel.IsRowIsometry k := ((mem_rowIsometrySubgroup₀_iff w.Completion).mp hk).2
  simp only [Set.mem_preimage, Units.embedProduct_apply, Set.mem_prod, Set.mem_image]
  exact ⟨fun i j => hk'.norm_apply_le_one i j, _, fun i j => hk'.inv.norm_apply_le_one i j, rfl⟩

scoped instance compactSpace_rowIsometrySubgroup₀ (w : InfinitePlace K) :
    CompactSpace (rowIsometrySubgroup₀ w.Completion) :=
  isCompact_iff_compactSpace.mp (isCompact_rowIsometrySubgroup₀ K w)

abbrev Grp : Type := (w : InfinitePlace K) → rowIsometrySubgroup₀ w.Completion

def matPi (κ : Grp K) : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K) :=
  Matrix.of fun i j => (fun w : InfinitePlace K =>
    (((κ w : GL (Fin 2) w.Completion) : Matrix (Fin 2) (Fin 2) w.Completion) i j) : InfiniteAdeleRing K)

theorem matPi_apply (κ : Grp K) (i j : Fin 2) (w : InfinitePlace K) :
    matPi K κ i j w = ((κ w : GL (Fin 2) w.Completion) : Matrix (Fin 2) (Fin 2) w.Completion) i j := rfl

theorem matPi_mul (κ κ' : Grp K) : matPi K (κ * κ') = matPi K κ * matPi K κ' := by
  ext i j
  funext w
  change AdelicLevel.archEval K w (matPi K (κ * κ') i j) = AdelicLevel.archEval K w ((matPi K κ * matPi K κ') i j)
  rw [Matrix.mul_apply, map_sum]
  simp only [map_mul]
  change ((((κ * κ') w : GL (Fin 2) w.Completion) : Matrix (Fin 2) (Fin 2) w.Completion)) i j =
    ∑ l, ((κ w : GL (Fin 2) w.Completion) : Matrix (Fin 2) (Fin 2) w.Completion) i l *
      ((κ' w : GL (Fin 2) w.Completion) : Matrix (Fin 2) (Fin 2) w.Completion) l j
  rw [Pi.mul_apply, Subgroup.coe_mul, Units.val_mul, Matrix.mul_apply]

theorem matPi_one : matPi K 1 = 1 := by
  ext i j
  funext w
  change (((1 : rowIsometrySubgroup₀ w.Completion) : GL (Fin 2) w.Completion) :
      Matrix (Fin 2) (Fin 2) w.Completion) i j = (1 : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K)) i j w
  rw [Subgroup.coe_one, Units.val_one]
  by_cases h : i = j
  · subst h; rw [Matrix.one_apply_eq, Matrix.one_apply_eq]; rfl
  · rw [Matrix.one_apply_ne h, Matrix.one_apply_ne h]; rfl

def Mmat (κ : Grp K) : Matrix (Fin 2) (Fin 2) (mixedEmbedding.mixedSpace K) :=
  (InfiniteAdeleRing.ringEquiv_mixedSpace K).toRingHom.mapMatrix (matPi K κ)

theorem Mmat_apply (κ : Grp K) (i j : Fin 2) :
    Mmat K κ i j = InfiniteAdeleRing.ringEquiv_mixedSpace K (matPi K κ i j) := rfl

theorem Mmat_mul (κ κ' : Grp K) : Mmat K (κ * κ') = Mmat K κ * Mmat K κ' := by
  rw [Mmat, matPi_mul, map_mul]; rfl

theorem Mmat_one : Mmat K 1 = 1 := by
  rw [Mmat, matPi_one, map_one]

theorem Mmat_inv_mul (κ : Grp K) : Mmat K κ⁻¹ * Mmat K κ = 1 := by
  rw [← Mmat_mul, inv_mul_cancel, Mmat_one]

theorem Mmat_mul_inv (κ : Grp K) : Mmat K κ * Mmat K κ⁻¹ = 1 := by
  rw [← Mmat_mul, mul_inv_cancel, Mmat_one]

theorem Mmat_mulSingle (w : InfinitePlace K) (κ : rowIsometrySubgroup₀ w.Completion) :
    Mmat K (Pi.mulSingle w κ) = Matrix.of (archEntries K (archRowIsometryInclAt₀ K w κ)) := by
  refine Matrix.ext fun i j => ?_
  rw [Mmat_apply, Matrix.of_apply, archEntries_apply]
  have hent : matPi K (Pi.mulSingle w κ) i j =
      ((archRowIsometryInclAt₀ K w κ : GL (Fin 2) (InfiniteAdeleRing K)) :
        Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K)) i j := by
    funext v
    rw [matPi_apply]
    change _ = archMatrixUpdate K w
      (((κ : GL (Fin 2) w.Completion) : Matrix (Fin 2) (Fin 2) w.Completion)) i j v
    by_cases hv : v = w
    · subst hv
      rw [Pi.mulSingle_eq_same, archMatrixUpdate_apply_self]
    · rw [Pi.mulSingle_eq_of_ne hv, archMatrixUpdate_apply_of_ne K w _ i j hv, Subgroup.coe_one,
        Units.val_one]
  rw [hent]

theorem real_rows (k : Matrix (Fin 2) (Fin 2) ℝ)
    (h : ∀ x y : ℝ, ‖x * k 0 0 + y * k 1 0‖ ^ 2 + ‖x * k 0 1 + y * k 1 1‖ ^ 2 = ‖x‖ ^ 2 + ‖y‖ ^ 2)
    (i l : Fin 2) : ∑ j, k i j * k l j = if i = l then 1 else 0 := by
  simp only [Real.norm_eq_abs, sq_abs] at h
  have h10 := h 1 0
  have h01 := h 0 1
  have h11 := h 1 1
  simp only [one_mul, zero_mul, add_zero, zero_add, one_pow, zero_pow two_ne_zero] at h10 h01 h11
  have hcross : k 0 0 * k 1 0 + k 0 1 * k 1 1 = 0 := by linear_combination (h11 - h10 - h01) / 2
  fin_cases i <;> fin_cases l
  · simp only [Fin.sum_univ_two, Fin.zero_eta, Fin.isValue, if_true]; linear_combination h10
  · simp only [Fin.sum_univ_two, Fin.zero_eta, Fin.mk_one, Fin.isValue, zero_ne_one, if_false]
    linear_combination hcross
  · simp only [Fin.sum_univ_two, Fin.zero_eta, Fin.mk_one, Fin.isValue, one_ne_zero, if_false]
    linear_combination hcross
  · simp only [Fin.sum_univ_two, Fin.mk_one, Fin.isValue, if_true]; linear_combination h01

theorem complex_rows (k : Matrix (Fin 2) (Fin 2) ℂ)
    (h : ∀ x y : ℂ, ‖x * k 0 0 + y * k 1 0‖ ^ 2 + ‖x * k 0 1 + y * k 1 1‖ ^ 2 = ‖x‖ ^ 2 + ‖y‖ ^ 2)
    (i l : Fin 2) : ∑ j, k i j * starRingEnd ℂ (k l j) = if i = l then 1 else 0 := by
  have key : ∀ x y : ℂ, Complex.normSq (x * k 0 0 + y * k 1 0) + Complex.normSq (x * k 0 1 + y * k 1 1) =
      Complex.normSq x + Complex.normSq y := by
    intro x y
    have := h x y
    simp only [Complex.sq_norm] at this
    exact this
  have h10 := key 1 0
  have h01 := key 0 1
  have h11 := key 1 1
  have hI1 := key Complex.I 1
  simp only [one_mul, zero_mul, add_zero, zero_add, map_one, map_zero,
    Complex.normSq_apply, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
    Complex.I_re, Complex.I_im, mul_one, mul_zero, zero_sub] at h10 h01 h11 hI1
  have hre : (k 0 0).re * (k 1 0).re + (k 0 0).im * (k 1 0).im + (k 0 1).re * (k 1 1).re + (k 0 1).im * (k 1 1).im = 0 := by
    linear_combination (h11 - h10 - h01) / 2
  have him : (k 0 0).im * (k 1 0).re - (k 0 0).re * (k 1 0).im + (k 0 1).im * (k 1 1).re - (k 0 1).re * (k 1 1).im = 0 := by
    linear_combination (h10 + h01 - hI1) / 2
  fin_cases i <;> fin_cases l
  · simp only [Fin.sum_univ_two, Fin.zero_eta, Fin.isValue, if_true]
    apply Complex.ext
    · simp only [Complex.add_re, Complex.mul_re, Complex.conj_re, Complex.conj_im, Complex.one_re]
      linear_combination h10
    · simp only [Complex.add_im, Complex.mul_im, Complex.conj_re, Complex.conj_im, Complex.one_im]
      ring
  · simp only [Fin.sum_univ_two, Fin.zero_eta, Fin.mk_one, Fin.isValue, zero_ne_one, if_false]
    apply Complex.ext
    · simp only [Complex.add_re, Complex.mul_re, Complex.conj_re, Complex.conj_im, Complex.zero_re]
      linear_combination hre
    · simp only [Complex.add_im, Complex.mul_im, Complex.conj_re, Complex.conj_im, Complex.zero_im]
      linear_combination him
  · simp only [Fin.sum_univ_two, Fin.zero_eta, Fin.mk_one, Fin.isValue, one_ne_zero, if_false]
    apply Complex.ext
    · simp only [Complex.add_re, Complex.mul_re, Complex.conj_re, Complex.conj_im, Complex.zero_re]
      linear_combination hre
    · simp only [Complex.add_im, Complex.mul_im, Complex.conj_re, Complex.conj_im, Complex.zero_im]
      linear_combination -him
  · simp only [Fin.sum_univ_two, Fin.mk_one, Fin.isValue, if_true]
    apply Complex.ext
    · simp only [Complex.add_re, Complex.mul_re, Complex.conj_re, Complex.conj_im, Complex.one_re]
      linear_combination h01
    · simp only [Complex.add_im, Complex.mul_im, Complex.conj_re, Complex.conj_im, Complex.one_im]
      ring

theorem rowIsometry_transport {L 𝕜 : Type*} [NormedField L] [NormedField 𝕜] (e : L →+* 𝕜)
    (he : ∀ x, ‖e x‖ = ‖x‖) (hs : Function.Surjective e) {k : GL (Fin 2) L}
    (hk : WindowedSiegel.IsRowIsometry k) (x y : 𝕜) :
    ‖x * e ((k : Matrix (Fin 2) (Fin 2) L) 0 0) + y * e ((k : Matrix (Fin 2) (Fin 2) L) 1 0)‖ ^ 2 +
        ‖x * e ((k : Matrix (Fin 2) (Fin 2) L) 0 1) + y * e ((k : Matrix (Fin 2) (Fin 2) L) 1 1)‖ ^ 2 =
      ‖x‖ ^ 2 + ‖y‖ ^ 2 := by
  obtain ⟨x, rfl⟩ := hs x
  obtain ⟨y, rfl⟩ := hs y
  simp only [← map_mul, ← map_add, he]
  exact hk.2 x y

theorem Mmat_mul_conjTranspose (κ : Grp K) : Mmat K κ * (Mmat K κ)ᴴ = 1 := by
  refine Matrix.ext fun i l => ?_
  rw [Matrix.mul_apply, Matrix.one_apply]
  simp only [Matrix.conjTranspose_apply, Mmat_apply, InfiniteAdeleRing.ringEquiv_mixedSpace_apply,
    matPi_apply]
  refine Prod.ext ?_ ?_
  · rw [Prod.fst_sum]
    funext r
    rw [Finset.sum_apply]
    simp only [Prod.fst_mul, Prod.fst_star, Pi.mul_apply, star_trivial]
    have hk : WindowedSiegel.IsRowIsometry (κ r.1 : GL (Fin 2) r.1.Completion) :=
      ((mem_rowIsometrySubgroup₀_iff r.1.Completion).mp (κ r.1).2).2
    have hrows := real_rows
      (fun i j => InfinitePlace.Completion.extensionEmbeddingOfIsReal r.2
        (((κ r.1 : GL (Fin 2) r.1.Completion) : Matrix (Fin 2) (Fin 2) r.1.Completion) i j))
      (rowIsometry_transport (InfinitePlace.Completion.extensionEmbeddingOfIsReal r.2)
        ((InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal r.2).norm_map_of_map_zero (map_zero _))
        (InfinitePlace.Completion.surjective_extensionEmbeddingOfIsReal r.2) hk) i l
    rw [hrows]
    split_ifs <;> rfl
  · rw [Prod.snd_sum]
    funext c
    rw [Finset.sum_apply]
    simp only [Prod.snd_mul, Prod.snd_star, Pi.mul_apply, Pi.star_apply, Complex.star_def]
    have hk : WindowedSiegel.IsRowIsometry (κ c.1 : GL (Fin 2) c.1.Completion) :=
      ((mem_rowIsometrySubgroup₀_iff c.1.Completion).mp (κ c.1).2).2
    have hrows := complex_rows
      (fun i j => InfinitePlace.Completion.extensionEmbedding c.1
        (((κ c.1 : GL (Fin 2) c.1.Completion) : Matrix (Fin 2) (Fin 2) c.1.Completion) i j))
      (rowIsometry_transport (InfinitePlace.Completion.extensionEmbedding c.1)
        ((InfinitePlace.Completion.isometry_extensionEmbedding c.1).norm_map_of_map_zero (map_zero _))
        (InfinitePlace.Completion.surjective_extensionEmbedding_of_isComplex c.2) hk) i l
    rw [hrows]
    split_ifs <;> rfl

theorem Mmat_inv_eq_conjTranspose (κ : Grp K) : Mmat K κ⁻¹ = (Mmat K κ)ᴴ := by
  calc Mmat K κ⁻¹ = Mmat K κ⁻¹ * (Mmat K κ * (Mmat K κ)ᴴ) := by rw [Mmat_mul_conjTranspose, Matrix.mul_one]
    _ = (Mmat K κ)ᴴ := by rw [← Matrix.mul_assoc, Mmat_inv_mul, Matrix.one_mul]

def rho : Grp K →* (Ent K →L[ℝ] Ent K) where
  toFun κ := (mulLeft K (Mmat K κ)).comp (mulRight K (Mmat K κ⁻¹))
  map_one' := by
    refine ContinuousLinearMap.ext fun E => ?_
    rw [inv_one, Mmat_one, ContinuousLinearMap.one_def, ContinuousLinearMap.id_apply,
      ContinuousLinearMap.comp_apply, mulRight_apply, mulLeft_apply, Equiv.apply_symm_apply,
      Matrix.mul_one, Matrix.one_mul, Equiv.symm_apply_apply]
  map_mul' κ κ' := by
    refine ContinuousLinearMap.ext fun E => ?_
    rw [ContinuousLinearMap.mul_def]
    simp only [ContinuousLinearMap.comp_apply, mulRight_apply, mulLeft_apply, Equiv.apply_symm_apply,
      mul_inv_rev, Mmat_mul, Matrix.mul_assoc]

theorem rho_apply (κ : Grp K) (E : Ent K) :
    rho K κ E = Matrix.of.symm (Mmat K κ * Matrix.of E * Mmat K κ⁻¹) := by
  change Matrix.of.symm (Mmat K κ * Matrix.of (Matrix.of.symm (Matrix.of E * Mmat K κ⁻¹))) = _
  rw [Equiv.apply_symm_apply, Matrix.mul_assoc]

theorem rho_apply_eq_conjTranspose (κ : Grp K) (E : Ent K) :
    rho K κ E = Matrix.of.symm (Mmat K κ * Matrix.of E * (Mmat K κ)ᴴ) := by
  rw [rho_apply, Mmat_inv_eq_conjTranspose]

theorem rho_one_eq (κ : Grp K) : rho K κ (one K) = one K := by
  rw [rho_apply, one, Equiv.apply_symm_apply, Matrix.mul_one, Mmat_mul_inv]

theorem rho_mulSingle_apply (w : InfinitePlace K) (κ : rowIsometrySubgroup₀ w.Completion) (E : Ent K) :
    rho K (Pi.mulSingle w κ) E =
      Matrix.of.symm (Matrix.of (archEntries K (archRowIsometryInclAt₀ K w κ)) * Matrix.of E *
        Matrix.of (archEntries K (archRowIsometryInclAt₀ K w κ⁻¹))) := by
  rw [rho_apply, ← Pi.mulSingle_inv, Mmat_mulSingle, Mmat_mulSingle]

theorem continuous_Mmat : Continuous (Mmat K) := by
  refine continuous_pi fun i => continuous_pi fun j => ?_
  change Continuous fun κ : Grp K => InfiniteAdeleRing.ringEquiv_mixedSpace K (matPi K κ i j)
  refine (AdelicBox.continuous_ringEquiv_mixedSpace K).comp ?_
  refine continuous_pi fun w => ?_
  change Continuous fun κ : Grp K =>
    ((κ w : GL (Fin 2) w.Completion) : Matrix (Fin 2) (Fin 2) w.Completion) i j
  exact (Units.continuous_val.matrix_elem i j).comp (continuous_subtype_val.comp (continuous_apply w))

theorem continuous_rho : Continuous fun p : Grp K × Ent K => rho K p.1 p.2 := by
  have h : (fun p : Grp K × Ent K => rho K p.1 p.2) =
      fun p => Matrix.of.symm (Mmat K p.1 * (Matrix.of p.2 * Mmat K p.1⁻¹)) := by
    funext p
    rw [rho_apply, Matrix.mul_assoc]
  rw [h]
  have hM1 : Continuous fun p : Grp K × Ent K => Mmat K p.1 := (continuous_Mmat K).comp continuous_fst
  have hM2 : Continuous fun p : Grp K × Ent K => Mmat K p.1⁻¹ :=
    (continuous_Mmat K).comp (continuous_inv.comp continuous_fst)
  have hE : Continuous fun p : Grp K × Ent K => (Matrix.of p.2 : Matrix (Fin 2) (Fin 2) _) := continuous_snd
  exact hM1.matrix_mul (hE.matrix_mul hM2)

theorem Lap_comp_rho {G : Ent K → ℂ} (hG : ContDiff ℝ (⊤ : ℕ∞) G) (κ : Grp K) :
    Lap K (fun x => G (rho K κ x)) = fun x => Lap K G (rho K κ x) := by
  funext E
  have hfun : (fun x => G (rho K κ x)) =
      fun X : Ent K => G (Matrix.of.symm (Mmat K κ * Matrix.of X * (Mmat K κ)ᴴ)) :=
    funext fun x => by rw [rho_apply_eq_conjTranspose]
  rw [hfun, rho_apply_eq_conjTranspose]
  exact NumberField.mixedEmbedding.sum_iteratedFDeriv_two_comp_conj_eq_of_mul_conjTranspose_eq_one K
    (Mmat K κ) (Mmat_mul_conjTranspose K κ) G (hG.of_le (WithTop.coe_le_coe.mpr le_top)) E

theorem LapIt_comp_rho (m : ℕ) {G : Ent K → ℂ} (hG : ContDiff ℝ (⊤ : ℕ∞) G) (κ : Grp K) :
    LapIt K m (fun x => G (rho K κ x)) = fun x => LapIt K m G (rho K κ x) := by
  induction m with
  | zero => rfl
  | succ m ih => rw [LapIt_succ, LapIt_succ, ih, Lap_comp_rho K (contDiff_LapIt K m hG)]

end CompactGroup

section Assembly

variable (K : Type) [Field K] [NumberField K]

theorem isAddHaarMeasure_volume_Ent : (volume : Measure (Ent K)).IsAddHaarMeasure := by
  haveI s0 : SigmaFinite (volume : Measure (mixedEmbedding.mixedSpace K)) := inferInstance
  haveI m0 : MeasurableAdd (mixedEmbedding.mixedSpace K) := inferInstance
  haveI h1 : (volume : Measure (Fin 2 → mixedEmbedding.mixedSpace K)).IsAddHaarMeasure := inferInstance
  haveI s1 : SigmaFinite (volume : Measure (Fin 2 → mixedEmbedding.mixedSpace K)) := inferInstance
  haveI b1 : BorelSpace (Fin 2 → mixedEmbedding.mixedSpace K) := Pi.borelSpace
  haveI m1 : MeasurableAdd (Fin 2 → mixedEmbedding.mixedSpace K) := inferInstance
  infer_instance

theorem hasCompactSupport_comp_mulLeft {Φ : Ent K → ℂ} (hΦc : HasCompactSupport Φ)
    {X : Matrix (Fin 2) (Fin 2) (mixedEmbedding.mixedSpace K)} (hX : IsUnit X.det) :
    HasCompactSupport fun E => Φ (mulLeft K X E) := by
  have h1 : ∀ E, mulLeft K X⁻¹ (mulLeft K X E) = E := fun E => by
    rw [mulLeft_apply, mulLeft_apply, Equiv.apply_symm_apply, ← Matrix.mul_assoc,
      Matrix.nonsing_inv_mul X hX, Matrix.one_mul, Equiv.symm_apply_apply]
  have h2 : ∀ E, mulLeft K X (mulLeft K X⁻¹ E) = E := fun E => by
    rw [mulLeft_apply, mulLeft_apply, Equiv.apply_symm_apply, ← Matrix.mul_assoc,
      Matrix.mul_nonsing_inv X hX, Matrix.one_mul, Equiv.symm_apply_apply]
  let e : Ent K ≃L[ℝ] Ent K := ContinuousLinearEquiv.equivOfInverse (mulLeft K X) (mulLeft K X⁻¹) h1 h2
  exact hΦc.comp_homeomorph e.toHomeomorph

theorem main (U : Set (Fin 2 → Fin 2 → mixedEmbedding.mixedSpace K)) (hU : U ∈ 𝓝 (archEntries K 1)) :
    ∃ (n : ℕ) (Ψ : Fin n → (Fin 2 → Fin 2 → mixedEmbedding.mixedSpace K) → ℂ),
      (∀ k, Continuous (Ψ k) ∧ HasCompactSupport (Ψ k) ∧ tsupport (Ψ k) ⊆ U ∧
        ∀ (w : InfinitePlace K) (κ : rowIsometrySubgroup₀ w.Completion)
            (E : Fin 2 → Fin 2 → mixedEmbedding.mixedSpace K),
          Ψ k (Matrix.of.symm
              (Matrix.of (archEntries K (archRowIsometryInclAt₀ K w κ)) * Matrix.of E *
                Matrix.of (archEntries K (archRowIsometryInclAt₀ K w κ⁻¹)))) = Ψ k E) ∧
      ∀ Φ : (Fin 2 → Fin 2 → mixedEmbedding.mixedSpace K) → ℂ,
        ContDiff ℝ (⊤ : ℕ∞) Φ → HasCompactSupport Φ →
          tsupport Φ ⊆ {E | IsUnit (Matrix.det (Matrix.of E))} →
        ∃ Φ' : Fin n → (Fin 2 → Fin 2 → mixedEmbedding.mixedSpace K) → ℂ,
          (∀ k, ContDiff ℝ (⊤ : ℕ∞) (Φ' k) ∧ tsupport (Φ' k) ⊆ tsupport Φ) ∧
          ∀ X : Fin 2 → Fin 2 → mixedEmbedding.mixedSpace K,
            Φ X = ∑ k, ∫ E, Φ' k (Matrix.of.symm (Matrix.of X * Matrix.of E)) * Ψ k E := by
  haveI b1 : BorelSpace (Fin 2 → mixedEmbedding.mixedSpace K) := Pi.borelSpace
  haveI b2 : BorelSpace (Ent K) := Pi.borelSpace
  haveI hHaar : (volume : Measure (Ent K)).IsAddHaarMeasure := isAddHaarMeasure_volume_Ent K
  rw [archEntries_one] at hU
  set m : ℕ := Module.finrank ℝ (Ent K) + 1 with hm_def
  have hm : Module.finrank ℝ (Ent K) < 2 * m := by omega

  have hex : ∀ W ∈ 𝓝 (one K), ∃ g₁ g₂ : Ent K → ℂ, Continuous g₁ ∧ Continuous g₂ ∧
      HasCompactSupport g₁ ∧ HasCompactSupport g₂ ∧ tsupport g₁ ⊆ W ∧ tsupport g₂ ⊆ W ∧
      ∀ F : Ent K → ℂ, ContDiff ℝ (⊤ : ℕ∞) F → HasCompactSupport F →
        F (one K) = (∫ x, LapIt K m F x * g₁ x) + ∫ x, F x * g₂ x := fun W hW =>
    LocalParametrix.exists_continuous_hasCompactSupport_apply_eq_integral_iterate_sum_iteratedFDeriv_add_integral_of_span_eq_top
      volume (Avf K) (one K) (span_Avf_one K) m hm W hW

  obtain ⟨g₁, g₂, hg₁c, hg₂c, hg₁s, hg₂s, hg₁U, hg₂U, hg₁i, hg₂i, hid⟩ :=
    LocalParametrix.exists_continuous_hasCompactSupport_invariant_apply_eq_integral_add_integral_of_compactSpace
      volume (rho K) (continuous_rho K) (one K) (rho_one_eq K) (LapIt K m)
      (fun F hF _ => (contDiff_LapIt K m hF).continuous)
      (fun κ F hF _ => LapIt_comp_rho K m hF κ) hex U hU
  refine ⟨2, ![g₁, g₂], ?_, ?_⟩
  · intro k
    fin_cases k
    · refine ⟨hg₁c, hg₁s, hg₁U, fun w κ E => ?_⟩
      simp only [Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero]
      rw [← rho_mulSingle_apply]
      exact hg₁i _ E
    · refine ⟨hg₂c, hg₂s, hg₂U, fun w κ E => ?_⟩
      simp only [Fin.mk_one, Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_fin_one]
      rw [← rho_mulSingle_apply]
      exact hg₂i _ E
  · intro Φ hΦ hΦc hΦS
    refine ⟨![LapIt K m Φ, Φ], ?_, ?_⟩
    · intro k
      fin_cases k
      · exact ⟨contDiff_LapIt K m hΦ, tsupport_LapIt_subset K m Φ⟩
      · exact ⟨hΦ, subset_rfl⟩
    · intro X
      rw [Fin.sum_univ_two]
      simp only [Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
      by_cases hX : IsUnit (Matrix.det (Matrix.of X))
      ·
        set F : Ent K → ℂ := fun E => Φ (mulLeft K (Matrix.of X) E) with hF_def
        have hFs : ContDiff ℝ (⊤ : ℕ∞) F := hΦ.comp (mulLeft K (Matrix.of X)).contDiff
        have hFc : HasCompactSupport F := hasCompactSupport_comp_mulLeft K hΦc hX
        have h1 := hid F hFs hFc
        have hF1 : F (one K) = Φ X := by
          simp only [hF_def, one, mulLeft_apply, Equiv.apply_symm_apply, Matrix.mul_one, Equiv.symm_apply_apply]
        rw [LapIt_comp_mulLeft K m hΦ (Matrix.of X), hF1] at h1
        exact h1
      ·
        have hΦX : Φ X = 0 := image_eq_zero_of_notMem_tsupport fun h => hX (hΦS h)
        have hzero : ∀ G : Ent K → ℂ, tsupport G ⊆ tsupport Φ →
            ∀ E : Ent K, G (Matrix.of.symm (Matrix.of X * Matrix.of E)) = 0 := by
          intro G hG E
          apply image_eq_zero_of_notMem_tsupport
          intro hmem
          have hu : IsUnit (Matrix.det (Matrix.of (Matrix.of.symm (Matrix.of X * Matrix.of E)))) :=
            hΦS (hG hmem)
          rw [Equiv.apply_symm_apply, Matrix.det_mul] at hu
          exact hX (isUnit_of_mul_isUnit_left hu)
        rw [hΦX]
        simp only [hzero (LapIt K m Φ) (tsupport_LapIt_subset K m Φ), hzero Φ subset_rfl, zero_mul,
          integral_zero, add_zero]

end Assembly

end R4ArchParam
p2m_reactivate "P2MW.S_AutomorphicForm_exists_conjInvariant_forall_exists_eq_sum_integral_comp_mul_archEntries.R4ArchParam"

end
p2m_reactivate "P2MW.S_AutomorphicForm_exists_conjInvariant_forall_exists_eq_sum_integral_comp_mul_archEntries.R4ArchParam"

open NumberField AutomorphicForm MeasureTheory

open scoped Classical in

theorem solution
    (K : Type) [Field K] [NumberField K]
    (U : Set (Fin 2 → Fin 2 → mixedEmbedding.mixedSpace K)) (hU : U ∈ nhds (archEntries K 1)) :
    ∃ (n : ℕ) (Ψ : Fin n → (Fin 2 → Fin 2 → mixedEmbedding.mixedSpace K) → ℂ),
      (∀ k, Continuous (Ψ k) ∧ HasCompactSupport (Ψ k) ∧ tsupport (Ψ k) ⊆ U ∧
        ∀ (w : InfinitePlace K) (κ : rowIsometrySubgroup₀ w.Completion)
            (E : Fin 2 → Fin 2 → mixedEmbedding.mixedSpace K),
          Ψ k (Matrix.of.symm
              (Matrix.of (archEntries K (archRowIsometryInclAt₀ K w κ)) * Matrix.of E *
                Matrix.of (archEntries K (archRowIsometryInclAt₀ K w κ⁻¹)))) = Ψ k E) ∧
      ∀ Φ : (Fin 2 → Fin 2 → mixedEmbedding.mixedSpace K) → ℂ,
        ContDiff ℝ (⊤ : ℕ∞) Φ → HasCompactSupport Φ →
          tsupport Φ ⊆ {E | IsUnit (Matrix.det (Matrix.of E))} →
        ∃ Φ' : Fin n → (Fin 2 → Fin 2 → mixedEmbedding.mixedSpace K) → ℂ,
          (∀ k, ContDiff ℝ (⊤ : ℕ∞) (Φ' k) ∧ tsupport (Φ' k) ⊆ tsupport Φ) ∧
          ∀ X : Fin 2 → Fin 2 → mixedEmbedding.mixedSpace K,
            Φ X = ∑ k, ∫ E, Φ' k (Matrix.of.symm (Matrix.of X * Matrix.of E)) * Ψ k E :=
  R4ArchParam.main K U hU

end S_AutomorphicForm_exists_conjInvariant_forall_exists_eq_sum_integral_comp_mul_archEntries
end P2MW
export P2MW.S_AutomorphicForm_exists_conjInvariant_forall_exists_eq_sum_integral_comp_mul_archEntries (solution)

-- Prove2me | solution 1 for AutomorphicForm.exists_forall_contDiff_norm_iteratedFDeriv_comp_flowChart_le_sum_foldr_archDeriv
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/a186f676-01bf-5062-855c-1f589fb41a14

import Definitions.Def_AutomorphicForm_ArchDerivCasimirComplex
import Definitions.Def_NumberField_PrincipalLevel
import Definitions.Def_AutomorphicForm_SmoothAutomorphicFnAt
import Definitions.Def_NumberField_AdelicHaar

import Theorems.Thm_PartialDeriv_contDiff_succ_and_norm_iteratedFDeriv_le_of_hasDerivAt_single
import Theorems.Thm_AutomorphicForm_flowChart_add_single_eq_mul_conj
import Theorems.Thm_AutomorphicForm_hasDerivAt_apply_mul_archRealGLAt_inv_mul_archFlowMatrix_mul
import Theorems.Thm_AutomorphicForm_hasDerivAt_apply_mul_archComplexGLAt_inv_mul_archFlowMatrixComplex_mul
import Theorems.Thm_AutomorphicForm_continuous_archFlowAt_and_continuous_archFlowAtComplex
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_forall_contDiff_norm_iteratedFDeriv_comp_flowChart_le_sum_foldr_archDeriv

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicHaar NumberField.InfinitePlace
open AutomorphicForm
open IsDedekindDomain

attribute [local instance] NumberField.AdelicHaar.glBorel
open scoped Classical

noncomputable section

namespace C3Proof

variable (K : Type) [Field K] [NumberField K]

abbrev Letter : Type :=
  (Σ' w : InfinitePlace K, Σ' _ : w.IsReal, ArchDir) ⊕ (Σ' w : InfinitePlace K, Σ' _ : w.IsComplex, ArchDirComplex)

def lettersAt : Letter K → Finset (Letter K) := fun d =>
  Sum.elim
    (fun d => ({Sum.inl ⟨d.1, d.2.1, ArchDir.H⟩, Sum.inl ⟨d.1, d.2.1, ArchDir.E⟩, Sum.inl ⟨d.1, d.2.1, ArchDir.Fm⟩} :
      Finset (Letter K)))
    (fun d => ({Sum.inr ⟨d.1, d.2.1, ArchDirComplex.H⟩, Sum.inr ⟨d.1, d.2.1, ArchDirComplex.E⟩,
      Sum.inr ⟨d.1, d.2.1, ArchDirComplex.Fm⟩, Sum.inr ⟨d.1, d.2.1, ArchDirComplex.iH⟩,
      Sum.inr ⟨d.1, d.2.1, ArchDirComplex.iE⟩, Sum.inr ⟨d.1, d.2.1, ArchDirComplex.iFm⟩} : Finset (Letter K))) d

theorem inl_mem_lettersAt (w : InfinitePlace K) (hw : w.IsReal) (d₀ dir : ArchDir) :
    (Sum.inl ⟨w, hw, dir⟩ : Letter K) ∈ lettersAt K (Sum.inl ⟨w, hw, d₀⟩) := by
  cases dir <;> simp [lettersAt]

theorem inr_mem_lettersAt (w : InfinitePlace K) (hw : w.IsComplex) (d₀ dir : ArchDirComplex) :
    (Sum.inr ⟨w, hw, dir⟩ : Letter K) ∈ lettersAt K (Sum.inr ⟨w, hw, d₀⟩) := by
  cases dir <;> simp [lettersAt]

variable (L₀ : List (Letter K))

def S : Finset (Letter K) := Finset.univ.biUnion fun i : Fin L₀.length => lettersAt K (L₀.get i)

def Λ : Finset (List (Letter K)) :=
  (Finset.range (L₀.length + 1)).biUnion fun k =>
    (Finset.univ : Finset (Fin k → ↥(S K L₀))).image fun f => List.ofFn fun i => ((f i) : Letter K)

theorem mem_Λ_iff (l : List (Letter K)) : l ∈ Λ K L₀ ↔ l.length ≤ L₀.length ∧ ∀ d ∈ l, d ∈ S K L₀ := by
  constructor
  · intro h
    obtain ⟨k, hk, hl⟩ := Finset.mem_biUnion.mp h
    obtain ⟨f, -, rfl⟩ := Finset.mem_image.mp hl
    refine ⟨by simpa [Nat.lt_succ_iff] using Finset.mem_range.mp hk, fun d hd => ?_⟩
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hd
    exact (f i).2
  · rintro ⟨hlen, hS⟩
    refine Finset.mem_biUnion.mpr ⟨l.length, Finset.mem_range.mpr (Nat.lt_succ_iff.mpr hlen), ?_⟩
    refine Finset.mem_image.mpr ⟨fun i => ⟨l.get i, hS _ (List.get_mem l i)⟩, Finset.mem_univ _, ?_⟩
    exact List.ofFn_get l

theorem nil_mem_Λ : ([] : List (Letter K)) ∈ Λ K L₀ :=
  (mem_Λ_iff K L₀ _).mpr ⟨by simp, fun d hd => by simp at hd⟩

theorem length_le_of_mem_Λ {l : List (Letter K)} (h : l ∈ Λ K L₀) : l.length ≤ L₀.length :=
  ((mem_Λ_iff K L₀ l).mp h).1

theorem cons_mem_Λ {l : List (Letter K)} (h : l ∈ Λ K L₀) (hl : l.length < L₀.length) {d : Letter K}
    (hd : d ∈ S K L₀) : d :: l ∈ Λ K L₀ := by
  rw [mem_Λ_iff] at h ⊢
  refine ⟨by simpa using hl, fun d' hd' => ?_⟩
  rcases List.mem_cons.mp hd' with rfl | hd'
  · exact hd
  · exact h.2 d' hd'

theorem mem_S_of_mem_lettersAt (j : Fin L₀.length) {d : Letter K} (hd : d ∈ lettersAt K (L₀.get j)) : d ∈ S K L₀ :=
  Finset.mem_biUnion.mpr ⟨j, Finset.mem_univ _, hd⟩

end C3Proof

namespace C3Proof

variable (K : Type) [Field K] [NumberField K] (L₀ : List (Letter K))

def facR (w : InfinitePlace K) (i : Fin L₀.length) (t : Fin L₀.length → ℝ) : GL (Fin 2) ℝ :=
  match L₀.get i with
  | Sum.inl d => if d.1 = w then archFlowMatrix d.2.2 (t i) else 1
  | Sum.inr _ => (1 : GL (Fin 2) ℝ)

def facC (w : InfinitePlace K) (i : Fin L₀.length) (t : Fin L₀.length → ℝ) : GL (Fin 2) ℂ :=
  match L₀.get i with
  | Sum.inr d => if d.1 = w then archFlowMatrixComplex d.2.2 (t i) else 1
  | Sum.inl _ => (1 : GL (Fin 2) ℂ)

def tailMatR (j : Fin L₀.length) (t : Fin L₀.length → ℝ) (w : InfinitePlace K) : GL (Fin 2) ℝ :=
  ((List.ofFn fun i : Fin L₀.length => facR K L₀ w i t).drop (j.val + 1)).prod

def tailMatC (j : Fin L₀.length) (t : Fin L₀.length → ℝ) (w : InfinitePlace K) : GL (Fin 2) ℂ :=
  ((List.ofFn fun i : Fin L₀.length => facC K L₀ w i t).drop (j.val + 1)).prod

def SmoothGL {𝔽 : Type} [RCLike 𝔽] {n : ℕ} (M : (Fin n → ℝ) → GL (Fin 2) 𝔽) : Prop :=
  (∀ p q, ContDiff ℝ (⊤ : ℕ∞) fun t => ((M t : GL (Fin 2) 𝔽) : Matrix (Fin 2) (Fin 2) 𝔽) p q) ∧
  (∀ p q, ContDiff ℝ (⊤ : ℕ∞) fun t => (((M t)⁻¹ : GL (Fin 2) 𝔽) : Matrix (Fin 2) (Fin 2) 𝔽) p q)

theorem smoothGL_one {𝔽 : Type} [RCLike 𝔽] {n : ℕ} : SmoothGL (fun _ : Fin n → ℝ => (1 : GL (Fin 2) 𝔽)) :=
  ⟨fun p q => contDiff_const, fun p q => by simp only [inv_one]; exact contDiff_const⟩

theorem smoothGL_mul {𝔽 : Type} [RCLike 𝔽] {n : ℕ} {M N : (Fin n → ℝ) → GL (Fin 2) 𝔽} (hM : SmoothGL M) (hN : SmoothGL N) :
    SmoothGL fun t => M t * N t := by
  refine ⟨fun p q => ?_, fun p q => ?_⟩
  · have : (fun t => ((M t * N t : GL (Fin 2) 𝔽) : Matrix (Fin 2) (Fin 2) 𝔽) p q) =
        fun t => ∑ k, ((M t : GL (Fin 2) 𝔽) : Matrix (Fin 2) (Fin 2) 𝔽) p k * ((N t : GL (Fin 2) 𝔽) : Matrix (Fin 2) (Fin 2) 𝔽) k q := by
      funext t; rw [Units.val_mul, Matrix.mul_apply]
    rw [this]
    exact ContDiff.sum fun k _ => (hM.1 p k).mul (hN.1 k q)
  · have : (fun t => (((M t * N t)⁻¹ : GL (Fin 2) 𝔽) : Matrix (Fin 2) (Fin 2) 𝔽) p q) =
        fun t => ∑ k, (((N t)⁻¹ : GL (Fin 2) 𝔽) : Matrix (Fin 2) (Fin 2) 𝔽) p k * (((M t)⁻¹ : GL (Fin 2) 𝔽) : Matrix (Fin 2) (Fin 2) 𝔽) k q := by
      funext t; rw [mul_inv_rev, Units.val_mul, Matrix.mul_apply]
    rw [this]
    exact ContDiff.sum fun k _ => (hN.2 p k).mul (hM.2 k q)

theorem smoothGL_list_prod {𝔽 : Type} [RCLike 𝔽] {n : ℕ} (L : List ((Fin n → ℝ) → GL (Fin 2) 𝔽))
    (h : ∀ M ∈ L, SmoothGL M) : SmoothGL fun t => (L.map fun M => M t).prod := by
  induction L with
  | nil => simpa using (smoothGL_one (𝔽 := 𝔽) (n := n))
  | cons M L ih =>
    simp only [List.map_cons, List.prod_cons]
    exact smoothGL_mul (h M List.mem_cons_self) (ih fun N hN => h N (List.mem_cons_of_mem _ hN))

theorem smoothGL_archFlowMatrix {n : ℕ} (dir : ArchDir) (i : Fin n) :
    SmoothGL fun t : Fin n → ℝ => archFlowMatrix dir (t i) := by
  have hinv : ∀ r : ℝ, (archFlowMatrix dir r)⁻¹ = archFlowMatrix dir (-r) := fun r =>
    inv_eq_of_mul_eq_one_right (by rw [← archFlowMatrix_add, add_neg_cancel, archFlowMatrix_zero])
  have key : ∀ (c : (Fin n → ℝ) → ℝ), ContDiff ℝ (⊤ : ℕ∞) c → ∀ p q,
      ContDiff ℝ (⊤ : ℕ∞) fun t => (archFlowMatrix dir (c t) : Matrix (Fin 2) (Fin 2) ℝ) p q := by
    intro c hc p q
    cases dir <;> fin_cases p <;> fin_cases q <;>
      simp only [archFlowMatrix, splitTorusGL2_coe, unipotentGL2_coe, lowerUnipotentGL2_coe,
        Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.empty_val', Matrix.cons_val_fin_one] <;>
      first
        | exact contDiff_const
        | exact hc
        | exact Real.contDiff_exp.comp hc
        | exact Real.contDiff_exp.comp hc.neg
  have hci : ContDiff ℝ (⊤ : ℕ∞) fun t : Fin n → ℝ => t i := contDiff_apply ℝ ℝ i
  exact ⟨key _ hci, fun p q => by simp only [hinv]; exact key _ hci.neg p q⟩

theorem smoothGL_archFlowMatrixComplex {n : ℕ} (dir : ArchDirComplex) (i : Fin n) :
    SmoothGL fun t : Fin n → ℝ => archFlowMatrixComplex dir (t i) := by
  have hinv : ∀ r : ℝ, (archFlowMatrixComplex dir r)⁻¹ = archFlowMatrixComplex dir (-r) := fun r =>
    inv_eq_of_mul_eq_one_right (by rw [← archFlowMatrixComplex_add, add_neg_cancel, archFlowMatrixComplex_zero])
  have key : ∀ (c : (Fin n → ℝ) → ℝ), ContDiff ℝ (⊤ : ℕ∞) c → ∀ p q,
      ContDiff ℝ (⊤ : ℕ∞) fun t => (archFlowMatrixComplex dir (c t) : Matrix (Fin 2) (Fin 2) ℂ) p q := by
    intro c hc p q
    have hcC : ContDiff ℝ (⊤ : ℕ∞) fun t => ((c t : ℝ) : ℂ) := Complex.ofRealCLM.contDiff.comp hc
    have hcI : ContDiff ℝ (⊤ : ℕ∞) fun t => ((c t : ℝ) : ℂ) * Complex.I := hcC.mul contDiff_const
    cases dir <;> fin_cases p <;> fin_cases q <;>
      simp only [archFlowMatrixComplex, splitTorusGL2Complex, unipotentGL2_coe, lowerUnipotentGL2_coe,
        Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.empty_val', Matrix.cons_val_fin_one] <;>
      first
        | exact contDiff_const
        | exact hcC
        | exact hcI
        | exact Complex.contDiff_exp.comp hcC
        | exact Complex.contDiff_exp.comp hcC.neg
        | exact Complex.contDiff_exp.comp hcI
        | exact Complex.contDiff_exp.comp hcI.neg
  have hci : ContDiff ℝ (⊤ : ℕ∞) fun t : Fin n → ℝ => t i := contDiff_apply ℝ ℝ i
  refine ⟨key _ hci, fun p q => ?_⟩
  simp only [hinv]
  have := key (fun t => -(t i)) hci.neg p q
  simpa using this

theorem smoothGL_facR (w : InfinitePlace K) (i : Fin L₀.length) : SmoothGL (facR K L₀ w i) := by
  unfold facR
  rcases L₀.get i with d | d
  · dsimp only
    split_ifs
    · exact smoothGL_archFlowMatrix d.2.2 i
    · exact smoothGL_one
  · exact smoothGL_one

theorem smoothGL_facC (w : InfinitePlace K) (i : Fin L₀.length) : SmoothGL (facC K L₀ w i) := by
  unfold facC
  rcases L₀.get i with d | d
  · exact smoothGL_one
  · dsimp only
    split_ifs
    · exact smoothGL_archFlowMatrixComplex d.2.2 i
    · exact smoothGL_one

theorem smoothGL_tailMatR (j : Fin L₀.length) (w : InfinitePlace K) : SmoothGL fun t => tailMatR K L₀ j t w := by
  have : (fun t => tailMatR K L₀ j t w) =
      fun t => (((List.ofFn fun i : Fin L₀.length => facR K L₀ w i).drop (j.val + 1)).map fun M => M t).prod := by
    funext t; rw [tailMatR, List.map_drop, List.map_ofFn]; rfl
  rw [this]
  exact smoothGL_list_prod _ fun M hM => by
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp (List.mem_of_mem_drop hM)
    exact smoothGL_facR K L₀ w i

theorem smoothGL_tailMatC (j : Fin L₀.length) (w : InfinitePlace K) : SmoothGL fun t => tailMatC K L₀ j t w := by
  have : (fun t => tailMatC K L₀ j t w) =
      fun t => (((List.ofFn fun i : Fin L₀.length => facC K L₀ w i).drop (j.val + 1)).map fun M => M t).prod := by
    funext t; rw [tailMatC, List.map_drop, List.map_ofFn]; rfl
  rw [this]
  exact smoothGL_list_prod _ fun M hM => by
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp (List.mem_of_mem_drop hM)
    exact smoothGL_facC K L₀ w i

end C3Proof

namespace C3Proof

variable (K : Type) [Field K] [NumberField K] (L₀ : List (Letter K))

def XC : ArchDirComplex → Matrix (Fin 2) (Fin 2) ℂ := fun d => match d with
  | .H => !![1, 0; 0, -1] | .E => !![0, 1; 0, 0] | .Fm => !![0, 0; 1, 0]
  | .iH => !![Complex.I, 0; 0, -Complex.I] | .iE => !![0, Complex.I; 0, 0] | .iFm => !![0, 0; Complex.I, 0]

def YR (j : Fin L₀.length) (w : InfinitePlace K) (dj : ArchDir) (t : Fin L₀.length → ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  (((tailMatR K L₀ j t w)⁻¹ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) * archDirMatrix dj *
    ((tailMatR K L₀ j t w : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ)

def YC (j : Fin L₀.length) (w : InfinitePlace K) (dj : ArchDirComplex) (t : Fin L₀.length → ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  (((tailMatC K L₀ j t w)⁻¹ : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) * XC dj *
    ((tailMatC K L₀ j t w : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ)

theorem contDiff_YR (j : Fin L₀.length) (w : InfinitePlace K) (dj : ArchDir) (p q : Fin 2) :
    ContDiff ℝ (⊤ : ℕ∞) fun t => YR K L₀ j w dj t p q := by
  obtain ⟨h1, h2⟩ := smoothGL_tailMatR K L₀ j w
  simp only [YR, Matrix.mul_apply]
  refine ContDiff.sum fun k _ => ContDiff.mul (ContDiff.sum fun l _ => (h2 p l).mul contDiff_const) (h1 k q)

theorem contDiff_YC (j : Fin L₀.length) (w : InfinitePlace K) (dj : ArchDirComplex) (p q : Fin 2) :
    ContDiff ℝ (⊤ : ℕ∞) fun t => YC K L₀ j w dj t p q := by
  obtain ⟨h1, h2⟩ := smoothGL_tailMatC K L₀ j w
  simp only [YC, Matrix.mul_apply]
  refine ContDiff.sum fun k _ => ContDiff.mul (ContDiff.sum fun l _ => (h2 p l).mul contDiff_const) (h1 k q)

def coefR (j : Fin L₀.length) (dir : ArchDir) (t : Fin L₀.length → ℝ) : ℝ :=
  match L₀.get j with
  | Sum.inl d =>
    match dir with
    | .H => (YR K L₀ j d.1 d.2.2 t 0 0 - YR K L₀ j d.1 d.2.2 t 1 1) / 2
    | .E => YR K L₀ j d.1 d.2.2 t 0 1
    | .Fm => YR K L₀ j d.1 d.2.2 t 1 0
  | Sum.inr _ => 0

def coefC (j : Fin L₀.length) (dir : ArchDirComplex) (t : Fin L₀.length → ℝ) : ℝ :=
  match L₀.get j with
  | Sum.inr d =>
    match dir with
    | .H => ((YC K L₀ j d.1 d.2.2 t 0 0 - YC K L₀ j d.1 d.2.2 t 1 1) / 2).re
    | .iH => ((YC K L₀ j d.1 d.2.2 t 0 0 - YC K L₀ j d.1 d.2.2 t 1 1) / 2).im
    | .E => (YC K L₀ j d.1 d.2.2 t 0 1).re
    | .iE => (YC K L₀ j d.1 d.2.2 t 0 1).im
    | .Fm => (YC K L₀ j d.1 d.2.2 t 1 0).re
    | .iFm => (YC K L₀ j d.1 d.2.2 t 1 0).im
  | Sum.inl _ => 0

theorem contDiff_coefR (j : Fin L₀.length) (dir : ArchDir) : ContDiff ℝ (⊤ : ℕ∞) (coefR K L₀ j dir) := by
  unfold coefR
  rcases L₀.get j with d | d
  · cases dir <;> dsimp only
    · exact ((contDiff_YR K L₀ j d.1 d.2.2 0 0).sub (contDiff_YR K L₀ j d.1 d.2.2 1 1)).div_const _
    · exact contDiff_YR K L₀ j d.1 d.2.2 0 1
    · exact contDiff_YR K L₀ j d.1 d.2.2 1 0
  · exact contDiff_const

theorem contDiff_coefC (j : Fin L₀.length) (dir : ArchDirComplex) : ContDiff ℝ (⊤ : ℕ∞) (coefC K L₀ j dir) := by
  unfold coefC
  rcases L₀.get j with d | d
  · exact contDiff_const
  · have hre : ∀ f : (Fin L₀.length → ℝ) → ℂ, ContDiff ℝ (⊤ : ℕ∞) f → ContDiff ℝ (⊤ : ℕ∞) fun t => (f t).re :=
      fun f hf => Complex.reCLM.contDiff.comp hf
    have him : ∀ f : (Fin L₀.length → ℝ) → ℂ, ContDiff ℝ (⊤ : ℕ∞) f → ContDiff ℝ (⊤ : ℕ∞) fun t => (f t).im :=
      fun f hf => Complex.imCLM.contDiff.comp hf
    have hd : ContDiff ℝ (⊤ : ℕ∞) fun t => (YC K L₀ j d.1 d.2.2 t 0 0 - YC K L₀ j d.1 d.2.2 t 1 1) / 2 :=
      ((contDiff_YC K L₀ j d.1 d.2.2 0 0).sub (contDiff_YC K L₀ j d.1 d.2.2 1 1)).div_const _
    cases dir <;> dsimp only
    · exact hre _ hd
    · exact hre _ (contDiff_YC K L₀ j d.1 d.2.2 0 1)
    · exact hre _ (contDiff_YC K L₀ j d.1 d.2.2 1 0)
    · exact him _ hd
    · exact him _ (contDiff_YC K L₀ j d.1 d.2.2 0 1)
    · exact him _ (contDiff_YC K L₀ j d.1 d.2.2 1 0)

theorem exists_bound_iteratedFDeriv_of_contDiff {n : ℕ} {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] (ℓ : ℝ)
    (f : (Fin n → ℝ) → V) (hf : ContDiff ℝ (⊤ : ℕ∞) f) (i : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Set.pi Set.univ (fun _ : Fin n => Set.Icc (-ℓ) ℓ), ‖iteratedFDeriv ℝ i f t‖ ≤ C := by
  have hK : IsCompact (Set.pi Set.univ (fun _ : Fin n => Set.Icc (-ℓ) ℓ)) := isCompact_univ_pi fun _ => isCompact_Icc
  have hc : Continuous fun t => iteratedFDeriv ℝ i f t := hf.continuous_iteratedFDeriv (by exact_mod_cast le_top)
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hc.continuousOn
  exact ⟨max C 0, le_max_right _ _, fun t ht => (hC t ht).trans (le_max_left _ _)⟩

end C3Proof

namespace C3Proof

variable (K : Type) [Field K] [NumberField K] (L₀ : List (Letter K))

def flowd : Letter K → ℝ → AdelicGL2 (𝓞 K) K :=
  fun d t => Sum.elim (fun d => archFlowAt d.2.1 d.2.2 t) (fun d => archFlowAtComplex d.2.1 d.2.2 t) d

def chartd (t : Fin L₀.length → ℝ) : AdelicGL2 (𝓞 K) K := (List.ofFn fun i => flowd K (L₀.get i) (t i)).prod

def Wd (l : List (Letter K)) (b : AdelicGL2 (𝓞 K) K → ℂ) : AdelicGL2 (𝓞 K) K → ℂ :=
  l.foldr (fun d φ => Sum.elim (fun d => archDerivAt d.2.1 d.2.2 φ) (fun d => archDerivAtComplex d.2.1 d.2.2 φ) d) b

def Reg (b : AdelicGL2 (𝓞 K) K → ℂ) : Prop :=
  ∀ l : List (Letter K), l.length ≤ L₀.length →
    Continuous (Wd K l b) ∧ (∀ (w : InfinitePlace K) (hw : w.IsReal), IsArchSmoothAt hw (Wd K l b)) ∧
      (∀ (w : InfinitePlace K) (hw : w.IsComplex), IsArchSmoothAtComplex hw (Wd K l b))

def Fd (b : AdelicGL2 (𝓞 K) K → ℂ) (x : AdelicGL2 (𝓞 K) K) (l : List (Letter K)) : (Fin L₀.length → ℝ) → ℂ :=
  fun t => Wd K l b (x * chartd K L₀ t)

def box (ℓ : ℝ) : Set (Fin L₀.length → ℝ) := Set.pi Set.univ fun _ => Set.Icc (-ℓ) ℓ

theorem continuous_chartd : Continuous (chartd K L₀) := by
  obtain ⟨hflR, hflC⟩ := AutomorphicForm.continuous_archFlowAt_and_continuous_archFlowAtComplex K
  have hflow : ∀ d : Letter K, Continuous (flowd K d) := by
    rintro (⟨w, hw, d⟩ | ⟨w, hw, d⟩)
    · exact hflR w hw d
    · exact hflC w hw d
  have : chartd K L₀ = fun t => (((List.finRange L₀.length).map fun j => flowd K (L₀.get j) (t j))).prod := by
    funext t; simp only [chartd, List.ofFn_eq_map]
  rw [this]
  exact continuous_list_prod _ fun j _ => (hflow _).comp (continuous_apply j)

def letR (j : Fin L₀.length) (dir : ArchDir) : Letter K :=
  match L₀.get j with
  | Sum.inl d => Sum.inl ⟨d.1, d.2.1, dir⟩
  | Sum.inr d => Sum.inr d

def letC (j : Fin L₀.length) (dir : ArchDirComplex) : Letter K :=
  match L₀.get j with
  | Sum.inr d => Sum.inr ⟨d.1, d.2.1, dir⟩
  | Sum.inl d => Sum.inl d

theorem letR_mem_S (j : Fin L₀.length) (dir : ArchDir) : letR K L₀ j dir ∈ S K L₀ := by
  refine mem_S_of_mem_lettersAt K L₀ j ?_
  unfold letR
  rcases hj : L₀.get j with ⟨w, hw, d⟩ | ⟨w, hw, d⟩
  · exact inl_mem_lettersAt K w hw d dir
  · exact inr_mem_lettersAt K w hw d d

theorem letC_mem_S (j : Fin L₀.length) (dir : ArchDirComplex) : letC K L₀ j dir ∈ S K L₀ := by
  refine mem_S_of_mem_lettersAt K L₀ j ?_
  unfold letC
  rcases hj : L₀.get j with ⟨w, hw, d⟩ | ⟨w, hw, d⟩
  · exact inl_mem_lettersAt K w hw d d
  · exact inr_mem_lettersAt K w hw d dir

def dR : Fin 3 → ArchDir := ![ArchDir.H, ArchDir.E, ArchDir.Fm]
def dC : Fin 6 → ArchDirComplex :=
  ![ArchDirComplex.H, ArchDirComplex.iH, ArchDirComplex.E, ArchDirComplex.iE, ArchDirComplex.Fm, ArchDirComplex.iFm]

def gj (b : AdelicGL2 (𝓞 K) K → ℂ) (x : AdelicGL2 (𝓞 K) K) (l : List (Letter K)) (j : Fin L₀.length) :
    (Fin L₀.length → ℝ) → ℂ := fun t =>
  (∑ a : Fin 3, ((coefR K L₀ j (dR a) t : ℝ) : ℂ) * Fd K L₀ b x (letR K L₀ j (dR a) :: l) t) +
    ∑ a : Fin 6, ((coefC K L₀ j (dC a) t : ℝ) : ℂ) * Fd K L₀ b x (letC K L₀ j (dC a) :: l) t

theorem hasDerivAt_Fd (b : AdelicGL2 (𝓞 K) K → ℂ) (hb : Reg K L₀ b) (x : AdelicGL2 (𝓞 K) K) (l : List (Letter K))
    (hl : l.length ≤ L₀.length) (t : Fin L₀.length → ℝ) (j : Fin L₀.length) :
    HasDerivAt (fun s : ℝ => Fd K L₀ b x l (t + s • (Pi.single j (1 : ℝ) : Fin L₀.length → ℝ))) (gj K L₀ b x l j t) 0 := by
  obtain ⟨-, hsmR, hsmC⟩ := hb l hl
  rcases hj : L₀.get j with ⟨w, hw, dj⟩ | ⟨w, hw, dj⟩
  ·
    have hcc : ∀ s : ℝ, chartd K L₀ (t + s • (Pi.single j (1 : ℝ) : Fin L₀.length → ℝ)) =
        chartd K L₀ t * archRealGLAt hw ((tailMatR K L₀ j t w)⁻¹ * archFlowMatrix dj s * tailMatR K L₀ j t w) := by
      intro s
      have h0 := AutomorphicForm.flowChart_add_single_eq_mul_conj K L₀ j t s
      simp only [hj] at h0
      exact h0
    have hfun : (fun s : ℝ => Fd K L₀ b x l (t + s • (Pi.single j (1 : ℝ) : Fin L₀.length → ℝ))) =
        fun s : ℝ => Wd K l b (x * chartd K L₀ t * archRealGLAt hw ((tailMatR K L₀ j t w)⁻¹ * archFlowMatrix dj s * tailMatR K L₀ j t w)) := by
      funext s; simp only [Fd, hcc s, mul_assoc]
    rw [hfun]
    have hD := AutomorphicForm.hasDerivAt_apply_mul_archRealGLAt_inv_mul_archFlowMatrix_mul K hw (Wd K l b) (hsmR w hw)
      (x * chartd K L₀ t) (tailMatR K L₀ j t w) dj
    refine hD.congr_deriv ?_
    simp only [gj, Fin.sum_univ_three, Fin.sum_univ_six, dR, dC, coefR, coefC, letR, letC, hj, YR, Fd, Wd, List.foldr_cons,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, Sum.elim_inl, Complex.ofReal_zero, zero_mul, add_zero,
      Fin.succ_zero_eq_one, Fin.succ_one_eq_two]
  ·
    have hcc : ∀ s : ℝ, chartd K L₀ (t + s • (Pi.single j (1 : ℝ) : Fin L₀.length → ℝ)) =
        chartd K L₀ t * archComplexGLAt hw ((tailMatC K L₀ j t w)⁻¹ * archFlowMatrixComplex dj s * tailMatC K L₀ j t w) := by
      intro s
      have h0 := AutomorphicForm.flowChart_add_single_eq_mul_conj K L₀ j t s
      simp only [hj] at h0
      exact h0
    have hfun : (fun s : ℝ => Fd K L₀ b x l (t + s • (Pi.single j (1 : ℝ) : Fin L₀.length → ℝ))) =
        fun s : ℝ => Wd K l b (x * chartd K L₀ t * archComplexGLAt hw ((tailMatC K L₀ j t w)⁻¹ * archFlowMatrixComplex dj s * tailMatC K L₀ j t w)) := by
      funext s; simp only [Fd, hcc s, mul_assoc]
    rw [hfun]
    have hD := AutomorphicForm.hasDerivAt_apply_mul_archComplexGLAt_inv_mul_archFlowMatrixComplex_mul K hw (Wd K l b) (hsmC w hw)
      (x * chartd K L₀ t) (tailMatC K L₀ j t w) dj

    have hD' : HasDerivAt
        (fun s : ℝ => Wd K l b (x * chartd K L₀ t * archComplexGLAt hw ((tailMatC K L₀ j t w)⁻¹ * archFlowMatrixComplex dj s * tailMatC K L₀ j t w)))
        ((((YC K L₀ j w dj t 0 0 - YC K L₀ j w dj t 1 1) / 2).re : ℂ) * archDerivAtComplex hw ArchDirComplex.H (Wd K l b) (x * chartd K L₀ t) +
          (((YC K L₀ j w dj t 0 0 - YC K L₀ j w dj t 1 1) / 2).im : ℂ) * archDerivAtComplex hw ArchDirComplex.iH (Wd K l b) (x * chartd K L₀ t) +
          ((YC K L₀ j w dj t 0 1).re : ℂ) * archDerivAtComplex hw ArchDirComplex.E (Wd K l b) (x * chartd K L₀ t) +
          ((YC K L₀ j w dj t 0 1).im : ℂ) * archDerivAtComplex hw ArchDirComplex.iE (Wd K l b) (x * chartd K L₀ t) +
          ((YC K L₀ j w dj t 1 0).re : ℂ) * archDerivAtComplex hw ArchDirComplex.Fm (Wd K l b) (x * chartd K L₀ t) +
          ((YC K L₀ j w dj t 1 0).im : ℂ) * archDerivAtComplex hw ArchDirComplex.iFm (Wd K l b) (x * chartd K L₀ t)) 0 := by
      cases dj <;> exact hD
    refine hD'.congr_deriv ?_
    simp only [gj, Fin.sum_univ_three, Fin.sum_univ_six, dR, dC, coefR, coefC, letR, letC, hj, Fd, Wd, List.foldr_cons,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, Sum.elim_inr, Complex.ofReal_zero, zero_mul, zero_add,
      Fin.succ_zero_eq_one, Fin.succ_one_eq_two]

end C3Proof

namespace C3Proof

variable (K : Type) [Field K] [NumberField K] (L₀ : List (Letter K))

theorem contDiff_coefR' (j : Fin L₀.length) (dir : ArchDir) :
    ContDiff ℝ (⊤ : ℕ∞) fun t => ((coefR K L₀ j dir t : ℝ) : ℂ) :=
  Complex.ofRealCLM.contDiff.comp (contDiff_coefR K L₀ j dir)

theorem contDiff_coefC' (j : Fin L₀.length) (dir : ArchDirComplex) :
    ContDiff ℝ (⊤ : ℕ∞) fun t => ((coefC K L₀ j dir t : ℝ) : ℂ) :=
  Complex.ofRealCLM.contDiff.comp (contDiff_coefC K L₀ j dir)

theorem exists_coef_bound (ℓ : ℝ) : ∃ A : ℝ, 0 ≤ A ∧
    (∀ (j : Fin L₀.length) (a : Fin 3) (i : ℕ), i ≤ L₀.length → ∀ t ∈ box K L₀ ℓ,
      ‖iteratedFDeriv ℝ i (fun t => ((coefR K L₀ j (dR a) t : ℝ) : ℂ)) t‖ ≤ A) ∧
    (∀ (j : Fin L₀.length) (a : Fin 6) (i : ℕ), i ≤ L₀.length → ∀ t ∈ box K L₀ ℓ,
      ‖iteratedFDeriv ℝ i (fun t => ((coefC K L₀ j (dC a) t : ℝ) : ℂ)) t‖ ≤ A) := by
  have hR : ∀ (j : Fin L₀.length) (a : Fin 3) (i : ℕ), ∃ B : ℝ, 0 ≤ B ∧ ∀ t ∈ box K L₀ ℓ,
      ‖iteratedFDeriv ℝ i (fun t => ((coefR K L₀ j (dR a) t : ℝ) : ℂ)) t‖ ≤ B :=
    fun j a i => exists_bound_iteratedFDeriv_of_contDiff ℓ _ (contDiff_coefR' K L₀ j (dR a)) i
  have hC : ∀ (j : Fin L₀.length) (a : Fin 6) (i : ℕ), ∃ B : ℝ, 0 ≤ B ∧ ∀ t ∈ box K L₀ ℓ,
      ‖iteratedFDeriv ℝ i (fun t => ((coefC K L₀ j (dC a) t : ℝ) : ℂ)) t‖ ≤ B :=
    fun j a i => exists_bound_iteratedFDeriv_of_contDiff ℓ _ (contDiff_coefC' K L₀ j (dC a)) i
  choose BR hBR using hR
  choose BC hBC using hC
  let U : Fin L₀.length → ℕ → ℝ := fun j i => (∑ a : Fin 3, BR j a i) + ∑ a : Fin 6, BC j a i
  let A : ℝ := ∑ j : Fin L₀.length, ∑ i ∈ Finset.range (L₀.length + 1), U j i
  have hU0 : ∀ j i, 0 ≤ U j i := fun j i =>
    add_nonneg (Finset.sum_nonneg fun a _ => (hBR j a i).1) (Finset.sum_nonneg fun a _ => (hBC j a i).1)
  have hUA : ∀ j i, i ≤ L₀.length → U j i ≤ A := by
    intro j i hi
    calc U j i ≤ ∑ i' ∈ Finset.range (L₀.length + 1), U j i' :=
          Finset.single_le_sum (f := fun i' => U j i') (fun i' _ => hU0 j i') (Finset.mem_range.mpr (Nat.lt_succ_iff.mpr hi))
      _ ≤ A := Finset.single_le_sum (f := fun j' => ∑ i' ∈ Finset.range (L₀.length + 1), U j' i')
          (fun j' _ => Finset.sum_nonneg fun i' _ => hU0 j' i') (Finset.mem_univ j)
  refine ⟨A, Finset.sum_nonneg fun j _ => Finset.sum_nonneg fun i _ => hU0 j i, ?_, ?_⟩
  · intro j a i hi t ht
    refine ((hBR j a i).2 t ht).trans ((?_ : BR j a i ≤ U j i).trans (hUA j i hi))
    exact (Finset.single_le_sum (f := fun a' => BR j a' i) (fun a' _ => (hBR j a' i).1) (Finset.mem_univ a)).trans
      (le_add_of_nonneg_right (Finset.sum_nonneg fun a' _ => (hBC j a' i).1))
  · intro j a i hi t ht
    refine ((hBC j a i).2 t ht).trans ((?_ : BC j a i ≤ U j i).trans (hUA j i hi))
    exact (Finset.single_le_sum (f := fun a' => BC j a' i) (fun a' _ => (hBC j a' i).1) (Finset.mem_univ a)).trans
      (le_add_of_nonneg_left (Finset.sum_nonneg fun a' _ => (hBR j a' i).1))

theorem norm_iteratedFDeriv_mul_le_of_bounds {n : ℕ} (c F : (Fin n → ℝ) → ℂ) {m k : ℕ} (hk : k ≤ m)
    (hc : ContDiff ℝ (⊤ : ℕ∞) c) (hF : ContDiff ℝ m F) (t : Fin n → ℝ) (A S : ℝ) (hA : 0 ≤ A) (hS : 0 ≤ S)
    (hcb : ∀ i, i ≤ k → ‖iteratedFDeriv ℝ i c t‖ ≤ A) (hFb : ∀ i, i ≤ k → ‖iteratedFDeriv ℝ i F t‖ ≤ S) :
    ‖iteratedFDeriv ℝ k (fun y => c y * F y) t‖ ≤ 2 ^ k * A * S := by
  have h := norm_iteratedFDeriv_mul_le (𝕜 := ℝ) (hc.of_le (by exact_mod_cast le_top)) hF t (n := k) (by exact_mod_cast hk)
  refine h.trans ?_
  calc ∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) * ‖iteratedFDeriv ℝ i c t‖ * ‖iteratedFDeriv ℝ (k - i) F t‖
      ≤ ∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) * A * S := by
        refine Finset.sum_le_sum fun i hi => ?_
        have hi' : i ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
        have h1 := hcb i hi'
        have h2 := hFb (k - i) (Nat.sub_le _ _)
        have : (0 : ℝ) ≤ k.choose i := by positivity
        calc (k.choose i : ℝ) * ‖iteratedFDeriv ℝ i c t‖ * ‖iteratedFDeriv ℝ (k - i) F t‖
            ≤ (k.choose i : ℝ) * A * ‖iteratedFDeriv ℝ (k - i) F t‖ := by gcongr
          _ ≤ (k.choose i : ℝ) * A * S := by gcongr
    _ = 2 ^ k * A * S := by
        rw [← Finset.sum_mul, ← Finset.sum_mul]
        congr 1; congr 1
        have := Nat.sum_range_choose k
        exact_mod_cast this

theorem main_induction (ℓ : ℝ) (hℓ : 0 < ℓ) : ∀ m : ℕ, ∃ C : ℝ, 0 ≤ C ∧
    ∀ b : AdelicGL2 (𝓞 K) K → ℂ, Reg K L₀ b → ∀ (x : AdelicGL2 (𝓞 K) K) (l : List (Letter K)),
      l ∈ Λ K L₀ → l.length + m ≤ L₀.length →
        ContDiff ℝ m (Fd K L₀ b x l) ∧
        ∀ k, k ≤ m → ∀ t ∈ box K L₀ ℓ,
          ‖iteratedFDeriv ℝ k (Fd K L₀ b x l) t‖ ≤ C * ∑ l' ∈ Λ K L₀, ‖Wd K l' b (x * chartd K L₀ t)‖
  | 0 => by
    refine ⟨1, zero_le_one, fun b hb x l hl hlen => ⟨?_, fun k hk t ht => ?_⟩⟩
    · have hc : Continuous (Wd K l b) := (hb l (by omega)).1
      exact contDiff_zero.2 (hc.comp (continuous_const.mul (continuous_chartd K L₀)))
    · obtain rfl : k = 0 := Nat.le_zero.mp hk
      rw [norm_iteratedFDeriv_zero, one_mul]
      exact Finset.single_le_sum (f := fun l' => ‖Wd K l' b (x * chartd K L₀ t)‖) (fun _ _ => norm_nonneg _) hl
  | m + 1 => by
    obtain ⟨C, hC0, hC⟩ := main_induction ℓ hℓ m
    obtain ⟨A, hA0, hAR, hAC⟩ := exists_coef_bound K L₀ ℓ
    set C' : ℝ := max 1 (9 * L₀.length * 2 ^ L₀.length * A * C) with hC'
    refine ⟨C', le_trans zero_le_one (le_max_left _ _), fun b hb x l hl hlen => ?_⟩
    have hl' : l.length ≤ L₀.length := by omega
    have hlt : l.length < L₀.length := by omega

    have hmemR : ∀ j a, letR K L₀ j (dR a) :: l ∈ Λ K L₀ := fun j a => cons_mem_Λ K L₀ hl hlt (letR_mem_S K L₀ j _)
    have hmemC : ∀ j a, letC K L₀ j (dC a) :: l ∈ Λ K L₀ := fun j a => cons_mem_Λ K L₀ hl hlt (letC_mem_S K L₀ j _)
    have hIR : ∀ j a, ContDiff ℝ m (Fd K L₀ b x (letR K L₀ j (dR a) :: l)) ∧ ∀ k, k ≤ m → ∀ t ∈ box K L₀ ℓ,
        ‖iteratedFDeriv ℝ k (Fd K L₀ b x (letR K L₀ j (dR a) :: l)) t‖ ≤ C * ∑ l' ∈ Λ K L₀, ‖Wd K l' b (x * chartd K L₀ t)‖ :=
      fun j a => hC b hb x _ (hmemR j a) (by simp; omega)
    have hIC : ∀ j a, ContDiff ℝ m (Fd K L₀ b x (letC K L₀ j (dC a) :: l)) ∧ ∀ k, k ≤ m → ∀ t ∈ box K L₀ ℓ,
        ‖iteratedFDeriv ℝ k (Fd K L₀ b x (letC K L₀ j (dC a) :: l)) t‖ ≤ C * ∑ l' ∈ Λ K L₀, ‖Wd K l' b (x * chartd K L₀ t)‖ :=
      fun j a => hC b hb x _ (hmemC j a) (by simp; omega)

    have hg : ∀ j, ContDiff ℝ m (gj K L₀ b x l j) := by
      intro j
      refine ContDiff.add (ContDiff.sum fun a _ => ?_) (ContDiff.sum fun a _ => ?_)
      · exact ((contDiff_coefR' K L₀ j (dR a)).of_le (by exact_mod_cast le_top)).mul (hIR j a).1
      · exact ((contDiff_coefC' K L₀ j (dC a)).of_le (by exact_mod_cast le_top)).mul (hIC j a).1
    obtain ⟨hcd, -, hbd⟩ := PartialDeriv.contDiff_succ_and_norm_iteratedFDeriv_le_of_hasDerivAt_single L₀.length m
      (Fd K L₀ b x l) (gj K L₀ b x l) hg (fun t j => hasDerivAt_Fd K L₀ b hb x l hl' t j)
    refine ⟨hcd, fun k hk t ht => ?_⟩
    set Sg : ℝ := ∑ l' ∈ Λ K L₀, ‖Wd K l' b (x * chartd K L₀ t)‖ with hSg
    have hSg0 : 0 ≤ Sg := Finset.sum_nonneg fun _ _ => norm_nonneg _
    have hC'1 : 1 ≤ C' := le_max_left _ _
    have hC'2 : 9 * L₀.length * 2 ^ L₀.length * A * C ≤ C' := le_max_right _ _
    rcases k with _ | k'
    · rw [norm_iteratedFDeriv_zero]
      calc ‖Fd K L₀ b x l t‖ ≤ Sg := Finset.single_le_sum (f := fun l' => ‖Wd K l' b (x * chartd K L₀ t)‖) (fun _ _ => norm_nonneg _) hl
        _ ≤ C' * Sg := le_mul_of_one_le_left hSg0 hC'1
    · have hk' : k' ≤ m := by omega
      have hk'n : k' ≤ L₀.length := by omega

      have hterm : ∀ (c F : (Fin L₀.length → ℝ) → ℂ), ContDiff ℝ (⊤ : ℕ∞) c → ContDiff ℝ m F →
          (∀ i, i ≤ k' → ‖iteratedFDeriv ℝ i c t‖ ≤ A) → (∀ i, i ≤ k' → ‖iteratedFDeriv ℝ i F t‖ ≤ C * Sg) →
          ‖iteratedFDeriv ℝ k' (fun y => c y * F y) t‖ ≤ 2 ^ L₀.length * A * (C * Sg) := by
        intro c F hc hF hcb hFb
        refine (norm_iteratedFDeriv_mul_le_of_bounds c F hk' hc hF t A (C * Sg) hA0 (mul_nonneg hC0 hSg0) hcb hFb).trans ?_
        gcongr <;> first | exact mul_nonneg hC0 hSg0 | norm_num | omega
      have hgj : ∀ j, ‖iteratedFDeriv ℝ k' (gj K L₀ b x l j) t‖ ≤ 9 * (2 ^ L₀.length * A * (C * Sg)) := by
        intro j
        have h1 : ∀ a : Fin 3, ContDiff ℝ k' (fun y => ((coefR K L₀ j (dR a) y : ℝ) : ℂ) * Fd K L₀ b x (letR K L₀ j (dR a) :: l) y) :=
          fun a => (((contDiff_coefR' K L₀ j (dR a)).of_le (by exact_mod_cast le_top)).mul (hIR j a).1).of_le (by exact_mod_cast hk')
        have h2 : ∀ a : Fin 6, ContDiff ℝ k' (fun y => ((coefC K L₀ j (dC a) y : ℝ) : ℂ) * Fd K L₀ b x (letC K L₀ j (dC a) :: l) y) :=
          fun a => (((contDiff_coefC' K L₀ j (dC a)).of_le (by exact_mod_cast le_top)).mul (hIC j a).1).of_le (by exact_mod_cast hk')
        have hsplit : iteratedFDeriv ℝ k' (gj K L₀ b x l j) t =
            (∑ a : Fin 3, iteratedFDeriv ℝ k' (fun y => ((coefR K L₀ j (dR a) y : ℝ) : ℂ) * Fd K L₀ b x (letR K L₀ j (dR a) :: l) y) t) +
              ∑ a : Fin 6, iteratedFDeriv ℝ k' (fun y => ((coefC K L₀ j (dC a) y : ℝ) : ℂ) * Fd K L₀ b x (letC K L₀ j (dC a) :: l) y) t := by
          have e1 : gj K L₀ b x l j = (fun y => ∑ a : Fin 3, ((coefR K L₀ j (dR a) y : ℝ) : ℂ) * Fd K L₀ b x (letR K L₀ j (dR a) :: l) y) +
              fun y => ∑ a : Fin 6, ((coefC K L₀ j (dC a) y : ℝ) : ℂ) * Fd K L₀ b x (letC K L₀ j (dC a) :: l) y := rfl
          rw [e1, iteratedFDeriv_add_apply (ContDiff.contDiffAt (ContDiff.sum fun a _ => h1 a))
            (ContDiff.contDiffAt (ContDiff.sum fun a _ => h2 a)),
            iteratedFDeriv_fun_sum_apply (fun a _ => (h1 a).contDiffAt), iteratedFDeriv_fun_sum_apply (fun a _ => (h2 a).contDiffAt)]
        rw [hsplit]
        refine (norm_add_le _ _).trans ?_
        have b1 : ∀ a : Fin 3, ‖iteratedFDeriv ℝ k' (fun y => ((coefR K L₀ j (dR a) y : ℝ) : ℂ) * Fd K L₀ b x (letR K L₀ j (dR a) :: l) y) t‖
            ≤ 2 ^ L₀.length * A * (C * Sg) :=
          fun a => hterm _ _ (contDiff_coefR' K L₀ j (dR a)) (hIR j a).1 (fun i hi => hAR j a i (by omega) t ht)
            (fun i hi => (hIR j a).2 i (by omega) t ht)
        have b2 : ∀ a : Fin 6, ‖iteratedFDeriv ℝ k' (fun y => ((coefC K L₀ j (dC a) y : ℝ) : ℂ) * Fd K L₀ b x (letC K L₀ j (dC a) :: l) y) t‖
            ≤ 2 ^ L₀.length * A * (C * Sg) :=
          fun a => hterm _ _ (contDiff_coefC' K L₀ j (dC a)) (hIC j a).1 (fun i hi => hAC j a i (by omega) t ht)
            (fun i hi => (hIC j a).2 i (by omega) t ht)
        calc ‖∑ a : Fin 3, iteratedFDeriv ℝ k' (fun y => ((coefR K L₀ j (dR a) y : ℝ) : ℂ) * Fd K L₀ b x (letR K L₀ j (dR a) :: l) y) t‖ +
              ‖∑ a : Fin 6, iteratedFDeriv ℝ k' (fun y => ((coefC K L₀ j (dC a) y : ℝ) : ℂ) * Fd K L₀ b x (letC K L₀ j (dC a) :: l) y) t‖
            ≤ (∑ a : Fin 3, (2 ^ L₀.length * A * (C * Sg))) + ∑ a : Fin 6, (2 ^ L₀.length * A * (C * Sg)) :=
              add_le_add ((norm_sum_le _ _).trans (Finset.sum_le_sum fun a _ => b1 a))
                ((norm_sum_le _ _).trans (Finset.sum_le_sum fun a _ => b2 a))
          _ = 9 * (2 ^ L₀.length * A * (C * Sg)) := by
              simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]; ring
      calc ‖iteratedFDeriv ℝ (k' + 1) (Fd K L₀ b x l) t‖ ≤ ∑ j, ‖iteratedFDeriv ℝ k' (gj K L₀ b x l j) t‖ := hbd k' hk' t
        _ ≤ ∑ j : Fin L₀.length, 9 * (2 ^ L₀.length * A * (C * Sg)) := Finset.sum_le_sum fun j _ => hgj j
        _ = (9 * L₀.length * 2 ^ L₀.length * A * C) * Sg := by
            simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]; ring
        _ ≤ C' * Sg := mul_le_mul_of_nonneg_right hC'2 hSg0

end C3Proof

open C3Proof in
theorem solution
    (K : Type) [Field K] [NumberField K]
    (L₀ : List ((Σ' w : InfinitePlace K, Σ' _ : w.IsReal, ArchDir) ⊕
          (Σ' w : InfinitePlace K, Σ' _ : w.IsComplex, ArchDirComplex)))
    (ℓ : ℝ) (hℓ : 0 < ℓ) :
    let W : List ((Σ' w : InfinitePlace K, Σ' _ : w.IsReal, ArchDir) ⊕
          (Σ' w : InfinitePlace K, Σ' _ : w.IsComplex, ArchDirComplex)) →
        (AdelicGL2 (𝓞 K) K → ℂ) → (AdelicGL2 (𝓞 K) K → ℂ) :=
      fun l b => l.foldr (fun d φ => Sum.elim (fun d => archDerivAt d.2.1 d.2.2 φ)
        (fun d => archDerivAtComplex d.2.1 d.2.2 φ) d) b
    let flow : ((Σ' w : InfinitePlace K, Σ' _ : w.IsReal, ArchDir) ⊕
          (Σ' w : InfinitePlace K, Σ' _ : w.IsComplex, ArchDirComplex)) → ℝ → AdelicGL2 (𝓞 K) K :=
      fun d t => Sum.elim (fun d => archFlowAt d.2.1 d.2.2 t) (fun d => archFlowAtComplex d.2.1 d.2.2 t) d
    let chart : (Fin L₀.length → ℝ) → AdelicGL2 (𝓞 K) K :=
      fun t => (List.ofFn fun j => flow (L₀.get j) (t j)).prod
    ∃ (Λ : Finset (List ((Σ' w : InfinitePlace K, Σ' _ : w.IsReal, ArchDir) ⊕
          (Σ' w : InfinitePlace K, Σ' _ : w.IsComplex, ArchDirComplex)))) (c : ℝ),
      (∀ l ∈ Λ, l.length ≤ L₀.length) ∧ 0 ≤ c ∧
      ∀ b : AdelicGL2 (𝓞 K) K → ℂ,
        (∀ l, l.length ≤ L₀.length →
          Continuous (W l b) ∧
          (∀ (w : InfinitePlace K) (hw : w.IsReal), IsArchSmoothAt hw (W l b)) ∧
          (∀ (w : InfinitePlace K) (hw : w.IsComplex), IsArchSmoothAtComplex hw (W l b))) →
        ∀ x : AdelicGL2 (𝓞 K) K,
          ContDiff ℝ L₀.length (fun t : Fin L₀.length → ℝ => b (x * chart t)) ∧
          ∀ k : ℕ, k ≤ L₀.length → ∀ t : Fin L₀.length → ℝ, (∀ j, t j ∈ Set.Icc (-ℓ) ℓ) →
            ‖iteratedFDeriv ℝ k (fun t : Fin L₀.length → ℝ => b (x * chart t)) t‖ ≤
              c * ∑ l ∈ Λ, ‖W l b (x * chart t)‖ := by
  intro W flow chart
  obtain ⟨C, hC0, hC⟩ := main_induction K L₀ ℓ hℓ L₀.length
  refine ⟨Λ K L₀, C, fun l hl => length_le_of_mem_Λ K L₀ hl, hC0, fun b hb x => ?_⟩
  have hreg : Reg K L₀ b := fun l hl => hb l hl
  obtain ⟨hcd, hbd⟩ := hC b hreg x [] (nil_mem_Λ K L₀) (by simp)
  refine ⟨hcd, fun k hk t ht => ?_⟩
  exact hbd k hk t (Set.mem_univ_pi.mpr ht)

end
end S_AutomorphicForm_exists_forall_contDiff_norm_iteratedFDeriv_comp_flowChart_le_sum_foldr_archDeriv
end P2MW
export P2MW.S_AutomorphicForm_exists_forall_contDiff_norm_iteratedFDeriv_comp_flowChart_le_sum_foldr_archDeriv (solution)

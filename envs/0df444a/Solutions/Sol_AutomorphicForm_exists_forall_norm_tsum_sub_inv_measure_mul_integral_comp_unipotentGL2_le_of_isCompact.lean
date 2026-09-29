-- Prove2me | solution 1 for AutomorphicForm.exists_forall_norm_tsum_sub_inv_measure_mul_integral_comp_unipotentGL2_le_of_isCompact
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/c8b42287-7b7d-535e-9261-896b3c73388a

import Theorems.Thm_exists_isCompact_tsupport_subset_and_norm_pow_mul_norm_iteratedFDeriv_comp_le_of_hasCompactSupport
import Theorems.Thm_NumberField_InfinitePlace_exists_sum_prod_inv_one_add_mul_pow_le
import Theorems.Thm_NumberField_AdelicFourier_fourierIntegral_comp_mul_left
import Theorems.Thm_NumberField_AdelicFourier_summable_translate_of_mem_schwartzBruhat
import Theorems.Thm_IsLocallyConstant_isLocallyConstant_fun_mul_apply_mul_of_hasCompactSupport
import Theorems.Thm_NumberField_AdelicFourier_fourierIntegral_mem_schwartzBruhat
import Theorems.Thm_NumberField_AdelicFourier_fourierIntegral_pureTensor_eq
import Theorems.Thm_NumberField_AdelicFourier_tsum_eq_inv_measure_mul_tsum_fourierIntegral
import Theorems.Thm_NumberField_AdelicFourier_integrable_of_mem_schwartzBruhat
import Theorems.Thm_NumberField_AdelicFourier_norm_apply_eq_one_of_isGlobalAddChar
import Theorems.Thm_NumberField_AdelicFourier_exists_ne_zero_apply_eq_fourierChar_trace_of_isGlobalAddChar
import Theorems.Thm_NumberField_AdeleRing_distribHaarChar_eq_prod_norm_pow_mult_of_snd_eq_one
import Theorems.Thm_IsDedekindDomain_FiniteAdeleRing_exists_ne_zero_forall_mul_apply_mem_adicCompletionIntegers_of_isCompact
import Theorems.Thm_AutomorphicForm_IsFactorizableTestFn_comp_mul_unipotentGL2_mul_mem_pureTensorSet
import Definitions.Def_AutomorphicForm_FactorizableTestFn
import Definitions.Def_AutomorphicForm_ConstantTerm
import Definitions.Def_NumberField_AdelicBox
import Definitions.Def_NumberField_AdelicHaar
import Definitions.Def_NumberField_AdelicFourier
import Definitions.Def_NumberField_AdelicTraceFin
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Fourier.FourierTransformDeriv
import Mathlib.RingTheory.Complex
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_forall_norm_tsum_sub_inv_measure_mul_integral_comp_unipotentGL2_le_of_isCompact
p2m_attr_erase "instance" "instCountableOfNumberField_definitions"

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

open MeasureTheory Set NumberField NumberField.InfinitePlace IsDedekindDomain
open NumberField.AdelicHaar NumberField.AdelicBox NumberField.AdelicFourier NumberField.AdelicLevel
open AutomorphicForm

open scoped SchwartzMap Classical

noncomputable section

namespace R4PoissonTail

section Matrices

variable {R : Type*} [CommRing R]

def e01 : Matrix (Fin 2) (Fin 2) R := !![0, 1; 0, 0]

theorem unipotentGL2_val_eq (w : R) :
    (unipotentGL2 w : Matrix (Fin 2) (Fin 2) R) = 1 + w • e01 := by
  ext i j
  rw [unipotentGL2_coe]
  fin_cases i <;> fin_cases j <;> simp [e01]

def dirMat (P₁ P₂ : GL (Fin 2) R) : Matrix (Fin 2) (Fin 2) R :=
  (P₁ : Matrix (Fin 2) (Fin 2) R) * (e01 * (P₂ : Matrix (Fin 2) (Fin 2) R))

theorem val_mul_unipotent_mul (P₁ P₂ : GL (Fin 2) R) (w : R) :
    ((P₁ * (unipotentGL2 w * P₂) : GL (Fin 2) R) : Matrix (Fin 2) (Fin 2) R)
      = ((P₁ * P₂ : GL (Fin 2) R) : Matrix (Fin 2) (Fin 2) R) + w • dirMat P₁ P₂ := by
  simp only [dirMat, Units.val_mul, unipotentGL2_val_eq, Matrix.add_mul, Matrix.one_mul,
    Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul]

theorem eq_zero_of_smul_dirMat_eq_zero (P₁ P₂ : GL (Fin 2) R) {w : R}
    (h : w • dirMat P₁ P₂ = 0) : w = 0 := by
  have h1 : ((P₁ * (unipotentGL2 w * P₂) : GL (Fin 2) R) : Matrix (Fin 2) (Fin 2) R)
      = ((P₁ * P₂ : GL (Fin 2) R) : Matrix (Fin 2) (Fin 2) R) := by
    rw [val_mul_unipotent_mul, h, add_zero]
  have h2 : unipotentGL2 w * P₂ = P₂ := mul_left_cancel (Units.ext h1)
  have h3 : unipotentGL2 w = 1 := mul_right_cancel (h2.trans (one_mul P₂).symm)
  have h4 := congrArg (fun M : GL (Fin 2) R => (M : Matrix (Fin 2) (Fin 2) R) 0 1) h3
  simpa [unipotentGL2_coe] using h4

theorem unipotentGL2_inv (w : R) : (unipotentGL2 w)⁻¹ = unipotentGL2 (-w) :=
  inv_eq_of_mul_eq_one_right (by rw [← unipotentGL2_add, add_neg_cancel, unipotentGL2_zero])

theorem continuous_unipotentGL2 [TopologicalSpace R] [IsTopologicalRing R] :
    Continuous (fun y : R => unipotentGL2 y) := by
  have hval : Continuous (fun y : R => ((unipotentGL2 y : GL (Fin 2) R) : Matrix (Fin 2) (Fin 2) R)) := by
    refine continuous_matrix fun i j => ?_
    simp only [unipotentGL2_coe]
    fin_cases i <;> fin_cases j <;> simp <;> fun_prop
  refine Units.continuous_iff.2 ⟨hval, ?_⟩
  simp only [unipotentGL2_inv]
  exact hval.comp continuous_neg

def diagFst (a : Rˣ) : GL (Fin 2) R where
  val := !![(a : R), 0; 0, 1]
  inv := !![((a⁻¹ : Rˣ) : R), 0; 0, 1]
  val_inv := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  inv_val := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem unipotentGL2_mul_eq_conj (a : Rˣ) (v : R) :
    unipotentGL2 (v * ((a⁻¹ : Rˣ) : R)) = diagFst a⁻¹ * unipotentGL2 v * diagFst a := by
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, diagFst, unipotentGL2_coe, mul_comm]

end Matrices

section Arch

variable (F : Type) [Field F] [NumberField F]

local notation "F∞" => InfiniteAdeleRing F
local notation "E∞" => mixedEmbedding.mixedSpace F
local notation "e∞" => InfiniteAdeleRing.ringEquiv_mixedSpace F

omit [NumberField F] in
theorem continuous_archEntries : Continuous (AutomorphicForm.archEntries F) := by
  refine continuous_pi fun i => continuous_pi fun j => ?_
  exact (NumberField.AdelicBox.continuous_ringEquiv_mixedSpace F).comp
    (Units.continuous_val.matrix_elem i j)

def sliceCentre (P : GL (Fin 2) F∞ × GL (Fin 2) F∞) : Fin 2 → Fin 2 → E∞ := archEntries F (P.1 * P.2)

def sliceLin (P : GL (Fin 2) F∞ × GL (Fin 2) F∞) : E∞ →L[ℝ] (Fin 2 → Fin 2 → E∞) :=
  LinearMap.toContinuousLinearMap
    (LinearMap.pi fun i => LinearMap.pi fun j => LinearMap.mulRight ℝ (e∞ (dirMat P.1 P.2 i j)))

theorem sliceLin_apply (P : GL (Fin 2) F∞ × GL (Fin 2) F∞) (v : E∞) (i j : Fin 2) :
    sliceLin F P v i j = v * e∞ (dirMat P.1 P.2 i j) := by
  simp [sliceLin]

theorem archEntries_mul_unipotent_mul (P : GL (Fin 2) F∞ × GL (Fin 2) F∞) (w : F∞) :
    archEntries F (P.1 * (unipotentGL2 w * P.2)) = sliceCentre F P + sliceLin F P (e∞ w) := by
  funext i j
  rw [archEntries_apply, val_mul_unipotent_mul, Pi.add_apply, Pi.add_apply, sliceLin_apply, sliceCentre,
    archEntries_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, map_add, map_mul]

theorem sliceLin_injective (P : GL (Fin 2) F∞ × GL (Fin 2) F∞) : Function.Injective (sliceLin F P) := by
  refine (injective_iff_map_eq_zero (sliceLin F P)).2 fun v hv => ?_
  have hv' : v = e∞ ((e∞).symm v) := ((e∞).apply_symm_apply v).symm
  have hw : (e∞).symm v • dirMat P.1 P.2 = 0 := by
    ext i j
    apply (e∞).injective
    rw [Matrix.smul_apply, smul_eq_mul, map_mul, ← sliceLin_apply, ← hv', hv, Matrix.zero_apply,
      map_zero]
    rfl
  rw [hv', eq_zero_of_smul_dirMat_eq_zero P.1 P.2 hw, map_zero]

theorem continuous_sliceCentre : Continuous (sliceCentre F) :=
  (continuous_archEntries F).comp (continuous_fst.mul continuous_snd)

theorem continuous_dirMat_apply (i j : Fin 2) :
    Continuous fun P : GL (Fin 2) F∞ × GL (Fin 2) F∞ => dirMat P.1 P.2 i j := by
  have h1 : Continuous fun P : GL (Fin 2) F∞ × GL (Fin 2) F∞ => ((P.1 : GL (Fin 2) F∞) : Matrix (Fin 2) (Fin 2) F∞) :=
    Units.continuous_val.comp continuous_fst
  have h2 : Continuous fun P : GL (Fin 2) F∞ × GL (Fin 2) F∞ =>
      e01 * ((P.2 : GL (Fin 2) F∞) : Matrix (Fin 2) (Fin 2) F∞) :=
    continuous_const.mul (Units.continuous_val.comp continuous_snd)
  exact (h1.mul h2).matrix_elem i j

theorem continuous_sliceLin : Continuous (sliceLin F) := by
  refine continuous_clm_apply.2 fun v => continuous_pi fun i => continuous_pi fun j => ?_
  simp only [sliceLin_apply]
  exact continuous_const.mul
    ((NumberField.AdelicBox.continuous_ringEquiv_mixedSpace F).comp (continuous_dirMat_apply F i j))

theorem glArch_unipotentGL2 (x : AdeleRing (𝓞 F) F) :
    glArch (𝓞 F) F (unipotentGL2 x) = unipotentGL2 x.1 := by
  apply Units.ext
  ext i j
  rw [glArch_apply, unipotentGL2_coe, unipotentGL2_coe]
  fin_cases i <;> fin_cases j <;> rfl

theorem glFin_unipotentGL2 (x : AdeleRing (𝓞 F) F) :
    glFin (𝓞 F) F (unipotentGL2 x) = unipotentGL2 x.2 := by
  apply Units.ext
  ext i j
  rw [glFin_apply, unipotentGL2_coe, unipotentGL2_coe]
  fin_cases i <;> fin_cases j <;> rfl

end Arch

section ArchCutoff

variable (F : Type) [Field F] [NumberField F]

theorem exists_contDiff_hasCompactSupport_eq_comp_archEntries
    {fa : GL (Fin 2) (InfiniteAdeleRing F) → ℂ} (hfa : AutomorphicForm.IsArchTestFactor F fa) :
    ∃ Φ : (Fin 2 → Fin 2 → mixedEmbedding.mixedSpace F) → ℂ,
      ContDiff ℝ (⊤ : ℕ∞) Φ ∧ HasCompactSupport Φ ∧ ∀ g, fa g = Φ (AutomorphicForm.archEntries F g) := by
  obtain ⟨⟨Φ, hΦ, hfaΦ⟩, hsupp⟩ := hfa
  obtain ⟨r, hr⟩ := ((hsupp.isCompact.image (continuous_archEntries F)).isBounded).subset_closedBall
    (0 : Fin 2 → Fin 2 → mixedEmbedding.mixedSpace F)
  let χ : ContDiffBump (0 : Fin 2 → Fin 2 → mixedEmbedding.mixedSpace F) :=
    ⟨max r 1, max r 1 + 1, lt_max_of_lt_right one_pos, lt_add_one _⟩
  refine ⟨fun x => ContDiffBump.toFun χ x • Φ x, χ.contDiff.smul hΦ, χ.hasCompactSupport.smul_right,
    fun g => ?_⟩
  show fa g = ContDiffBump.toFun χ (AutomorphicForm.archEntries F g) • Φ (AutomorphicForm.archEntries F g)
  by_cases hg : fa g = 0
  · rw [show Φ (AutomorphicForm.archEntries F g) = 0 from (hfaΦ g).symm.trans hg, smul_zero]
    exact hg
  · have hmem : AutomorphicForm.archEntries F g ∈ Metric.closedBall (0 : Fin 2 → Fin 2 → _) χ.rIn :=
      Metric.closedBall_subset_closedBall (le_max_left r 1) (hr ⟨g, subset_tsupport _ hg, rfl⟩)
    rw [χ.one_of_mem_closedBall hmem, one_smul]
    exact hfaΦ g

end ArchCutoff

section Family

variable {F : Type} [Field F] [NumberField F]
variable {f : GL (Fin 2) (AdeleRing (𝓞 F) F) → ℂ} (hf : IsFactorizableTestFn F f)

local notation "𝔸" => AdeleRing (𝓞 F) F
local notation "𝔸f" => FiniteAdeleRing (𝓞 F) F
local notation "F∞" => InfiniteAdeleRing F
local notation "E∞" => mixedEmbedding.mixedSpace F
local notation "e∞" => InfiniteAdeleRing.ringEquiv_mixedSpace F
local notation "GL𝔸" => GL (Fin 2) (AdeleRing (𝓞 F) F)

def archFactor : GL (Fin 2) F∞ → ℂ := hf.choose

def finFactor : GL (Fin 2) 𝔸f → ℂ := hf.choose_spec.choose

theorem isArchTestFactor_archFactor : IsArchTestFactor F (archFactor hf) :=
  hf.choose_spec.choose_spec.1

theorem isFinTestFactor_finFactor : IsFinTestFactor F (finFactor hf) :=
  hf.choose_spec.choose_spec.2.1

theorem apply_eq_archFactor_mul_finFactor (g : GL𝔸) :
    f g = archFactor hf (glArch (𝓞 F) F g) * finFactor hf (glFin (𝓞 F) F g) :=
  hf.choose_spec.choose_spec.2.2 g

def entryFn : (Fin 2 → Fin 2 → E∞) → ℂ :=
  (exists_contDiff_hasCompactSupport_eq_comp_archEntries F (isArchTestFactor_archFactor hf)).choose

theorem contDiff_entryFn : ContDiff ℝ (⊤ : ℕ∞) (entryFn hf) :=
  (exists_contDiff_hasCompactSupport_eq_comp_archEntries F (isArchTestFactor_archFactor hf)).choose_spec.1

theorem hasCompactSupport_entryFn : HasCompactSupport (entryFn hf) :=
  (exists_contDiff_hasCompactSupport_eq_comp_archEntries F
    (isArchTestFactor_archFactor hf)).choose_spec.2.1

theorem archFactor_eq_entryFn (g : GL (Fin 2) F∞) : archFactor hf g = entryFn hf (archEntries F g) :=
  (exists_contDiff_hasCompactSupport_eq_comp_archEntries F
    (isArchTestFactor_archFactor hf)).choose_spec.2.2 g

def archPair (p : GL𝔸 × GL𝔸) : GL (Fin 2) F∞ × GL (Fin 2) F∞ := (glArch (𝓞 F) F p.1, glArch (𝓞 F) F p.2)

theorem continuous_archPair : Continuous (archPair (F := F)) :=
  ((continuous_glArch (𝓞 F) F).comp continuous_fst).prodMk ((continuous_glArch (𝓞 F) F).comp continuous_snd)

def sliceArch (p : GL𝔸 × GL𝔸) : 𝓢(E∞, ℂ) where
  toFun v := entryFn hf (sliceCentre F (archPair p) + sliceLin F (archPair p) v)
  smooth' := (contDiff_entryFn hf).comp (contDiff_const.add (sliceLin F (archPair p)).contDiff)
  decay' := by
    intro a n
    obtain ⟨-, hC⟩ :=
      exists_isCompact_tsupport_subset_and_norm_pow_mul_norm_iteratedFDeriv_comp_le_of_hasCompactSupport
        (P := Unit) (contDiff_entryFn hf) (hasCompactSupport_entryFn hf) isCompact_singleton
        (c := fun _ => sliceCentre F (archPair p)) (ℓ := fun _ => sliceLin F (archPair p))
        continuousOn_const continuousOn_const (fun _ _ => sliceLin_injective F _)
    obtain ⟨C, hC'⟩ := hC a n
    exact ⟨C, fun v => hC' () (Set.mem_singleton _) v⟩

theorem sliceArch_apply (p : GL𝔸 × GL𝔸) (v : E∞) :
    sliceArch hf p v = archFactor hf (glArch (𝓞 F) F p.1 * (unipotentGL2 ((e∞).symm v) * glArch (𝓞 F) F p.2)) := by
  rw [archFactor_eq_entryFn]
  rw [show glArch (𝓞 F) F p.1 * (unipotentGL2 ((e∞).symm v) * glArch (𝓞 F) F p.2)
      = (archPair p).1 * (unipotentGL2 ((e∞).symm v) * (archPair p).2) from rfl,
    archEntries_mul_unipotent_mul, RingEquiv.apply_symm_apply]
  rfl

def sliceFin (p : GL𝔸 × GL𝔸) : 𝔸f → ℂ :=
  fun y => finFactor hf (glFin (𝓞 F) F p.1 * (unipotentGL2 y * glFin (𝓞 F) F p.2))

theorem continuous_mul_unipotentGL2_mul {R : Type*} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
    (a b : GL (Fin 2) R) : Continuous (fun y : R => a * (unipotentGL2 y * b)) :=
  continuous_const.mul (continuous_unipotentGL2.mul continuous_const)

theorem isLocallyConstant_sliceFin (p : GL𝔸 × GL𝔸) : IsLocallyConstant (sliceFin hf p) :=
  (isFinTestFactor_finFactor hf).1.comp_continuous (continuous_mul_unipotentGL2_mul _ _)

theorem entry_unconj {R : Type*} [CommRing R] (a b : GL (Fin 2) R) (y : R) :
    ((a⁻¹ * (a * (unipotentGL2 y * b)) * b⁻¹ : GL (Fin 2) R) : Matrix (Fin 2) (Fin 2) R) 0 1 = y := by
  rw [show a⁻¹ * (a * (unipotentGL2 y * b)) * b⁻¹ = unipotentGL2 y by group, unipotentGL2_coe]
  rfl

theorem continuous_readOff {R : Type*} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
    (a b : GL (Fin 2) R) :
    Continuous fun M : GL (Fin 2) R => ((a⁻¹ * M * b⁻¹ : GL (Fin 2) R) : Matrix (Fin 2) (Fin 2) R) 0 1 :=
  (Units.continuous_val.comp ((continuous_const.mul continuous_id).mul continuous_const)).matrix_elem 0 1

theorem hasCompactSupport_sliceFin (p : GL𝔸 × GL𝔸) : HasCompactSupport (sliceFin hf p) := by
  refine HasCompactSupport.intro
    ((isFinTestFactor_finFactor hf).2.isCompact.image
      (continuous_readOff (glFin (𝓞 F) F p.1) (glFin (𝓞 F) F p.2)))
    fun y hy => ?_
  by_contra hne
  exact hy ⟨glFin (𝓞 F) F p.1 * (unipotentGL2 y * glFin (𝓞 F) F p.2), subset_tsupport _ hne,
    entry_unconj _ _ y⟩

theorem slice_eq_tensor (p : GL𝔸 × GL𝔸) :
    (fun s : 𝔸 => f (p.1 * unipotentGL2 s * p.2))
      = fun x => sliceArch hf p (e∞ x.1) * sliceFin hf p x.2 := by
  funext x
  rw [sliceArch_apply, RingEquiv.symm_apply_apply]
  simp only [sliceFin, apply_eq_archFactor_mul_finFactor hf, map_mul, glArch_unipotentGL2, glFin_unipotentGL2,
    mul_assoc]

include hf in
theorem slice_mem_pureTensorSet (p : GL𝔸 × GL𝔸) :
    (fun s : 𝔸 => f (p.1 * unipotentGL2 s * p.2)) ∈ pureTensorSet F := by
  rw [slice_eq_tensor hf p]
  exact tensor_mem_pureTensorSet _ _ (isLocallyConstant_sliceFin hf p) (hasCompactSupport_sliceFin hf p)

end Family

section FourierDecay

open Real VectorFourier
open scoped FourierTransform

variable {E V W : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
  [NormedAddCommGroup W] [NormedSpace ℝ W]

theorem pow_mul_norm_fourierIntegral_le_of_coercive (L : V →L[ℝ] W →L[ℝ] ℝ)
    {μ : Measure V} [μ.IsAddHaarMeasure] {f : V → E} {n : ℕ} (hf : ContDiff ℝ n f)
    (h'f : ∀ j : ℕ, j ≤ n → Integrable (fun v => ‖iteratedFDeriv ℝ j f v‖) μ)
    {c : ℝ} (hc : 0 ≤ c) (hL : ∀ w : W, ∃ v : V, ‖v‖ ≤ 1 ∧ c * ‖w‖ ≤ ‖L v w‖) (w : W) :
    (c * ‖w‖) ^ n * ‖VectorFourier.fourierIntegral 𝐞 μ L.toLinearMap₁₂ f w‖
      ≤ 2 ^ n * ∑ j ∈ Finset.range (n + 1), ∫ v, ‖iteratedFDeriv ℝ j f v‖ ∂μ := by
  obtain ⟨v, hv1, hvw⟩ := hL w
  have h'f' : ∀ (k j : ℕ), (k : ℕ∞) ≤ (0 : ℕ) → (j : ℕ∞) ≤ (n : ℕ) →
      Integrable (fun x => ‖x‖ ^ k * ‖iteratedFDeriv ℝ j f x‖) μ := by
    intro k j hk hj
    have hk0 : k = 0 := by exact_mod_cast (nonpos_iff_eq_zero.mp (by exact_mod_cast hk))
    subst hk0
    simpa using h'f j (by exact_mod_cast hj)
  have key := pow_mul_norm_iteratedFDeriv_fourierIntegral_le L (K := (0 : ℕ)) (N := (n : ℕ))
    (hf := hf) h'f' (k := 0) (n := n) le_rfl le_rfl v w
  rw [norm_iteratedFDeriv_zero, pow_zero, mul_one] at key
  have hsum : ∑ p ∈ Finset.range (0 + 1) ×ˢ Finset.range (n + 1),
        ∫ x, ‖x‖ ^ p.1 * ‖iteratedFDeriv ℝ p.2 f x‖ ∂μ
      = ∑ j ∈ Finset.range (n + 1), ∫ x, ‖iteratedFDeriv ℝ j f x‖ ∂μ := by
    rw [Finset.sum_product, zero_add, Finset.range_one, Finset.sum_singleton]
    simp
  rw [hsum] at key
  have hS : 0 ≤ ∑ j ∈ Finset.range (n + 1), ∫ x, ‖iteratedFDeriv ℝ j f x‖ ∂μ :=
    Finset.sum_nonneg fun j _ => integral_nonneg fun x => norm_nonneg _
  calc (c * ‖w‖) ^ n * ‖VectorFourier.fourierIntegral 𝐞 μ L.toLinearMap₁₂ f w‖
      ≤ |L v w| ^ n * ‖VectorFourier.fourierIntegral 𝐞 μ L.toLinearMap₁₂ f w‖ := by
        gcongr
        exact hvw.trans_eq (Real.norm_eq_abs _)
    _ ≤ ‖v‖ ^ n * (2 * 0 + 2) ^ n
          * ∑ j ∈ Finset.range (n + 1), ∫ x, ‖iteratedFDeriv ℝ j f x‖ ∂μ := by
        simpa using key
    _ ≤ 1 ^ n * (2 * 0 + 2) ^ n
          * ∑ j ∈ Finset.range (n + 1), ∫ x, ‖iteratedFDeriv ℝ j f x‖ ∂μ := by
        gcongr
    _ = 2 ^ n * ∑ j ∈ Finset.range (n + 1), ∫ v, ‖iteratedFDeriv ℝ j f v‖ ∂μ := by norm_num

end FourierDecay

section TraceCoercive

p2m_open "Finset Set.Finset"

theorem trace_pi_apply {R S ι : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [Module.Free R S] [Module.Finite R S] [Fintype ι] (x : ι → S) :
    Algebra.trace R (ι → S) x = ∑ i, Algebra.trace R S (x i) := by
  classical
  let b := Module.Free.chooseBasis R S
  rw [Algebra.trace_eq_matrix_trace (Pi.basis fun _ : ι => b) x]
  simp_rw [Algebra.trace_eq_matrix_trace b]
  simp only [Matrix.trace, Matrix.diag_apply, Algebra.leftMulMatrix_eq_repr_mul, Pi.basis_apply,
    Pi.basis_repr, Pi.mul_apply, Pi.single_eq_same]
  exact Fintype.sum_sigma (fun ik : (Σ _ : ι, Module.Free.ChooseBasisIndex R S) =>
    b.repr (x ik.1 * b ik.2) ik.2)

theorem trace_realProdComplex_apply {ι₁ ι₂ : Type*} [Fintype ι₁] [Fintype ι₂]
    (w : (ι₁ → ℝ) × (ι₂ → ℂ)) :
    Algebra.trace ℝ ((ι₁ → ℝ) × (ι₂ → ℂ)) w = ∑ r, w.1 r + ∑ c, 2 * (w.2 c).re := by
  rw [Algebra.trace_prod_apply, trace_pi_apply, trace_pi_apply]
  simp only [Algebra.trace_self_apply, Algebra.trace_complex_apply]

section CLM

variable (V : Type*) [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

def bilinFormCLM (B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) : V →L[ℝ] V →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap
    ((LinearMap.toContinuousLinearMap : (V →ₗ[ℝ] ℝ) ≃ₗ[ℝ] (V →L[ℝ] ℝ)).toLinearMap ∘ₗ B)

@[scoped simp] theorem bilinFormCLM_apply (B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (v w : V) :
    bilinFormCLM V B v w = B v w := rfl

theorem toLinearMap₁₂_bilinFormCLM (B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) :
    (bilinFormCLM V B).toLinearMap₁₂ = B := by
  ext v w
  rfl

end CLM

theorem re_conj_mul_self (z : ℂ) : (starRingEnd ℂ z * z).re = ‖z‖ ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_apply, Complex.mul_re, Complex.conj_re, Complex.conj_im]
  ring

theorem traceForm_coercive {ι₁ ι₂ : Type*} [Fintype ι₁] [Fintype ι₂]
    (w : (ι₁ → ℝ) × (ι₂ → ℂ)) :
    ∃ v : (ι₁ → ℝ) × (ι₂ → ℂ), ‖v‖ ≤ 1 ∧
      1 * ‖w‖ ≤ ‖Algebra.traceForm ℝ ((ι₁ → ℝ) × (ι₂ → ℂ)) v w‖ := by
  set S : ℝ := ∑ r, w.1 r ^ 2 + ∑ c, 2 * ‖w.2 c‖ ^ 2 with hS
  have hS1 : 0 ≤ ∑ r, w.1 r ^ 2 := Finset.sum_nonneg fun r _ => sq_nonneg _
  have hS2 : 0 ≤ ∑ c, 2 * ‖w.2 c‖ ^ 2 :=
    Finset.sum_nonneg fun c _ => mul_nonneg zero_le_two (sq_nonneg _)
  have hS0 : 0 ≤ S := add_nonneg hS1 hS2
  have h1 : ‖w.1‖ ≤ Real.sqrt S := by
    refine (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg S)).2 fun r => ?_
    rw [Real.norm_eq_abs]
    refine Real.abs_le_sqrt ?_
    calc w.1 r ^ 2 ≤ ∑ r, w.1 r ^ 2 :=
          Finset.single_le_sum (f := fun r => w.1 r ^ 2) (fun i _ => sq_nonneg _) (mem_univ r)
      _ ≤ S := le_add_of_nonneg_right hS2
  have h2 : ‖w.2‖ ≤ Real.sqrt S := by
    refine (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg S)).2 fun c => ?_
    refine Real.le_sqrt_of_sq_le ?_
    calc ‖w.2 c‖ ^ 2 ≤ 2 * ‖w.2 c‖ ^ 2 := by nlinarith [sq_nonneg ‖w.2 c‖]
      _ ≤ ∑ c, 2 * ‖w.2 c‖ ^ 2 :=
          Finset.single_le_sum (f := fun c => 2 * ‖w.2 c‖ ^ 2)
            (fun i _ => mul_nonneg zero_le_two (sq_nonneg _)) (mem_univ c)
      _ ≤ S := le_add_of_nonneg_left hS1
  have hw : ‖w‖ ≤ Real.sqrt S := by
    rw [Prod.norm_def]; exact max_le h1 h2
  have hww : ‖w‖ * ‖w‖ ≤ S := by
    calc ‖w‖ * ‖w‖ ≤ Real.sqrt S * Real.sqrt S :=
          mul_le_mul hw hw (norm_nonneg _) (Real.sqrt_nonneg _)
      _ = S := Real.mul_self_sqrt hS0
  set v₀ : (ι₁ → ℝ) × (ι₂ → ℂ) := (w.1, fun c => starRingEnd ℂ (w.2 c)) with hv₀
  have hv₀_norm : ‖v₀‖ ≤ ‖w‖ := by
    rw [Prod.norm_def, Prod.norm_def]
    refine max_le_max le_rfl ?_
    refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun c => ?_
    show ‖starRingEnd ℂ (w.2 c)‖ ≤ ‖w.2‖
    rw [Complex.norm_conj]
    exact norm_le_pi_norm (w.2) c
  have htr : Algebra.trace ℝ ((ι₁ → ℝ) × (ι₂ → ℂ)) (v₀ * w) = S := by
    rw [trace_realProdComplex_apply]
    simp only [hv₀, Prod.fst_mul, Prod.snd_mul, Pi.mul_apply, re_conj_mul_self, hS]
    congr 1
    exact Finset.sum_congr rfl fun r _ => by ring
  refine ⟨‖w‖⁻¹ • v₀, ?_, ?_⟩
  · rw [norm_smul, norm_inv, norm_norm]
    calc ‖w‖⁻¹ * ‖v₀‖ ≤ ‖w‖⁻¹ * ‖w‖ :=
          mul_le_mul_of_nonneg_left hv₀_norm (inv_nonneg.2 (norm_nonneg _))
      _ = ‖w‖ / ‖w‖ := inv_mul_eq_div _ _
      _ ≤ 1 := div_self_le_one _
  · rw [one_mul, Algebra.traceForm_apply, smul_mul_assoc, map_smul, smul_eq_mul, htr,
      Real.norm_of_nonneg (mul_nonneg (inv_nonneg.2 (norm_nonneg _)) hS0)]
    rcases (norm_nonneg w).eq_or_lt with h0 | hpos
    · rw [← h0]; simp
    · exact (le_inv_mul_iff₀ hpos).2 hww

open NumberField.mixedEmbedding in
theorem traceForm_mixedSpace_coercive (F : Type*) [Field F] [NumberField F] (w : mixedSpace F) :
    ∃ v : mixedSpace F, ‖v‖ ≤ 1 ∧
      1 * ‖w‖ ≤ ‖bilinFormCLM (mixedSpace F) (Algebra.traceForm ℝ (mixedSpace F)) v w‖ := by
  simpa only [bilinFormCLM_apply] using traceForm_coercive w

theorem fourierIntegral_eq_vectorFourier_traceForm
    {A : Type*} [CommRing A] [Algebra ℝ A] [MeasurableSpace A]
    (ψ : AddChar A ℂ) (hψ : ∀ a : A, ψ a = ((Real.fourierChar (Algebra.trace ℝ A a) : Circle) : ℂ))
    (μ : Measure A) (f : A → ℂ) (w : A) :
    NumberField.AdelicFourier.fourierIntegral ψ μ f w
      = VectorFourier.fourierIntegral Real.fourierChar μ (Algebra.traceForm ℝ A) f w := by
  simp only [NumberField.AdelicFourier.fourierIntegral, VectorFourier.fourierIntegral, hψ,
    Circle.smul_def, smul_eq_mul, Algebra.traceForm_apply, map_neg]

end TraceCoercive

section ArchDecay

theorem one_add_pow_le {x : ℝ} (hx : 0 ≤ x) (N : ℕ) : (1 + x) ^ N ≤ 2 ^ N * (x ^ N + 1) := by
  have h2 : 1 + x ≤ 2 * max x 1 := by
    rcases le_total x 1 with h | h
    · rw [max_eq_right h]; linarith
    · rw [max_eq_left h]; linarith
  calc (1 + x) ^ N ≤ (2 * max x 1) ^ N := pow_le_pow_left₀ (by positivity) h2 N
    _ = 2 ^ N * (max x 1) ^ N := mul_pow 2 (max x 1) N
    _ ≤ 2 ^ N * (x ^ N + 1) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        rcases le_total x 1 with h | h
        · rw [max_eq_right h, one_pow]; linarith [pow_nonneg hx N]
        · rw [max_eq_left h]; linarith

section Places

variable (F : Type) [Field F] [NumberField F]

local notation "𝔸" => AdeleRing (𝓞 F) F
local notation "ι" => algebraMap F (AdeleRing (𝓞 F) F)
local notation "F∞" => InfiniteAdeleRing F
local notation "E∞" => mixedEmbedding.mixedSpace F
local notation "e∞" => InfiniteAdeleRing.ringEquiv_mixedSpace F

theorem norm_apply_le_norm_ringEquiv (x : F∞) (w : InfinitePlace F) : ‖x w‖ ≤ ‖e∞ x‖ := by
  rw [InfiniteAdeleRing.ringEquiv_mixedSpace_apply, Prod.norm_def]
  rcases w.isReal_or_isComplex with hw | hw
  · refine le_trans ?_ (le_max_left _ _)
    rw [← (InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal hw).norm_map_of_map_zero
      (map_zero _) (x w)]
    exact norm_le_pi_norm
      (fun v : {w : InfinitePlace F // w.IsReal} =>
        InfinitePlace.Completion.extensionEmbeddingOfIsReal v.2 (x v.1)) ⟨w, hw⟩
  · refine le_trans ?_ (le_max_right _ _)
    rw [← (InfinitePlace.Completion.isometry_extensionEmbedding w).norm_map_of_map_zero
      (map_zero _) (x w)]
    exact norm_le_pi_norm
      (fun v : {w : InfinitePlace F // w.IsComplex} =>
        InfinitePlace.Completion.extensionEmbedding v.1 (x v.1)) ⟨w, hw⟩

omit [NumberField F] in
theorem norm_algebraMap_completion (w : InfinitePlace F) (ξ : F) :
    ‖algebraMap F w.Completion ξ‖ = w ξ := by
  rw [show algebraMap F w.Completion ξ = (((WithAbs.equiv w.1).symm ξ : WithAbs w.1) : w.Completion)
    from rfl, InfinitePlace.Completion.norm_coe]
  rfl

theorem norm_archMul_apply (α : 𝔸ˣ) (t : ℝ) (hαa : ∀ v : InfinitePlace F, ‖(α : 𝔸).1 v‖ = t)
    (ξ : F) (w : InfinitePlace F) : ‖((α : 𝔸) * ι ξ).1 w‖ = t * w ξ := by
  rw [show ((α : 𝔸) * ι ξ).1 w = (α : 𝔸).1 w * algebraMap F w.Completion ξ from rfl, norm_mul, hαa w,
    norm_algebraMap_completion]

theorem prod_one_add_mul_pow_le (α : 𝔸ˣ) (t : ℝ) (ht : 1 ≤ t)
    (hαa : ∀ v : InfinitePlace F, ‖(α : 𝔸).1 v‖ = t) (ξ : F) (M : ℕ) :
    ∏ w : InfinitePlace F, (1 + t * w ξ) ^ M
      ≤ (1 + ‖e∞ ((α : 𝔸) * ι ξ).1‖) ^ (M * Fintype.card (InfinitePlace F)) := by
  have ht0 : 0 ≤ t := zero_le_one.trans ht
  calc ∏ w : InfinitePlace F, (1 + t * w ξ) ^ M
      ≤ ∏ _w : InfinitePlace F, (1 + ‖e∞ ((α : 𝔸) * ι ξ).1‖) ^ M := by
        refine Finset.prod_le_prod (fun w _ => by positivity) fun w _ => ?_
        refine pow_le_pow_left₀ (by positivity) ?_ M
        rw [← norm_archMul_apply F α t hαa ξ w]
        exact add_le_add le_rfl (norm_apply_le_norm_ringEquiv F _ w)
    _ = (1 + ‖e∞ ((α : 𝔸) * ι ξ).1‖) ^ (M * Fintype.card (InfinitePlace F)) := by
        rw [Finset.prod_const, Finset.card_univ, pow_mul]

end Places

section Uniform

variable {F : Type} [Field F] [NumberField F]
variable {f : GL (Fin 2) (AdeleRing (𝓞 F) F) → ℂ} (hf : IsFactorizableTestFn F f)

local notation "𝔸" => AdeleRing (𝓞 F) F
local notation "ι" => algebraMap F (AdeleRing (𝓞 F) F)
local notation "F∞" => InfiniteAdeleRing F
local notation "E∞" => mixedEmbedding.mixedSpace F
local notation "e∞" => InfiniteAdeleRing.ringEquiv_mixedSpace F
local notation "GL𝔸" => GL (Fin 2) (AdeleRing (𝓞 F) F)

theorem coe_sliceArch (p : GL𝔸 × GL𝔸) :
    ⇑(sliceArch hf p) = fun v => entryFn hf (sliceCentre F (archPair p) + sliceLin F (archPair p) v) :=
  rfl

theorem uniform_support_and_bounds {Q : Set (GL𝔸 × GL𝔸)} (hQ : IsCompact Q) :
    (∃ S : Set E∞, IsCompact S ∧ ∀ p ∈ Q, tsupport (⇑(sliceArch hf p)) ⊆ S) ∧
      ∀ j : ℕ, ∃ C : ℝ, ∀ p ∈ Q, ∀ v : E∞, ‖iteratedFDeriv ℝ j (⇑(sliceArch hf p)) v‖ ≤ C := by
  have hQ' : IsCompact (archPair '' Q) := hQ.image continuous_archPair
  obtain ⟨hS, hC⟩ :=
    exists_isCompact_tsupport_subset_and_norm_pow_mul_norm_iteratedFDeriv_comp_le_of_hasCompactSupport
      (contDiff_entryFn hf) (hasCompactSupport_entryFn hf) hQ'
      (c := sliceCentre F) (ℓ := sliceLin F)
      (continuous_sliceCentre F).continuousOn (continuous_sliceLin F).continuousOn
      (fun q _ => sliceLin_injective F q)
  refine ⟨?_, fun j => ?_⟩
  · obtain ⟨S, hS, hsub⟩ := hS
    refine ⟨S, hS, fun p hp => ?_⟩
    rw [coe_sliceArch]
    exact hsub (archPair p) ⟨p, hp, rfl⟩
  · obtain ⟨C, hC'⟩ := hC 0 j
    refine ⟨C, fun p hp v => ?_⟩
    have h := hC' (archPair p) ⟨p, hp, rfl⟩ v
    rw [pow_zero, one_mul] at h
    rw [coe_sliceArch]
    exact h

theorem integral_norm_iteratedFDeriv_le {Q : Set (GL𝔸 × GL𝔸)} (hQ : IsCompact Q) (j : ℕ) :
    ∃ C : ℝ, ∀ p ∈ Q,
      Integrable (fun v => ‖iteratedFDeriv ℝ j (⇑(sliceArch hf p)) v‖) volume ∧
        ∫ v, ‖iteratedFDeriv ℝ j (⇑(sliceArch hf p)) v‖ ≤ C := by
  obtain ⟨⟨S, hS, hsub⟩, hC⟩ := uniform_support_and_bounds hf hQ
  obtain ⟨C, hC'⟩ := hC j
  refine ⟨C * volume.real S, fun p hp => ?_⟩
  have hcs : HasCompactSupport (⇑(sliceArch hf p)) :=
    IsCompact.of_isClosed_subset hS (isClosed_tsupport _) (hsub p hp)
  have hcont : Continuous fun v => iteratedFDeriv ℝ j (⇑(sliceArch hf p)) v :=
    ((sliceArch hf p).smooth ⊤).continuous_iteratedFDeriv (by exact_mod_cast le_top)
  have hint : Integrable (fun v => ‖iteratedFDeriv ℝ j (⇑(sliceArch hf p)) v‖) volume :=
    (hcont.norm).integrable_of_hasCompactSupport (hcs.iteratedFDeriv j).norm
  refine ⟨hint, ?_⟩
  have hzero : ∀ v, v ∉ S → ‖iteratedFDeriv ℝ j (⇑(sliceArch hf p)) v‖ = 0 := by
    intro v hv
    rw [norm_eq_zero]
    exact image_eq_zero_of_notMem_tsupport fun h =>
      hv (hsub p hp (tsupport_iteratedFDeriv_subset j h))
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hzero]
  refine (Real.le_norm_self _).trans ?_
  refine norm_setIntegral_le_of_norm_le_const hS.measure_lt_top fun v _ => ?_
  rw [norm_norm]
  exact hC' p hp v

theorem pow_mul_norm_fourierIntegral_le {Q : Set (GL𝔸 × GL𝔸)} (hQ : IsCompact Q)
    (N : ℕ) {ψ : AddChar 𝔸 ℂ}
    (hψa : ∀ a : E∞,
      ψ.compAddMonoidHom ((AddMonoidHom.inl (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F)).comp
        (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm.toAddMonoidHom) a
          = ((Real.fourierChar (Algebra.trace ℝ E∞ a) : Circle) : ℂ)) :
    ∃ B : ℝ, ∀ p ∈ Q, ∀ η : E∞,
      ‖η‖ ^ N * ‖fourierIntegral
          (ψ.compAddMonoidHom ((AddMonoidHom.inl (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F)).comp
            (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm.toAddMonoidHom))
          volume (⇑(sliceArch hf p)) η‖ ≤ B := by
  choose C hC using fun j => integral_norm_iteratedFDeriv_le hf hQ j
  refine ⟨2 ^ N * ∑ j ∈ Finset.range (N + 1), C j, fun p hp η => ?_⟩
  rw [fourierIntegral_eq_vectorFourier_traceForm _ hψa volume (⇑(sliceArch hf p)) η,
    ← toLinearMap₁₂_bilinFormCLM E∞ (Algebra.traceForm ℝ E∞)]
  have key := pow_mul_norm_fourierIntegral_le_of_coercive
    (bilinFormCLM E∞ (Algebra.traceForm ℝ E∞)) (μ := volume) (n := N)
    ((sliceArch hf p).smooth N) (fun j _ => (hC j p hp).1) zero_le_one
    (traceForm_mixedSpace_coercive F) η
  rw [one_mul] at key
  refine key.trans (mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun j _ => (hC j p hp).2) ?_)
  positivity

theorem one_add_norm_pow_mul_norm_fourierIntegral_le {Q : Set (GL𝔸 × GL𝔸)} (hQ : IsCompact Q)
    (N : ℕ) {ψ : AddChar 𝔸 ℂ}
    (hψa : ∀ a : E∞,
      ψ.compAddMonoidHom ((AddMonoidHom.inl (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F)).comp
        (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm.toAddMonoidHom) a
          = ((Real.fourierChar (Algebra.trace ℝ E∞ a) : Circle) : ℂ)) :
    ∃ B : ℝ, ∀ p ∈ Q, ∀ η : E∞,
      (1 + ‖η‖) ^ N * ‖fourierIntegral
          (ψ.compAddMonoidHom ((AddMonoidHom.inl (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F)).comp
            (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm.toAddMonoidHom))
          volume (⇑(sliceArch hf p)) η‖ ≤ B := by
  obtain ⟨BN, hBN⟩ := pow_mul_norm_fourierIntegral_le hf hQ N hψa
  obtain ⟨B0, hB0⟩ := pow_mul_norm_fourierIntegral_le hf hQ 0 hψa
  refine ⟨2 ^ N * (BN + B0), fun p hp η => ?_⟩
  have hN := hBN p hp η
  have h0 := hB0 p hp η
  rw [pow_zero, one_mul] at h0
  have hX := norm_nonneg (fourierIntegral
    (ψ.compAddMonoidHom ((AddMonoidHom.inl (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F)).comp
      (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm.toAddMonoidHom))
    volume (⇑(sliceArch hf p)) η)
  calc (1 + ‖η‖) ^ N * _ ≤ 2 ^ N * (‖η‖ ^ N + 1) * _ :=
        mul_le_mul_of_nonneg_right (one_add_pow_le (norm_nonneg η) N) hX
    _ = 2 ^ N * (‖η‖ ^ N * _ + _) := by ring
    _ ≤ 2 ^ N * (BN + B0) := mul_le_mul_of_nonneg_left (add_le_add hN h0) (by positivity)

theorem archDecayOn {Q : Set (GL𝔸 × GL𝔸)} (hQ : IsCompact Q) {ψ : AddChar 𝔸 ℂ}
    (hψa : ∀ a : E∞,
      ψ.compAddMonoidHom ((AddMonoidHom.inl (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F)).comp
        (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm.toAddMonoidHom) a
          = ((Real.fourierChar (Algebra.trace ℝ E∞ a) : Circle) : ℂ)) (M : ℕ) :
    ∃ A : ℝ, ∀ p ∈ Q, ∀ (α : 𝔸ˣ) (t : ℝ), 1 ≤ t →
      (∀ v : InfinitePlace F, ‖(α : 𝔸).1 v‖ = t) → ∀ ξ : F,
        ‖fourierIntegral
            (ψ.compAddMonoidHom ((AddMonoidHom.inl (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F)).comp
              (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm.toAddMonoidHom))
            volume (⇑(sliceArch hf p)) (e∞ ((α : 𝔸) * ι ξ).1)‖
          ≤ A * ∏ w : InfinitePlace F, ((1 + t * w ξ) ^ M)⁻¹ := by
  obtain ⟨B, hB⟩ :=
    one_add_norm_pow_mul_norm_fourierIntegral_le hf hQ (M * Fintype.card (InfinitePlace F)) hψa
  refine ⟨max B 0, ?_⟩
  intro p hp α t ht hαa ξ
  have key := hB p hp (e∞ ((α : 𝔸) * ι ξ).1)
  have hprod := prod_one_add_mul_pow_le F α t ht hαa ξ M
  have ht0 : 0 ≤ t := zero_le_one.trans ht
  have hpos : 0 < ∏ w : InfinitePlace F, (1 + t * w ξ) ^ M :=
    Finset.prod_pos fun w _ => pow_pos (by positivity) M
  rw [Finset.prod_inv_distrib]
  refine (le_mul_inv_iff₀ hpos).2 ?_
  calc _ * ∏ w : InfinitePlace F, (1 + t * w ξ) ^ M
      ≤ _ * (1 + ‖e∞ ((α : 𝔸) * ι ξ).1‖) ^ (M * Fintype.card (InfinitePlace F)) :=
        mul_le_mul_of_nonneg_left hprod (norm_nonneg _)
    _ = (1 + ‖e∞ ((α : 𝔸) * ι ξ).1‖) ^ (M * Fintype.card (InfinitePlace F)) * _ := mul_comm _ _
    _ ≤ B := key
    _ ≤ max B 0 := le_max_left _ _

end Uniform

end ArchDecay

section FinSupport

theorem exists_ne_zero_forall_mem_range_of_isCompact
    (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K] [IsFractionRing R K]
    {C : Set (FiniteAdeleRing R K)} (hC : IsCompact C) :
    ∃ s : R, s ≠ 0 ∧ ∀ k : K, algebraMap K (FiniteAdeleRing R K) k ∈ C →
      algebraMap R K s * k ∈ (algebraMap R K).range := by
  obtain ⟨s, hs0, hs⟩ :=
    IsDedekindDomain.FiniteAdeleRing.exists_ne_zero_forall_mul_apply_mem_adicCompletionIntegers_of_isCompact R K hC
  refine ⟨s, hs0, fun k hk => HeightOneSpectrum.mem_integers_of_valuation_le_one K _ fun v => ?_⟩
  have h := hs _ hk v
  have hcomp : (algebraMap R (FiniteAdeleRing R K) s * algebraMap K (FiniteAdeleRing R K) k) v
      = algebraMap K (v.adicCompletion K) (algebraMap R K s * k) := by
    rw [map_mul]
    rfl
  rw [hcomp, HeightOneSpectrum.mem_adicCompletionIntegers] at h
  have hval : Valued.v (algebraMap K (v.adicCompletion K) (algebraMap R K s * k))
      = v.valuation K (algebraMap R K s * k) :=
    HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v (algebraMap R K s * k)
  rw [hval] at h
  exact h

theorem exists_ne_zero_forall_exists_coe_eq_mul_of_isCompact
    (F : Type*) [Field F] [NumberField F]
    {C : Set (FiniteAdeleRing (NumberField.RingOfIntegers F) F)} (hC : IsCompact C) :
    ∃ s : NumberField.RingOfIntegers F, s ≠ 0 ∧ ∀ ξ : F,
      algebraMap F (FiniteAdeleRing (NumberField.RingOfIntegers F) F) ξ ∈ C →
        ∃ a : NumberField.RingOfIntegers F, (a : F) = (s : F) * ξ := by
  obtain ⟨s, hs0, hs⟩ := exists_ne_zero_forall_mem_range_of_isCompact (NumberField.RingOfIntegers F) F hC
  refine ⟨s, hs0, fun ξ hξ => ?_⟩
  obtain ⟨a, ha⟩ := hs ξ hξ
  exact ⟨a, ha⟩

variable (F : Type) [Field F] [NumberField F]

local notation "𝔸" => AdeleRing (𝓞 F) F
local notation "𝔸f" => FiniteAdeleRing (𝓞 F) F
local notation "F∞" => InfiniteAdeleRing F
local notation "E∞" => mixedEmbedding.mixedSpace F
local notation "e∞" => InfiniteAdeleRing.ringEquiv_mixedSpace F
local notation "μ𝔸" => NumberField.AdelicHaar.adelicAddHaar (𝓞 F) F
local notation "GL𝔸" => GL (Fin 2) (AdeleRing (𝓞 F) F)

attribute [local instance] NumberField.AdelicHaar.adeleBorel
  NumberField.AdelicHaar.borelSpace_adeleBorel
  NumberField.AdelicHaar.isAddHaarMeasure_adelicAddHaar

def stdBump : ContDiffBump (0 : E∞) := ⟨1, 2, one_pos, one_lt_two⟩

def testFn : E∞ → ℂ := fun v => ((ContDiffBump.toFun (stdBump F) v : ℝ) : ℂ)

theorem contDiff_testFn : ContDiff ℝ (⊤ : ℕ∞) (testFn F) :=
  Complex.ofRealCLM.contDiff.comp (stdBump F).contDiff

theorem hasCompactSupport_testFn : HasCompactSupport (testFn F) :=
  (stdBump F).hasCompactSupport.comp_left Complex.ofReal_zero

theorem integral_testFn_ne_zero : ∫ v, testFn F v ≠ 0 := by
  unfold testFn
  rw [integral_complex_ofReal, Ne, Complex.ofReal_eq_zero]
  exact ((stdBump F).integral_pos (μ := volume)).ne'

def testSchwartz : 𝓢(E∞, ℂ) where
  toFun v := testFn F ((0 : E∞) + ContinuousLinearMap.id ℝ E∞ v)
  smooth' := (contDiff_testFn F).comp (contDiff_const.add (ContinuousLinearMap.id ℝ E∞).contDiff)
  decay' := by
    intro a n
    obtain ⟨-, hC⟩ :=
      exists_isCompact_tsupport_subset_and_norm_pow_mul_norm_iteratedFDeriv_comp_le_of_hasCompactSupport
        (P := Unit) (contDiff_testFn F) (hasCompactSupport_testFn F) isCompact_singleton
        (c := fun _ => (0 : E∞)) (ℓ := fun _ => ContinuousLinearMap.id ℝ E∞)
        continuousOn_const continuousOn_const (fun _ _ => Function.injective_id)
    obtain ⟨C, hC'⟩ := hC a n
    exact ⟨C, fun v => hC' () (Set.mem_singleton _) v⟩

theorem testSchwartz_apply (v : E∞) : testSchwartz F v = testFn F v := by
  show testFn F ((0 : E∞) + v) = _
  rw [zero_add]

theorem fourierIntegral_testSchwartz_zero (ψA : AddChar E∞ ℂ) :
    fourierIntegral ψA volume (⇑(testSchwartz F)) 0 = ∫ v, testFn F v := by
  simp only [fourierIntegral, mul_zero, neg_zero, AddChar.map_zero_eq_one, one_mul,
    testSchwartz_apply]

variable {F}

theorem bounded_and_hasCompactSupport_of_mem_schwartzBruhat {Φ : 𝔸 → ℂ}
    (hΦ : Φ ∈ schwartzBruhat F) :
    (∃ B : ℝ, ∀ y : 𝔸f, ‖Φ ((0 : F∞), y)‖ ≤ B) ∧ HasCompactSupport (fun y : 𝔸f => Φ ((0 : F∞), y)) := by
  refine schwartzBruhat_induction (p := fun Φ _ =>
    (∃ B : ℝ, ∀ y : 𝔸f, ‖Φ ((0 : F∞), y)‖ ≤ B) ∧ HasCompactSupport (fun y : 𝔸f => Φ ((0 : F∞), y)))
    ?_ ?_ ?_ ?_ hΦ
  · rintro _ ⟨g, h, hlc, hcs, rfl⟩
    obtain ⟨C, hC⟩ := hcs.exists_bound_of_continuous hlc.continuous
    refine ⟨⟨‖g (e∞ 0)‖ * C, fun y => ?_⟩, ?_⟩
    · show ‖g (e∞ 0) * h y‖ ≤ _
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (hC y) (norm_nonneg _)
    · show HasCompactSupport (fun y => g (e∞ 0) * h y)
      exact hcs.mul_left (f := fun _ => g (e∞ 0))
  · refine ⟨⟨0, fun y => ?_⟩, ?_⟩
    · rw [show (0 : 𝔸 → ℂ) ((0 : F∞), y) = 0 from rfl, norm_zero]
    · exact HasCompactSupport.intro isCompact_empty fun _ _ => rfl
  · rintro Φ₁ Φ₂ - - ⟨⟨B₁, hB₁⟩, hc₁⟩ ⟨⟨B₂, hB₂⟩, hc₂⟩
    refine ⟨⟨B₁ + B₂, fun y => ?_⟩, hc₁.add hc₂⟩
    exact (norm_add_le _ _).trans (add_le_add (hB₁ y) (hB₂ y))
  · rintro c Φ - ⟨⟨B, hB⟩, hc⟩
    refine ⟨⟨‖c‖ * B, fun y => ?_⟩, hc.smul_left (f := fun _ => c)⟩
    show ‖c • Φ ((0 : F∞), y)‖ ≤ _
    rw [norm_smul]
    exact mul_le_mul_of_nonneg_left (hB y) (norm_nonneg _)

theorem bounded_and_hasCompactSupport_finTransform
    [MeasurableSpace 𝔸f] [BorelSpace 𝔸f] (ν : Measure 𝔸f) [ν.IsAddHaarMeasure]
    {ψ : AddChar 𝔸 ℂ} (hψ : IsGlobalAddChar F ψ)
    {h : 𝔸f → ℂ} (hlc : IsLocallyConstant h) (hcs : HasCompactSupport h) :
    (∃ B : ℝ, ∀ y : 𝔸f,
      ‖fourierIntegral (ψ.compAddMonoidHom (AddMonoidHom.inr (InfiniteAdeleRing F) 𝔸f)) ν h y‖ ≤ B) ∧
      HasCompactSupport
        (fourierIntegral (ψ.compAddMonoidHom (AddMonoidHom.inr (InfiniteAdeleRing F) 𝔸f)) ν h) := by
  have hψu : ∀ a : 𝔸, ‖ψ a‖ = 1 := norm_apply_eq_one_of_isGlobalAddChar F hψ
  have hmem : (fun x : 𝔸 => testSchwartz F (e∞ x.1) * h x.2) ∈ schwartzBruhat F :=
    mem_schwartzBruhat_of_mem_pureTensorSet (tensor_mem_pureTensorSet (testSchwartz F) h hlc hcs)
  obtain ⟨⟨B, hB⟩, hcsF⟩ := bounded_and_hasCompactSupport_of_mem_schwartzBruhat
    (fourierIntegral_mem_schwartzBruhat F μ𝔸 hψ hmem)
  set c : ℂ := (((μ𝔸) (adelicBox F)).toReal : ℂ) /
      ((ZLattice.covolume (mixedEmbedding.integerLattice F) volume : ℂ)
        * ((ν (AdelicBox.integralFiniteAdeles (𝓞 F) F)).toReal : ℂ)) with hcdef
  set I : ℂ := fourierIntegral
      (ψ.compAddMonoidHom ((AddMonoidHom.inl (InfiniteAdeleRing F) 𝔸f).comp
        (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm.toAddMonoidHom))
      volume (⇑(testSchwartz F)) (e∞ 0) with hIdef
  have hc0 : c ≠ 0 := by
    have h1 : ((μ𝔸) (adelicBox F)).toReal ≠ 0 := ENNReal.toReal_ne_zero.2
      ⟨(measure_adelicBox_pos F μ𝔸).ne', (measure_adelicBox_lt_top F μ𝔸).ne⟩
    have h2 : ZLattice.covolume (mixedEmbedding.integerLattice F) volume ≠ 0 :=
      (ZLattice.covolume_pos (mixedEmbedding.integerLattice F) volume).ne'
    have h0O : (0 : 𝔸f) ∈ AdelicBox.integralFiniteAdeles (𝓞 F) F := fun v => by
      rw [show (0 : 𝔸f) v = 0 from rfl]
      exact zero_mem _
    have h3 : (ν (AdelicBox.integralFiniteAdeles (𝓞 F) F)).toReal ≠ 0 := ENNReal.toReal_ne_zero.2
      ⟨((AdelicBox.isOpen_integralFiniteAdeles F).measure_pos ν ⟨0, h0O⟩).ne',
        (AdelicBox.isCompact_integralFiniteAdeles F).measure_lt_top.ne⟩
    rw [hcdef]
    exact div_ne_zero (Complex.ofReal_ne_zero.2 h1)
      (mul_ne_zero (Complex.ofReal_ne_zero.2 h2) (Complex.ofReal_ne_zero.2 h3))
  have hI0 : I ≠ 0 := by
    rw [hIdef, map_zero, fourierIntegral_testSchwartz_zero]
    exact integral_testFn_ne_zero F
  have hcI : c * I ≠ 0 := mul_ne_zero hc0 hI0
  have hX : ∀ y : 𝔸f,
      fourierIntegral (ψ.compAddMonoidHom (AddMonoidHom.inr (InfiniteAdeleRing F) 𝔸f)) ν h y
        = (c * I)⁻¹ * fourierIntegral ψ μ𝔸 (fun x : 𝔸 => testSchwartz F (e∞ x.1) * h x.2)
            ((0 : F∞), y) := by
    intro y
    have h91 : fourierIntegral ψ μ𝔸 (fun x : 𝔸 => testSchwartz F (e∞ x.1) * h x.2) ((0 : F∞), y)
        = c * I * fourierIntegral (ψ.compAddMonoidHom (AddMonoidHom.inr (InfiniteAdeleRing F) 𝔸f))
            ν h y :=
      fourierIntegral_pureTensor_eq F μ𝔸 ν hψ.continuous hψu (testSchwartz F) hlc hcs ((0 : F∞), y)
    rw [h91, inv_mul_cancel_left₀ hcI]
  refine ⟨⟨‖(c * I)⁻¹‖ * B, fun y => ?_⟩, ?_⟩
  · rw [hX y, norm_mul]
    exact mul_le_mul_of_nonneg_left (hB y) (norm_nonneg _)
  · rw [show fourierIntegral (ψ.compAddMonoidHom (AddMonoidHom.inr (InfiniteAdeleRing F) 𝔸f)) ν h
        = fun y => (c * I)⁻¹ * fourierIntegral ψ μ𝔸 (fun x : 𝔸 => testSchwartz F (e∞ x.1) * h x.2)
            ((0 : F∞), y) from funext hX]
    exact hcsF.mul_left (f := fun _ => (c * I)⁻¹)

variable {f : GL (Fin 2) (AdeleRing (𝓞 F) F) → ℂ} (hf : IsFactorizableTestFn F f)

theorem finite_image_sliceFin {Q : Set (GL𝔸 × GL𝔸)} (hQ : IsCompact Q) :
    ((fun p => sliceFin hf p) '' Q).Finite := by
  haveI : CompactSpace Q := isCompact_iff_compactSpace.mp hQ
  have hΛ := (isFinTestFactor_finFactor hf).1.isLocallyConstant_fun_mul_apply_mul_of_hasCompactSupport
    (isFinTestFactor_finFactor hf).2 (unipotentGL2 (R := 𝔸f))
  have hκ : Continuous fun p : Q =>
      (glFin (𝓞 F) F ((p : GL𝔸 × GL𝔸).1), glFin (𝓞 F) F ((p : GL𝔸 × GL𝔸).2)) :=
    ((continuous_glFin (𝓞 F) F).comp (continuous_fst.comp continuous_subtype_val)).prodMk
      ((continuous_glFin (𝓞 F) F).comp (continuous_snd.comp continuous_subtype_val))
  refine ((hΛ.comp_continuous hκ).range_finite).subset ?_
  rintro _ ⟨p, hp, rfl⟩
  refine ⟨⟨p, hp⟩, ?_⟩
  funext y
  show finFactor hf (glFin (𝓞 F) F p.1 * unipotentGL2 y * glFin (𝓞 F) F p.2) = sliceFin hf p y
  simp only [sliceFin, mul_assoc]

theorem finSupportOn [MeasurableSpace 𝔸f] [BorelSpace 𝔸f] (ν : Measure 𝔸f) [ν.IsAddHaarMeasure]
    {ψ : AddChar 𝔸 ℂ} (hψ : IsGlobalAddChar F ψ) {Q : Set (GL𝔸 × GL𝔸)} (hQ : IsCompact Q) :
    ∃ C : Set 𝔸f, IsCompact C ∧ ∃ Bf : ℝ, ∀ p ∈ Q, ∀ y : 𝔸f,
      ‖fourierIntegral (ψ.compAddMonoidHom (AddMonoidHom.inr (InfiniteAdeleRing F) 𝔸f)) ν (sliceFin hf p) y‖
          ≤ Bf ∧
        (fourierIntegral (ψ.compAddMonoidHom (AddMonoidHom.inr (InfiniteAdeleRing F) 𝔸f)) ν (sliceFin hf p) y
          ≠ 0 → y ∈ C) := by
  set S : Set (𝔸f → ℂ) := (fun p => sliceFin hf p) '' Q with hSdef
  have hSfin : S.Finite := finite_image_sliceFin hf hQ
  have hmemS : ∀ p ∈ Q, sliceFin hf p ∈ S := fun p hp => ⟨p, hp, rfl⟩
  have hS : ∀ h ∈ S, IsLocallyConstant h ∧ HasCompactSupport h := by
    rintro h ⟨p, -, rfl⟩
    exact ⟨isLocallyConstant_sliceFin hf p, hasCompactSupport_sliceFin hf p⟩
  let β : (𝔸f → ℂ) → ℝ := fun h =>
    if hh : IsLocallyConstant h ∧ HasCompactSupport h then
      Classical.choose (bounded_and_hasCompactSupport_finTransform ν hψ hh.1 hh.2).1 else 0
  have hβ : ∀ h : 𝔸f → ℂ, ∀ hh : IsLocallyConstant h ∧ HasCompactSupport h, ∀ y : 𝔸f,
      ‖fourierIntegral (ψ.compAddMonoidHom (AddMonoidHom.inr (InfiniteAdeleRing F) 𝔸f)) ν h y‖
        ≤ β h := by
    intro h hh y
    have : β h = Classical.choose (bounded_and_hasCompactSupport_finTransform ν hψ hh.1 hh.2).1 :=
      dif_pos hh
    rw [this]
    exact Classical.choose_spec (bounded_and_hasCompactSupport_finTransform ν hψ hh.1 hh.2).1 y
  refine ⟨⋃ h ∈ S, tsupport
      (fourierIntegral (ψ.compAddMonoidHom (AddMonoidHom.inr (InfiniteAdeleRing F) 𝔸f)) ν h),
    hSfin.isCompact_biUnion fun h hh =>
      (bounded_and_hasCompactSupport_finTransform ν hψ (hS h hh).1 (hS h hh).2).2,
    ∑ h ∈ hSfin.toFinset, max (β h) 0, fun p hp y => ⟨?_, fun hne => ?_⟩⟩
  · refine (hβ _ ⟨isLocallyConstant_sliceFin hf p, hasCompactSupport_sliceFin hf p⟩ y).trans ?_
    exact (le_max_left _ _).trans
      (Finset.single_le_sum (fun h _ => le_max_right _ _) (hSfin.mem_toFinset.2 (hmemS p hp)))
  · exact Set.mem_biUnion (hmemS p hp) (subset_tsupport _ hne)

end FinSupport

section SliceDecay

variable (F : Type) [Field F] [NumberField F]

local notation "𝔸" => AdeleRing (𝓞 F) F
local notation "𝔸f" => FiniteAdeleRing (𝓞 F) F
local notation "ι" => algebraMap F (AdeleRing (𝓞 F) F)
local notation "F∞" => InfiniteAdeleRing F
local notation "E∞" => mixedEmbedding.mixedSpace F
local notation "e∞" => InfiniteAdeleRing.ringEquiv_mixedSpace F
local notation "μ𝔸" => NumberField.AdelicHaar.adelicAddHaar (𝓞 F) F
local notation "GL𝔸" => GL (Fin 2) (AdeleRing (𝓞 F) F)

attribute [local instance] NumberField.AdelicHaar.adeleBorel
  NumberField.AdelicHaar.borelSpace_adeleBorel
  NumberField.AdelicHaar.isAddHaarMeasure_adelicAddHaar

theorem sliceDecayOn {f : GL𝔸 → ℂ} (hf : IsFactorizableTestFn F f)
    {ψ : AddChar 𝔸 ℂ} (hψ : IsGlobalAddChar F ψ)
    (hψa : ∀ a : E∞,
      ψ.compAddMonoidHom ((AddMonoidHom.inl (InfiniteAdeleRing F) 𝔸f).comp
        (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm.toAddMonoidHom) a
          = ((Real.fourierChar (Algebra.trace ℝ E∞ a) : Circle) : ℂ))
    {Q : Set (GL𝔸 × GL𝔸)} (hQ : IsCompact Q) :
    ∃ s : 𝓞 F, s ≠ 0 ∧ ∀ M : ℕ, ∃ B : ℝ, ∀ p ∈ Q, ∀ (α : 𝔸ˣ) (t : ℝ), 1 ≤ t →
      (α : 𝔸).2 = 1 → (∀ v : InfinitePlace F, ‖(α : 𝔸).1 v‖ = t) → ∀ ξ : F,
        ‖fourierIntegral ψ μ𝔸 (fun s : 𝔸 => f (p.1 * unipotentGL2 s * p.2)) ((α : 𝔸) * ι ξ)‖
            ≤ B * ∏ w : InfinitePlace F, ((1 + t * w ξ) ^ M)⁻¹ ∧
        (fourierIntegral ψ μ𝔸 (fun s : 𝔸 => f (p.1 * unipotentGL2 s * p.2)) ((α : 𝔸) * ι ξ) ≠ 0 →
          ∃ a : 𝓞 F, (a : F) = (s : F) * ξ) := by
  borelize 𝔸f
  set ν : Measure 𝔸f := Measure.addHaar with hν
  have hψu : ∀ a : 𝔸, ‖ψ a‖ = 1 := norm_apply_eq_one_of_isGlobalAddChar F hψ
  obtain ⟨C, hC, Bf, hfinB⟩ := finSupportOn hf ν hψ hQ
  obtain ⟨s, hs0, hsC⟩ := exists_ne_zero_forall_exists_coe_eq_mul_of_isCompact F hC
  refine ⟨s, hs0, fun M => ?_⟩
  obtain ⟨A, hA⟩ := archDecayOn hf hQ hψa M
  set c : ℂ := (((μ𝔸) (adelicBox F)).toReal : ℂ) /
      ((ZLattice.covolume (mixedEmbedding.integerLattice F) volume : ℂ)
        * ((ν (AdelicBox.integralFiniteAdeles (𝓞 F) F)).toReal : ℂ)) with hcdef
  refine ⟨‖c‖ * A * Bf, ?_⟩
  intro p hp α t ht hαf hαa ξ
  have hT : ∀ w : 𝔸, fourierIntegral ψ μ𝔸 (fun s : 𝔸 => f (p.1 * unipotentGL2 s * p.2)) w
      = c * fourierIntegral
            (ψ.compAddMonoidHom ((AddMonoidHom.inl (InfiniteAdeleRing F) 𝔸f).comp
              (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm.toAddMonoidHom))
            volume (⇑(sliceArch hf p)) (e∞ w.1)
          * fourierIntegral (ψ.compAddMonoidHom (AddMonoidHom.inr (InfiniteAdeleRing F) 𝔸f))
            ν (sliceFin hf p) w.2 := by
    intro w
    rw [slice_eq_tensor hf p]
    exact fourierIntegral_pureTensor_eq F μ𝔸 ν hψ.continuous hψu (sliceArch hf p)
      (isLocallyConstant_sliceFin hf p) (hasCompactSupport_sliceFin hf p) w
  have hw2 : ((α : 𝔸) * ι ξ).2 = algebraMap F 𝔸f ξ := by
    show (α : 𝔸).2 * (ι ξ).2 = _
    rw [hαf, one_mul]
    rfl
  obtain ⟨hYb, hYC⟩ := hfinB p hp ((α : 𝔸) * ι ξ).2
  refine ⟨?_, fun hne => ?_⟩
  · rw [hT, norm_mul, norm_mul]
    have hX := hA p hp α t ht hαa ξ
    refine (mul_le_mul (mul_le_mul_of_nonneg_left hX (norm_nonneg _)) hYb (norm_nonneg _)
      (mul_nonneg (norm_nonneg _) ((norm_nonneg _).trans hX))).trans_eq ?_
    ring
  · rw [hT] at hne
    exact hsC ξ (hw2 ▸ hYC (right_ne_zero_of_mul hne))

end SliceDecay

section Character

variable (F : Type) [Field F] [NumberField F]

local notation "𝔸" => AdeleRing (𝓞 F) F
local notation "𝔸f" => FiniteAdeleRing (𝓞 F) F
local notation "ι" => algebraMap F (AdeleRing (𝓞 F) F)
local notation "F∞" => InfiniteAdeleRing F
local notation "E∞" => mixedEmbedding.mixedSpace F
local notation "e∞" => InfiniteAdeleRing.ringEquiv_mixedSpace F

theorem exists_isGlobalAddChar_std :
    ∃ ψ : AddChar 𝔸 ℂ, IsGlobalAddChar F ψ ∧ ∀ a : E∞,
      ψ.compAddMonoidHom ((AddMonoidHom.inl (InfiniteAdeleRing F) 𝔸f).comp
        (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm.toAddMonoidHom) a
          = ((Real.fourierChar (Algebra.trace ℝ E∞ a) : Circle) : ℂ) := by
  set ψ₀ : AddChar 𝔸 ℂ := NumberField.StandardAddChar.stdAddChar F with hψ₀def
  have hψ₀ : IsGlobalAddChar F ψ₀ := (NumberField.StandardAddChar.adelicTraceData F).isGlobalAddChar_psiK
  obtain ⟨a, ha0, ha⟩ := exists_ne_zero_apply_eq_fourierChar_trace_of_isGlobalAddChar F hψ₀
  set ψ : AddChar 𝔸 ℂ := ψ₀.compAddMonoidHom (AddMonoidHom.mulLeft (ι a)) with hψdef
  have hψapp : ∀ x : 𝔸, ψ x = ψ₀ (ι a * x) := fun x => rfl
  refine ⟨ψ, ⟨?_, ?_, ?_⟩, fun v => ?_⟩
  · intro α
    rw [hψapp, ← map_mul]
    exact hψ₀.principalInvariant (a * α)
  · show Continuous fun x => ψ x
    simp_rw [hψapp]
    exact hψ₀.continuous.comp (continuous_const.mul continuous_id)
  · intro h1
    apply hψ₀.nontrivial
    ext x
    have hx : x = ι a * (ι a⁻¹ * x) := by
      rw [← mul_assoc, ← map_mul, mul_inv_cancel₀ ha0, map_one, one_mul]
    rw [hx, ← hψapp, h1]
    rfl
  · show ψ (((e∞).symm v, 0) : 𝔸) = _
    have hx0 : ∀ x0 : 𝔸, x0 = ((e∞).symm v, 0) →
        ψ x0 = ((Real.fourierChar (Algebra.trace ℝ E∞ v) : Circle) : ℂ) := by
      intro x0 hx0
      rw [hψapp]
      have hprod : ι a * x0 = ((algebraMap F F∞ a * (e∞).symm v, 0) : 𝔸) := by
        subst hx0
        exact Prod.ext rfl (mul_zero _)
      rw [hprod, ha ((e∞).symm v), RingEquiv.apply_symm_apply]
    exact hx0 _ rfl

end Character

section Assembly

variable (F : Type) [Field F] [NumberField F]

local notation "𝔸" => AdeleRing (𝓞 F) F
local notation "𝔸f" => FiniteAdeleRing (𝓞 F) F
local notation "ι" => algebraMap F (AdeleRing (𝓞 F) F)
local notation "F∞" => InfiniteAdeleRing F
local notation "E∞" => mixedEmbedding.mixedSpace F
local notation "e∞" => InfiniteAdeleRing.ringEquiv_mixedSpace F
local notation "μ𝔸" => NumberField.AdelicHaar.adelicAddHaar (𝓞 F) F
local notation "GL𝔸" => GL (Fin 2) (AdeleRing (𝓞 F) F)

attribute [local instance] NumberField.AdelicHaar.adeleBorel
  NumberField.AdelicHaar.borelSpace_adeleBorel
  NumberField.AdelicHaar.isAddHaarMeasure_adelicAddHaar

theorem fourierIntegral_zero_right (ψ : AddChar 𝔸 ℂ) (μ : Measure 𝔸) (Φ : 𝔸 → ℂ) :
    fourierIntegral ψ μ Φ 0 = ∫ t, Φ t ∂μ := by
  simp [fourierIntegral_def]

theorem norm_fourierIntegral_affine (ψ : AddChar 𝔸 ℂ) (hψu : ∀ x : 𝔸, ‖ψ x‖ = 1) (Ψ : 𝔸 → ℂ)
    (τ : 𝔸ˣ) (β η : 𝔸) :
    ‖fourierIntegral ψ μ𝔸 (fun s => Ψ ((τ : 𝔸) * s + β)) η‖
      = ((distribHaarChar 𝔸 τ : ℝ))⁻¹ * ‖fourierIntegral ψ μ𝔸 Ψ (((τ⁻¹ : 𝔸ˣ) : 𝔸) * η)‖ := by
  have h1 : (fun s => Ψ ((τ : 𝔸) * s + β)) = fun v => (Ψ ∘ fun u => u + β) ((τ : 𝔸) * v) := by
    funext v; rfl
  rw [h1, fourierIntegral_comp_mul_left F μ𝔸 ψ (Ψ ∘ fun u => u + β) τ η,
    fourierIntegral_comp_add_right ψ μ𝔸 Ψ β]
  rw [norm_mul, norm_mul, hψu, one_mul, norm_inv, Complex.norm_real,
    Real.norm_of_nonneg (NNReal.coe_nonneg _)]

theorem main (φ : GL𝔸 → ℂ) (hφ : IsFactorizableTestFn F φ)
    (Q : Set (GL𝔸 × GL𝔸)) (hQ : IsCompact Q) (N : ℕ) :
    ∃ C : ℝ, ∀ p ∈ Q, ∀ (a : 𝔸ˣ) (t : ℝ), 1 ≤ t → (a : 𝔸).2 = 1 →
      (∀ w : InfinitePlace F, ‖(a : 𝔸).1 w‖ = t) → ∀ e : 𝔸,
        ‖(∑' β : F, φ (p.1 * unipotentGL2 ((ι β + e) * ↑a⁻¹) * p.2)) -
            ((μ𝔸 (adelicBox F)).toReal : ℂ)⁻¹ *
              ∫ u, φ (p.1 * unipotentGL2 ((u + e) * ↑a⁻¹) * p.2) ∂μ𝔸‖
          ≤ C * t⁻¹ ^ N := by
  classical
  obtain ⟨ψ, hψ, hψa⟩ := exists_isGlobalAddChar_std F
  have hψu : ∀ x : 𝔸, ‖ψ x‖ = 1 := norm_apply_eq_one_of_isGlobalAddChar F hψ
  obtain ⟨s, hs, hdec⟩ := sliceDecayOn F hφ hψ hψa hQ
  obtain ⟨M, C, hC0, hLS⟩ := NumberField.InfinitePlace.exists_sum_prod_inv_one_add_mul_pow_le F hs (N + 1)
  obtain ⟨B, hB⟩ := hdec M
  set B₀ : ℝ := max B 0 with hB₀def
  have hB₀ : 0 ≤ B₀ := le_max_right _ _
  have hBB₀ : B ≤ B₀ := le_max_left _ _
  set m₀ : ℝ := ‖((((μ𝔸) (adelicBox F)).toReal : ℂ))⁻¹‖ with hm₀def
  refine ⟨m₀ * (B₀ * C), fun p hp a t ht haf haa e => ?_⟩
  have ht0 : 0 < t := one_pos.trans_le ht
  have hnpos : 0 < Module.finrank ℚ F := Module.finrank_pos

  set g : 𝔸 → ℂ := fun v => φ (p.1 * unipotentGL2 v * p.2) with hgdef
  set Ψ : 𝔸 → ℂ := fun v => g (((a⁻¹ : 𝔸ˣ) : 𝔸) * v + ((a⁻¹ : 𝔸ˣ) : 𝔸) * e) with hΨdef
  have hΨ_apply : ∀ v : 𝔸, φ (p.1 * unipotentGL2 ((v + e) * ↑a⁻¹) * p.2) = Ψ v := by
    intro v
    simp only [hΨdef, hgdef]
    rw [show (v + e) * ((a⁻¹ : 𝔸ˣ) : 𝔸) = ((a⁻¹ : 𝔸ˣ) : 𝔸) * v + ((a⁻¹ : 𝔸ˣ) : 𝔸) * e by ring]

  have hΨslice : Ψ = fun v => φ ((p.1 * diagFst a⁻¹)
      * unipotentGL2 v * (diagFst a * unipotentGL2 (((a⁻¹ : 𝔸ˣ) : 𝔸) * e) * p.2)) := by
    funext v
    simp only [hΨdef, hgdef]
    rw [unipotentGL2_add, mul_comm (((a⁻¹ : 𝔸ˣ) : 𝔸)) v, unipotentGL2_mul_eq_conj]
    simp only [mul_assoc]
  have hΨSB : Ψ ∈ schwartzBruhat F := by
    rw [hΨslice]
    exact mem_schwartzBruhat_of_mem_pureTensorSet
      (AutomorphicForm.IsFactorizableTestFn.comp_mul_unipotentGL2_mul_mem_pureTensorSet F hφ _ _)
  have hgSB : g ∈ schwartzBruhat F :=
    mem_schwartzBruhat_of_mem_pureTensorSet
      (AutomorphicForm.IsFactorizableTestFn.comp_mul_unipotentGL2_mul_mem_pureTensorSet F hφ _ _)

  have hP := tsum_eq_inv_measure_mul_tsum_fourierIntegral F μ𝔸 hψ hΨSB
  have hint : Integrable Ψ μ𝔸 := integrable_of_mem_schwartzBruhat F μ𝔸 hΨSB
  have hzero : fourierIntegral ψ μ𝔸 Ψ 0 = ∫ u, Ψ u ∂μ𝔸 := fourierIntegral_zero_right F ψ μ𝔸 Ψ
  have hLHS : (∑' β : F, φ (p.1 * unipotentGL2 ((ι β + e) * ↑a⁻¹) * p.2)) -
        ((μ𝔸 (adelicBox F)).toReal : ℂ)⁻¹ * ∫ u, φ (p.1 * unipotentGL2 ((u + e) * ↑a⁻¹) * p.2) ∂μ𝔸
      = ((μ𝔸 (adelicBox F)).toReal : ℂ)⁻¹ *
          (∑' β : F, fourierIntegral ψ μ𝔸 Ψ (ι β) - fourierIntegral ψ μ𝔸 Ψ 0) := by
    simp_rw [hΨ_apply]
    rw [hP, hzero, mul_sub]
  rw [hLHS]

  have htn : ∏ v : InfinitePlace F, t ^ v.mult = t ^ Module.finrank ℚ F := by
    rw [Finset.prod_pow_eq_pow_sum, NumberField.InfinitePlace.sum_mult_eq]
  have hδ : ((distribHaarChar 𝔸 a⁻¹ : ℝ))⁻¹ = t ^ Module.finrank ℚ F := by
    rw [map_inv, NNReal.coe_inv, inv_inv,
      NumberField.AdeleRing.distribHaarChar_eq_prod_norm_pow_mult_of_snd_eq_one F a haf, ← htn]
    exact Finset.prod_congr rfl fun v _ => by rw [haa v]

  have hG3 : ∀ η : 𝔸, ‖fourierIntegral ψ μ𝔸 Ψ η‖
      = t ^ Module.finrank ℚ F * ‖fourierIntegral ψ μ𝔸 g ((a : 𝔸) * η)‖ := by
    intro η
    have h := norm_fourierIntegral_affine F ψ hψu g a⁻¹ (((a⁻¹ : 𝔸ˣ) : 𝔸) * e) η
    rw [inv_inv] at h
    rw [show Ψ = fun v => g (((a⁻¹ : 𝔸ˣ) : 𝔸) * v + ((a⁻¹ : 𝔸ˣ) : 𝔸) * e) from rfl, h, hδ]

  have hSB : fourierIntegral ψ μ𝔸 Ψ ∈ schwartzBruhat F := fourierIntegral_mem_schwartzBruhat F μ𝔸 hψ hΨSB
  have hsumm : Summable fun ξ : F => fourierIntegral ψ μ𝔸 Ψ (ι ξ) := by
    simpa only [zero_add] using summable_translate_of_mem_schwartzBruhat F hSB 0
  have hsplit := hsumm.tsum_eq_add_tsum_ite 0
  rw [map_zero] at hsplit
  rw [hsplit, add_sub_cancel_left]

  set H : ℝ := t ^ Module.finrank ℚ F with hHdef
  have hH1 : 1 ≤ H := one_le_pow₀ ht
  have hH0 : 0 < H := one_pos.trans_le hH1
  set nrm : F → ℝ := fun ζ => ‖fourierIntegral ψ μ𝔸 g ((a : 𝔸) * ι ζ)‖ with hnrmdef
  set b : F → ℝ := fun ξ => if ξ = 0 then 0 else H * nrm ξ with hbdef
  have hb0 : 0 ≤ b := fun ξ => by
    simp only [hbdef, Pi.zero_apply]
    split_ifs
    · exact le_rfl
    · exact mul_nonneg hH0.le (norm_nonneg _)
  have hpt : ∀ ξ : F, ‖(if ξ = 0 then 0 else fourierIntegral ψ μ𝔸 Ψ (ι ξ))‖ ≤ b ξ := by
    intro ξ
    by_cases hξ : ξ = 0
    · simp [hbdef, hξ]
    · rw [if_neg hξ, hG3]
      simp [hbdef, hnrmdef, hξ, hHdef]
  have hpartial : ∀ u : Finset F, ∑ ξ ∈ u, b ξ ≤ B₀ * C * H⁻¹ ^ N := by
    intro u
    have h1 : ∑ ξ ∈ u, b ξ = H * ∑ ζ ∈ u.filter (· ≠ 0), nrm ζ := by
      rw [Finset.mul_sum, Finset.sum_filter]
      refine Finset.sum_congr rfl fun ξ _ => ?_
      by_cases hξ : ξ = 0 <;> simp [hbdef, hξ]
    set v : Finset F := u.filter (· ≠ 0) with hvdef
    have hv0 : ∀ ζ ∈ v, ζ ≠ 0 := fun ζ hζ => (Finset.mem_filter.1 hζ).2
    set good : F → Prop := fun ζ => ∃ a' : 𝓞 F, (a' : F) = (s : F) * ζ with hgooddef
    have h2 : ∑ ζ ∈ v, nrm ζ = ∑ ζ ∈ v.filter good, nrm ζ := by
      refine (Finset.sum_filter_of_ne fun ζ hζ hne => ?_).symm
      have hne' : fourierIntegral ψ μ𝔸 g ((a : 𝔸) * ι ζ) ≠ 0 := by
        intro h0; apply hne; simp [hnrmdef, h0]
      exact (hB p hp a t ht haf haa ζ).2 hne'
    have h3 : ∑ ζ ∈ v.filter good, nrm ζ
        ≤ B₀ * ∑ ζ ∈ v.filter good, ∏ w' : InfinitePlace F, ((1 + t * w' ζ) ^ M)⁻¹ := by
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun ζ hζ => ?_
      refine ((hB p hp a t ht haf haa ζ).1).trans ?_
      exact mul_le_mul_of_nonneg_right hBB₀ (Finset.prod_nonneg fun w' _ => by positivity)
    have h4 : ∑ ζ ∈ v.filter good, ∏ w' : InfinitePlace F, ((1 + t * w' ζ) ^ M)⁻¹
        ≤ C * ((H) ^ (N + 1))⁻¹ := by
      set yv : InfinitePlace F → ℝ := fun _ => t with hydef
      have hy : ∀ w', yv w' = t := fun _ => rfl
      have hyprod : ∏ w', yv w' ^ w'.mult = H := by rw [hHdef]; exact htn
      have h := hLS yv (fun _ => ht0) (by rw [hyprod]; exact hH1) (v.filter good)
        (fun ζ hζ => ⟨hv0 ζ (Finset.mem_filter.1 hζ).1, (Finset.mem_filter.1 hζ).2⟩)
      rw [hyprod] at h
      simp only [hy] at h
      exact h
    have hkey : H * ((H) ^ (N + 1))⁻¹ = H⁻¹ ^ N := by
      rw [inv_pow, pow_succ, mul_inv, mul_comm ((H ^ N)⁻¹), ← mul_assoc, mul_inv_cancel₀ hH0.ne', one_mul]
    calc ∑ ξ ∈ u, b ξ = H * ∑ ζ ∈ v, nrm ζ := h1
      _ ≤ H * (B₀ * (C * ((H) ^ (N + 1))⁻¹)) := by
          rw [h2]
          exact mul_le_mul_of_nonneg_left (h3.trans (mul_le_mul_of_nonneg_left h4 hB₀)) hH0.le
      _ = B₀ * C * H⁻¹ ^ N := by rw [← hkey]; ring
  have hbsum : Summable b := summable_of_sum_le hb0 hpartial
  have htail : ‖∑' ξ : F, (if ξ = 0 then 0 else fourierIntegral ψ μ𝔸 Ψ (ι ξ))‖ ≤ B₀ * C * H⁻¹ ^ N :=
    (tsum_of_norm_bounded hbsum.hasSum hpt).trans (Real.tsum_le_of_sum_le hb0 hpartial)

  have hHt : H⁻¹ ^ N ≤ t⁻¹ ^ N := by
    refine pow_le_pow_left₀ (inv_nonneg.mpr hH0.le) ?_ N
    rw [hHdef]
    exact inv_anti₀ ht0 (le_self_pow₀ ht hnpos.ne')
  calc ‖((((μ𝔸) (adelicBox F)).toReal : ℂ))⁻¹ *
          ∑' ξ : F, (if ξ = 0 then 0 else fourierIntegral ψ μ𝔸 Ψ (ι ξ))‖
      ≤ m₀ * (B₀ * C * H⁻¹ ^ N) := by
        rw [norm_mul, hm₀def]
        exact mul_le_mul_of_nonneg_left htail (norm_nonneg _)
    _ ≤ m₀ * (B₀ * C * t⁻¹ ^ N) := by
        refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hHt (mul_nonneg hB₀ hC0)) (norm_nonneg _)
    _ = m₀ * (B₀ * C) * t⁻¹ ^ N := by ring

end Assembly

end R4PoissonTail
p2m_reactivate "P2MW.S_AutomorphicForm_exists_forall_norm_tsum_sub_inv_measure_mul_integral_comp_unipotentGL2_le_of_isCompact.R4PoissonTail"

theorem solution
    (F : Type) [Field F] [NumberField F]
    (φ : Matrix.GeneralLinearGroup (Fin 2) (AdeleRing (𝓞 F) F) → ℂ)
    (hφ : AutomorphicForm.IsFactorizableTestFn F φ)
    (Q : Set (Matrix.GeneralLinearGroup (Fin 2) (AdeleRing (𝓞 F) F) ×
      Matrix.GeneralLinearGroup (Fin 2) (AdeleRing (𝓞 F) F))) (hQ : IsCompact Q) (N : ℕ) :
    ∃ C : ℝ, ∀ p ∈ Q, ∀ (a : (AdeleRing (𝓞 F) F)ˣ) (t : ℝ), 1 ≤ t → (a : AdeleRing (𝓞 F) F).2 = 1 →
      (∀ w : InfinitePlace F, ‖(a : AdeleRing (𝓞 F) F).1 w‖ = t) → ∀ e : AdeleRing (𝓞 F) F,
        ‖(∑' β : F, φ (p.1 * AutomorphicForm.unipotentGL2
              ((algebraMap F (AdeleRing (𝓞 F) F) β + e) * ↑a⁻¹) * p.2)) -
            ((adelicAddHaar (𝓞 F) F (adelicBox F)).toReal : ℂ)⁻¹ *
              ∫ u, φ (p.1 * AutomorphicForm.unipotentGL2 ((u + e) * ↑a⁻¹) * p.2) ∂(adelicAddHaar (𝓞 F) F)‖
          ≤ C * t⁻¹ ^ N :=
  R4PoissonTail.main F φ hφ Q hQ N

end
p2m_reactivate "P2MW.S_AutomorphicForm_exists_forall_norm_tsum_sub_inv_measure_mul_integral_comp_unipotentGL2_le_of_isCompact.R4PoissonTail"

end S_AutomorphicForm_exists_forall_norm_tsum_sub_inv_measure_mul_integral_comp_unipotentGL2_le_of_isCompact
end P2MW
export P2MW.S_AutomorphicForm_exists_forall_norm_tsum_sub_inv_measure_mul_integral_comp_unipotentGL2_le_of_isCompact (solution)

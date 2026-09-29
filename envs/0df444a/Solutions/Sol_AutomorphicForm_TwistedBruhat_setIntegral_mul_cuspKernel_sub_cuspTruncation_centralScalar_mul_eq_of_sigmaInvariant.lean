-- Prove2me | solution 1 for AutomorphicForm.TwistedBruhat.setIntegral_mul_cuspKernel_sub_cuspTruncation_centralScalar_mul_eq_of_sigmaInvariant
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/51f8ab8a-dc0a-59b9-9d18-8ea8e36a4089

import Mathlib
import Definitions.Def_AutomorphicForm_TwistedCuspKernel
import Definitions.Def_M4aHerbrand_IdeleClassVocab
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_TwistedBruhat_setIntegral_mul_cuspKernel_sub_cuspTruncation_centralScalar_mul_eq_of_sigmaInvariant

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

open MeasureTheory NumberField
open scoped Pointwise

noncomputable section

namespace R1CentreAbsorb

open NumberField IsDedekindDomain
open AutomorphicForm AutomorphicForm.WindowedSiegel NumberField.AdelicLevel NumberField.AdelicHeight

section Height

variable {K : Type*} [NormedField K]

theorem rowMaxNorm_scalar_entries_mul {s : GL (Fin 2) K} {z : K}
    (h10 : (s : Matrix (Fin 2) (Fin 2) K) 1 0 = 0) (h11 : (s : Matrix (Fin 2) (Fin 2) K) 1 1 = z)
    (g : GL (Fin 2) K) :
    rowMaxNorm ((s * g : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)
      = ‖z‖ * rowMaxNorm (g : Matrix (Fin 2) (Fin 2) K) := by
  have hbot : ∀ j : Fin 2,
      ((s : Matrix (Fin 2) (Fin 2) K) * (g : Matrix (Fin 2) (Fin 2) K)) 1 j
        = z * (g : Matrix (Fin 2) (Fin 2) K) 1 j := by
    intro j
    rw [Matrix.mul_apply, Fin.sum_univ_two, h10, h11]
    ring
  unfold rowMaxNorm
  rw [Matrix.GeneralLinearGroup.coe_mul, hbot 0, hbot 1, norm_mul, norm_mul,
    mul_max_of_nonneg _ _ (norm_nonneg z)]

theorem finLocalHeight_scalar_entries_mul {s : GL (Fin 2) K} {z : K} (hz : z ≠ 0)
    (h00 : (s : Matrix (Fin 2) (Fin 2) K) 0 0 = z) (h01 : (s : Matrix (Fin 2) (Fin 2) K) 0 1 = 0)
    (h10 : (s : Matrix (Fin 2) (Fin 2) K) 1 0 = 0) (h11 : (s : Matrix (Fin 2) (Fin 2) K) 1 1 = z)
    (g : GL (Fin 2) K) :
    finLocalHeight (s * g) = finLocalHeight g := by
  have hdets : (s : Matrix (Fin 2) (Fin 2) K).det = z ^ 2 := by
    rw [Matrix.det_fin_two, h00, h01, h10, h11]; ring
  have hdet : ‖((s * g : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K).det‖
      = ‖z‖ ^ 2 * ‖(g : Matrix (Fin 2) (Fin 2) K).det‖ := by
    rw [Matrix.GeneralLinearGroup.coe_mul, Matrix.det_mul, hdets, norm_mul, norm_pow]
  have hz2 : (0 : ℝ) < ‖z‖ ^ 2 := pow_pos (norm_pos_iff.2 hz) 2
  unfold finLocalHeight
  rw [hdet, rowMaxNorm_scalar_entries_mul h10 h11 g, mul_pow,
    mul_div_mul_left _ _ hz2.ne']

variable (F : Type) [Field F] [NumberField F]

theorem adelicHeight_centralScalar_mul (z : (AdeleRing (𝓞 F) F)ˣ) (g : AdelicGL2 (𝓞 F) F) :
    adelicHeight F (centralScalar (𝓞 F) F z * g) = adelicHeight F g := by
  have hcoe : ∀ i j : Fin 2, ((centralScalar (𝓞 F) F z : AdelicGL2 (𝓞 F) F) :
      Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) i j = if i = j then (z : AdeleRing (𝓞 F) F) else 0 := by
    intro i j
    show Matrix.scalar (Fin 2) (z : AdeleRing (𝓞 F) F) i j = _
    rw [Matrix.scalar_apply, Matrix.diagonal_apply]
  unfold adelicHeight
  rw [map_mul, map_mul]
  congr 1
  · refine archHeight_scalar_entries_mul F (z := (z : AdeleRing (𝓞 F) F).1) (fun v => ?_) ?_ ?_ ?_ ?_ _
    · exact (Units.map ((archEval F v).comp (adeleArch (𝓞 F) F)).toMonoidHom z).ne_zero
    all_goals rw [glArch_apply, hcoe]; rfl
  · unfold finHeight
    refine finprod_congr fun v => ?_
    rw [map_mul]
    refine finLocalHeight_scalar_entries_mul (z := ((z : AdeleRing (𝓞 F) F).2) v) ?_ ?_ ?_ ?_ ?_ _
    · exact (Units.map ((finAdeleEval (𝓞 F) F v).comp (adeleFin (𝓞 F) F)).toMonoidHom z).ne_zero
    all_goals rw [finComponent_apply, glFin_apply, hcoe]; rfl

end Height

end R1CentreAbsorb

open Polynomial

namespace R1CentreAbsorb

section Cells

open AutomorphicForm

variable {K : Type*} [Field K]

theorem X_sub_C_sq (a : K) : ((X - C a) ^ 2 : K[X]) = X ^ 2 - C (2 * a) * X + C (a ^ 2) := by
  rw [map_mul, map_pow, show (C (2 : K)) = 2 from map_ofNat C 2]; ring

theorem trace_det_of_charpoly_eq {M : Matrix (Fin 2) (Fin 2) K} {a : K} (h : M.charpoly = (X - C a) ^ 2) :
    M.trace = 2 * a ∧ M.det = a ^ 2 := by
  rw [Matrix.charpoly_fin_two, X_sub_C_sq] at h
  have h1 := congrArg (fun p : K[X] => p.coeff 1) h
  have h0 := congrArg (fun p : K[X] => p.coeff 0) h
  simp only [coeff_add, coeff_sub, coeff_X_pow, coeff_C_mul, coeff_X_one, coeff_C, if_true,
    mul_one] at h1 h0
  norm_num at h1 h0
  exact ⟨h1, h0⟩

theorem isCentralType_smul_iff {M : Matrix (Fin 2) (Fin 2) K} {t : K} (ht : t ≠ 0) :
    IsCentralType (t • M) ↔ IsCentralType M := by
  constructor
  · rintro ⟨c, hc⟩
    refine ⟨t⁻¹ * c, ?_⟩
    have := congrArg (fun N : Matrix (Fin 2) (Fin 2) K => t⁻¹ • N) hc
    simpa only [smul_smul, inv_mul_cancel₀ ht, one_smul] using this
  · rintro ⟨c, rfl⟩
    exact ⟨t * c, by rw [smul_smul]⟩

theorem isUnipotentType_smul {M : Matrix (Fin 2) (Fin 2) K} {t : K} (ht : t ≠ 0) (h : IsUnipotentType M) :
    IsUnipotentType (t • M) := by
  obtain ⟨hnc, a, ha⟩ := h
  obtain ⟨htr, hdet⟩ := trace_det_of_charpoly_eq ha
  refine ⟨(isCentralType_smul_iff ht).not.mpr hnc, t * a, ?_⟩
  rw [Matrix.charpoly_fin_two, Matrix.trace_smul, Matrix.det_smul, Fintype.card_fin, htr, hdet, X_sub_C_sq,
    smul_eq_mul]
  congr 2 <;> [(congr 2; ring); (congr 1; ring)]

theorem isUnipotentType_smul_iff {M : Matrix (Fin 2) (Fin 2) K} {t : K} (ht : t ≠ 0) :
    IsUnipotentType (t • M) ↔ IsUnipotentType M := by
  refine ⟨fun h => ?_, isUnipotentType_smul ht⟩
  have := isUnipotentType_smul (inv_ne_zero ht) h
  rwa [smul_smul, inv_mul_cancel₀ ht, one_smul] at this

theorem coe_mul_scalar (γ : GL (Fin 2) K) (t : Kˣ) :
    ((γ * Matrix.GeneralLinearGroup.scalar (Fin 2) t : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) =
      (t : K) • (γ : Matrix (Fin 2) (Fin 2) K) := by
  rw [Matrix.GeneralLinearGroup.coe_mul]
  show (γ : Matrix (Fin 2) (Fin 2) K) * Matrix.scalar (Fin 2) (t : K) = _
  rw [← (Matrix.scalar_commute (t : K) (fun r' => mul_comm _ r') _).eq, Matrix.scalar_apply,
    ← Matrix.smul_eq_diagonal_mul]

theorem mul_scalar_mem_unipotentCell_iff (γ : GL (Fin 2) K) (t : Kˣ) :
    γ * Matrix.GeneralLinearGroup.scalar (Fin 2) t ∈ unipotentCell K ↔ γ ∈ unipotentCell K := by
  rw [mem_unipotentCell_iff, mem_unipotentCell_iff, coe_mul_scalar]
  exact isUnipotentType_smul_iff t.ne_zero

end Cells

section NormClasses

open LT.TwistedNorm AutomorphicForm

theorem sigmaPartialNorm_mul_of_mem_center {G : Type*} [Group G] (σ : G →* G) (x : G) {y : G}
    (hy : y ∈ Subgroup.center G) (r : ℕ) :
    sigmaPartialNorm σ (x * y) r = sigmaPartialNorm σ x r * sigmaPartialNorm σ y r := by
  induction r with
  | zero => simp
  | succ r ih =>
      rw [sigmaPartialNorm_succ', sigmaPartialNorm_succ', sigmaPartialNorm_succ', ih, map_mul]
      have hc := Subgroup.mem_center_iff.mp hy (σ (sigmaPartialNorm σ x r))
      calc x * y * (σ (sigmaPartialNorm σ x r) * σ (sigmaPartialNorm σ y r))
          = x * (y * σ (sigmaPartialNorm σ x r)) * σ (sigmaPartialNorm σ y r) := by group
        _ = x * (σ (sigmaPartialNorm σ x r) * y) * σ (sigmaPartialNorm σ y r) := by rw [hc]
        _ = x * σ (sigmaPartialNorm σ x r) * (y * σ (sigmaPartialNorm σ y r)) := by group

variable {K L : Type*} [Field K] [Field L] [Algebra K L]

theorem scalar_mem_center (s : Lˣ) : Matrix.GeneralLinearGroup.scalar (Fin 2) s ∈ Subgroup.center (GL (Fin 2) L) := by
  rw [Subgroup.mem_center_iff]
  intro g
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  rw [Matrix.GeneralLinearGroup.coe_mul, Matrix.GeneralLinearGroup.coe_mul]
  exact congrFun (congrFun (Matrix.scalar_commute (n := Fin 2) (s : L) (fun r' => mul_comm _ r')
    (g : Matrix (Fin 2) (Fin 2) L)).eq i) j |>.symm

theorem map_scalar {R S : Type*} [CommRing R] [CommRing S] (σ : R →+* S) (s : Rˣ) :
    Matrix.GeneralLinearGroup.map σ (Matrix.GeneralLinearGroup.scalar (Fin 2) s) =
      Matrix.GeneralLinearGroup.scalar (Fin 2) (Units.map (σ : R →* S) s) := by
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  show σ (Matrix.scalar (Fin 2) (s : R) i j) = Matrix.scalar (Fin 2) (σ (s : R)) i j
  rw [Matrix.scalar_apply, Matrix.scalar_apply, Matrix.diagonal_apply, Matrix.diagonal_apply]
  split_ifs <;> simp

theorem map_algebraMap_scalar (t : Kˣ) :
    Matrix.GeneralLinearGroup.map (algebraMap K L) (Matrix.GeneralLinearGroup.scalar (Fin 2) t) =
      Matrix.GeneralLinearGroup.scalar (Fin 2) (Units.map (algebraMap K L : K →* L) t) :=
  map_scalar (algebraMap K L) t

variable [FiniteDimensional K L] [IsGalois K L]

theorem sigmaNormPow_mul_scalar {σ : L ≃ₐ[K] L} (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (δ : GL (Fin 2) L) (s : Lˣ) :
    sigmaNormPow (Matrix.GeneralLinearGroup.map (σ : L →+* L)) (Module.finrank K L)
        (δ * Matrix.GeneralLinearGroup.scalar (Fin 2) s) =
      sigmaNormPow (Matrix.GeneralLinearGroup.map (σ : L →+* L)) (Module.finrank K L) δ *
        Matrix.GeneralLinearGroup.map (algebraMap K L)
          (Matrix.GeneralLinearGroup.scalar (Fin 2) (Units.map (Algebra.norm K : L →* K) s)) := by
  rw [sigmaNormPow_def, sigmaPartialNorm_mul_of_mem_center _ _ (scalar_mem_center s), ← sigmaNormPow_def,
    ← sigmaNormPow_def]
  congr 1
  have h := hom_sigmaNormPow (Units.map ((σ : L →+* L) : L →* L)) (Matrix.GeneralLinearGroup.map (σ : L →+* L))
    (Matrix.GeneralLinearGroup.scalar (Fin 2)) (fun x => (map_scalar (σ : L →+* L) x).symm) (Module.finrank K L) s
  rw [← h, map_algebraMap_scalar]
  congr 1
  ext
  rw [coe_sigmaNormPow_units_eq_algebraMap_norm hgen]
  rfl

omit [FiniteDimensional K L] [IsGalois K L] in
theorem isNormRep_of_isConj {σ : L ≃ₐ[K] L} {γ γ' : GL (Fin 2) K} {δ : GL (Fin 2) L}
    (h : IsNormRep σ γ δ) (hc : IsConj γ γ') : IsNormRep σ γ' δ := by
  obtain ⟨P, hP⟩ := h
  obtain ⟨c, rfl⟩ := isConj_iff.mp hc
  refine ⟨P * Matrix.GeneralLinearGroup.map (algebraMap K L) c⁻¹, ?_⟩
  rw [map_mul, map_mul, ← hP, map_inv]
  group

omit [FiniteDimensional K L] [IsGalois K L] in
theorem isNormRep_mul_scalar {σ : L ≃ₐ[K] L} (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    [FiniteDimensional K L] [IsGalois K L]
    {γ : GL (Fin 2) K} {δ : GL (Fin 2) L} (h : IsNormRep σ γ δ) (s : Lˣ) :
    IsNormRep σ (γ * Matrix.GeneralLinearGroup.scalar (Fin 2) (Units.map (Algebra.norm K : L →* K) s))
      (δ * Matrix.GeneralLinearGroup.scalar (Fin 2) s) := by
  obtain ⟨P, hP⟩ := h
  refine ⟨P, ?_⟩
  rw [sigmaNormPow_mul_scalar hgen, map_mul, ← hP]
  have hc := Subgroup.mem_center_iff.mp
    (scalar_mem_center (Units.map (algebraMap K L : K →* L) (Units.map (Algebra.norm K : L →* K) s))) P
  rw [← map_algebraMap_scalar] at hc
  simp only [mul_assoc, hc]

end NormClasses

section CuspIndex

open LT.TwistedNorm AutomorphicForm AutomorphicForm.TwistedBruhat

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]

theorem mul_scalar_mem_normUnipotentSet {σ : L ≃ₐ[K] L} (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    {δ : GL (Fin 2) L} (hδ : δ ∈ normUnipotentSet K L σ hgen) (s : Lˣ) :
    δ * Matrix.GeneralLinearGroup.scalar (Fin 2) s ∈ normUnipotentSet K L σ hgen := by
  obtain ⟨γ, hγ, hcls⟩ := hδ
  rw [normClassMap_mk, ConjClasses.mk_eq_mk_iff_isConj] at hcls
  have hrep : IsNormRep σ γ δ := isNormRep_of_isConj (isNormRep_normRep hgen δ) hcls
  refine ⟨_, ?_, normClassMap_mk_eq_of_isNormRep hgen (isNormRep_mul_scalar hgen hrep s)⟩
  exact (mul_scalar_mem_unipotentCell_iff γ _).mpr hγ

theorem scalar_apply_one_zero (s : Lˣ) :
    ((Matrix.GeneralLinearGroup.scalar (Fin 2) s : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 := by
  show Matrix.scalar (Fin 2) (s : L) 1 0 = 0
  simp [Matrix.scalar_apply]

theorem scalar_mem_borelSubgroup (s : Lˣ) :
    Matrix.GeneralLinearGroup.scalar (Fin 2) s ∈ borelSubgroup L :=
  scalar_apply_one_zero s

theorem mul_scalar_mem_cuspIndex {σ : L ≃ₐ[K] L} (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    {δ : GL (Fin 2) L}
    (hδ : δ ∈ normUnipotentSet K L σ hgen ∩ (borelSubgroup L : Set (GL (Fin 2) L))) (s : Lˣ) :
    δ * Matrix.GeneralLinearGroup.scalar (Fin 2) s ∈
      normUnipotentSet K L σ hgen ∩ (borelSubgroup L : Set (GL (Fin 2) L)) :=
  ⟨mul_scalar_mem_normUnipotentSet hgen hδ.1 s, (borelSubgroup L).mul_mem hδ.2 (scalar_mem_borelSubgroup s)⟩

theorem bijOn_mul_scalar_cuspIndex {σ : L ≃ₐ[K] L} (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ) (s : Lˣ) :
    Set.BijOn (fun δ : GL (Fin 2) L => δ * Matrix.GeneralLinearGroup.scalar (Fin 2) s)
      (normUnipotentSet K L σ hgen ∩ (borelSubgroup L : Set (GL (Fin 2) L)))
      (normUnipotentSet K L σ hgen ∩ (borelSubgroup L : Set (GL (Fin 2) L))) := by
  refine ⟨fun δ hδ => mul_scalar_mem_cuspIndex hgen hδ s, fun δ _ δ' _ h => mul_right_cancel h, fun δ hδ => ?_⟩
  refine ⟨δ * Matrix.GeneralLinearGroup.scalar (Fin 2) s⁻¹, mul_scalar_mem_cuspIndex hgen hδ s⁻¹, ?_⟩
  simp only [map_inv, inv_mul_cancel_right]

end CuspIndex

section BorelOne

open AutomorphicForm AutomorphicForm.TwistedBruhat

variable {K L : Type} [Field K] [Field L] [Algebra K L]

def dr (g : GL (Fin 2) L) : L := (g : Matrix (Fin 2) (Fin 2) L) 0 0 / (g : Matrix (Fin 2) (Fin 2) L) 1 1

theorem mul_apply_one_zero_of_upper {g h : GL (Fin 2) L}
    (hg : (g : Matrix (Fin 2) (Fin 2) L) 1 0 = 0) (hh : (h : Matrix (Fin 2) (Fin 2) L) 1 0 = 0) :
    ((g * h : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 := by
  rw [Matrix.GeneralLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two, hg, hh]; ring

theorem mul_apply_zero_zero_of_upper (g : GL (Fin 2) L) {h : GL (Fin 2) L}
    (hh : (h : Matrix (Fin 2) (Fin 2) L) 1 0 = 0) :
    ((g * h : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) 0 0 =
      (g : Matrix (Fin 2) (Fin 2) L) 0 0 * (h : Matrix (Fin 2) (Fin 2) L) 0 0 := by
  rw [Matrix.GeneralLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two, hh]; ring

theorem mul_apply_one_one_of_upper {g : GL (Fin 2) L} (hg : (g : Matrix (Fin 2) (Fin 2) L) 1 0 = 0)
    (h : GL (Fin 2) L) :
    ((g * h : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) 1 1 =
      (g : Matrix (Fin 2) (Fin 2) L) 1 1 * (h : Matrix (Fin 2) (Fin 2) L) 1 1 := by
  rw [Matrix.GeneralLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two, hg]; ring

theorem dr_mul {g h : GL (Fin 2) L}
    (hg : (g : Matrix (Fin 2) (Fin 2) L) 1 0 = 0) (hh : (h : Matrix (Fin 2) (Fin 2) L) 1 0 = 0) :
    dr (g * h) = dr g * dr h := by
  unfold dr
  rw [mul_apply_zero_zero_of_upper g hh, mul_apply_one_one_of_upper hg h, mul_div_mul_comm]

theorem apply_one_one_ne_zero_of_upper {g : GL (Fin 2) L} (hg : (g : Matrix (Fin 2) (Fin 2) L) 1 0 = 0) :
    (g : Matrix (Fin 2) (Fin 2) L) 1 1 ≠ 0 := by
  intro h
  have hdet := (Matrix.isUnits_det_units g).ne_zero
  rw [Matrix.det_fin_two, hg, h] at hdet
  simp at hdet

theorem apply_zero_zero_ne_zero_of_upper {g : GL (Fin 2) L} (hg : (g : Matrix (Fin 2) (Fin 2) L) 1 0 = 0) :
    (g : Matrix (Fin 2) (Fin 2) L) 0 0 ≠ 0 := by
  intro h
  have hdet := (Matrix.isUnits_det_units g).ne_zero
  rw [Matrix.det_fin_two, hg, h] at hdet
  simp at hdet

theorem dr_ne_zero_of_upper {g : GL (Fin 2) L} (hg : (g : Matrix (Fin 2) (Fin 2) L) 1 0 = 0) : dr g ≠ 0 :=
  div_ne_zero (apply_zero_zero_ne_zero_of_upper hg) (apply_one_one_ne_zero_of_upper hg)

theorem dr_one : dr (1 : GL (Fin 2) L) = 1 := by
  unfold dr; simp

theorem inv_apply_one_zero_of_upper {g : GL (Fin 2) L} (hg : (g : Matrix (Fin 2) (Fin 2) L) 1 0 = 0) :
    ((g⁻¹ : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 :=
  (borelSubgroup L).inv_mem hg

theorem dr_inv {g : GL (Fin 2) L} (hg : (g : Matrix (Fin 2) (Fin 2) L) 1 0 = 0) : dr g⁻¹ = (dr g)⁻¹ := by
  have h := dr_mul (inv_apply_one_zero_of_upper hg) hg
  rw [inv_mul_cancel, dr_one] at h
  exact eq_inv_of_mul_eq_one_left h.symm

theorem norm_inv' {x : L} (hx : x ≠ 0) : Algebra.norm K x⁻¹ = (Algebra.norm K x)⁻¹ :=
  eq_inv_of_mul_eq_one_left (by rw [← map_mul, inv_mul_cancel₀ hx, map_one])

theorem mem_borelNormOneSet_iff {γ : GL (Fin 2) L} :
    γ ∈ borelNormOneSet K L ↔ (γ : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧ Algebra.norm K (dr γ) = 1 :=
  Iff.rfl

theorem mul_mem_borelNormOneSet {g h : GL (Fin 2) L} (hg : g ∈ borelNormOneSet K L) (hh : h ∈ borelNormOneSet K L) :
    g * h ∈ borelNormOneSet K L := by
  rw [mem_borelNormOneSet_iff] at hg hh ⊢
  refine ⟨mul_apply_one_zero_of_upper hg.1 hh.1, ?_⟩
  rw [dr_mul hg.1 hh.1, map_mul, hg.2, hh.2, mul_one]

theorem inv_mem_borelNormOneSet {g : GL (Fin 2) L} (hg : g ∈ borelNormOneSet K L) : g⁻¹ ∈ borelNormOneSet K L := by
  rw [mem_borelNormOneSet_iff] at hg ⊢
  refine ⟨inv_apply_one_zero_of_upper hg.1, ?_⟩
  rw [dr_inv hg.1, norm_inv' (dr_ne_zero_of_upper hg.1), hg.2, inv_one]

theorem scalar_mem_borelNormOneSet (s : Lˣ) : Matrix.GeneralLinearGroup.scalar (Fin 2) s ∈ borelNormOneSet K L := by
  refine ⟨?_, ?_⟩
  · show Matrix.scalar (Fin 2) (s : L) 1 0 = 0
    simp [Matrix.scalar_apply]
  · show Algebra.norm K (Matrix.scalar (Fin 2) (s : L) 0 0 / Matrix.scalar (Fin 2) (s : L) 1 1) = 1
    simp [Matrix.scalar_apply]

theorem bijOn_mul_borelNormOneSet {b : GL (Fin 2) L} (hb : b ∈ borelNormOneSet K L) :
    Set.BijOn (fun δ : GL (Fin 2) L => δ * b) (borelNormOneSet K L) (borelNormOneSet K L) := by
  refine ⟨fun δ hδ => mul_mem_borelNormOneSet hδ hb, fun δ _ δ' _ h => mul_right_cancel h, fun δ hδ => ?_⟩
  exact ⟨δ * b⁻¹, mul_mem_borelNormOneSet hδ (inv_mem_borelNormOneSet hb), by simp⟩

end BorelOne

end R1CentreAbsorb

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicBox
open IsDedekindDomain AutomorphicForm
open scoped Pointwise

namespace R1CentreAbsorb

section AdelicAlgebra

variable (K L : Type) [Field K] [Field L] [NumberField L] [Algebra K L]
variable (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L)

theorem sigmaAdelicAct_centralScalar (z : (AdeleRing (𝓞 L) L)ˣ) :
    sigmaAdelicAct K L D σ (centralScalar (𝓞 L) L z) = centralScalar (𝓞 L) L (D.unitsAct σ z) := by
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  change ((D.act σ : RingAut (AdeleRing (𝓞 L) L)).toRingHom) (Matrix.scalar (Fin 2) (z : AdeleRing (𝓞 L) L) i j) =
    Matrix.scalar (Fin 2) ((D.act σ : RingAut (AdeleRing (𝓞 L) L)) (z : AdeleRing (𝓞 L) L)) i j
  rw [Matrix.scalar_apply, Matrix.scalar_apply, Matrix.diagonal_apply, Matrix.diagonal_apply]
  split_ifs <;> simp

theorem centralScalar_comm (w : (AdeleRing (𝓞 L) L)ˣ) (y : AdelicGL2 (𝓞 L) L) :
    centralScalar (𝓞 L) L w * y = y * centralScalar (𝓞 L) L w := by
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  rw [Matrix.GeneralLinearGroup.coe_mul, Matrix.GeneralLinearGroup.coe_mul]
  exact congrFun (congrFun (Matrix.scalar_commute (w : AdeleRing (𝓞 L) L) (fun r' => mul_comm _ r')
    (y : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L))).eq i) j

theorem mul_cs_left (g y : AdelicGL2 (𝓞 L) L) (w : (AdeleRing (𝓞 L) L)ˣ) :
    g * (centralScalar (𝓞 L) L w * y) = centralScalar (𝓞 L) L w * (g * y) := by
  rw [← mul_assoc, ← centralScalar_comm, mul_assoc]

theorem centralScalar_principal (q : Lˣ) :
    centralScalar (𝓞 L) L (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L) q) =
      globalPoints (𝓞 L) L (Matrix.GeneralLinearGroup.scalar (Fin 2) q) := by
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  show Matrix.scalar (Fin 2) (algebraMap L (AdeleRing (𝓞 L) L) (q : L)) i j =
    algebraMap L (AdeleRing (𝓞 L) L) (Matrix.scalar (Fin 2) (q : L) i j)
  rw [Matrix.scalar_apply, Matrix.scalar_apply, Matrix.diagonal_apply, Matrix.diagonal_apply]
  split_ifs <;> simp

theorem unitsAct_principal (q : Lˣ) :
    D.unitsAct σ (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L) q) =
      Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L) (Units.map (σ : L →* L) q) :=
  Units.ext (D.compat σ (q : L))

theorem sigmaAdelicAct_centralScalar_principal (q : Lˣ) :
    sigmaAdelicAct K L D σ (centralScalar (𝓞 L) L (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L) q)) =
      globalPoints (𝓞 L) L (Matrix.GeneralLinearGroup.scalar (Fin 2) (Units.map (σ : L →* L) q)) := by
  rw [sigmaAdelicAct_centralScalar, unitsAct_principal, centralScalar_principal]

theorem sigmaAdelicAct_globalPoints' (g : GL (Fin 2) L) :
    sigmaAdelicAct K L D σ (globalPoints (𝓞 L) L g) =
      globalPoints (𝓞 L) L (Matrix.GeneralLinearGroup.map (σ : L →+* L) g) :=
  sigmaAdelicAct_globalPoints K L D σ g

theorem inv_cs_mul_conj (a : (AdeleRing (𝓞 L) L)ˣ) (x G Y : AdelicGL2 (𝓞 L) L) :
    (centralScalar (𝓞 L) L a * x)⁻¹ * G * sigmaAdelicAct K L D σ (Y * (centralScalar (𝓞 L) L a * x)) =
      x⁻¹ * G * sigmaAdelicAct K L D σ
        (Y * (centralScalar (𝓞 L) L (a * (D.unitsAct σ⁻¹ a)⁻¹) * x)) := by
  have ht : sigmaAdelicAct K L D σ (centralScalar (𝓞 L) L (a * (D.unitsAct σ⁻¹ a)⁻¹)) =
      sigmaAdelicAct K L D σ (centralScalar (𝓞 L) L a) * (centralScalar (𝓞 L) L a)⁻¹ := by
    rw [sigmaAdelicAct_centralScalar, sigmaAdelicAct_centralScalar, map_mul, map_inv, map_mul, map_inv, map_inv]
    congr 3
    rw [← MulAut.mul_apply, mul_inv_cancel, MulAut.one_apply]
  rw [map_mul, map_mul, map_mul, map_mul, ht, mul_inv_rev, ← map_inv]
  simp only [mul_assoc, mul_cs_left]

end AdelicAlgebra

section KernelIdentities

open AutomorphicForm.TwistedBruhat NumberField.AdelicHeight

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
variable (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L)
variable (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)

theorem cuspKernel_centralScalar_mul (φ : AdelicGL2 (𝓞 L) L → ℂ) (z a : (AdeleRing (𝓞 L) L)ˣ)
    (g : AdelicGL2 (𝓞 L) L) :
    cuspKernel K L D σ hgen φ z (centralScalar (𝓞 L) L a * g) =
      cuspKernel K L D σ hgen φ (z * (a * (D.unitsAct σ⁻¹ a)⁻¹)) g := by
  unfold cuspKernel
  refine finsum_mem_congr rfl fun δ _ => ?_
  rw [inv_cs_mul_conj]
  simp only [map_mul, map_inv, mul_assoc]

theorem cuspKernel_principal_mul (φ : AdelicGL2 (𝓞 L) L → ℂ) (q : Lˣ) (z : (AdeleRing (𝓞 L) L)ˣ)
    (g : AdelicGL2 (𝓞 L) L) :
    cuspKernel K L D σ hgen φ (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L) q * z) g =
      cuspKernel K L D σ hgen φ z g := by
  unfold cuspKernel
  refine finsum_mem_eq_of_bijOn _ (bijOn_mul_scalar_cuspIndex hgen (Units.map (σ : L →* L) q)) fun δ _ => ?_
  rw [map_mul (centralScalar (𝓞 L) L), mul_assoc (centralScalar (𝓞 L) L _), map_mul (sigmaAdelicAct K L D σ),
    sigmaAdelicAct_centralScalar_principal, map_mul (globalPoints (𝓞 L) L)]
  simp only [mul_assoc]

theorem finsum_borelNormOne_globalPoints_mul (φ : AdelicGL2 (𝓞 L) L → ℂ) (x y : AdelicGL2 (𝓞 L) L)
    {b : GL (Fin 2) L} (hb : b ∈ borelNormOneSet K L) :
    (∑ᶠ δ ∈ borelNormOneSet K L, φ (x⁻¹ * globalPoints (𝓞 L) L δ * sigmaAdelicAct K L D σ
        (globalPoints (𝓞 L) L b * y))) =
      ∑ᶠ δ ∈ borelNormOneSet K L, φ (x⁻¹ * globalPoints (𝓞 L) L δ * sigmaAdelicAct K L D σ y) := by
  have hσb : Matrix.GeneralLinearGroup.map (σ : L →+* L) b ∈ borelNormOneSet K L := by
    rw [mem_borelNormOneSet_iff] at hb ⊢
    refine ⟨by rw [show ((Matrix.GeneralLinearGroup.map (σ : L →+* L) b : GL (Fin 2) L) :
        Matrix (Fin 2) (Fin 2) L) 1 0 = σ ((b : Matrix (Fin 2) (Fin 2) L) 1 0) from rfl, hb.1, map_zero], ?_⟩
    have hdr : dr (Matrix.GeneralLinearGroup.map (σ : L →+* L) b) = σ (dr b) := by
      unfold dr; rw [map_div₀]; rfl
    rw [hdr, Algebra.norm_eq_of_algEquiv, hb.2]
  refine finsum_mem_eq_of_bijOn _ (bijOn_mul_borelNormOneSet hσb) fun δ _ => ?_
  rw [map_mul (sigmaAdelicAct K L D σ), sigmaAdelicAct_globalPoints', map_mul (globalPoints (𝓞 L) L)]
  simp only [mul_assoc]

theorem cuspTruncation_centralScalar_mul (R : ℝ) (φ : AdelicGL2 (𝓞 L) L → ℂ) (z a : (AdeleRing (𝓞 L) L)ˣ)
    (g : AdelicGL2 (𝓞 L) L) :
    cuspTruncation K L D σ R φ z (centralScalar (𝓞 L) L a * g) =
      cuspTruncation K L D σ R φ (z * (a * (D.unitsAct σ⁻¹ a)⁻¹)) g := by
  unfold cuspTruncation
  have hmem : centralScalar (𝓞 L) L z * (centralScalar (𝓞 L) L a * g) ∈ highSet (adelicHeight L) (Real.exp R) ↔
      centralScalar (𝓞 L) L (z * (a * (D.unitsAct σ⁻¹ a)⁻¹)) * g ∈ highSet (adelicHeight L) (Real.exp R) := by
    rw [mem_highSet_iff, mem_highSet_iff, adelicHeight_centralScalar_mul, adelicHeight_centralScalar_mul,
      adelicHeight_centralScalar_mul]
  by_cases hx : centralScalar (𝓞 L) L z * (centralScalar (𝓞 L) L a * g) ∈ highSet (adelicHeight L) (Real.exp R)
  · rw [Set.indicator_of_mem hx, Set.indicator_of_mem (hmem.mp hx)]
    unfold constantTerm constantTermIntegrand
    refine integral_congr_ae (Filter.Eventually.of_forall fun n => ?_)
    show (∑ᶠ δ ∈ borelNormOneSet K L, φ ((centralScalar (𝓞 L) L a * g)⁻¹ * globalPoints (𝓞 L) L δ *
        sigmaAdelicAct K L D σ (unipotentGL2 n * (centralScalar (𝓞 L) L z * (centralScalar (𝓞 L) L a * g))))) =
      ∑ᶠ δ ∈ borelNormOneSet K L, φ (g⁻¹ * globalPoints (𝓞 L) L δ *
        sigmaAdelicAct K L D σ (unipotentGL2 n * (centralScalar (𝓞 L) L (z * (a * (D.unitsAct σ⁻¹ a)⁻¹)) * g)))
    refine finsum_mem_congr rfl fun δ _ => ?_
    rw [← mul_assoc (unipotentGL2 n), inv_cs_mul_conj]
    simp only [map_mul, map_inv, mul_assoc]
  · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem (fun h' => hx (hmem.mpr h'))]

theorem cuspTruncation_principal_mul (R : ℝ) (φ : AdelicGL2 (𝓞 L) L → ℂ) (q : Lˣ) (z : (AdeleRing (𝓞 L) L)ˣ)
    (g : AdelicGL2 (𝓞 L) L) :
    cuspTruncation K L D σ R φ (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L) q * z) g =
      cuspTruncation K L D σ R φ z g := by
  unfold cuspTruncation
  have hmem : centralScalar (𝓞 L) L (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L) q * z) * g ∈
        highSet (adelicHeight L) (Real.exp R) ↔
      centralScalar (𝓞 L) L z * g ∈ highSet (adelicHeight L) (Real.exp R) := by
    rw [mem_highSet_iff, mem_highSet_iff, map_mul, mul_assoc, adelicHeight_centralScalar_mul,
      adelicHeight_centralScalar_mul]
  by_cases hx : centralScalar (𝓞 L) L z * g ∈ highSet (adelicHeight L) (Real.exp R)
  · rw [Set.indicator_of_mem hx, Set.indicator_of_mem (hmem.mpr hx)]
    unfold constantTerm constantTermIntegrand
    refine integral_congr_ae (Filter.Eventually.of_forall fun n => ?_)
    show (∑ᶠ δ ∈ borelNormOneSet K L, φ (g⁻¹ * globalPoints (𝓞 L) L δ * sigmaAdelicAct K L D σ
        (unipotentGL2 n * (centralScalar (𝓞 L) L (Units.map _ q * z) * g)))) =
      ∑ᶠ δ ∈ borelNormOneSet K L, φ (g⁻¹ * globalPoints (𝓞 L) L δ * sigmaAdelicAct K L D σ
        (unipotentGL2 n * (centralScalar (𝓞 L) L z * g)))
    rw [map_mul (centralScalar (𝓞 L) L), mul_assoc (centralScalar (𝓞 L) L _), mul_cs_left, centralScalar_principal]
    exact finsum_borelNormOne_globalPoints_mul K L D σ φ g _ (scalar_mem_borelNormOneSet q)
  · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem (fun h' => hx (hmem.mp h'))]

end KernelIdentities

section Fold

open AutomorphicForm.TwistedBruhat

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
variable (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L)
variable (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)

theorem countable_units : Countable Lˣ := by
  haveI : Countable L := (Module.Free.chooseBasis ℚ L).equivFun.toEquiv.countable_iff.2 inferInstance
  exact Function.Injective.countable (f := (Units.val : Lˣ → L)) Units.val_injective

theorem fold_centralScalar_mul {mZ : MeasurableSpace (AdeleRing (𝓞 L) L)ˣ} [BorelSpace (AdeleRing (𝓞 L) L)ˣ]
    (νZL : Measure (AdeleRing (𝓞 L) L)ˣ) [νZL.IsMulLeftInvariant] (ΩL : Set (AdeleRing (𝓞 L) L)ˣ)
    (hΩL : IsFundamentalDomain
      (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L)).range ΩL νZL)
    (ξ' : (AdeleRing (𝓞 L) L)ˣ →* ℂˣ)
    (hξt : ∀ q : Lˣ, ξ' (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L) q) = 1)
    (R : ℝ) (φ : AdelicGL2 (𝓞 L) L → ℂ) (a : (AdeleRing (𝓞 L) L)ˣ) (g : AdelicGL2 (𝓞 L) L) :
    (∫ z in ΩL, ((ξ' z : ℂˣ) : ℂ) *
        (cuspKernel K L D σ hgen φ z (centralScalar (𝓞 L) L a * g) -
          cuspTruncation K L D σ R φ z (centralScalar (𝓞 L) L a * g)) ∂νZL) =
      ((ξ' (a * (D.unitsAct σ⁻¹ a)⁻¹) : ℂˣ) : ℂ)⁻¹ *
        ∫ z in ΩL, ((ξ' z : ℂˣ) : ℂ) *
          (cuspKernel K L D σ hgen φ z g - cuspTruncation K L D σ R φ z g) ∂νZL := by
  simp_rw [cuspKernel_centralScalar_mul, cuspTruncation_centralScalar_mul]
  generalize a * (D.unitsAct σ⁻¹ a)⁻¹ = t
  set F : (AdeleRing (𝓞 L) L)ˣ → ℂ := fun w =>
    cuspKernel K L D σ hgen φ w g - cuspTruncation K L D σ R φ w g with hF
  have hpt : ∀ z, ((ξ' z : ℂˣ) : ℂ) * F (z * t) =
      ((ξ' t : ℂˣ) : ℂ)⁻¹ * (((ξ' (t * z) : ℂˣ) : ℂ) * F (t * z)) := by
    intro z
    rw [mul_comm z t, map_mul, Units.val_mul]
    simp only [← mul_assoc, inv_mul_cancel₀ (Units.ne_zero _), one_mul]
  show (∫ z in ΩL, ((ξ' z : ℂˣ) : ℂ) * F (z * t) ∂νZL) = ((ξ' t : ℂˣ) : ℂ)⁻¹ * ∫ z in ΩL, ((ξ' z : ℂˣ) : ℂ) * F z ∂νZL
  simp_rw [hpt]
  rw [integral_const_mul]
  congr 1

  have h1 : ∫ z in ΩL, ((ξ' (t * z) : ℂˣ) : ℂ) * F (t * z) ∂νZL =
      ∫ w in t • ΩL, ((ξ' w : ℂˣ) : ℂ) * F w ∂νZL := by
    rw [← Set.image_smul]
    exact ((measurePreserving_mul_left νZL t).setIntegral_image_emb (MeasurableEquiv.mulLeft t).measurableEmbedding
      (fun w => ((ξ' w : ℂˣ) : ℂ) * F w) ΩL).symm
  rw [h1]
  haveI : Countable (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L)).range := by
    haveI := countable_units (L := L)
    exact (MonoidHom.rangeRestrict_surjective _).countable
  refine (hΩL.smul_of_comm t).setIntegral_eq hΩL fun r w => ?_
  obtain ⟨_, q, rfl⟩ := r
  show ((ξ' (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L) q * w) : ℂˣ) : ℂ) *
      F (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L) q * w) =
    ((ξ' w : ℂˣ) : ℂ) * F w
  rw [map_mul, hξt, one_mul, hF]
  simp only []
  rw [cuspKernel_principal_mul, cuspTruncation_principal_mul]

def toTop (G : Type*) [Group G] : G →* (⊤ : Subgroup G) where
  toFun z := ⟨z, Subgroup.mem_top z⟩
  map_one' := rfl
  map_mul' _ _ := rfl

end Fold

end R1CentreAbsorb

open R1CentreAbsorb
open scoped TensorProduct

theorem solution
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    [MeasurableSpace (AdeleRing (𝓞 L) L)ˣ] [BorelSpace (AdeleRing (𝓞 L) L)ˣ] (νZL : Measure (AdeleRing (𝓞 L) L)ˣ)
    [νZL.IsHaarMeasure] (ΩL : Set (AdeleRing (𝓞 L) L)ˣ)
    (hΩL : IsFundamentalDomain
      (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L)).range ΩL νZL)
    (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L) (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (ξL : (⊤ : Subgroup (AdeleRing (𝓞 L) L)ˣ) →* ℂˣ)
    (hξt : ∀ z : (AdeleRing (𝓞 L) L)ˣ,
      z ∈ (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L)).range →
        ξL ⟨z, Subgroup.mem_top z⟩ = 1)
    (hξσ : ∀ z₀ : (AdeleRing (𝓞 L) L)ˣ,
      ξL ⟨M4aHerbrand.IdeleGaloisDescent.unitsAct D σ z₀, Subgroup.mem_top _⟩ = ξL ⟨z₀, Subgroup.mem_top z₀⟩)
    (φ : AdelicGL2 (𝓞 L) L → ℂ) (R : ℝ) (u : (AdeleRing (𝓞 L) L)ˣ) (g : AdelicGL2 (𝓞 L) L) :
    ∫ z in ΩL, ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
        (TwistedBruhat.cuspKernel K L D σ hgen φ z (centralScalar (𝓞 L) L u * g) -
          TwistedBruhat.cuspTruncation K L D σ R φ z (centralScalar (𝓞 L) L u * g)) ∂νZL =
      ∫ z in ΩL, ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
        (TwistedBruhat.cuspKernel K L D σ hgen φ z g - TwistedBruhat.cuspTruncation K L D σ R φ z g) ∂νZL := by
  set ξ' : (AdeleRing (𝓞 L) L)ˣ →* ℂˣ := ξL.comp (toTop (AdeleRing (𝓞 L) L)ˣ) with hξ'
  have hξ'_apply : ∀ z : (AdeleRing (𝓞 L) L)ˣ, ξ' z = ξL ⟨z, Subgroup.mem_top z⟩ := fun z => rfl
  have hξt' : ∀ q : Lˣ, ξ' (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L) q) = 1 :=
    fun q => (hξ'_apply _).trans (hξt _ ⟨q, rfl⟩)
  have key := fold_centralScalar_mul K L D σ hgen νZL ΩL hΩL ξ' hξt' R φ u g

  have hu : D.unitsAct σ (D.unitsAct σ⁻¹ u) = u := by
    rw [← MulAut.mul_apply, ← map_mul, mul_inv_cancel, map_one, MulAut.one_apply]
  have hσu : ξ' (D.unitsAct σ⁻¹ u) = ξ' u := by
    rw [hξ'_apply, hξ'_apply]
    have h := hξσ (D.unitsAct σ⁻¹ u)
    rw [hu] at h
    exact h.symm
  have hone : ξ' (u * (D.unitsAct σ⁻¹ u)⁻¹) = 1 := by
    rw [map_mul, map_inv, hσu, mul_inv_cancel]
  rw [hone, Units.val_one, inv_one, one_mul] at key
  simpa only [hξ'_apply] using key

end
end S_AutomorphicForm_TwistedBruhat_setIntegral_mul_cuspKernel_sub_cuspTruncation_centralScalar_mul_eq_of_sigmaInvariant
end P2MW
export P2MW.S_AutomorphicForm_TwistedBruhat_setIntegral_mul_cuspKernel_sub_cuspTruncation_centralScalar_mul_eq_of_sigmaInvariant (solution)

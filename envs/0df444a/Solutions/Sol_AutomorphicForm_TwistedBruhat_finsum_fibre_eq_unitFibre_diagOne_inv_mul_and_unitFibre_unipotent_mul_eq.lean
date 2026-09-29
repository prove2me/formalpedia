-- Prove2me | solution 1 for AutomorphicForm.TwistedBruhat.finsum_fibre_eq_unitFibre_diagOne_inv_mul_and_unitFibre_unipotent_mul_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/cf82ac25-25bd-5921-be21-601112f42b3f

import Definitions.Def_AutomorphicForm_TwistedCuspKernel
import Definitions.Def_M4aHerbrand_IdeleClassVocab
import Definitions.Def_NumberField_AdelicHaar
import Definitions.Def_NumberField_AdelicLevel
import Definitions.Def_NumberField_AdelicBox
import Definitions.Def_NumberField_TateGlobalZeta
import Theorems.Thm_NumberField_AdelicHeight_adelicHeight_globalPoints_mul_of_mem_borelSubgroup
import Theorems.Thm_AutomorphicForm_ideleNorm_det_globalPoints
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_TwistedBruhat_finsum_fibre_eq_unitFibre_diagOne_inv_mul_and_unitFibre_unipotent_mul_eq

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
open IsDedekindDomain AutomorphicForm
open scoped Pointwise ENNReal NNReal

noncomputable section

namespace R1IwTorEq

section MatrixAlgebra

variable {A B : Type*} [CommRing A] [CommRing B]

theorem map_unipotentGL2 (f : A →+* B) (q : A) :
    Matrix.GeneralLinearGroup.map f (unipotentGL2 q) = unipotentGL2 (f q) := by
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  change f ((unipotentGL2 q : Matrix (Fin 2) (Fin 2) A) i j) = (unipotentGL2 (f q) : Matrix (Fin 2) (Fin 2) B) i j
  rw [unipotentGL2_coe, unipotentGL2_coe]
  fin_cases i <;> fin_cases j <;> simp

theorem map_diagOne (f : A →+* B) (u : Aˣ) :
    Matrix.GeneralLinearGroup.map f (diagOne u) = diagOne (Units.map (f : A →* B) u) := by
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  change f ((diagOne u : Matrix (Fin 2) (Fin 2) A) i j) = (diagOne (Units.map (f : A →* B) u) : Matrix (Fin 2) (Fin 2) B) i j
  rw [diagOne_coe_apply, diagOne_coe_apply]
  fin_cases i <;> fin_cases j <;> simp

theorem diagOne_inv_mul_unipotentGL2 (u : Aˣ) (q : A) :
    (diagOne u)⁻¹ * unipotentGL2 q = unipotentGL2 (((u⁻¹ : Aˣ) : A) * q) * (diagOne u)⁻¹ := by
  rw [← map_inv]
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  rw [Matrix.GeneralLinearGroup.coe_mul, Matrix.GeneralLinearGroup.coe_mul, Matrix.mul_apply, Matrix.mul_apply,
    Fin.sum_univ_two, Fin.sum_univ_two, diagOne_coe_apply, diagOne_coe_apply, diagOne_coe_apply, diagOne_coe_apply,
    unipotentGL2_coe, unipotentGL2_coe]
  fin_cases i <;> fin_cases j <;> simp [mul_comm]

theorem diagOne_mul_mul_diagOne_apply (e f : Aˣ) (δ : GL (Fin 2) A) (i j : Fin 2) :
    ((diagOne e * δ * diagOne f : GL (Fin 2) A) : Matrix (Fin 2) (Fin 2) A) i j =
      Matrix.diagonal ![(e : A), 1] i i * (δ : Matrix (Fin 2) (Fin 2) A) i j * Matrix.diagonal ![(f : A), 1] j j := by
  rw [Matrix.GeneralLinearGroup.coe_mul, Matrix.GeneralLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two,
    Matrix.mul_apply, Matrix.mul_apply, Fin.sum_univ_two, Fin.sum_univ_two]
  simp only [diagOne_coe_apply]
  fin_cases i <;> fin_cases j <;> simp

theorem unipotent_mul_mul_unipotent_apply (x y : A) (δ : GL (Fin 2) A) (h10 : (δ : Matrix (Fin 2) (Fin 2) A) 1 0 = 0) :
    ((unipotentGL2 x * δ * unipotentGL2 y : GL (Fin 2) A) : Matrix (Fin 2) (Fin 2) A) 1 0 = 0 ∧
    ((unipotentGL2 x * δ * unipotentGL2 y : GL (Fin 2) A) : Matrix (Fin 2) (Fin 2) A) 1 1 =
      (δ : Matrix (Fin 2) (Fin 2) A) 1 1 ∧
    ((unipotentGL2 x * δ * unipotentGL2 y : GL (Fin 2) A) : Matrix (Fin 2) (Fin 2) A) 0 0 =
      (δ : Matrix (Fin 2) (Fin 2) A) 0 0 := by
  have h : ∀ i j, ((unipotentGL2 x * δ * unipotentGL2 y : GL (Fin 2) A) : Matrix (Fin 2) (Fin 2) A) i j =
      ∑ k : Fin 2, (∑ l : Fin 2, (!![1, x; 0, 1] : Matrix (Fin 2) (Fin 2) A) i l * (δ : Matrix (Fin 2) (Fin 2) A) l k) *
        (!![1, y; 0, 1] : Matrix (Fin 2) (Fin 2) A) k j := by
    intro i j
    rw [Matrix.GeneralLinearGroup.coe_mul, Matrix.GeneralLinearGroup.coe_mul, Matrix.mul_apply]
    simp only [Matrix.mul_apply, unipotentGL2_coe]
  refine ⟨?_, ?_, ?_⟩ <;> rw [h, Fin.sum_univ_two, Fin.sum_univ_two, Fin.sum_univ_two] <;> simp [h10]

end MatrixAlgebra

section AdelicAlgebra

variable (K L : Type) [Field K] [Field L] [NumberField L] [Algebra K L]
variable (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L)

theorem centralScalar_comm (w : (AdeleRing (𝓞 L) L)ˣ) (y : AdelicGL2 (𝓞 L) L) :
    centralScalar (𝓞 L) L w * y = y * centralScalar (𝓞 L) L w := by
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  rw [Matrix.GeneralLinearGroup.coe_mul, Matrix.GeneralLinearGroup.coe_mul]
  exact congrFun (congrFun (Matrix.scalar_commute (w : AdeleRing (𝓞 L) L) (fun r' => mul_comm _ r')
    (y : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L))).eq i) j

theorem sigmaAdelicAct_globalPoints' (g : GL (Fin 2) L) :
    sigmaAdelicAct K L D σ (globalPoints (𝓞 L) L g) =
      globalPoints (𝓞 L) L (Matrix.GeneralLinearGroup.map (σ : L →+* L) g) :=
  sigmaAdelicAct_globalPoints K L D σ g

theorem globalPoints_diagOne (e : Lˣ) :
    globalPoints (𝓞 L) L (diagOne e) =
      diagOne (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L) e) :=
  map_diagOne (algebraMap L (AdeleRing (𝓞 L) L)) e

theorem globalPoints_unipotentGL2 (l : L) :
    globalPoints (𝓞 L) L (unipotentGL2 l) = unipotentGL2 (algebraMap L (AdeleRing (𝓞 L) L) l) :=
  map_unipotentGL2 (algebraMap L (AdeleRing (𝓞 L) L)) l

theorem torus_term (e : Lˣ) (δ' : GL (Fin 2) L) (g y : AdelicGL2 (𝓞 L) L) :
    g⁻¹ * globalPoints (𝓞 L) L (diagOne e * δ' * (Matrix.GeneralLinearGroup.map (σ : L →+* L) (diagOne e))⁻¹) *
        sigmaAdelicAct K L D σ y =
      ((globalPoints (𝓞 L) L (diagOne e))⁻¹ * g)⁻¹ * globalPoints (𝓞 L) L δ' *
        sigmaAdelicAct K L D σ ((globalPoints (𝓞 L) L (diagOne e))⁻¹ * y) := by
  rw [map_mul, map_mul, map_inv, ← sigmaAdelicAct_globalPoints' K L D σ, map_mul (sigmaAdelicAct K L D σ), map_inv,
    mul_inv_rev, inv_inv]
  simp only [mul_assoc]

theorem unipotent_term (l : L) (δ : GL (Fin 2) L) (g y : AdelicGL2 (𝓞 L) L) :
    (globalPoints (𝓞 L) L (unipotentGL2 l) * g)⁻¹ * globalPoints (𝓞 L) L δ *
        sigmaAdelicAct K L D σ (globalPoints (𝓞 L) L (unipotentGL2 l) * y) =
      g⁻¹ * globalPoints (𝓞 L) L ((unipotentGL2 l)⁻¹ * δ * Matrix.GeneralLinearGroup.map (σ : L →+* L) (unipotentGL2 l)) *
        sigmaAdelicAct K L D σ y := by
  rw [map_mul (globalPoints (𝓞 L) L), map_mul (globalPoints (𝓞 L) L), map_inv, ← sigmaAdelicAct_globalPoints' K L D σ,
    map_mul (sigmaAdelicAct K L D σ), mul_inv_rev]
  simp only [mul_assoc]

end AdelicAlgebra

section IndexSets

open LT.TwistedNorm AutomorphicForm.TwistedBruhat

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
variable (σ : L ≃ₐ[K] L) (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)

def Ia (a : L) : Set (GL (Fin 2) L) :=
  {δ : GL (Fin 2) L | δ ∈ TwistedBruhat.normUnipotentSet K L σ hgen ∧
    (δ : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧ (δ : Matrix (Fin 2) (Fin 2) L) 1 1 = 1 ∧
    (δ : Matrix (Fin 2) (Fin 2) L) 0 0 = a}

def Ja (a : L) : Set (GL (Fin 2) L) :=
  {δ : GL (Fin 2) L |
    (δ : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧ (δ : Matrix (Fin 2) (Fin 2) L) 1 1 = 1 ∧
    (δ : Matrix (Fin 2) (Fin 2) L) 0 0 = a}

theorem sigmaConj_mem_normUnipotentSet {δ : GL (Fin 2) L} (hδ : δ ∈ normUnipotentSet K L σ hgen) (h : GL (Fin 2) L) :
    h⁻¹ * δ * Matrix.GeneralLinearGroup.map (σ : L →+* L) h ∈ normUnipotentSet K L σ hgen := by
  obtain ⟨γ, hγ, hcls⟩ := hδ
  refine ⟨γ, hγ, ?_⟩
  rw [← hcls]
  exact congrArg _ (SigmaConjClasses.mk_eq_mk_iff_exists_eq_inv_mul_mul_map.mpr ⟨h, rfl⟩).symm

def torC (e : Lˣ) (δ : GL (Fin 2) L) : GL (Fin 2) L :=
  diagOne e * δ * (Matrix.GeneralLinearGroup.map (σ : L →+* L) (diagOne e))⁻¹

theorem torC_eq (e : Lˣ) (δ : GL (Fin 2) L) :
    torC K L σ e δ = diagOne e * δ * diagOne (Units.map ((σ : L →+* L) : L →* L) e)⁻¹ := by
  rw [torC, map_diagOne, map_inv]

theorem torC_eq_conj (e : Lˣ) (δ : GL (Fin 2) L) :
    torC K L σ e δ = (diagOne e)⁻¹⁻¹ * δ * Matrix.GeneralLinearGroup.map (σ : L →+* L) (diagOne e)⁻¹ := by
  rw [torC, inv_inv, map_inv]

theorem torC_apply (e : Lˣ) (δ : GL (Fin 2) L) :
    ((torC K L σ e δ : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) 1 0 = (δ : Matrix (Fin 2) (Fin 2) L) 1 0 * (σ (e : L))⁻¹ ∧
    ((torC K L σ e δ : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) 1 1 = (δ : Matrix (Fin 2) (Fin 2) L) 1 1 ∧
    ((torC K L σ e δ : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) 0 0 =
      (e : L) * (δ : Matrix (Fin 2) (Fin 2) L) 0 0 * (σ (e : L))⁻¹ := by
  rw [torC_eq]
  refine ⟨?_, ?_, ?_⟩ <;> rw [diagOne_mul_mul_diagOne_apply] <;> simp

def torCinv (e : Lˣ) (δ : GL (Fin 2) L) : GL (Fin 2) L :=
  (diagOne e)⁻¹ * δ * Matrix.GeneralLinearGroup.map (σ : L →+* L) (diagOne e)

theorem torCinv_apply (e : Lˣ) (δ : GL (Fin 2) L) :
    ((torCinv K L σ e δ : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) 1 0 = (δ : Matrix (Fin 2) (Fin 2) L) 1 0 * σ (e : L) ∧
    ((torCinv K L σ e δ : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) 1 1 = (δ : Matrix (Fin 2) (Fin 2) L) 1 1 ∧
    ((torCinv K L σ e δ : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) 0 0 =
      ((e⁻¹ : Lˣ) : L) * (δ : Matrix (Fin 2) (Fin 2) L) 0 0 * σ (e : L) := by
  rw [torCinv, map_diagOne, ← map_inv]
  refine ⟨?_, ?_, ?_⟩ <;> rw [diagOne_mul_mul_diagOne_apply] <;> simp

theorem torC_torCinv (e : Lˣ) (δ : GL (Fin 2) L) : torC K L σ e (torCinv K L σ e δ) = δ := by
  simp only [torC, torCinv]; group

theorem torCinv_torC (e : Lˣ) (δ : GL (Fin 2) L) : torCinv K L σ e (torC K L σ e δ) = δ := by
  simp only [torC, torCinv]; group

variable {a : L} {e : Lˣ}

theorem bijOn_torC_Ia (ha : a * σ (e : L) = (e : L)) : Set.BijOn (torC K L σ e) (Ia K L σ hgen 1) (Ia K L σ hgen a) := by
  have hσe : σ (e : L) ≠ 0 := by rw [ne_eq, map_eq_zero]; exact e.ne_zero
  have ha' : a = (e : L) * (σ (e : L))⁻¹ := (eq_mul_inv_iff_mul_eq₀ hσe).mpr ha
  refine ⟨fun δ hδ => ?_, fun δ _ δ' _ h => ?_, fun δ hδ => ?_⟩
  · obtain ⟨hNU, h10, h11, h00⟩ := hδ
    obtain ⟨t10, t11, t00⟩ := torC_apply K L σ e δ
    refine ⟨?_, by rw [t10, h10, zero_mul], by rw [t11, h11], by rw [t00, h00, mul_one, ha']⟩
    rw [torC_eq_conj]; exact sigmaConj_mem_normUnipotentSet K L σ hgen hNU _
  · simpa only [torCinv_torC] using congrArg (torCinv K L σ e) h
  · obtain ⟨hNU, h10, h11, h00⟩ := hδ
    obtain ⟨t10, t11, t00⟩ := torCinv_apply K L σ e δ
    refine ⟨torCinv K L σ e δ, ⟨sigmaConj_mem_normUnipotentSet K L σ hgen hNU _, by rw [t10, h10, zero_mul],
      by rw [t11, h11], ?_⟩, torC_torCinv K L σ e δ⟩
    rw [t00, h00, ha', Units.val_inv_eq_inv_val]
    field_simp

theorem bijOn_torC_Ja (ha : a * σ (e : L) = (e : L)) : Set.BijOn (torC K L σ e) (Ja L 1) (Ja L a) := by
  have hσe : σ (e : L) ≠ 0 := by rw [ne_eq, map_eq_zero]; exact e.ne_zero
  have ha' : a = (e : L) * (σ (e : L))⁻¹ := (eq_mul_inv_iff_mul_eq₀ hσe).mpr ha
  refine ⟨fun δ hδ => ?_, fun δ _ δ' _ h => ?_, fun δ hδ => ?_⟩
  · obtain ⟨h10, h11, h00⟩ := hδ
    obtain ⟨t10, t11, t00⟩ := torC_apply K L σ e δ
    exact ⟨by rw [t10, h10, zero_mul], by rw [t11, h11], by rw [t00, h00, mul_one, ha']⟩
  · simpa only [torCinv_torC] using congrArg (torCinv K L σ e) h
  · obtain ⟨h10, h11, h00⟩ := hδ
    obtain ⟨t10, t11, t00⟩ := torCinv_apply K L σ e δ
    refine ⟨torCinv K L σ e δ, ⟨by rw [t10, h10, zero_mul], by rw [t11, h11], ?_⟩, torC_torCinv K L σ e δ⟩
    rw [t00, h00, ha', Units.val_inv_eq_inv_val]
    field_simp

def uniC (l : L) (δ : GL (Fin 2) L) : GL (Fin 2) L :=
  (unipotentGL2 l)⁻¹ * δ * Matrix.GeneralLinearGroup.map (σ : L →+* L) (unipotentGL2 l)

theorem unipotentGL2_inv' {A : Type*} [CommRing A] (x : A) : (unipotentGL2 x)⁻¹ = unipotentGL2 (-x) :=
  inv_eq_of_mul_eq_one_right (by rw [← unipotentGL2_add, add_neg_cancel, unipotentGL2_zero])

theorem uniC_eq (l : L) (δ : GL (Fin 2) L) : uniC K L σ l δ = unipotentGL2 (-l) * δ * unipotentGL2 (σ l) := by
  rw [uniC, map_unipotentGL2, unipotentGL2_inv']
  rfl

def uniCinv (l : L) (δ : GL (Fin 2) L) : GL (Fin 2) L :=
  unipotentGL2 l * δ * (Matrix.GeneralLinearGroup.map (σ : L →+* L) (unipotentGL2 l))⁻¹

theorem uniCinv_eq (l : L) (δ : GL (Fin 2) L) : uniCinv K L σ l δ = unipotentGL2 l * δ * unipotentGL2 (-σ l) := by
  rw [uniCinv, map_unipotentGL2, unipotentGL2_inv']
  rfl

theorem uniC_uniCinv (l : L) (δ : GL (Fin 2) L) : uniC K L σ l (uniCinv K L σ l δ) = δ := by
  simp only [uniC, uniCinv]; group

theorem uniCinv_uniC (l : L) (δ : GL (Fin 2) L) : uniCinv K L σ l (uniC K L σ l δ) = δ := by
  simp only [uniC, uniCinv]; group

theorem bijOn_uniC_Ia (l : L) : Set.BijOn (uniC K L σ l) (Ia K L σ hgen 1) (Ia K L σ hgen 1) := by
  refine ⟨fun δ hδ => ?_, fun δ _ δ' _ h => ?_, fun δ hδ => ?_⟩
  · obtain ⟨hNU, h10, h11, h00⟩ := hδ
    obtain ⟨t10, t11, t00⟩ := unipotent_mul_mul_unipotent_apply (-l) (σ l) δ h10
    rw [← uniC_eq] at t10 t11 t00
    exact ⟨sigmaConj_mem_normUnipotentSet K L σ hgen hNU _, t10, by rw [t11, h11], by rw [t00, h00]⟩
  · simpa only [uniCinv_uniC] using congrArg (uniCinv K L σ l) h
  · obtain ⟨hNU, h10, h11, h00⟩ := hδ
    obtain ⟨t10, t11, t00⟩ := unipotent_mul_mul_unipotent_apply l (-σ l) δ h10
    rw [← uniCinv_eq] at t10 t11 t00
    refine ⟨uniCinv K L σ l δ, ⟨?_, t10, by rw [t11, h11], by rw [t00, h00]⟩, uniC_uniCinv K L σ l δ⟩
    have h := sigmaConj_mem_normUnipotentSet K L σ hgen hNU (unipotentGL2 l)⁻¹
    rwa [inv_inv, map_inv] at h

theorem bijOn_uniC_Ja (l : L) : Set.BijOn (uniC K L σ l) (Ja L 1) (Ja L 1) := by
  refine ⟨fun δ hδ => ?_, fun δ _ δ' _ h => ?_, fun δ hδ => ?_⟩
  · obtain ⟨h10, h11, h00⟩ := hδ
    obtain ⟨t10, t11, t00⟩ := unipotent_mul_mul_unipotent_apply (-l) (σ l) δ h10
    rw [← uniC_eq] at t10 t11 t00
    exact ⟨t10, by rw [t11, h11], by rw [t00, h00]⟩
  · simpa only [uniCinv_uniC] using congrArg (uniCinv K L σ l) h
  · obtain ⟨h10, h11, h00⟩ := hδ
    obtain ⟨t10, t11, t00⟩ := unipotent_mul_mul_unipotent_apply l (-σ l) δ h10
    rw [← uniCinv_eq] at t10 t11 t00
    exact ⟨uniCinv K L σ l δ, ⟨t10, by rw [t11, h11], by rw [t00, h00]⟩, uniC_uniCinv K L σ l δ⟩

theorem bijOn_mul_unipotent_Ja (m : L) : Set.BijOn (fun δ : GL (Fin 2) L => δ * unipotentGL2 m) (Ja L 1) (Ja L 1) := by
  have hmaps : ∀ m : L, Set.MapsTo (fun δ : GL (Fin 2) L => δ * unipotentGL2 m) (Ja L 1) (Ja L 1) := by
    intro m δ hδ
    obtain ⟨h10, h11, h00⟩ := hδ
    obtain ⟨t10, t11, t00⟩ := unipotent_mul_mul_unipotent_apply 0 m δ h10
    rw [unipotentGL2_zero, one_mul] at t10 t11 t00
    exact ⟨t10, by rw [t11, h11], by rw [t00, h00]⟩
  refine ⟨hmaps m, fun δ _ δ' _ h => mul_right_cancel h, fun δ hδ => ⟨δ * unipotentGL2 (-m), hmaps (-m) hδ, ?_⟩⟩
  show δ * unipotentGL2 (-m) * unipotentGL2 m = δ
  rw [mul_assoc, ← unipotentGL2_add, neg_add_cancel, unipotentGL2_zero, mul_one]

end IndexSets

section Kernel

open AutomorphicForm.TwistedBruhat

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
variable (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L)
variable (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)

def Kat (T : Set (GL (Fin 2) L)) (φ : AdelicGL2 (𝓞 L) L → ℂ) (g y : AdelicGL2 (𝓞 L) L) : ℂ :=
  ∑ᶠ δ ∈ T, φ (g⁻¹ * globalPoints (𝓞 L) L δ * sigmaAdelicAct K L D σ y)

theorem Kat_Ia_eq (φ : AdelicGL2 (𝓞 L) L → ℂ) {e : Lˣ} {a : L} (ha : a * σ (e : L) = (e : L)) (g y : AdelicGL2 (𝓞 L) L) :
    Kat K L D σ (Ia K L σ hgen a) φ g y =
      Kat K L D σ (Ia K L σ hgen 1) φ ((globalPoints (𝓞 L) L (diagOne e))⁻¹ * g)
        ((globalPoints (𝓞 L) L (diagOne e))⁻¹ * y) := by
  unfold Kat
  refine (finsum_mem_eq_of_bijOn _ (bijOn_torC_Ia K L σ hgen ha) fun δ _ => ?_).symm
  exact congrArg φ (torus_term K L D σ e δ g y).symm

theorem Kat_Ja_eq (φ : AdelicGL2 (𝓞 L) L → ℂ) {e : Lˣ} {a : L} (ha : a * σ (e : L) = (e : L)) (g y : AdelicGL2 (𝓞 L) L) :
    Kat K L D σ (Ja L a) φ g y =
      Kat K L D σ (Ja L 1) φ ((globalPoints (𝓞 L) L (diagOne e))⁻¹ * g)
        ((globalPoints (𝓞 L) L (diagOne e))⁻¹ * y) := by
  unfold Kat
  refine (finsum_mem_eq_of_bijOn _ (bijOn_torC_Ja K L σ ha) fun δ _ => ?_).symm
  exact congrArg φ (torus_term K L D σ e δ g y).symm

theorem Kat_Ia_unipotent (φ : AdelicGL2 (𝓞 L) L → ℂ) (l : L) (g y : AdelicGL2 (𝓞 L) L) :
    Kat K L D σ (Ia K L σ hgen 1) φ (globalPoints (𝓞 L) L (unipotentGL2 l) * g)
        (globalPoints (𝓞 L) L (unipotentGL2 l) * y) = Kat K L D σ (Ia K L σ hgen 1) φ g y := by
  unfold Kat
  exact finsum_mem_eq_of_bijOn _ (bijOn_uniC_Ia K L σ hgen l) fun δ _ => congrArg φ (unipotent_term K L D σ l δ g y)

theorem Kat_Ja_unipotent (φ : AdelicGL2 (𝓞 L) L → ℂ) (l : L) (g y : AdelicGL2 (𝓞 L) L) :
    Kat K L D σ (Ja L 1) φ (globalPoints (𝓞 L) L (unipotentGL2 l) * g)
        (globalPoints (𝓞 L) L (unipotentGL2 l) * y) = Kat K L D σ (Ja L 1) φ g y := by
  unfold Kat
  exact finsum_mem_eq_of_bijOn _ (bijOn_uniC_Ja K L σ l) fun δ _ => congrArg φ (unipotent_term K L D σ l δ g y)

theorem Kat_Ja_unipotentGL2_add (φ : AdelicGL2 (𝓞 L) L → ℂ) (l : L) (q : AdeleRing (𝓞 L) L) (g y : AdelicGL2 (𝓞 L) L) :
    Kat K L D σ (Ja L 1) φ g (unipotentGL2 (algebraMap L (AdeleRing (𝓞 L) L) l + q) * y) =
      Kat K L D σ (Ja L 1) φ g (unipotentGL2 q * y) := by
  unfold Kat
  have hy : unipotentGL2 (algebraMap L (AdeleRing (𝓞 L) L) l + q) * y =
      globalPoints (𝓞 L) L (unipotentGL2 l) * (unipotentGL2 q * y) := by
    rw [unipotentGL2_add, globalPoints_unipotentGL2, mul_assoc]
  rw [hy, map_mul (sigmaAdelicAct K L D σ), sigmaAdelicAct_globalPoints', map_unipotentGL2]
  refine finsum_mem_eq_of_bijOn (fun δ => δ * unipotentGL2 ((σ : L →+* L) l)) (bijOn_mul_unipotent_Ja L _)
    fun δ _ => ?_
  simp only [map_mul, mul_assoc]

end Kernel

section Box

variable (L : Type) [Field L] [NumberField L]

attribute [local instance] NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.borelSpace_adeleBorel
  NumberField.AdelicHaar.isAddHaarMeasure_adelicAddHaar

theorem distribHaarChar_principal (e : Lˣ) :
    distribHaarChar (AdeleRing (𝓞 L) L) (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L) e) = 1 := by
  have h := AutomorphicForm.ideleNorm_det_globalPoints (F := L) (diagOne e)
  have hdet : Matrix.GeneralLinearGroup.det (globalPoints (𝓞 L) L (diagOne e)) =
      Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L) e := by
    rw [globalPoints_diagOne]
    refine Units.ext ?_
    rw [Matrix.GeneralLinearGroup.val_det_apply]
    show (Matrix.diagonal ![((Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L) e :
      (AdeleRing (𝓞 L) L)ˣ) : AdeleRing (𝓞 L) L), 1]).det = _
    rw [Matrix.det_diagonal, Fin.prod_univ_two]
    simp
  rw [hdet, NumberField.TateGlobal.ideleNorm] at h
  exact_mod_cast h

variable {L}

scoped instance regular_adelicAddHaar : (adelicAddHaar (𝓞 L) L).Regular := by
  show (Measure.addHaar : Measure (AdeleRing (𝓞 L) L)).Regular
  rw [Measure.addHaar]; infer_instance

theorem measurePreserving_smul_of_distribHaarChar_eq_one {u : (AdeleRing (𝓞 L) L)ˣ}
    (hu : distribHaarChar (AdeleRing (𝓞 L) L) u = 1) :
    MeasurePreserving (fun q : AdeleRing (𝓞 L) L => u • q) (adelicAddHaar (𝓞 L) L) (adelicAddHaar (𝓞 L) L) := by
  refine ⟨measurable_const_smul u, Measure.ext fun s hs => ?_⟩
  rw [Measure.map_apply (measurable_const_smul u) hs, Set.preimage_smul, ← distribHaarChar_mul, map_inv, hu, inv_one,
    ENNReal.coe_one, one_mul]

variable (L)

scoped instance : MeasurableConstVAdd (AdeleRing.principalSubgroup (𝓞 L) L) (AdeleRing (𝓞 L) L) :=
  ⟨fun c => measurable_const_add (c : AdeleRing (𝓞 L) L)⟩

scoped instance : VAddInvariantMeasure (AdeleRing.principalSubgroup (𝓞 L) L) (AdeleRing (𝓞 L) L) (adelicAddHaar (𝓞 L) L) :=
  ⟨fun c s hs => measure_preimage_add (adelicAddHaar (𝓞 L) L) (c : AdeleRing (𝓞 L) L) s⟩

theorem countable_principalSubgroup : Countable (AdeleRing.principalSubgroup (𝓞 L) L) := by
  haveI : Countable L := (Module.Free.chooseBasis ℚ L).equivFun.toEquiv.countable_iff.2 inferInstance
  exact (Set.countable_range (algebraMap L (AdeleRing (𝓞 L) L))).to_subtype

def prinMul (e : Lˣ) : AdeleRing.principalSubgroup (𝓞 L) L ≃ AdeleRing.principalSubgroup (𝓞 L) L where
  toFun g := ⟨algebraMap L (AdeleRing (𝓞 L) L) (e : L) * g, by
    obtain ⟨_, l, rfl⟩ := g; exact ⟨(e : L) * l, by simp⟩⟩
  invFun g := ⟨algebraMap L (AdeleRing (𝓞 L) L) ((e⁻¹ : Lˣ) : L) * g, by
    obtain ⟨_, l, rfl⟩ := g; exact ⟨((e⁻¹ : Lˣ) : L) * l, by simp⟩⟩
  left_inv g := by
    refine Subtype.ext ?_
    show algebraMap L _ ((e⁻¹ : Lˣ) : L) * (algebraMap L _ (e : L) * (g : AdeleRing (𝓞 L) L)) = g
    rw [← mul_assoc, ← map_mul, Units.inv_mul, map_one, one_mul]
  right_inv g := by
    refine Subtype.ext ?_
    show algebraMap L _ (e : L) * (algebraMap L _ ((e⁻¹ : Lˣ) : L) * (g : AdeleRing (𝓞 L) L)) = g
    rw [← mul_assoc, ← map_mul, Units.mul_inv, map_one, one_mul]

theorem isAddFundamentalDomain_smul (e : Lˣ) {X : Set (AdeleRing (𝓞 L) L)}
    (hX : IsAddFundamentalDomain (AdeleRing.principalSubgroup (𝓞 L) L) X (adelicAddHaar (𝓞 L) L)) :
    IsAddFundamentalDomain (AdeleRing.principalSubgroup (𝓞 L) L)
      ((Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L) e)⁻¹ • X) (adelicAddHaar (𝓞 L) L) := by
  set E := Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L) e with hE
  have hE1 : distribHaarChar (AdeleRing (𝓞 L) L) E = 1 := distribHaarChar_principal L e
  set f : AdeleRing (𝓞 L) L ≃ AdeleRing (𝓞 L) L := MulAction.toPerm (E⁻¹) with hf
  have hfimg : f '' X = E⁻¹ • X := by rw [← Set.image_smul]; rfl
  rw [← hfimg]
  refine hX.image_of_equiv f ?_ (prinMul L e) fun g x => ?_
  · have hsymm : (f.symm : AdeleRing (𝓞 L) L → AdeleRing (𝓞 L) L) = fun q => E • q := by
      funext q; simp [hf, MulAction.toPerm_symm_apply, inv_inv]
    rw [hsymm]
    exact (measurePreserving_smul_of_distribHaarChar_eq_one hE1).quasiMeasurePreserving
  · show E⁻¹ • ((prinMul L e g : AdeleRing (𝓞 L) L) + x) = (g : AdeleRing (𝓞 L) L) + E⁻¹ • x
    show ((E⁻¹ : (AdeleRing (𝓞 L) L)ˣ) : AdeleRing (𝓞 L) L) * (algebraMap L _ (e : L) * (g : AdeleRing (𝓞 L) L) + x) =
      (g : AdeleRing (𝓞 L) L) + ((E⁻¹ : (AdeleRing (𝓞 L) L)ˣ) : AdeleRing (𝓞 L) L) * x
    have hEe : ((E⁻¹ : (AdeleRing (𝓞 L) L)ˣ) : AdeleRing (𝓞 L) L) * algebraMap L _ (e : L) = 1 := Units.inv_mul E
    rw [mul_add, ← mul_assoc, hEe, one_mul]

theorem integral_cond_smul_eq (e : Lˣ) (P : AdeleRing (𝓞 L) L → ℂ)
    (hP : ∀ (l : L) (q : AdeleRing (𝓞 L) L), P (algebraMap L (AdeleRing (𝓞 L) L) l + q) = P q) :
    ∫ q, P (((Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L) e)⁻¹ :
        (AdeleRing (𝓞 L) L)ˣ) • q) ∂(ProbabilityTheory.cond (adelicAddHaar (𝓞 L) L) (adelicBox L)) =
      ∫ q, P q ∂(ProbabilityTheory.cond (adelicAddHaar (𝓞 L) L) (adelicBox L)) := by
  set E := Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L) e with hE
  haveI := countable_principalSubgroup L
  have hE1 : distribHaarChar (AdeleRing (𝓞 L) L) E⁻¹ = 1 := by rw [map_inv, distribHaarChar_principal, inv_one]
  have hmp := measurePreserving_smul_of_distribHaarChar_eq_one hE1
  rw [ProbabilityTheory.cond, integral_smul_measure, integral_smul_measure]
  congr 1
  have hpre : (fun q : AdeleRing (𝓞 L) L => E⁻¹ • q) ⁻¹' (E⁻¹ • adelicBox L) = adelicBox L := by
    ext q; exact Set.smul_mem_smul_set_iff
  calc ∫ q in adelicBox L, P (E⁻¹ • q) ∂adelicAddHaar (𝓞 L) L
      = ∫ q in (fun q : AdeleRing (𝓞 L) L => E⁻¹ • q) ⁻¹' (E⁻¹ • adelicBox L), P (E⁻¹ • q) ∂adelicAddHaar (𝓞 L) L := by
        rw [hpre]
    _ = ∫ q in E⁻¹ • adelicBox L, P q ∂adelicAddHaar (𝓞 L) L :=
        hmp.setIntegral_preimage_emb (measurableEmbedding_const_smul _) P _
    _ = ∫ q in adelicBox L, P q ∂adelicAddHaar (𝓞 L) L :=
        (isAddFundamentalDomain_smul L e (isAddFundamentalDomain_adelicBox_adelicAddHaar L)).setIntegral_eq
          (isAddFundamentalDomain_adelicBox_adelicAddHaar L) fun g q => by
            obtain ⟨_, l, rfl⟩ := g
            exact hP l q

end Box

section Truncation

open AutomorphicForm.TwistedBruhat NumberField.AdelicHeight

attribute [local instance] NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.borelSpace_adeleBorel

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
variable (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L)
variable (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)

def Tat (T : Set (GL (Fin 2) L)) (R : ℝ) (φ : AdelicGL2 (𝓞 L) L → ℂ) (g w : AdelicGL2 (𝓞 L) L) : ℂ :=
  Set.indicator (highSet (adelicHeight L) (Real.exp R))
    (@constantTerm _ (adeleBorel (𝓞 L) L) _ _
      (@ProbabilityTheory.cond _ (adeleBorel (𝓞 L) L) (adelicAddHaar (𝓞 L) L) (adelicBox L))
      (fun t => unipotentGL2 t)
      (fun y => ∑ᶠ δ ∈ T, φ (g⁻¹ * globalPoints (𝓞 L) L δ * sigmaAdelicAct K L D σ y))) w

theorem Tat_eq (T : Set (GL (Fin 2) L)) (R : ℝ) (φ : AdelicGL2 (𝓞 L) L → ℂ) (g w : AdelicGL2 (𝓞 L) L) :
    Tat K L D σ T R φ g w = Set.indicator (highSet (adelicHeight L) (Real.exp R))
      (fun w => ∫ q, Kat K L D σ T φ g (unipotentGL2 q * w) ∂(ProbabilityTheory.cond (adelicAddHaar (𝓞 L) L) (adelicBox L)))
      w := rfl

theorem mem_highSet_globalPoints_mul_iff {γ : GL (Fin 2) L} (hγ : γ ∈ borelSubgroup L) (R : ℝ) (w : AdelicGL2 (𝓞 L) L) :
    globalPoints (𝓞 L) L γ * w ∈ highSet (adelicHeight L) (Real.exp R) ↔ w ∈ highSet (adelicHeight L) (Real.exp R) := by
  rw [mem_highSet_iff, mem_highSet_iff, adelicHeight_globalPoints_mul_of_mem_borelSubgroup L hγ]

theorem diagOne_inv_mem_borelSubgroup (e : Lˣ) : (diagOne e)⁻¹ ∈ borelSubgroup L := by
  rw [← map_inv]
  show (diagOne e⁻¹ : Matrix (Fin 2) (Fin 2) L) 1 0 = 0
  rw [diagOne_coe_apply]; simp

theorem unipotentGL2_mem_borelSubgroup (l : L) : unipotentGL2 l ∈ borelSubgroup L := by
  show (unipotentGL2 l : Matrix (Fin 2) (Fin 2) L) 1 0 = 0
  rw [unipotentGL2_coe]; simp

theorem Tat_Ja_eq (R : ℝ) (φ : AdelicGL2 (𝓞 L) L → ℂ) {e : Lˣ} {a : L} (ha : a * σ (e : L) = (e : L))
    (ζ : (AdeleRing (𝓞 L) L)ˣ) (g : AdelicGL2 (𝓞 L) L) :
    Tat K L D σ (Ja L a) R φ g (centralScalar (𝓞 L) L ζ * g) =
      Tat K L D σ (Ja L 1) R φ ((globalPoints (𝓞 L) L (diagOne e))⁻¹ * g)
        (centralScalar (𝓞 L) L ζ * ((globalPoints (𝓞 L) L (diagOne e))⁻¹ * g)) := by
  set H := globalPoints (𝓞 L) L (diagOne e) with hH
  set E := Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L) e with hE
  have hHE : H = diagOne E := globalPoints_diagOne L e
  have hcs : centralScalar (𝓞 L) L ζ * (H⁻¹ * g) = H⁻¹ * (centralScalar (𝓞 L) L ζ * g) := by
    rw [← mul_assoc, ← mul_assoc, centralScalar_comm]
  have hmem : centralScalar (𝓞 L) L ζ * (H⁻¹ * g) ∈ highSet (adelicHeight L) (Real.exp R) ↔
      centralScalar (𝓞 L) L ζ * g ∈ highSet (adelicHeight L) (Real.exp R) := by
    rw [hcs, hH, ← map_inv]
    exact mem_highSet_globalPoints_mul_iff L (diagOne_inv_mem_borelSubgroup L e) R _
  rw [Tat_eq, Tat_eq]
  by_cases hx : centralScalar (𝓞 L) L ζ * g ∈ highSet (adelicHeight L) (Real.exp R)
  swap
  · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem (fun h' => hx (hmem.mp h'))]
  rw [Set.indicator_of_mem hx, Set.indicator_of_mem (hmem.mpr hx)]

  have hpt : ∀ q : AdeleRing (𝓞 L) L, Kat K L D σ (Ja L a) φ g (unipotentGL2 q * (centralScalar (𝓞 L) L ζ * g)) =
      Kat K L D σ (Ja L 1) φ (H⁻¹ * g) (unipotentGL2 ((E⁻¹ : (AdeleRing (𝓞 L) L)ˣ) • q) *
        (centralScalar (𝓞 L) L ζ * (H⁻¹ * g))) := by
    intro q
    rw [Kat_Ja_eq K L D σ φ ha, ← hH, ← mul_assoc H⁻¹, hHE, diagOne_inv_mul_unipotentGL2, ← hHE, hcs]
    simp only [mul_assoc, Units.smul_def, smul_eq_mul]
  simp_rw [hpt]
  exact integral_cond_smul_eq L e
    (fun q => Kat K L D σ (Ja L 1) φ (H⁻¹ * g) (unipotentGL2 q * (centralScalar (𝓞 L) L ζ * (H⁻¹ * g))))
    fun l q => Kat_Ja_unipotentGL2_add K L D σ φ l q _ _

theorem Tat_Ja_unipotent (R : ℝ) (φ : AdelicGL2 (𝓞 L) L → ℂ) (l : L) (ζ : (AdeleRing (𝓞 L) L)ˣ) (g : AdelicGL2 (𝓞 L) L) :
    Tat K L D σ (Ja L 1) R φ (globalPoints (𝓞 L) L (unipotentGL2 l) * g)
        (centralScalar (𝓞 L) L ζ * (globalPoints (𝓞 L) L (unipotentGL2 l) * g)) =
      Tat K L D σ (Ja L 1) R φ g (centralScalar (𝓞 L) L ζ * g) := by
  set N := globalPoints (𝓞 L) L (unipotentGL2 l) with hN
  have hcs : centralScalar (𝓞 L) L ζ * (N * g) = N * (centralScalar (𝓞 L) L ζ * g) := by
    rw [← mul_assoc, ← mul_assoc, centralScalar_comm]
  have hmem : centralScalar (𝓞 L) L ζ * (N * g) ∈ highSet (adelicHeight L) (Real.exp R) ↔
      centralScalar (𝓞 L) L ζ * g ∈ highSet (adelicHeight L) (Real.exp R) := by
    rw [hcs, hN]
    exact mem_highSet_globalPoints_mul_iff L (unipotentGL2_mem_borelSubgroup L l) R _
  rw [Tat_eq, Tat_eq]
  by_cases hx : centralScalar (𝓞 L) L ζ * g ∈ highSet (adelicHeight L) (Real.exp R)
  swap
  · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem (fun h' => hx (hmem.mp h'))]
  rw [Set.indicator_of_mem hx, Set.indicator_of_mem (hmem.mpr hx)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun q => ?_)

  have hcomm : unipotentGL2 q * (N * (centralScalar (𝓞 L) L ζ * g)) = N * (unipotentGL2 q * (centralScalar (𝓞 L) L ζ * g)) := by
    rw [hN, globalPoints_unipotentGL2]
    simp only [← mul_assoc]
    rw [← unipotentGL2_add, ← unipotentGL2_add, add_comm]
  show Kat K L D σ (Ja L 1) φ (N * g) (unipotentGL2 q * (centralScalar (𝓞 L) L ζ * (N * g))) =
    Kat K L D σ (Ja L 1) φ g (unipotentGL2 q * (centralScalar (𝓞 L) L ζ * g))
  rw [hcs, hcomm, hN, Kat_Ja_unipotent]

end Truncation

end R1IwTorEq
p2m_reactivate "P2MW.S_AutomorphicForm_TwistedBruhat_finsum_fibre_eq_unitFibre_diagOne_inv_mul_and_unitFibre_unipotent_mul_eq.R1IwTorEq"

end
p2m_reactivate "P2MW.S_AutomorphicForm_TwistedBruhat_finsum_fibre_eq_unitFibre_diagOne_inv_mul_and_unitFibre_unipotent_mul_eq.R1IwTorEq"

section Solution

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
open IsDedekindDomain
open AutomorphicForm
open scoped Pointwise

theorem solution
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L)
    (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (φ : AdelicGL2 (𝓞 L) L → ℂ) (R : ℝ) :
    (∀ (e : Lˣ) (a : L), a * σ (e : L) = (e : L) →
      ∀ (ζ : (AdeleRing (𝓞 L) L)ˣ) (g : AdelicGL2 (𝓞 L) L),
        (∑ᶠ δ ∈ {δ : GL (Fin 2) L | δ ∈ TwistedBruhat.normUnipotentSet K L σ hgen ∧
            (δ : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧ (δ : Matrix (Fin 2) (Fin 2) L) 1 1 = 1 ∧
            (δ : Matrix (Fin 2) (Fin 2) L) 0 0 = a},
            φ (g⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ *
              AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.centralScalar (𝓞 L) L ζ * g)) =
          ∑ᶠ δ ∈ {δ : GL (Fin 2) L | δ ∈ TwistedBruhat.normUnipotentSet K L σ hgen ∧
            (δ : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧ (δ : Matrix (Fin 2) (Fin 2) L) 1 1 = 1 ∧
            (δ : Matrix (Fin 2) (Fin 2) L) 0 0 = 1},
            φ (((AutomorphicForm.globalPoints (𝓞 L) L (diagOne e))⁻¹ * g)⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ *
              AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.centralScalar (𝓞 L) L ζ *
                ((AutomorphicForm.globalPoints (𝓞 L) L (diagOne e))⁻¹ * g)))) ∧
        Set.indicator (AutomorphicForm.highSet (NumberField.AdelicHeight.adelicHeight L) (Real.exp R))
            (@AutomorphicForm.constantTerm _ (adeleBorel (𝓞 L) L) _ _
              (@ProbabilityTheory.cond _ (adeleBorel (𝓞 L) L) (adelicAddHaar (𝓞 L) L) (adelicBox L))
              (fun t => AutomorphicForm.unipotentGL2 t)
              (fun y => ∑ᶠ δ ∈ {δ : GL (Fin 2) L |
                  (δ : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧ (δ : Matrix (Fin 2) (Fin 2) L) 1 1 = 1 ∧
                  (δ : Matrix (Fin 2) (Fin 2) L) 0 0 = a},
                φ (g⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ * AutomorphicForm.sigmaAdelicAct K L D σ y)))
            (AutomorphicForm.centralScalar (𝓞 L) L ζ * g) =
          Set.indicator (AutomorphicForm.highSet (NumberField.AdelicHeight.adelicHeight L) (Real.exp R))
            (@AutomorphicForm.constantTerm _ (adeleBorel (𝓞 L) L) _ _
              (@ProbabilityTheory.cond _ (adeleBorel (𝓞 L) L) (adelicAddHaar (𝓞 L) L) (adelicBox L))
              (fun t => AutomorphicForm.unipotentGL2 t)
              (fun y => ∑ᶠ δ ∈ {δ : GL (Fin 2) L |
                  (δ : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧ (δ : Matrix (Fin 2) (Fin 2) L) 1 1 = 1 ∧
                  (δ : Matrix (Fin 2) (Fin 2) L) 0 0 = 1},
                φ (((AutomorphicForm.globalPoints (𝓞 L) L (diagOne e))⁻¹ * g)⁻¹ *
                  AutomorphicForm.globalPoints (𝓞 L) L δ * AutomorphicForm.sigmaAdelicAct K L D σ y)))
            (AutomorphicForm.centralScalar (𝓞 L) L ζ * ((AutomorphicForm.globalPoints (𝓞 L) L (diagOne e))⁻¹ * g))) ∧
    (∀ (l : L) (ζ : (AdeleRing (𝓞 L) L)ˣ) (g : AdelicGL2 (𝓞 L) L),
        (∑ᶠ δ ∈ {δ : GL (Fin 2) L | δ ∈ TwistedBruhat.normUnipotentSet K L σ hgen ∧
            (δ : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧ (δ : Matrix (Fin 2) (Fin 2) L) 1 1 = 1 ∧
            (δ : Matrix (Fin 2) (Fin 2) L) 0 0 = 1},
            φ ((AutomorphicForm.globalPoints (𝓞 L) L (AutomorphicForm.unipotentGL2 l) * g)⁻¹ *
              AutomorphicForm.globalPoints (𝓞 L) L δ *
              AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.centralScalar (𝓞 L) L ζ *
                (AutomorphicForm.globalPoints (𝓞 L) L (AutomorphicForm.unipotentGL2 l) * g))) =
          ∑ᶠ δ ∈ {δ : GL (Fin 2) L | δ ∈ TwistedBruhat.normUnipotentSet K L σ hgen ∧
            (δ : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧ (δ : Matrix (Fin 2) (Fin 2) L) 1 1 = 1 ∧
            (δ : Matrix (Fin 2) (Fin 2) L) 0 0 = 1},
            φ (g⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ *
              AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.centralScalar (𝓞 L) L ζ * g))) ∧
        Set.indicator (AutomorphicForm.highSet (NumberField.AdelicHeight.adelicHeight L) (Real.exp R))
            (@AutomorphicForm.constantTerm _ (adeleBorel (𝓞 L) L) _ _
              (@ProbabilityTheory.cond _ (adeleBorel (𝓞 L) L) (adelicAddHaar (𝓞 L) L) (adelicBox L))
              (fun t => AutomorphicForm.unipotentGL2 t)
              (fun y => ∑ᶠ δ ∈ {δ : GL (Fin 2) L |
                  (δ : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧ (δ : Matrix (Fin 2) (Fin 2) L) 1 1 = 1 ∧
                  (δ : Matrix (Fin 2) (Fin 2) L) 0 0 = 1},
                φ ((AutomorphicForm.globalPoints (𝓞 L) L (AutomorphicForm.unipotentGL2 l) * g)⁻¹ *
                  AutomorphicForm.globalPoints (𝓞 L) L δ * AutomorphicForm.sigmaAdelicAct K L D σ y)))
            (AutomorphicForm.centralScalar (𝓞 L) L ζ * (AutomorphicForm.globalPoints (𝓞 L) L (AutomorphicForm.unipotentGL2 l) * g)) =
          Set.indicator (AutomorphicForm.highSet (NumberField.AdelicHeight.adelicHeight L) (Real.exp R))
            (@AutomorphicForm.constantTerm _ (adeleBorel (𝓞 L) L) _ _
              (@ProbabilityTheory.cond _ (adeleBorel (𝓞 L) L) (adelicAddHaar (𝓞 L) L) (adelicBox L))
              (fun t => AutomorphicForm.unipotentGL2 t)
              (fun y => ∑ᶠ δ ∈ {δ : GL (Fin 2) L |
                  (δ : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧ (δ : Matrix (Fin 2) (Fin 2) L) 1 1 = 1 ∧
                  (δ : Matrix (Fin 2) (Fin 2) L) 0 0 = 1},
                φ (g⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ * AutomorphicForm.sigmaAdelicAct K L D σ y)))
            (AutomorphicForm.centralScalar (𝓞 L) L ζ * g)) := by
  refine ⟨fun e a ha ζ g => ⟨?_, ?_⟩, fun l ζ g => ⟨?_, ?_⟩⟩
  · have h := R1IwTorEq.Kat_Ia_eq K L D σ hgen φ ha g (centralScalar (𝓞 L) L ζ * g)
    rw [← mul_assoc _ (centralScalar (𝓞 L) L ζ), ← R1IwTorEq.centralScalar_comm, mul_assoc] at h
    exact h
  · exact R1IwTorEq.Tat_Ja_eq K L D σ R φ ha ζ g
  · have h := R1IwTorEq.Kat_Ia_unipotent K L D σ hgen φ l g (centralScalar (𝓞 L) L ζ * g)
    rw [← mul_assoc _ (centralScalar (𝓞 L) L ζ), ← R1IwTorEq.centralScalar_comm, mul_assoc] at h
    exact h
  · exact R1IwTorEq.Tat_Ja_unipotent K L D σ R φ l ζ g

end Solution
p2m_reactivate "P2MW.S_AutomorphicForm_TwistedBruhat_finsum_fibre_eq_unitFibre_diagOne_inv_mul_and_unitFibre_unipotent_mul_eq.R1IwTorEq"

end S_AutomorphicForm_TwistedBruhat_finsum_fibre_eq_unitFibre_diagOne_inv_mul_and_unitFibre_unipotent_mul_eq
end P2MW
export P2MW.S_AutomorphicForm_TwistedBruhat_finsum_fibre_eq_unitFibre_diagOne_inv_mul_and_unitFibre_unipotent_mul_eq (solution)

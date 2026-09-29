-- Prove2me | solution 1 for AutomorphicForm.exists_subgroup_isClosed_and_mem_iff_diagonal_and_sigmaAdelicAct_mul_inv_mem_center_and_exists_isHaarMeasure
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/ce983b8a-c7a3-5049-a773-b22f8dabbbf2

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_AutomorphicForm_FormalBaseChange
import Definitions.Def_NumberField_PrincipalLevel
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_LanglandsTunnell_ConverseData
import Definitions.Def_LocalLanglands_HeckeCosetLocal
import Definitions.Def_M4aHerbrand_GenuineDescent
import Definitions.Def_TwistedNormClasses
import Definitions.Def_AdelicDock_LocalEmbedding
import Definitions.Def_AutomorphicForm_GL2ConjugacyCells
import Definitions.Def_AutomorphicForm_TruncationOperator
import Definitions.Def_AutomorphicForm_TwistedAdelicKernel
import Definitions.Def_NumberField_AdelicHeight
import Definitions.Def_AutomorphicForm_WeylIntertwining
import Definitions.Def_HaarQuotient
import Definitions.Def_AutomorphicForm_FactorizableTestFn

import Definitions.Def_AutomorphicForm_BorelSubgroup
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_subgroup_isClosed_and_mem_iff_diagonal_and_sigmaAdelicAct_mul_inv_mem_center_and_exists_isHaarMeasure

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
open IsDedekindDomain
open scoped TensorProduct Pointwise ComplexConjugate

attribute [local instance] NumberField.AdelicHaar.glBorel

namespace FDTUR

open AutomorphicForm

variable (K L : Type) [Field K] [Field L] [NumberField L] [Algebra K L]
  (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L)

theorem val_mul_apply (x y : AdelicGL2 (𝓞 L) L) (i j : Fin 2) :
    ((x * y : AdelicGL2 (𝓞 L) L) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) i j =
      (x : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) i 0 * (y : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) 0 j +
        (x : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) i 1 * (y : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) 1 j := by
  rw [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two]

theorem inv_offdiag_eq_zero (a : AdelicGL2 (𝓞 L) L)
    (h10 : (a : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) 1 0 = 0)
    (h01 : (a : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) 0 1 = 0) :
    ((a⁻¹ : AdelicGL2 (𝓞 L) L) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) 1 0 = 0 ∧
      ((a⁻¹ : AdelicGL2 (𝓞 L) L) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) 0 1 = 0 := by

  have hb : a ∈ adelicBorel (𝓞 L) L := h10
  set u := borelDiagFst (⟨a, hb⟩ : ↥(adelicBorel (𝓞 L) L)) with hu
  set v := borelDiagSnd (⟨a, hb⟩ : ↥(adelicBorel (𝓞 L) L)) with hv
  have hu' : ((u : (AdeleRing (𝓞 L) L)ˣ) : AdeleRing (𝓞 L) L) = (a : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) 0 0 :=
    borelDiagFst_apply_val _
  have hv' : ((v : (AdeleRing (𝓞 L) L)ˣ) : AdeleRing (𝓞 L) L) = (a : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) 1 1 :=
    borelDiagSnd_apply_val _
  have e1 : ∀ i j, ((a⁻¹ * a : AdelicGL2 (𝓞 L) L) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) i j =
      if i = j then 1 else 0 := by
    intro i j; rw [inv_mul_cancel, Units.val_one, Matrix.one_apply]
  have e10 := e1 1 0
  have e01 := e1 0 1
  rw [val_mul_apply] at e10 e01
  simp only [Fin.one_eq_zero_iff, OfNat.ofNat_ne_one, if_false, h10, mul_zero, add_zero, h01,
    Fin.zero_eq_one_iff, zero_add] at e10 e01

  constructor
  · have := congrArg (fun t => t * ((u⁻¹ : (AdeleRing (𝓞 L) L)ˣ) : AdeleRing (𝓞 L) L)) e10
    simp only [zero_mul] at this
    rw [← this, mul_assoc, ← hu', Units.mul_inv, mul_one]
  · have := congrArg (fun t => t * ((v⁻¹ : (AdeleRing (𝓞 L) L)ˣ) : AdeleRing (𝓞 L) L)) e01
    simp only [zero_mul] at this
    rw [← this, mul_assoc, ← hv', Units.mul_inv, mul_one]

def twistedCentraliser : Subgroup (AdelicGL2 (𝓞 L) L) where
  carrier := {h | (h : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) 1 0 = 0 ∧
    (h : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) 0 1 = 0 ∧
    sigmaAdelicAct K L D σ h * h⁻¹ ∈ Subgroup.center (AdelicGL2 (𝓞 L) L)}
  mul_mem' := by
    rintro a b ⟨ha10, ha01, hac⟩ ⟨hb10, hb01, hbc⟩
    refine ⟨?_, ?_, ?_⟩
    · rw [val_mul_apply, ha10, hb10, zero_mul, mul_zero, add_zero]
    · rw [val_mul_apply, ha01, hb01, mul_zero, zero_mul, add_zero]
    · have hcomm := Subgroup.mem_center_iff.1 hbc (sigmaAdelicAct K L D σ a)
      have : sigmaAdelicAct K L D σ (a * b) * (a * b)⁻¹ =
          (sigmaAdelicAct K L D σ b * b⁻¹) * (sigmaAdelicAct K L D σ a * a⁻¹) := by
        rw [map_mul, mul_inv_rev]
        calc sigmaAdelicAct K L D σ a * sigmaAdelicAct K L D σ b * (b⁻¹ * a⁻¹)
            = (sigmaAdelicAct K L D σ a * (sigmaAdelicAct K L D σ b * b⁻¹)) * a⁻¹ := by group
          _ = ((sigmaAdelicAct K L D σ b * b⁻¹) * sigmaAdelicAct K L D σ a) * a⁻¹ := by rw [hcomm]
          _ = _ := by group
      rw [this]
      exact Subgroup.mul_mem _ hbc hac
  one_mem' := ⟨by simp, by simp, by rw [map_one, inv_one, mul_one]; exact Subgroup.one_mem _⟩
  inv_mem' := by
    rintro a ⟨ha10, ha01, hac⟩
    obtain ⟨hi10, hi01⟩ := inv_offdiag_eq_zero L a ha10 ha01
    refine ⟨hi10, hi01, ?_⟩
    have hmem := Subgroup.inv_mem _ hac
    have hcomm := Subgroup.mem_center_iff.1 hmem a⁻¹
    have : sigmaAdelicAct K L D σ a⁻¹ * (a⁻¹)⁻¹ = (sigmaAdelicAct K L D σ a * a⁻¹)⁻¹ := by
      rw [map_inv, inv_inv]
      calc (sigmaAdelicAct K L D σ a)⁻¹ * a = (sigmaAdelicAct K L D σ a * a⁻¹ * a)⁻¹ * a := by group
        _ = a⁻¹ * (sigmaAdelicAct K L D σ a * a⁻¹)⁻¹ * a := by rw [mul_inv_rev]
        _ = (sigmaAdelicAct K L D σ a * a⁻¹)⁻¹ * a⁻¹ * a := by rw [hcomm]
        _ = (sigmaAdelicAct K L D σ a * a⁻¹)⁻¹ := by group
    rw [this]
    exact hmem

theorem mem_twistedCentraliser_iff (h : AdelicGL2 (𝓞 L) L) :
    h ∈ twistedCentraliser K L D σ ↔
      ((h : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) 1 0 = 0 ∧
       (h : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) 0 1 = 0 ∧
       sigmaAdelicAct K L D σ h * h⁻¹ ∈ Subgroup.center (AdelicGL2 (𝓞 L) L)) := Iff.rfl

theorem isClosed_center : IsClosed (Subgroup.center (AdelicGL2 (𝓞 L) L) : Set (AdelicGL2 (𝓞 L) L)) := by
  have : (Subgroup.center (AdelicGL2 (𝓞 L) L) : Set (AdelicGL2 (𝓞 L) L)) =
      ⋂ g : AdelicGL2 (𝓞 L) L, {h | g * h = h * g} := by
    ext h
    simp only [SetLike.mem_coe, Subgroup.mem_center_iff, Set.mem_iInter, Set.mem_setOf_eq]
  rw [this]
  exact isClosed_iInter fun g => isClosed_eq (continuous_const.mul continuous_id) (continuous_id.mul continuous_const)

theorem isClosed_twistedCentraliser :
    IsClosed (twistedCentraliser K L D σ : Set (AdelicGL2 (𝓞 L) L)) := by
  have hσc : Continuous (sigmaAdelicAct K L D σ) := AutomorphicForm.continuous_sigmaAdelicAct K L D σ
  have e10 : Continuous fun g : AdelicGL2 (𝓞 L) L => (g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) 1 0 :=
    Units.continuous_val.matrix_elem 1 0
  have e01 : Continuous fun g : AdelicGL2 (𝓞 L) L => (g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) 0 1 :=
    Units.continuous_val.matrix_elem 0 1
  have : (twistedCentraliser K L D σ : Set (AdelicGL2 (𝓞 L) L)) =
      ((fun g : AdelicGL2 (𝓞 L) L => (g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) 1 0) ⁻¹' {0}) ∩
      (((fun g : AdelicGL2 (𝓞 L) L => (g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) 0 1) ⁻¹' {0}) ∩
      ((fun g => sigmaAdelicAct K L D σ g * g⁻¹) ⁻¹' (Subgroup.center (AdelicGL2 (𝓞 L) L) : Set (AdelicGL2 (𝓞 L) L)))) := by
    ext h; exact Iff.rfl
  rw [this]
  exact (isClosed_singleton.preimage e10).inter ((isClosed_singleton.preimage e01).inter
    ((isClosed_center L).preimage (hσc.mul continuous_inv)))

theorem twistedCentraliser_comm (a b : ↥(twistedCentraliser K L D σ)) : a * b = b * a := by
  apply Subtype.ext
  obtain ⟨ha10, ha01, -⟩ := a.2
  obtain ⟨hb10, hb01, -⟩ := b.2
  show (a : AdelicGL2 (𝓞 L) L) * b = b * a
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  rw [val_mul_apply, val_mul_apply]
  fin_cases i <;> fin_cases j <;> simp [ha10, ha01, hb10, hb01, mul_comm]

attribute [local instance] NumberField.AdelicHaar.glBorel

theorem exists_twistedCentraliser_haar :
    ∃ H : Subgroup (AdelicGL2 (𝓞 L) L), IsClosed (H : Set (AdelicGL2 (𝓞 L) L)) ∧
      (∀ h : AdelicGL2 (𝓞 L) L, h ∈ H ↔
        ((h : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) 1 0 = 0 ∧
         (h : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) 0 1 = 0 ∧
         sigmaAdelicAct K L D σ h * h⁻¹ ∈ Subgroup.center (AdelicGL2 (𝓞 L) L))) ∧
      ∃ μH : Measure H, μH.IsHaarMeasure ∧ μH.IsMulRightInvariant := by
  haveI : BorelSpace (AdelicGL2 (𝓞 L) L) := NumberField.AdelicHaar.borelSpace_glBorel (Fin 2) (𝓞 L) L
  refine ⟨twistedCentraliser K L D σ, isClosed_twistedCentraliser K L D σ, fun h => Iff.rfl, ?_⟩
  haveI : LocallyCompactSpace ↥(twistedCentraliser K L D σ) := (isClosed_twistedCentraliser K L D σ).locallyCompactSpace
  refine ⟨MeasureTheory.Measure.haar, inferInstance, ⟨fun g => ?_⟩⟩
  have : (fun h : ↥(twistedCentraliser K L D σ) => h * g) = fun h => g * h :=
    funext fun h => twistedCentraliser_comm K L D σ h g
  rw [this]
  exact MeasureTheory.map_mul_left_eq_self _ g

end FDTUR

open AutomorphicForm in
open scoped TensorProduct.RightActions in
theorem solution
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L) :
    ∃ H : Subgroup (AdelicGL2 (𝓞 L) L), IsClosed (H : Set (AdelicGL2 (𝓞 L) L)) ∧
      (∀ h : AdelicGL2 (𝓞 L) L, h ∈ H ↔
        ((h : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) 1 0 = 0 ∧
         (h : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) 0 1 = 0 ∧
         AutomorphicForm.sigmaAdelicAct K L D σ h * h⁻¹ ∈ Subgroup.center (AdelicGL2 (𝓞 L) L))) ∧
      ∃ μH : Measure H, μH.IsHaarMeasure ∧ μH.IsMulRightInvariant :=
  FDTUR.exists_twistedCentraliser_haar K L D σ

end S_AutomorphicForm_exists_subgroup_isClosed_and_mem_iff_diagonal_and_sigmaAdelicAct_mul_inv_mem_center_and_exists_isHaarMeasure
end P2MW
export P2MW.S_AutomorphicForm_exists_subgroup_isClosed_and_mem_iff_diagonal_and_sigmaAdelicAct_mul_inv_mem_center_and_exists_isHaarMeasure (solution)

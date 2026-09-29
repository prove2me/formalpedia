-- Prove2me | solution 1 for AutomorphicForm.isMulRightInvariant_of_isHaarMeasure_generalLinearGroup_of_finite_maximalSpectrum
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/086f0ee3-5969-55d5-b6a5-7b2cd49db9cf

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_isMulRightInvariant_of_isHaarMeasure_generalLinearGroup_of_finite_maximalSpectrum

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open MeasureTheory MeasureTheory.Measure Matrix

noncomputable section

namespace P2mGL2SemilocalUnimodular

section Elements

variable {A : Type*} [CommRing A]

def glOf (M : Matrix (Fin 2) (Fin 2) A) (h : IsUnit M.det) : GL (Fin 2) A :=
  Matrix.GeneralLinearGroup.mk'' M h

@[scoped simp] theorem coe_glOf (M : Matrix (Fin 2) (Fin 2) A) (h : IsUnit M.det) :
    ((glOf M h : GL (Fin 2) A) : Matrix (Fin 2) (Fin 2) A) = M := rfl

theorem det_T01 (c : A) : IsUnit (!![(1 : A), c; 0, 1]).det := by
  rw [Matrix.det_fin_two_of]; simp

theorem det_T10 (c : A) : IsUnit (!![(1 : A), 0; c, 1]).det := by
  rw [Matrix.det_fin_two_of]; simp

theorem det_Dg (a b : Aˣ) : IsUnit (!![(a : A), 0; 0, (b : A)]).det := by
  rw [Matrix.det_fin_two_of, zero_mul, sub_zero]; exact a.isUnit.mul b.isUnit

theorem det_W : IsUnit (!![(0 : A), 1; 1, 0]).det := by
  rw [Matrix.det_fin_two_of, zero_mul, one_mul, zero_sub]; exact isUnit_one.neg

def T01 (c : A) : GL (Fin 2) A := glOf !![(1 : A), c; 0, 1] (det_T01 c)

def T10 (c : A) : GL (Fin 2) A := glOf !![(1 : A), 0; c, 1] (det_T10 c)

def Dg (a b : Aˣ) : GL (Fin 2) A := glOf !![(a : A), 0; 0, (b : A)] (det_Dg a b)

def W : GL (Fin 2) A := glOf !![(0 : A), 1; 1, 0] det_W

theorem T01_mul_T01 (c d : A) : T01 c * T01 d = T01 (c + d) := by
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  simp only [Units.val_mul, T01, coe_glOf]
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, add_comm]

theorem T01_zero : T01 (0 : A) = 1 := by
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  simp only [T01, coe_glOf, Units.val_one]
  fin_cases i <;> fin_cases j <;> simp

theorem N_mul_T01 (c : A) : Dg (-1) 1 * T01 c = T01 (-c) * Dg (-1) 1 := by
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  simp only [Units.val_mul, T01, Dg, coe_glOf]
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem N_mul_T10 (c : A) : Dg 1 (-1) * T10 c = T10 (-c) * Dg 1 (-1) := by
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  simp only [Units.val_mul, T10, Dg, coe_glOf]
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem W_mul_Dg (a b : Aˣ) : W * Dg a b = Dg b a * W := by
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  simp only [Units.val_mul, W, Dg, coe_glOf]
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem Dg_mul_Dg_comm (a b : Aˣ) (g : GL (Fin 2) A) :
    g * (Dg a b * Dg b a) = Dg a b * Dg b a * g := by
  have hval : ((Dg a b : GL (Fin 2) A) : Matrix (Fin 2) (Fin 2) A) *
      ((Dg b a : GL (Fin 2) A) : Matrix (Fin 2) (Fin 2) A) =
      ((a : A) * b) • (1 : Matrix (Fin 2) (Fin 2) A) := by
    simp only [Dg, coe_glOf]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, mul_comm]
  apply Units.ext
  simp only [Units.val_mul]
  rw [hval, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, Matrix.one_mul]

theorem T01_mul_eq (g : GL (Fin 2) A) (t : A) (u : Aˣ)
    (hu : (u : A) = (g : Matrix (Fin 2) (Fin 2) A) 0 0 + t * (g : Matrix (Fin 2) (Fin 2) A) 1 0) :
    T01 t * g =
      T10 ((g : Matrix (Fin 2) (Fin 2) A) 1 0 * ↑u⁻¹) *
        Dg u (u⁻¹ * Matrix.GeneralLinearGroup.det g) *
        T01 (↑u⁻¹ * ((g : Matrix (Fin 2) (Fin 2) A) 0 1 + t * (g : Matrix (Fin 2) (Fin 2) A) 1 1)) := by
  have huv : (u : A) * ↑u⁻¹ = 1 := u.mul_inv
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  simp only [Units.val_mul, T01, T10, Dg, coe_glOf, Matrix.GeneralLinearGroup.val_det_apply,
    Matrix.det_fin_two]
  fin_cases i <;> fin_cases j <;>
    simp only [Matrix.mul_apply, Fin.sum_univ_two, Fin.zero_eta, Fin.mk_one, Fin.isValue,
      Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_fin_one, Matrix.empty_val', one_mul, zero_mul, mul_one, mul_zero,
      add_zero, zero_add]
  · exact hu.symm
  · linear_combination
      (-((g : Matrix (Fin 2) (Fin 2) A) 0 1 + t * (g : Matrix (Fin 2) (Fin 2) A) 1 1)) * huv
  · linear_combination (-((g : Matrix (Fin 2) (Fin 2) A) 1 0)) * huv
  · linear_combination
      (-((g : Matrix (Fin 2) (Fin 2) A) 1 1 +
          (g : Matrix (Fin 2) (Fin 2) A) 1 0 * ↑u⁻¹ *
            ((g : Matrix (Fin 2) (Fin 2) A) 0 1 + t * (g : Matrix (Fin 2) (Fin 2) A) 1 1))) * huv +
        (↑u⁻¹ * (g : Matrix (Fin 2) (Fin 2) A) 1 1) * hu

end Elements

section StableRange

variable {A : Type*} [CommRing A] [Finite (MaximalSpectrum A)]

theorem exists_isUnit_add_mul {a c : A}
    (h : ∀ m : MaximalSpectrum A, a ∈ m.asIdeal → c ∉ m.asIdeal) :
    ∃ t : A, IsUnit (a + t * c) := by
  classical
  have hI : Pairwise (Function.onFun IsCoprime fun m : MaximalSpectrum A => m.asIdeal) := by
    intro m m' hne
    show IsCoprime m.asIdeal m'.asIdeal
    exact Ideal.isCoprime_of_isMaximal (fun h => hne (MaximalSpectrum.ext h))
  obtain ⟨x, hx⟩ := Ideal.quotientInfToPiQuotient_surj hI
    (fun m => if a ∈ m.asIdeal then 1 else 0)
  obtain ⟨t, rfl⟩ := Ideal.Quotient.mk_surjective x
  refine ⟨t, ?_⟩
  by_contra hu
  obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal (Ideal.span {a + t * c})
    (fun h' => hu (Ideal.span_singleton_eq_top.1 h'))
  have hmem : a + t * c ∈ M := hle (Ideal.mem_span_singleton_self _)
  let m : MaximalSpectrum A := ⟨M, hM⟩
  have ht : Ideal.Quotient.mk M t = if a ∈ M then 1 else 0 := by
    have := congr_fun hx m
    rwa [Ideal.quotientInfToPiQuotient_mk'] at this
  by_cases ha : a ∈ M
  · rw [if_pos ha] at ht
    have ht1 : t - 1 ∈ M := by
      rw [← Ideal.Quotient.eq, map_one]; exact ht
    have hc : c ∈ M := by
      have e : a + t * c - a - (t - 1) * c = c := by ring
      rw [← e]
      exact M.sub_mem (M.sub_mem hmem ha) (M.mul_mem_right _ ht1)
    exact h m ha hc
  · rw [if_neg ha] at ht
    have ht0 : t ∈ M := Ideal.Quotient.eq_zero_iff_mem.1 ht
    apply ha
    have e : a + t * c - t * c = a := by ring
    rw [← e]
    exact M.sub_mem hmem (M.mul_mem_right _ ht0)

theorem not_mem_of_mem (g : GL (Fin 2) A) (m : MaximalSpectrum A)
    (ha : (g : Matrix (Fin 2) (Fin 2) A) 0 0 ∈ m.asIdeal) :
    (g : Matrix (Fin 2) (Fin 2) A) 1 0 ∉ m.asIdeal := by
  intro hc
  have hdet : (g : Matrix (Fin 2) (Fin 2) A).det ∈ m.asIdeal := by
    rw [Matrix.det_fin_two]
    exact m.asIdeal.sub_mem (m.asIdeal.mul_mem_right _ ha) (m.asIdeal.mul_mem_left _ hc)
  exact m.isMaximal.ne_top (Ideal.eq_top_of_isUnit_mem _ hdet (Matrix.isUnits_det_units g))

theorem exists_T01_mul_eq (g : GL (Fin 2) A) :
    ∃ (t x y : A) (u w : Aˣ), T01 t * g = T10 x * Dg u w * T01 y := by
  obtain ⟨t, hu⟩ := exists_isUnit_add_mul (fun m hm => not_mem_of_mem g m hm)
  exact ⟨t, _, _, hu.unit, _, T01_mul_eq g t hu.unit (by rw [IsUnit.unit_spec])⟩

end StableRange

section ModularCharacter

variable {A : Type*} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
  [LocallyCompactSpace (GL (Fin 2) A)]

noncomputable abbrev mc : GL (Fin 2) A →* NNReal := modularCharacter

theorem mc_pos (g : GL (Fin 2) A) : 0 < mc g := modularCharacterFun_pos g

theorem mc_eq_of_mul_eq_mul {x y y' : GL (Fin 2) A} (h : x * y = y' * x) : mc y = mc y' := by
  have h1 : mc x * mc y = mc y' * mc x := by rw [← map_mul, ← map_mul, h]
  rw [mul_comm (mc y') (mc x)] at h1
  exact mul_left_cancel₀ (mc_pos x).ne' h1

theorem mc_eq_one_of_forall_comm {z : GL (Fin 2) A} (hz : ∀ g : GL (Fin 2) A, g * z = z * g) :
    mc z = 1 := by
  borelize (GL (Fin 2) A)
  show modularCharacterFun z = 1
  rw [modularCharacterFun_eq_haarScalarFactor MeasureTheory.Measure.haar z]
  have hfun : (fun x : GL (Fin 2) A => x * z) = fun x => z * x := funext fun x => hz x
  have h1 : Measure.map (fun x : GL (Fin 2) A => x * z) haar = haar := by
    rw [hfun]; exact map_mul_left_eq_self haar z
  have key : ∀ (μ' : Measure (GL (Fin 2) A)) [IsFiniteMeasureOnCompacts μ']
      [IsMulLeftInvariant μ'], μ' = haar → haarScalarFactor μ' haar = 1 := by
    intro μ' _ _ h
    subst h
    exact haarScalarFactor_self _
  exact key _ h1

theorem nnreal_eq_one_of_mul_self_eq_one {a : NNReal} (h : a * a = 1) : a = 1 := by
  have h' : (a : ℝ) * a = 1 := by exact_mod_cast h
  have ha : (0 : ℝ) ≤ a := a.coe_nonneg
  have : (a : ℝ) = 1 := by nlinarith
  exact_mod_cast this

theorem mc_T01 (c : A) : mc (T01 c) = 1 := by
  apply nnreal_eq_one_of_mul_self_eq_one
  have h1 : mc (T01 c) = mc (T01 (-c)) := mc_eq_of_mul_eq_mul (N_mul_T01 c)
  calc mc (T01 c) * mc (T01 c) = mc (T01 (-c)) * mc (T01 c) := by rw [← h1]
    _ = mc (T01 (-c) * T01 c) := (map_mul _ _ _).symm
    _ = 1 := by rw [T01_mul_T01, neg_add_cancel, T01_zero, map_one]

theorem W_mul_T01 (c : A) : (W : GL (Fin 2) A) * T01 c = T10 c * W := by
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  simp only [Units.val_mul, W, T01, T10, coe_glOf]
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem mc_T10 (c : A) : mc (T10 c) = 1 := by
  rw [← mc_eq_of_mul_eq_mul (W_mul_T01 c)]; exact mc_T01 c

theorem mc_Dg (a b : Aˣ) : mc (Dg a b) = 1 := by
  apply nnreal_eq_one_of_mul_self_eq_one
  have h1 : mc (Dg a b) = mc (Dg b a) := mc_eq_of_mul_eq_mul (W_mul_Dg a b)
  calc mc (Dg a b) * mc (Dg a b) = mc (Dg a b) * mc (Dg b a) := by rw [← h1]
    _ = mc (Dg a b * Dg b a) := (map_mul _ _ _).symm
    _ = 1 := mc_eq_one_of_forall_comm (Dg_mul_Dg_comm a b)

theorem modularCharacter_eq_one [Finite (MaximalSpectrum A)] (g : GL (Fin 2) A) :
    modularCharacter g = 1 := by
  obtain ⟨t, x, y, u, w, hdec⟩ := exists_T01_mul_eq g
  have h1 : mc (T01 t * g) = 1 := by
    rw [hdec, map_mul, map_mul, mc_T10, mc_Dg, mc_T01, one_mul, one_mul]
  rw [map_mul, mc_T01, one_mul] at h1
  exact h1

end ModularCharacter

section Frame

variable (A : Type) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]

theorem secondCountableTopology_GL [SecondCountableTopology A] :
    SecondCountableTopology (GL (Fin 2) A) := by
  haveI : SecondCountableTopology (Matrix (Fin 2) (Fin 2) A) :=
    inferInstanceAs (SecondCountableTopology (Fin 2 → Fin 2 → A))
  haveI : SecondCountableTopology (Matrix (Fin 2) (Fin 2) A)ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.isInducing.secondCountableTopology
  exact Units.isEmbedding_embedProduct.isInducing.secondCountableTopology

theorem locallyCompactSpace_GL [T2Space A] [LocallyCompactSpace A] :
    LocallyCompactSpace (GL (Fin 2) A) := by
  haveI : T2Space (Matrix (Fin 2) (Fin 2) A) := inferInstanceAs (T2Space (Fin 2 → Fin 2 → A))
  haveI : LocallyCompactSpace (Matrix (Fin 2) (Fin 2) A) :=
    inferInstanceAs (LocallyCompactSpace (Fin 2 → Fin 2 → A))
  exact Units.isClosedEmbedding_embedProduct.locallyCompactSpace

theorem isMulRightInvariant [T2Space A] [LocallyCompactSpace A] [SecondCountableTopology A]
    [Finite (MaximalSpectrum A)]
    (μA : @Measure (GL (Fin 2) A) (AutomorphicForm.glBorelOf A))
    (hμA : @Measure.IsHaarMeasure (GL (Fin 2) A) _ _ (AutomorphicForm.glBorelOf A) μA) :
    @Measure.IsMulRightInvariant (GL (Fin 2) A) (AutomorphicForm.glBorelOf A) _ μA := by
  letI : MeasurableSpace (GL (Fin 2) A) := AutomorphicForm.glBorelOf A
  haveI : BorelSpace (GL (Fin 2) A) := ⟨rfl⟩
  haveI := locallyCompactSpace_GL A
  haveI := secondCountableTopology_GL A
  haveI : IsHaarMeasure μA := hμA
  refine ⟨fun g => ?_⟩
  rw [isMulLeftInvariant_eq_smul (Measure.map (· * g) μA) μA,
    ← modularCharacterFun_eq_haarScalarFactor μA g]
  have : modularCharacterFun g = 1 := modularCharacter_eq_one g
  rw [this, one_smul]

end Frame

end P2mGL2SemilocalUnimodular
p2m_reactivate "P2MW.S_AutomorphicForm_isMulRightInvariant_of_isHaarMeasure_generalLinearGroup_of_finite_maximalSpectrum.P2mGL2SemilocalUnimodular"

end
p2m_reactivate "P2MW.S_AutomorphicForm_isMulRightInvariant_of_isHaarMeasure_generalLinearGroup_of_finite_maximalSpectrum.P2mGL2SemilocalUnimodular"

theorem solution
    (A : Type) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [T2Space A]
    [LocallyCompactSpace A] [SecondCountableTopology A] [Finite (MaximalSpectrum A)]
    (μA : @MeasureTheory.Measure (GL (Fin 2) A) (AutomorphicForm.glBorelOf A))
    (hμA : @MeasureTheory.Measure.IsHaarMeasure (GL (Fin 2) A) _ _
      (AutomorphicForm.glBorelOf A) μA) :
    @MeasureTheory.Measure.IsMulRightInvariant (GL (Fin 2) A) (AutomorphicForm.glBorelOf A) _ μA :=
  P2mGL2SemilocalUnimodular.isMulRightInvariant A μA hμA

end S_AutomorphicForm_isMulRightInvariant_of_isHaarMeasure_generalLinearGroup_of_finite_maximalSpectrum
end P2MW
export P2MW.S_AutomorphicForm_isMulRightInvariant_of_isHaarMeasure_generalLinearGroup_of_finite_maximalSpectrum (solution)

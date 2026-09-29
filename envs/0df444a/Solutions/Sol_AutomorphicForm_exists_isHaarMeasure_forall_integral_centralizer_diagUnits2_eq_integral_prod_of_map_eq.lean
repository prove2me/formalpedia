-- Prove2me | solution 1 for AutomorphicForm.exists_isHaarMeasure_forall_integral_centralizer_diagUnits2_eq_integral_prod_of_map_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/01d65675-5cc3-592e-99be-f3c3adafcb09

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_LanglandsTunnell_CubicInduction_TorusValues
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_isHaarMeasure_forall_integral_centralizer_diagUnits2_eq_integral_prod_of_map_eq

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option synthInstance.maxSize 8192

open MeasureTheory NumberField IsDedekindDomain
open scoped ENNReal NNReal

attribute [local instance] AutomorphicForm.centralizerBorel

open LanglandsTunnell.CubicInduction (diagUnits2)

set_option linter.unusedSectionVars false

noncomputable section

namespace TPIN

open AutomorphicForm Topology

variable (K : Type) [Field K] [NumberField K]

scoped instance secondCountable_completion (w : InfinitePlace K) : SecondCountableTopology w.Completion :=
  (InfinitePlace.Completion.isometry_extensionEmbedding w).isEmbedding.secondCountableTopology

scoped instance secondCountable_Koo : SecondCountableTopology (InfiniteAdeleRing K) :=
  inferInstanceAs (SecondCountableTopology ((w : InfinitePlace K) → w.Completion))

scoped instance secondCountable_units : SecondCountableTopology (InfiniteAdeleRing K)ˣ := by
  haveI : SecondCountableTopology (InfiniteAdeleRing K)ᵐᵒᵖ := MulOpposite.opHomeomorph.symm.secondCountableTopology
  exact Units.isEmbedding_embedProduct.secondCountableTopology

scoped instance locallyCompact_units : LocallyCompactSpace (InfiniteAdeleRing K)ˣ :=
  Units.isClosedEmbedding_embedProduct.locallyCompactSpace

scoped instance secondCountable_GL : SecondCountableTopology (GL (Fin 2) (InfiniteAdeleRing K)) := by
  haveI : SecondCountableTopology (Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K)) :=
    inferInstanceAs (SecondCountableTopology (Fin 2 → Fin 2 → InfiniteAdeleRing K))
  haveI : SecondCountableTopology (Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K))ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.secondCountableTopology
  exact Units.isEmbedding_embedProduct.secondCountableTopology

scoped instance locallyCompact_GL : LocallyCompactSpace (GL (Fin 2) (InfiniteAdeleRing K)) := by
  haveI : LocallyCompactSpace (Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K)) :=
    inferInstanceAs (LocallyCompactSpace (Fin 2 → Fin 2 → InfiniteAdeleRing K))
  haveI : LocallyCompactSpace (Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K))ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.isClosedEmbedding.locallyCompactSpace
  exact Units.isClosedEmbedding_embedProduct.locallyCompactSpace

abbrev Cent (p q : (InfiniteAdeleRing K)ˣ) : Subgroup (GL (Fin 2) (InfiniteAdeleRing K)) :=
  Subgroup.centralizer ({diagUnits2 p q} : Set (GL (Fin 2) (InfiniteAdeleRing K)))

scoped instance borelSpace_Cent (p q : (InfiniteAdeleRing K)ˣ) : BorelSpace (Cent K p q) := ⟨rfl⟩

theorem isUnit_sub_of_isRegularSemisimple (p q : (InfiniteAdeleRing K)ˣ)
    (h : AutomorphicForm.IsRegularSemisimple (diagUnits2 p q)) :
    IsUnit ((p : InfiniteAdeleRing K) - (q : InfiniteAdeleRing K)) := by
  unfold AutomorphicForm.IsRegularSemisimple at h
  rw [LanglandsTunnell.CubicInduction.coe_diagUnits2, Matrix.trace_fin_two_of, Matrix.det_fin_two_of] at h
  have e : ((p : InfiniteAdeleRing K) + (q : InfiniteAdeleRing K)) ^ 2 - 4 * ((p : InfiniteAdeleRing K) * q - 0 * 0) =
      ((p : InfiniteAdeleRing K) - q) ^ 2 := by ring
  rw [e, isUnit_pow_iff two_ne_zero] at h
  exact h

theorem mem_Cent_iff {p q : (InfiniteAdeleRing K)ˣ} (hpq : IsUnit ((p : InfiniteAdeleRing K) - (q : InfiniteAdeleRing K)))
    (x : GL (Fin 2) (InfiniteAdeleRing K)) :
    x ∈ Cent K p q ↔ ((x : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K)) 0 1 = 0 ∧
      (x : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K)) 1 0 = 0) := by
  rw [Cent, Subgroup.mem_centralizer_iff]
  simp only [Set.mem_singleton_iff, forall_eq]
  obtain ⟨u, hu⟩ := hpq
  constructor
  · intro h
    have h' := congrArg (fun g : GL (Fin 2) (InfiniteAdeleRing K) => (g : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K))) h
    simp only [Units.val_mul, LanglandsTunnell.CubicInduction.coe_diagUnits2] at h'
    have h01 := congrFun (congrFun h' 0) 1
    have h10 := congrFun (congrFun h' 1) 0
    simp [Matrix.mul_apply, Fin.sum_univ_two] at h01 h10

    constructor
    · have : ((p : InfiniteAdeleRing K) - q) * (x : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K)) 0 1 = 0 := by
        linear_combination h01
      rw [← hu] at this
      exact (Units.mul_right_eq_zero u).mp this
    · have : ((p : InfiniteAdeleRing K) - q) * (x : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K)) 1 0 = 0 := by
        linear_combination (-1 : InfiniteAdeleRing K) * h10
      rw [← hu] at this
      exact (Units.mul_right_eq_zero u).mp this
  · rintro ⟨h01, h10⟩
    apply Units.ext
    simp only [Units.val_mul, LanglandsTunnell.CubicInduction.coe_diagUnits2]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, h01, h10, mul_comm]

theorem diagUnits2_mem_Cent (p q : (InfiniteAdeleRing K)ˣ) (r : (InfiniteAdeleRing K)ˣ × (InfiniteAdeleRing K)ˣ) :
    (diagUnits2 r.1 r.2 : GL (Fin 2) (InfiniteAdeleRing K)) ∈ Cent K p q := by
  rw [Cent, Subgroup.mem_centralizer_iff]
  simp only [Set.mem_singleton_iff, forall_eq]
  apply Units.ext
  simp only [Units.val_mul, LanglandsTunnell.CubicInduction.coe_diagUnits2]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, mul_comm]

def e00 {p q : (InfiniteAdeleRing K)ˣ} (hpq : IsUnit ((p : InfiniteAdeleRing K) - (q : InfiniteAdeleRing K)))
    (x : Cent K p q) : (InfiniteAdeleRing K)ˣ where
  val := ((x : GL (Fin 2) (InfiniteAdeleRing K)) : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K)) 0 0
  inv := (((x : GL (Fin 2) (InfiniteAdeleRing K))⁻¹ : GL (Fin 2) (InfiniteAdeleRing K)) :
    Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K)) 0 0
  val_inv := by
    have hx := (mem_Cent_iff K hpq _).mp x.2
    have h := congrFun (congrFun (Units.mul_inv (x : GL (Fin 2) (InfiniteAdeleRing K))) 0) 0
    rw [Matrix.mul_apply, Fin.sum_univ_two, hx.1, zero_mul, add_zero] at h
    rw [h]; rfl
  inv_val := by
    have hx := (mem_Cent_iff K hpq _).mp x.2
    have h := congrFun (congrFun (Units.inv_mul (x : GL (Fin 2) (InfiniteAdeleRing K))) 0) 0
    have hx' := (mem_Cent_iff K hpq _).mp (x⁻¹).2
    rw [Matrix.mul_apply, Fin.sum_univ_two] at h
    have : (((x⁻¹ : Cent K p q) : GL (Fin 2) (InfiniteAdeleRing K)) : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K)) 0 1 = 0 := hx'.1
    have e2 : (((x : GL (Fin 2) (InfiniteAdeleRing K))⁻¹ : GL (Fin 2) (InfiniteAdeleRing K)) :
        Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K)) 0 1 = 0 := this
    rw [e2, zero_mul, add_zero] at h
    rw [h]; rfl

def e11 {p q : (InfiniteAdeleRing K)ˣ} (hpq : IsUnit ((p : InfiniteAdeleRing K) - (q : InfiniteAdeleRing K)))
    (x : Cent K p q) : (InfiniteAdeleRing K)ˣ where
  val := ((x : GL (Fin 2) (InfiniteAdeleRing K)) : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K)) 1 1
  inv := (((x : GL (Fin 2) (InfiniteAdeleRing K))⁻¹ : GL (Fin 2) (InfiniteAdeleRing K)) :
    Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K)) 1 1
  val_inv := by
    have hx := (mem_Cent_iff K hpq _).mp x.2
    have h := congrFun (congrFun (Units.mul_inv (x : GL (Fin 2) (InfiniteAdeleRing K))) 1) 1
    rw [Matrix.mul_apply, Fin.sum_univ_two, hx.2, zero_mul, zero_add] at h
    rw [h]; rfl
  inv_val := by
    have h := congrFun (congrFun (Units.inv_mul (x : GL (Fin 2) (InfiniteAdeleRing K))) 1) 1
    have hx' := (mem_Cent_iff K hpq _).mp (x⁻¹).2
    rw [Matrix.mul_apply, Fin.sum_univ_two] at h
    have e2 : (((x : GL (Fin 2) (InfiniteAdeleRing K))⁻¹ : GL (Fin 2) (InfiniteAdeleRing K)) :
        Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K)) 1 0 = 0 := hx'.2
    rw [e2, zero_mul, zero_add] at h
    rw [h]; rfl

def phi {p q : (InfiniteAdeleRing K)ˣ} (hpq : IsUnit ((p : InfiniteAdeleRing K) - (q : InfiniteAdeleRing K))) :
    ((InfiniteAdeleRing K)ˣ × (InfiniteAdeleRing K)ˣ) ≃* Cent K p q where
  toFun r := ⟨diagUnits2 r.1 r.2, diagUnits2_mem_Cent K p q r⟩
  invFun x := (e00 K hpq x, e11 K hpq x)
  left_inv r := by
    apply Prod.ext
    · apply Units.ext
      show (((diagUnits2 r.1 r.2 : GL (Fin 2) (InfiniteAdeleRing K))) : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K)) 0 0 = _
      simp [LanglandsTunnell.CubicInduction.coe_diagUnits2]
    · apply Units.ext
      show (((diagUnits2 r.1 r.2 : GL (Fin 2) (InfiniteAdeleRing K))) : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K)) 1 1 = _
      simp [LanglandsTunnell.CubicInduction.coe_diagUnits2]
  right_inv x := by
    have hx := (mem_Cent_iff K hpq _).mp x.2
    apply Subtype.ext
    apply Units.ext
    simp only [LanglandsTunnell.CubicInduction.coe_diagUnits2]
    ext i j
    fin_cases i <;> fin_cases j
    · rfl
    · simp [hx.1]
    · simp [hx.2]
    · rfl
  map_mul' r r' := by
    apply Subtype.ext
    show (diagUnits2 (r.1 * r'.1) (r.2 * r'.2) : GL (Fin 2) (InfiniteAdeleRing K)) = diagUnits2 r.1 r.2 * diagUnits2 r'.1 r'.2
    apply Units.ext
    simp only [Units.val_mul, LanglandsTunnell.CubicInduction.coe_diagUnits2]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem diagUnits2_val (a b : (InfiniteAdeleRing K)ˣ) :
    ((diagUnits2 a b : GL (Fin 2) (InfiniteAdeleRing K)) : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K)) =
      Matrix.diagonal ![(a : InfiniteAdeleRing K), (b : InfiniteAdeleRing K)] := by
  rw [LanglandsTunnell.CubicInduction.coe_diagUnits2]
  ext i j; fin_cases i <;> fin_cases j <;> rfl

theorem diagUnits2_val' (a b : (InfiniteAdeleRing K)ˣ) :
    ((diagUnits2 a b : GL (Fin 2) (InfiniteAdeleRing K)) : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K)) =
      !![(a : InfiniteAdeleRing K), 0; 0, (b : InfiniteAdeleRing K)] := by
  rw [diagUnits2_val]
  ext i j; fin_cases i <;> fin_cases j <;> simp

theorem continuous_diagUnits2 :
    Continuous (fun p : (InfiniteAdeleRing K)ˣ × (InfiniteAdeleRing K)ˣ => (diagUnits2 p.1 p.2 : GL (Fin 2) (InfiniteAdeleRing K))) := by
  have hval : Continuous fun p : (InfiniteAdeleRing K)ˣ × (InfiniteAdeleRing K)ˣ =>
      ((diagUnits2 p.1 p.2 : GL (Fin 2) (InfiniteAdeleRing K)) : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K)) := by
    simp_rw [diagUnits2_val]
    refine (continuous_pi fun i => ?_).matrix_diagonal
    fin_cases i
    · exact Units.continuous_val.comp continuous_fst
    · exact Units.continuous_val.comp continuous_snd
  refine Units.continuous_iff.mpr ⟨hval, ?_⟩
  have : ∀ p : (InfiniteAdeleRing K)ˣ × (InfiniteAdeleRing K)ˣ,
      (diagUnits2 p.1 p.2 : GL (Fin 2) (InfiniteAdeleRing K))⁻¹ = diagUnits2 p⁻¹.1 p⁻¹.2 := by
    intro p
    rw [inv_eq_iff_mul_eq_one]
    apply Units.ext
    rw [Units.val_mul, diagUnits2_val, diagUnits2_val, Matrix.diagonal_mul_diagonal, Units.val_one]
    ext i j; fin_cases i <;> fin_cases j <;> simp
  simp_rw [this]
  exact hval.comp continuous_inv

theorem continuous_phi {p q : (InfiniteAdeleRing K)ˣ} (hpq : IsUnit ((p : InfiniteAdeleRing K) - (q : InfiniteAdeleRing K))) :
    Continuous (phi K hpq) :=
  (continuous_diagUnits2 K).subtype_mk _

theorem continuous_phi_symm {p q : (InfiniteAdeleRing K)ˣ} (hpq : IsUnit ((p : InfiniteAdeleRing K) - (q : InfiniteAdeleRing K))) :
    Continuous (phi K hpq).symm := by
  have hc : Continuous fun x : Cent K p q => ((x : GL (Fin 2) (InfiniteAdeleRing K)) : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K)) :=
    Units.continuous_val.comp continuous_subtype_val
  have hci : Continuous fun x : Cent K p q =>
      (((x : GL (Fin 2) (InfiniteAdeleRing K))⁻¹ : GL (Fin 2) (InfiniteAdeleRing K)) : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K)) :=
    Units.continuous_coe_inv.comp continuous_subtype_val
  show Continuous fun x : Cent K p q => (e00 K hpq x, e11 K hpq x)
  refine Continuous.prodMk ?_ ?_
  · exact Units.continuous_iff.mpr ⟨hc.matrix_elem 0 0, hci.matrix_elem 0 0⟩
  · exact Units.continuous_iff.mpr ⟨hc.matrix_elem 1 1, hci.matrix_elem 1 1⟩

def psi {p q : (InfiniteAdeleRing K)ˣ} (hpq : IsUnit ((p : InfiniteAdeleRing K) - (q : InfiniteAdeleRing K))) :
    ((InfiniteAdeleRing K)ˣ × (InfiniteAdeleRing K)ˣ) ≃ₜ Cent K p q :=
  { toEquiv := (phi K hpq).toEquiv
    continuous_toFun := continuous_phi K hpq
    continuous_invFun := continuous_phi_symm K hpq }

def Ent (p q : (InfiniteAdeleRing K)ˣ) (x : Cent K p q) : InfiniteAdeleRing K × InfiniteAdeleRing K :=
  ((((x : GL (Fin 2) (InfiniteAdeleRing K)) : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K)) 0 0,
    ((x : GL (Fin 2) (InfiniteAdeleRing K)) : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K)) 1 1))

def iota2 (r : (InfiniteAdeleRing K)ˣ × (InfiniteAdeleRing K)ˣ) : InfiniteAdeleRing K × InfiniteAdeleRing K :=
  ((r.1 : InfiniteAdeleRing K), (r.2 : InfiniteAdeleRing K))

theorem Ent_comp_psi {p q : (InfiniteAdeleRing K)ˣ} (hpq : IsUnit ((p : InfiniteAdeleRing K) - (q : InfiniteAdeleRing K))) :
    (Ent K p q) ∘ (psi K hpq) = iota2 K := by
  funext r
  simp [Ent, psi, phi, iota2, LanglandsTunnell.CubicInduction.coe_diagUnits2]

theorem continuous_iota2 : Continuous (iota2 K) :=
  (Units.continuous_val.comp continuous_fst).prodMk (Units.continuous_val.comp continuous_snd)

theorem injective_iota2 : Function.Injective (iota2 K) := by
  intro r r' h
  simp only [iota2, Prod.mk.injEq] at h
  exact Prod.ext (Units.ext h.1) (Units.ext h.2)

section Haar

variable [MeasurableSpace (InfiniteAdeleRing K)] [BorelSpace (InfiniteAdeleRing K)]
  [MeasurableSpace (InfiniteAdeleRing K)ˣ] [BorelSpace (InfiniteAdeleRing K)ˣ]

theorem key {p q : (InfiniteAdeleRing K)ˣ} (hpq : IsUnit ((p : InfiniteAdeleRing K) - (q : InfiniteAdeleRing K)))
    (ρ₀ : Measure (InfiniteAdeleRing K)ˣ) [ρ₀.IsHaarMeasure]
    (τ : Measure (Cent K p q)) [τ.IsHaarMeasure] :
    ∃ c : ℝ≥0, τ = Measure.map (psi K hpq) ((c : ℝ≥0∞) • ρ₀.prod ρ₀) := by
  set τ' : Measure ((InfiniteAdeleRing K)ˣ × (InfiniteAdeleRing K)ˣ) := Measure.map (phi K hpq).symm τ with hτ'
  haveI : τ'.IsHaarMeasure := (phi K hpq).symm.isHaarMeasure_map τ (continuous_phi_symm K hpq) (continuous_phi K hpq)
  obtain ⟨c, h1⟩ : ∃ c : ℝ≥0, τ' = (c : ℝ≥0∞) • ρ₀.prod ρ₀ :=
    ⟨Measure.haarScalarFactor τ' (ρ₀.prod ρ₀), Measure.isMulLeftInvariant_eq_smul τ' (ρ₀.prod ρ₀)⟩
  refine ⟨c, ?_⟩
  have h2 : τ = Measure.map (psi K hpq).toMeasurableEquiv τ' := by
    have : ((phi K hpq).symm : Cent K p q → (InfiniteAdeleRing K)ˣ × (InfiniteAdeleRing K)ˣ) =
        (psi K hpq).toMeasurableEquiv.symm := rfl
    rw [hτ', this, MeasurableEquiv.map_map_symm]
  rw [h2, h1, Homeomorph.toMeasurableEquiv_coe]

end Haar

end TPIN
p2m_reactivate "P2MW.S_AutomorphicForm_exists_isHaarMeasure_forall_integral_centralizer_diagUnits2_eq_integral_prod_of_map_eq.TPIN"

end
p2m_reactivate "P2MW.S_AutomorphicForm_exists_isHaarMeasure_forall_integral_centralizer_diagUnits2_eq_integral_prod_of_map_eq.TPIN"

theorem solution
    (K : Type) [Field K] [NumberField K]
    [MeasurableSpace (InfiniteAdeleRing K)] [BorelSpace (InfiniteAdeleRing K)]
    [MeasurableSpace (InfiniteAdeleRing K)ˣ] [BorelSpace (InfiniteAdeleRing K)ˣ]
    (τ₀ : Measure (InfiniteAdeleRing K × InfiniteAdeleRing K)) :
    ∃ ρ : Measure (InfiniteAdeleRing K)ˣ, ρ.IsHaarMeasure ∧
      ∀ (p q : (InfiniteAdeleRing K)ˣ), AutomorphicForm.IsRegularSemisimple (diagUnits2 p q) →
      ∀ (τ : Measure (Subgroup.centralizer ({diagUnits2 p q} : Set (GL (Fin 2) (InfiniteAdeleRing K))))),
        τ.IsHaarMeasure →
        Measure.map
            (fun x : Subgroup.centralizer ({diagUnits2 p q} : Set (GL (Fin 2) (InfiniteAdeleRing K))) =>
              ((((x : GL (Fin 2) (InfiniteAdeleRing K)) : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K)) 0 0,
                ((x : GL (Fin 2) (InfiniteAdeleRing K)) : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K)) 1 1) :
                InfiniteAdeleRing K × InfiniteAdeleRing K))
            τ = τ₀ →
      ∀ g : GL (Fin 2) (InfiniteAdeleRing K) → ℂ,
        ∫ x, g (x : GL (Fin 2) (InfiniteAdeleRing K)) ∂τ =
          ∫ r : (InfiniteAdeleRing K)ˣ × (InfiniteAdeleRing K)ˣ, g (diagUnits2 r.1 r.2) ∂(ρ.prod ρ) := by
  classical
  haveI : ∀ (p q : (InfiniteAdeleRing K)ˣ), BorelSpace (TPIN.Cent K p q) := fun p q => ⟨rfl⟩
  set ρ₀ : Measure (InfiniteAdeleRing K)ˣ := Measure.haar with hρ₀

  set m : Measure (InfiniteAdeleRing K × InfiniteAdeleRing K) := Measure.map (TPIN.iota2 K) (ρ₀.prod ρ₀) with hm

  obtain ⟨K₀⟩ : Nonempty (TopologicalSpace.PositiveCompacts (InfiniteAdeleRing K)ˣ) := inferInstance
  have hS : m (TPIN.iota2 K '' ((K₀ : Set (InfiniteAdeleRing K)ˣ) ×ˢ (K₀ : Set (InfiniteAdeleRing K)ˣ))) =
      ρ₀ K₀ * ρ₀ K₀ := by
    rw [hm, Measure.map_apply (TPIN.continuous_iota2 K).measurable
      (((K₀.isCompact.prod K₀.isCompact).image (TPIN.continuous_iota2 K)).measurableSet),
      Set.preimage_image_eq _ (TPIN.injective_iota2 K), Measure.prod_prod]
  have hS0 : m (TPIN.iota2 K '' ((K₀ : Set (InfiniteAdeleRing K)ˣ) ×ˢ (K₀ : Set (InfiniteAdeleRing K)ˣ))) ≠ 0 := by
    rw [hS]; exact mul_ne_zero (Measure.measure_pos_of_nonempty_interior ρ₀ K₀.interior_nonempty).ne' (Measure.measure_pos_of_nonempty_interior ρ₀ K₀.interior_nonempty).ne'
  have hStop : m (TPIN.iota2 K '' ((K₀ : Set (InfiniteAdeleRing K)ˣ) ×ˢ (K₀ : Set (InfiniteAdeleRing K)ˣ))) ≠ ∞ := by
    rw [hS]; exact ENNReal.mul_ne_top K₀.isCompact.measure_lt_top.ne K₀.isCompact.measure_lt_top.ne

  have hpush : ∀ (p q : (InfiniteAdeleRing K)ˣ) (hpq : IsUnit ((p : InfiniteAdeleRing K) - (q : InfiniteAdeleRing K)))
      (c : ℝ≥0),
      Measure.map (TPIN.Ent K p q) (Measure.map (TPIN.psi K hpq) ((c : ℝ≥0∞) • ρ₀.prod ρ₀)) = (c : ℝ≥0∞) • m := by
    intro p q hpq c
    have hEm : Measurable (TPIN.Ent K p q) :=
      ((((Units.continuous_val.comp continuous_subtype_val).matrix_elem 0 0).prodMk
        ((Units.continuous_val.comp continuous_subtype_val).matrix_elem 1 1)) :
          Continuous (TPIN.Ent K p q)).measurable
    rw [Measure.map_map hEm (TPIN.psi K hpq).continuous.measurable, TPIN.Ent_comp_psi, Measure.map_smul, hm]
  by_cases hex : ∃ (p q : (InfiniteAdeleRing K)ˣ) (τ : Measure (TPIN.Cent K p q)),
      AutomorphicForm.IsRegularSemisimple (diagUnits2 p q) ∧ τ.IsHaarMeasure ∧
        Measure.map (TPIN.Ent K p q) τ = τ₀
  · obtain ⟨p₁, q₁, τ₁, hreg₁, hH₁, hE₁⟩ := hex
    change Measure.map (TPIN.Ent K p₁ q₁) τ₁ = τ₀ at hE₁
    haveI := hH₁
    have hpq₁ := TPIN.isUnit_sub_of_isRegularSemisimple K p₁ q₁ hreg₁
    obtain ⟨c₁, hc₁⟩ := TPIN.key K hpq₁ ρ₀ τ₁
    have hτ₀ : τ₀ = (c₁ : ℝ≥0∞) • m := by rw [← hE₁, hc₁, hpush]
    have hc₁0 : (c₁ : ℝ≥0∞) ≠ 0 := by
      intro h0
      have : τ₁ = 0 := by rw [hc₁, h0, zero_smul, Measure.map_zero]
      exact (IsOpen.measure_ne_zero τ₁ isOpen_univ Set.univ_nonempty) (by rw [this]; rfl)
    refine ⟨(NNReal.sqrt c₁ : ℝ≥0) • ρ₀, ?_, ?_⟩
    · exact Measure.IsHaarMeasure.nnreal_smul ρ₀ (NNReal.sqrt_pos.mpr (pos_iff_ne_zero.mpr (by exact_mod_cast hc₁0))).ne'
    intro p q hreg τ hτ hE g
    haveI := hτ
    change Measure.map (TPIN.Ent K p q) τ = τ₀ at hE
    have hpq := TPIN.isUnit_sub_of_isRegularSemisimple K p q hreg
    obtain ⟨c, hc⟩ := TPIN.key K hpq ρ₀ τ

    have hcc : (c : ℝ≥0∞) = c₁ := by
      have h := hE
      rw [hc, hpush, hτ₀] at h
      have h' := congrArg (fun μ : Measure (InfiniteAdeleRing K × InfiniteAdeleRing K) =>
        μ (TPIN.iota2 K '' ((K₀ : Set (InfiniteAdeleRing K)ˣ) ×ˢ (K₀ : Set (InfiniteAdeleRing K)ˣ)))) h
      simp only [Measure.smul_apply, smul_eq_mul] at h'
      exact (ENNReal.mul_left_inj hS0 hStop).mp h'
    have hprod : (((NNReal.sqrt c₁ : ℝ≥0) • ρ₀).prod ((NNReal.sqrt c₁ : ℝ≥0) • ρ₀)) =
        (c₁ : ℝ≥0∞) • ρ₀.prod ρ₀ := by
      have e : ((NNReal.sqrt c₁ : ℝ≥0) • ρ₀) = ((NNReal.sqrt c₁ : ℝ≥0) : ℝ≥0∞) • ρ₀ := rfl
      rw [e, Measure.prod_smul_left, Measure.prod_smul_right, smul_smul, ← ENNReal.coe_mul, NNReal.mul_self_sqrt]
    rw [hprod, hc, hcc]
    rw [show (TPIN.psi K hpq : (InfiniteAdeleRing K)ˣ × (InfiniteAdeleRing K)ˣ → TPIN.Cent K p q) =
      (TPIN.psi K hpq).toMeasurableEquiv from (Homeomorph.toMeasurableEquiv_coe _).symm,
      integral_map_equiv]
    rfl
  · refine ⟨ρ₀, inferInstance, ?_⟩
    intro p q hreg τ hτ hE g
    exact absurd ⟨p, q, τ, hreg, hτ, hE⟩ hex

end S_AutomorphicForm_exists_isHaarMeasure_forall_integral_centralizer_diagUnits2_eq_integral_prod_of_map_eq
end P2MW
export P2MW.S_AutomorphicForm_exists_isHaarMeasure_forall_integral_centralizer_diagUnits2_eq_integral_prod_of_map_eq (solution)

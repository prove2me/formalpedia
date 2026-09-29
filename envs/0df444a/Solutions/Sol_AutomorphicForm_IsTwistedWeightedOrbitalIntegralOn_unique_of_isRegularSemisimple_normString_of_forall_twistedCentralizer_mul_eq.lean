-- Prove2me | solution 1 for AutomorphicForm.IsTwistedWeightedOrbitalIntegralOn.unique_of_isRegularSemisimple_normString_of_forall_twistedCentralizer_mul_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/f25aa271-0b35-5db9-8061-13cf056fa7ef

import Definitions.Def_AutomorphicForm_WeightedOrbitalRelation
import Theorems.Thm_MeasureTheory_integral_mul_eq_integral_mul_of_integral_subgroup_translate_eq_one
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_IsTwistedWeightedOrbitalIntegralOn_unique_of_isRegularSemisimple_normString_of_forall_twistedCentralizer_mul_eq

set_option autoImplicit false
set_option linter.unusedSectionVars false

open MeasureTheory TopologicalSpace
open scoped TensorProduct TensorProduct.RightActions

namespace P2mTwistedWeightedOrbitalUnique

section Algebra

variable {A : Type*} [CommRing A]

theorem entries_of_commute (g X : Matrix (Fin 2) (Fin 2) A) (h : X * g = g * X) (u : A)
    (hu : u * ((g 0 0 - g 1 1) ^ 2 + 4 * g 0 1 * g 1 0) = 1) :
    X 0 1 = u * (4 * g 1 0 * X 0 1 + (g 0 0 - g 1 1) * (X 0 0 - X 1 1)) * g 0 1 ∧
    X 1 0 = u * (4 * g 1 0 * X 0 1 + (g 0 0 - g 1 1) * (X 0 0 - X 1 1)) * g 1 0 ∧
    X 0 0 - X 1 1 = u * (4 * g 1 0 * X 0 1 + (g 0 0 - g 1 1) * (X 0 0 - X 1 1)) * (g 0 0 - g 1 1) := by
  have e00 := congr_fun (congr_fun h 0) 0
  have e01 := congr_fun (congr_fun h 0) 1
  have e10 := congr_fun (congr_fun h 1) 0
  simp only [Matrix.mul_apply, Fin.sum_univ_two] at e00 e01 e10
  refine ⟨?_, ?_, ?_⟩
  · linear_combination (-(X 0 1)) * hu + (-(u * (g 0 0 - g 1 1))) * e01
  · linear_combination (-(X 1 0)) * hu + (u * (g 0 0 - g 1 1)) * e10 +
      (-(4 * u * g 1 0)) * e00
  · linear_combination (-(X 0 0 - X 1 1)) * hu + (4 * u * g 1 0) * e01

theorem mul_comm_of_mem_centralizer {γ : GL (Fin 2) A} (hγ : AutomorphicForm.IsRegularSemisimple γ)
    {s t : GL (Fin 2) A} (hs : s ∈ Subgroup.centralizer ({γ} : Set (GL (Fin 2) A)))
    (ht : t ∈ Subgroup.centralizer ({γ} : Set (GL (Fin 2) A))) : s * t = t * s := by
  rw [Subgroup.mem_centralizer_singleton_iff] at hs ht
  obtain ⟨u, hu⟩ := IsUnit.exists_left_inv hγ
  set g : Matrix (Fin 2) (Fin 2) A := (γ : Matrix (Fin 2) (Fin 2) A) with hg
  have hu' : u * ((g 0 0 - g 1 1) ^ 2 + 4 * g 0 1 * g 1 0) = 1 := by
    rw [Matrix.trace_fin_two, Matrix.det_fin_two] at hu
    linear_combination hu
  have hsX : (s : Matrix (Fin 2) (Fin 2) A) * g = g * s := by
    simpa [hg] using congrArg Units.val hs
  have htX : (t : Matrix (Fin 2) (Fin 2) A) * g = g * t := by
    simpa [hg] using congrArg Units.val ht
  obtain ⟨a1, a2, a3⟩ := entries_of_commute g s hsX u hu'
  obtain ⟨b1, b2, b3⟩ := entries_of_commute g t htX u hu'
  set X : Matrix (Fin 2) (Fin 2) A := (s : Matrix (Fin 2) (Fin 2) A)
  set Y : Matrix (Fin 2) (Fin 2) A := (t : Matrix (Fin 2) (Fin 2) A)
  set p := u * (4 * g 1 0 * X 0 1 + (g 0 0 - g 1 1) * (X 0 0 - X 1 1))
  set q := u * (4 * g 1 0 * Y 0 1 + (g 0 0 - g 1 1) * (Y 0 0 - Y 1 1))
  apply Units.ext
  change X * Y = Y * X
  ext i j
  fin_cases i <;> fin_cases j <;> simp only [Matrix.mul_apply, Fin.sum_univ_two, Fin.zero_eta,
    Fin.mk_one]
  · linear_combination (Y 1 0) * a1 + (p * g 0 1) * b2 - (X 1 0) * b1 - (q * g 0 1) * a2
  · linear_combination (X 0 0 - X 1 1) * b1 + (q * g 0 1) * a3 - (Y 0 0 - Y 1 1) * a1 -
      (p * g 0 1) * b3
  · linear_combination (Y 0 0 - Y 1 1) * a2 + (p * g 1 0) * b3 - (X 0 0 - X 1 1) * b2 -
      (q * g 1 0) * a3
  · linear_combination (Y 0 1) * a2 + (p * g 1 0) * b1 - (X 0 1) * b2 - (q * g 1 0) * a1

end Algebra

section Twist

variable (K L : Type) [Field K] [Field L] [Algebra K L] (A : Type) [CommRing A] [Algebra K A]
  (σ : L ≃ₐ[K] L)

theorem sigmaTensor_iterate (k : ℕ) (y : L ⊗[K] A) :
    (AutomorphicForm.sigmaTensor K L A σ)^[k] y =
      Algebra.TensorProduct.map (σ ^ k).toAlgHom (AlgHom.id K A) y := by
  induction k generalizing y with
  | zero =>
      simp only [Function.iterate_zero, id_eq, pow_zero]
      induction y using TensorProduct.induction_on with
      | zero => simp
      | tmul a b => simp [Algebra.TensorProduct.map_tmul]
      | add x y hx hy => rw [map_add, ← hx, ← hy]
  | succ k ih =>
      rw [Function.iterate_succ_apply', ih]
      induction y using TensorProduct.induction_on with
      | zero => simp
      | tmul a b =>
          simp [AutomorphicForm.sigmaTensor, Algebra.TensorProduct.map_tmul, pow_succ',
            AlgEquiv.mul_apply]
      | add x y hx hy => rw [map_add, map_add, hx, hy, map_add]

theorem sigmaGL_iterate_finrank (hσ : σ ^ Module.finrank K L = 1) (x : GL (Fin 2) (L ⊗[K] A)) :
    (AutomorphicForm.sigmaGL K L A σ)^[Module.finrank K L] x = x := by
  have hentry : ∀ (k : ℕ) (x : GL (Fin 2) (L ⊗[K] A)) (i j : Fin 2),
      ((AutomorphicForm.sigmaGL K L A σ)^[k] x) i j = (AutomorphicForm.sigmaTensor K L A σ)^[k] (x i j) := by
    intro k
    induction k with
    | zero => intro x i j; rfl
    | succ k ih =>
        intro x i j
        rw [Function.iterate_succ_apply', Function.iterate_succ_apply', AutomorphicForm.sigmaGL,
          Matrix.GeneralLinearGroup.map_apply, ← AutomorphicForm.sigmaGL, ih]
  apply Units.ext
  ext i j
  rw [hentry, sigmaTensor_iterate, hσ]
  induction (x i j) using TensorProduct.induction_on with
  | zero => simp
  | tmul a b => simp [Algebra.TensorProduct.map_tmul]
  | add x y hx hy => rw [map_add, hx, hy]

theorem twistedCentralizer_le_centralizer_normString (hσ : σ ^ Module.finrank K L = 1)
    (δ : GL (Fin 2) (L ⊗[K] A)) :
    AutomorphicForm.twistedCentralizer K L A σ δ ≤
      Subgroup.centralizer ({AutomorphicForm.normString K L A σ δ} : Set (GL (Fin 2) (L ⊗[K] A))) := by
  intro t ht
  set s := AutomorphicForm.sigmaGL K L A σ with hs
  have htδ : t * δ = δ * s t := by
    have h := (AutomorphicForm.mem_sigmaCentralizer_iff).1 ht
    rw [← hs] at h
    exact mul_inv_eq_iff_eq_mul.1 h
  have hmul : ∀ (k : ℕ) (x y : GL (Fin 2) (L ⊗[K] A)), s^[k] (x * y) = s^[k] x * s^[k] y := by
    intro k
    induction k with
    | zero => intro x y; rfl
    | succ k ih => intro x y; simp only [Function.iterate_succ_apply', ih, map_mul]

  have hP : ∀ k : ℕ, t * ((List.range k).map fun i => s^[i] δ).prod =
      ((List.range k).map fun i => s^[i] δ).prod * s^[k] t := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
        rw [List.range_succ, List.map_append, List.prod_append, List.map_singleton,
          List.prod_singleton, ← mul_assoc, ih, mul_assoc, mul_assoc]
        congr 1
        have h1 : s^[k] t * s^[k] δ = s^[k] (t * δ) := (hmul k t δ).symm
        rw [h1, htδ, hmul, ← Function.iterate_succ_apply s k t]
  rw [Subgroup.mem_centralizer_singleton_iff]
  have h := hP (Module.finrank K L)
  rw [sigmaGL_iterate_finrank K L A σ hσ] at h
  exact h

end Twist

section Topology

variable (A : Type) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]

theorem t2Space_GL [T2Space A] : T2Space (GL (Fin 2) A) := by
  haveI : T2Space (Matrix (Fin 2) (Fin 2) A) := inferInstanceAs (T2Space (Fin 2 → Fin 2 → A))
  exact Units.isEmbedding_embedProduct.t2Space

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

theorem isInvInvariant_of_comm [T2Space A] [LocallyCompactSpace A] [SecondCountableTopology A]
    (T : Subgroup (GL (Fin 2) A)) (hT : IsClosed (T : Set (GL (Fin 2) A)))
    (hcomm : ∀ s t : T, s * t = t * s) [MeasurableSpace T] [BorelSpace T]
    (τ : Measure T) [τ.IsHaarMeasure] : τ.IsInvInvariant := by
  haveI := t2Space_GL A
  haveI := secondCountableTopology_GL A
  haveI := locallyCompactSpace_GL A
  letI : CommGroup T := { mul_comm := hcomm }
  haveI : LocallyCompactSpace T := hT.isClosedEmbedding_subtypeVal.locallyCompactSpace
  haveI : SecondCountableTopology T :=
    (Topology.IsInducing.subtypeVal : Topology.IsInducing (Subtype.val : T → GL (Fin 2) A)).secondCountableTopology
  haveI : PseudoMetrizableSpace T := PseudoMetrizableSpace.of_regularSpace_secondCountableTopology T
  haveI : SigmaCompactSpace T := sigmaCompactSpace_of_locallyCompact_secondCountable
  haveI : τ.InnerRegular := inferInstance
  exact Measure.IsHaarMeasure.isInvInvariant_of_innerRegular τ

end Topology

section TensorTopology

variable (K L : Type) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
  (A : Type) [CommRing A] [Algebra K A] [TopologicalSpace A] [IsTopologicalRing A]

theorem secondCountableTopology_tensor [SecondCountableTopology A] :
    SecondCountableTopology (L ⊗[K] A) := by
  haveI := AutomorphicForm.isTopologicalRing_tensor K L A
  let ι := Module.Free.ChooseBasisIndex A (L ⊗[K] A)
  haveI : Fintype ι := Module.Free.ChooseBasisIndex.fintype A (L ⊗[K] A)
  let b : Module.Basis ι A (L ⊗[K] A) := Module.Free.chooseBasis A (L ⊗[K] A)
  let e : (L ⊗[K] A) ≃ₗ[A] (ι → A) := b.equivFun
  have h1 : Continuous e := IsModuleTopology.continuous_of_linearMap e.toLinearMap
  have h2 : Continuous e.symm := IsModuleTopology.continuous_of_linearMap e.symm.toLinearMap
  let eh : (L ⊗[K] A) ≃ₜ (ι → A) :=
    { toEquiv := e.toEquiv, continuous_toFun := h1, continuous_invFun := h2 }
  exact eh.isInducing.secondCountableTopology

theorem continuous_sigmaTensor (σ : L ≃ₐ[K] L) : Continuous (AutomorphicForm.sigmaTensor K L A σ) := by
  haveI := AutomorphicForm.isTopologicalRing_tensor K L A
  have h := IsModuleTopology.continuous_of_linearMap
    (TensorProduct.RightActions.AlgebraMap.baseChange K L L A σ.toAlgHom).toLinearMap
  exact h

theorem continuous_sigmaGL (σ : L ≃ₐ[K] L) : Continuous (AutomorphicForm.sigmaGL K L A σ) := by
  haveI := AutomorphicForm.isTopologicalRing_tensor K L A
  refine Continuous.units_map _ ?_
  exact continuous_id.matrix_map (continuous_sigmaTensor K L A σ)

theorem isClosed_twistedCentralizer [T2Space A] (σ : L ≃ₐ[K] L) (δ : GL (Fin 2) (L ⊗[K] A)) :
    IsClosed ((AutomorphicForm.twistedCentralizer K L A σ δ : Subgroup (GL (Fin 2) (L ⊗[K] A))) :
      Set (GL (Fin 2) (L ⊗[K] A))) := by
  haveI := AutomorphicForm.isTopologicalGroup_tensorGL K L A
  haveI := AutomorphicForm.t2Space_tensorGL K L A
  have hc : Continuous fun t : GL (Fin 2) (L ⊗[K] A) =>
      t * δ * (AutomorphicForm.sigmaGL K L A σ t)⁻¹ :=
    (continuous_id.mul continuous_const).mul (continuous_sigmaGL K L A σ).inv
  have : ((AutomorphicForm.twistedCentralizer K L A σ δ : Subgroup (GL (Fin 2) (L ⊗[K] A))) :
      Set (GL (Fin 2) (L ⊗[K] A))) =
      (fun t : GL (Fin 2) (L ⊗[K] A) => t * δ * (AutomorphicForm.sigmaGL K L A σ t)⁻¹) ⁻¹' {δ} := by
    ext t
    exact AutomorphicForm.mem_sigmaCentralizer_iff
  rw [this]
  exact (isClosed_singleton).preimage hc

end TensorTopology

section Main

variable (K L : Type) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
  (A : Type) [CommRing A] [Algebra K A] [TopologicalSpace A] [IsTopologicalRing A] [T2Space A]
  [LocallyCompactSpace A] [SecondCountableTopology A]
  (σ : L ≃ₐ[K] L)

theorem main (hσ : σ ^ Module.finrank K L = 1)
    (μ : @Measure (GL (Fin 2) (L ⊗[K] A)) (AutomorphicForm.glBorelOf (L ⊗[K] A)))
    (hμ : @Measure.IsHaarMeasure (GL (Fin 2) (L ⊗[K] A)) _ _ (AutomorphicForm.glBorelOf (L ⊗[K] A)) μ)
    (δ : GL (Fin 2) (L ⊗[K] A))
    (hδ : AutomorphicForm.IsRegularSemisimple (AutomorphicForm.normString K L A σ δ))
    (τ' : @Measure (AutomorphicForm.twistedCentralizer K L A σ δ)
      (AutomorphicForm.twistedCentralizerBorel K L A σ δ))
    (hτ' : @Measure.IsHaarMeasure _ _ _ (AutomorphicForm.twistedCentralizerBorel K L A σ δ) τ')
    (wt : GL (Fin 2) (L ⊗[K] A) → ℝ) (hwtc : Continuous wt)
    (hwt : ∀ t : AutomorphicForm.twistedCentralizer K L A σ δ, ∀ x : GL (Fin 2) (L ⊗[K] A),
      wt ((t : GL (Fin 2) (L ⊗[K] A)) * x) = wt x)
    (φ : GL (Fin 2) (L ⊗[K] A) → ℂ) (hφm : Measurable[AutomorphicForm.glBorelOf (L ⊗[K] A)] φ)
    (hφb : ∃ C : ℝ, ∀ g, ‖φ g‖ ≤ C)
    {J'₁ J'₂ : ℂ} (h₁ : AutomorphicForm.IsTwistedWeightedOrbitalIntegralOn K L A σ μ wt δ τ' φ J'₁)
    (h₂ : AutomorphicForm.IsTwistedWeightedOrbitalIntegralOn K L A σ μ wt δ τ' φ J'₂) : J'₁ = J'₂ := by
  haveI := AutomorphicForm.isTopologicalRing_tensor K L A
  haveI := AutomorphicForm.t2Space_tensor K L A
  haveI := AutomorphicForm.locallyCompactSpace_tensor K L A
  haveI := secondCountableTopology_tensor K L A
  letI : MeasurableSpace (GL (Fin 2) (L ⊗[K] A)) := AutomorphicForm.glBorelOf (L ⊗[K] A)
  haveI : BorelSpace (GL (Fin 2) (L ⊗[K] A)) := AutomorphicForm.borelSpace_glBorelOf (L ⊗[K] A)
  letI : MeasurableSpace (AutomorphicForm.twistedCentralizer K L A σ δ) :=
    AutomorphicForm.twistedCentralizerBorel K L A σ δ
  haveI : BorelSpace (AutomorphicForm.twistedCentralizer K L A σ δ) := ⟨rfl⟩
  haveI := hμ
  haveI := hτ'
  haveI := t2Space_GL (L ⊗[K] A)
  haveI := secondCountableTopology_GL (L ⊗[K] A)
  haveI := locallyCompactSpace_GL (L ⊗[K] A)
  have hTc := isClosed_twistedCentralizer K L A σ δ
  have hle := twistedCentralizer_le_centralizer_normString K L A σ hσ δ
  have hcomm : ∀ s t : AutomorphicForm.twistedCentralizer K L A σ δ, s * t = t * s := fun s t =>
    Subtype.ext (mul_comm_of_mem_centralizer hδ (hle s.2) (hle t.2))
  haveI : τ'.IsInvInvariant := isInvInvariant_of_comm (L ⊗[K] A) _ hTc hcomm τ'
  obtain ⟨w₁, hw₁, rfl⟩ := h₁
  obtain ⟨w₂, hw₂, rfl⟩ := h₂
  set s := AutomorphicForm.sigmaGL K L A σ with hs

  set S : Set (GL (Fin 2) (L ⊗[K] A)) := tsupport w₁ ∪ tsupport w₂ with hS_def
  have hS : IsCompact S := hw₁.2.2.1.union hw₂.2.2.1
  obtain ⟨M, hM⟩ : ∃ M : ℝ, ∀ x ∈ S, |wt x| ≤ M := by
    obtain ⟨C, hC⟩ := hS.exists_bound_of_continuousOn hwtc.continuousOn
    exact ⟨C, fun x hx => by simpa only [Real.norm_eq_abs] using hC x hx⟩

  set wt' : GL (Fin 2) (L ⊗[K] A) → ℝ := fun x => max (-M) (min M (wt x)) with hwt'_def
  have hwt'T : ∀ (t : AutomorphicForm.twistedCentralizer K L A σ δ) (x : GL (Fin 2) (L ⊗[K] A)), wt' ((t : GL (Fin 2) (L ⊗[K] A)) * x) = wt' x := by
    intro t x
    simp only [hwt'_def, hwt]
  have hwt'b : ∀ x, |wt' x| ≤ |M| := by
    intro x
    rw [abs_le]
    refine ⟨le_trans (neg_le_neg (le_abs_self M)) (le_max_left _ _), max_le ?_ ?_⟩
    · exact neg_le_abs M
    · exact le_trans (min_le_left _ _) (le_abs_self M)
  have hwt'eq : ∀ x ∈ S, wt' x = wt x := by
    intro x hx
    have h := abs_le.1 (hM x hx)
    show max (-M) (min M (wt x)) = wt x
    rw [min_eq_right h.2, max_eq_right h.1]
  have hwt'm : Measurable wt' :=
    measurable_const.max (measurable_const.min hwtc.measurable)

  set F : GL (Fin 2) (L ⊗[K] A) → ℂ := fun x => φ (x⁻¹ * δ * s x) * (wt' x : ℂ) with hF_def
  have hfcm : Measurable fun x : GL (Fin 2) (L ⊗[K] A) => φ (x⁻¹ * δ * s x) :=
    hφm.comp ((continuous_inv.mul continuous_const).mul (continuous_sigmaGL K L A σ)).measurable
  have hFm : Measurable F := hfcm.mul (Complex.continuous_ofReal.measurable.comp hwt'm)
  have hFb : ∃ C : ℝ, ∀ x : GL (Fin 2) (L ⊗[K] A), ‖F x‖ ≤ C := by
    obtain ⟨C, hC⟩ := hφb
    refine ⟨C * |M|, fun x => ?_⟩
    rw [hF_def, norm_mul, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_mul (hC _) (hwt'b x) (abs_nonneg _) (le_trans (norm_nonneg _) (hC (x⁻¹ * δ * s x)))
  have hFT : ∀ (t : AutomorphicForm.twistedCentralizer K L A σ δ) (x : GL (Fin 2) (L ⊗[K] A)), F ((t : GL (Fin 2) (L ⊗[K] A)) * x) = F x := by
    intro t x
    have key : (t : GL (Fin 2) (L ⊗[K] A))⁻¹ * δ * s t = δ :=
      (AutomorphicForm.mem_sigmaCentralizer_iff_inv).1 t.2
    have hconj : ((t : GL (Fin 2) (L ⊗[K] A)) * x)⁻¹ * δ * s (t * x) = x⁻¹ * δ * s x := by
      calc ((t : GL (Fin 2) (L ⊗[K] A)) * x)⁻¹ * δ * s (t * x)
          = x⁻¹ * ((t : GL (Fin 2) (L ⊗[K] A))⁻¹ * δ * s t) * s x := by
            simp only [mul_inv_rev, map_mul, mul_assoc]
        _ = x⁻¹ * δ * s x := by rw [key]
    simp only [hF_def, hconj, hwt'T]
  have hsec : ∀ w : GL (Fin 2) (L ⊗[K] A) → ℝ, AutomorphicForm.IsTwistedSectionFnOn K L A σ δ τ' φ w →
      (∀ x, 0 ≤ w x) ∧ Measurable w ∧ HasCompactSupport w ∧
        ∀ x, F x ≠ 0 → ∫ t : AutomorphicForm.twistedCentralizer K L A σ δ, w ((t : GL (Fin 2) (L ⊗[K] A)) * x) ∂τ' = 1 :=
    fun w hw => ⟨hw.1, hw.2.1, hw.2.2.1, fun x hx => hw.2.2.2 x (mul_ne_zero_iff.1 hx).1⟩
  have key := MeasureTheory.integral_mul_eq_integral_mul_of_integral_subgroup_translate_eq_one
    (AutomorphicForm.twistedCentralizer K L A σ δ) hTc μ τ' F hFm hFb hFT w₁ w₂ (hsec w₁ hw₁) (hsec w₂ hw₂)

  have hswap : ∀ w : GL (Fin 2) (L ⊗[K] A) → ℝ, tsupport w ⊆ S →
      (fun x => φ (x⁻¹ * δ * s x) * (wt x : ℂ) * (w x : ℂ)) = fun x => F x * (w x : ℂ) := by
    intro w hw
    funext x
    by_cases hx : w x = 0
    · simp only [hx, hF_def, Complex.ofReal_zero, mul_zero]
    · have hxS : x ∈ S := hw (subset_tsupport w (Function.mem_support.2 hx))
      simp only [hF_def, hwt'eq x hxS]
  rw [hswap w₁ (Set.subset_union_left), hswap w₂ (Set.subset_union_right)]
  exact key

end Main

end P2mTwistedWeightedOrbitalUnique

theorem solution
    (K L : Type) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
    (A : Type) [CommRing A] [Algebra K A] [TopologicalSpace A] [IsTopologicalRing A] [T2Space A]
    [LocallyCompactSpace A] [SecondCountableTopology A]
    (σ : L ≃ₐ[K] L) (hσ : σ ^ Module.finrank K L = 1)
    (μ : @Measure (GL (Fin 2) (L ⊗[K] A)) (AutomorphicForm.glBorelOf (L ⊗[K] A)))
    (hμ : @Measure.IsHaarMeasure (GL (Fin 2) (L ⊗[K] A)) _ _ (AutomorphicForm.glBorelOf (L ⊗[K] A)) μ)
    (δ : GL (Fin 2) (L ⊗[K] A))
    (hδ : AutomorphicForm.IsRegularSemisimple (AutomorphicForm.normString K L A σ δ))
    (τ' : @Measure (AutomorphicForm.twistedCentralizer K L A σ δ)
      (AutomorphicForm.twistedCentralizerBorel K L A σ δ))
    (hτ' : @Measure.IsHaarMeasure _ _ _ (AutomorphicForm.twistedCentralizerBorel K L A σ δ) τ')
    (wt : GL (Fin 2) (L ⊗[K] A) → ℝ) (hwtc : Continuous wt)
    (hwt : ∀ t : AutomorphicForm.twistedCentralizer K L A σ δ, ∀ x : GL (Fin 2) (L ⊗[K] A),
      wt ((t : GL (Fin 2) (L ⊗[K] A)) * x) = wt x)
    (φ : GL (Fin 2) (L ⊗[K] A) → ℂ) (hφm : Measurable[AutomorphicForm.glBorelOf (L ⊗[K] A)] φ)
    (hφb : ∃ C : ℝ, ∀ g, ‖φ g‖ ≤ C)
    {J'₁ J'₂ : ℂ} (h₁ : AutomorphicForm.IsTwistedWeightedOrbitalIntegralOn K L A σ μ wt δ τ' φ J'₁)
    (h₂ : AutomorphicForm.IsTwistedWeightedOrbitalIntegralOn K L A σ μ wt δ τ' φ J'₂) : J'₁ = J'₂ :=
  P2mTwistedWeightedOrbitalUnique.main K L A σ hσ μ hμ δ hδ τ' hτ' wt hwtc hwt φ hφm hφb h₁ h₂

end S_AutomorphicForm_IsTwistedWeightedOrbitalIntegralOn_unique_of_isRegularSemisimple_normString_of_forall_twistedCentralizer_mul_eq
end P2MW
export P2MW.S_AutomorphicForm_IsTwistedWeightedOrbitalIntegralOn_unique_of_isRegularSemisimple_normString_of_forall_twistedCentralizer_mul_eq (solution)

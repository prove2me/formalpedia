-- Prove2me | solution 1 for AutomorphicForm.exists_isTwistedSectionFnOn_and_continuous_of_isRegularSemisimple_normString_of_hasCompactSupport_of_isArtinianRing
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/e4ed72b3-a630-5607-adb4-3e0c32b24509

import Theorems.Thm_AutomorphicForm_exists_isCompact_setOf_mem_centralizer_normString_twistedConj_mem_subset_twistedCentralizer_mul_of_isArtinianRing
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_isTwistedSectionFnOn_and_continuous_of_isRegularSemisimple_normString_of_hasCompactSupport_of_isArtinianRing

set_option autoImplicit false
set_option linter.unusedSectionVars false

open MeasureTheory TopologicalSpace Topology Filter Set
open scoped TensorProduct TensorProduct.RightActions Pointwise

noncomputable section

namespace P2mTwistedSectionLocal

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

theorem isRegularSemisimple_map {B : Type*} [CommRing B] (f : A →+* B) {γ : GL (Fin 2) A}
    (hγ : AutomorphicForm.IsRegularSemisimple γ) :
    AutomorphicForm.IsRegularSemisimple (Matrix.GeneralLinearGroup.map (n := Fin 2) f γ) := by
  unfold AutomorphicForm.IsRegularSemisimple at hγ ⊢
  have hval : ((Matrix.GeneralLinearGroup.map (n := Fin 2) f γ : GL (Fin 2) B) :
      Matrix (Fin 2) (Fin 2) B) = f.mapMatrix (γ : Matrix (Fin 2) (Fin 2) A) := rfl
  rw [hval, ← RingHom.map_det, RingHom.mapMatrix_apply, ← AddMonoidHom.map_trace]
  have h := hγ.map f
  rwa [map_sub, map_pow, map_mul, map_ofNat] at h

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
      ((AutomorphicForm.sigmaGL K L A σ)^[k] x) i j =
        (AutomorphicForm.sigmaTensor K L A σ)^[k] (x i j) := by
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

theorem sigmaGL_iterate_mul (k : ℕ) (x y : GL (Fin 2) (L ⊗[K] A)) :
    (AutomorphicForm.sigmaGL K L A σ)^[k] (x * y) =
      (AutomorphicForm.sigmaGL K L A σ)^[k] x * (AutomorphicForm.sigmaGL K L A σ)^[k] y := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [Function.iterate_succ_apply', ih, map_mul]

theorem sigmaGL_iterate_inv (k : ℕ) (x : GL (Fin 2) (L ⊗[K] A)) :
    (AutomorphicForm.sigmaGL K L A σ)^[k] x⁻¹ = ((AutomorphicForm.sigmaGL K L A σ)^[k] x)⁻¹ := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [Function.iterate_succ_apply', ih, map_inv]

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
  have hmul : ∀ (k : ℕ) (x y : GL (Fin 2) (L ⊗[K] A)), s^[k] (x * y) = s^[k] x * s^[k] y :=
    fun k x y => sigmaGL_iterate_mul K L A σ k x y
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

def pnorm (k : ℕ) (y : GL (Fin 2) (L ⊗[K] A)) : GL (Fin 2) (L ⊗[K] A) :=
  ((List.range k).map fun i => (AutomorphicForm.sigmaGL K L A σ)^[i] y).prod

theorem pnorm_zero (y : GL (Fin 2) (L ⊗[K] A)) : pnorm K L A σ 0 y = 1 := by
  simp [pnorm]

theorem pnorm_succ (k : ℕ) (y : GL (Fin 2) (L ⊗[K] A)) :
    pnorm K L A σ (k + 1) y = pnorm K L A σ k y * (AutomorphicForm.sigmaGL K L A σ)^[k] y := by
  simp [pnorm, List.range_succ, List.map_append, List.prod_append]

theorem normString_eq_pnorm (y : GL (Fin 2) (L ⊗[K] A)) :
    AutomorphicForm.normString K L A σ y = pnorm K L A σ (Module.finrank K L) y := rfl

theorem pnorm_twistedConj (k : ℕ) (δ x : GL (Fin 2) (L ⊗[K] A)) :
    pnorm K L A σ k (x⁻¹ * δ * AutomorphicForm.sigmaGL K L A σ x) =
      x⁻¹ * pnorm K L A σ k δ * (AutomorphicForm.sigmaGL K L A σ)^[k] x := by
  induction k with
  | zero => simp [pnorm_zero]
  | succ k ih =>
      rw [pnorm_succ, ih, pnorm_succ, sigmaGL_iterate_mul, sigmaGL_iterate_mul, sigmaGL_iterate_inv,
        Function.iterate_succ_apply]
      group

theorem normString_twistedConj (hσ : σ ^ Module.finrank K L = 1) (δ x : GL (Fin 2) (L ⊗[K] A)) :
    AutomorphicForm.normString K L A σ (x⁻¹ * δ * AutomorphicForm.sigmaGL K L A σ x) =
      x⁻¹ * AutomorphicForm.normString K L A σ δ * x := by
  rw [normString_eq_pnorm, normString_eq_pnorm, pnorm_twistedConj, sigmaGL_iterate_finrank K L A σ hσ]

theorem pow_finrank_eq_one [FiniteDimensional K L] : σ ^ Module.finrank K L = 1 := by
  have h1 : orderOf σ ∣ Nat.card (L ≃ₐ[K] L) := orderOf_dvd_natCard σ
  have h2 : Nat.card (L ≃ₐ[K] L) ∣ Module.finrank K L := by
    have h := IntermediateField.finrank_fixedField_eq_card (⊤ : Subgroup (L ≃ₐ[K] L))
    rw [Subgroup.card_top] at h
    have := Module.finrank_mul_finrank K (IntermediateField.fixedField (⊤ : Subgroup (L ≃ₐ[K] L))) L
    rw [h] at this
    exact Dvd.intro_left _ this
  exact orderOf_dvd_iff_pow_eq_one.1 (h1.trans h2)

end Twist

section GLTopology

variable (A : Type*) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]

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

end GLTopology

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

theorem continuous_sigmaGL_iterate (σ : L ≃ₐ[K] L) (k : ℕ) :
    Continuous ((AutomorphicForm.sigmaGL K L A σ)^[k]) := by
  induction k with
  | zero => exact continuous_id
  | succ k ih =>
      have h : ((AutomorphicForm.sigmaGL K L A σ)^[k + 1]) =
          (AutomorphicForm.sigmaGL K L A σ) ∘ ((AutomorphicForm.sigmaGL K L A σ)^[k]) :=
        Function.iterate_succ' _ _
      rw [h]
      exact (continuous_sigmaGL K L A σ).comp ih

theorem continuous_pnorm (σ : L ≃ₐ[K] L) (k : ℕ) : Continuous (pnorm K L A σ k) := by
  haveI := AutomorphicForm.isTopologicalGroup_tensorGL K L A
  induction k with
  | zero =>
      have h : pnorm K L A σ 0 = fun _ => 1 := funext fun y => pnorm_zero K L A σ y
      rw [h]
      exact continuous_const
  | succ k ih =>
      have h : pnorm K L A σ (k + 1) =
          fun y => pnorm K L A σ k y * (AutomorphicForm.sigmaGL K L A σ)^[k] y :=
        funext fun y => pnorm_succ K L A σ k y
      rw [h]
      exact ih.mul (continuous_sigmaGL_iterate K L A σ k)

theorem continuous_normString (σ : L ≃ₐ[K] L) : Continuous (AutomorphicForm.normString K L A σ) := by
  have h : AutomorphicForm.normString K L A σ = pnorm K L A σ (Module.finrank K L) :=
    funext fun y => normString_eq_pnorm K L A σ y
  rw [h]
  exact continuous_pnorm K L A σ _

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

section Conj

open Matrix

variable {A : Type*} [CommRing A]

def cyc (M : Matrix (Fin 2) (Fin 2) A) (a b : A) : Matrix (Fin 2) (Fin 2) A :=
  !![a, M 0 0 * a + M 0 1 * b; b, M 1 0 * a + M 1 1 * b]

private def _root_.P2mTwistedSectionLocal.comp (t d : A) : Matrix (Fin 2) (Fin 2) A := !![0, -d; 1, t]

p2m_export "P2mTwistedSectionLocal" "comp"
theorem det_cyc (M : Matrix (Fin 2) (Fin 2) A) (a b : A) :
    (cyc M a b).det = M 1 0 * a ^ 2 + (M 1 1 - M 0 0) * a * b - M 0 1 * b ^ 2 := by
  simp [cyc, Matrix.det_fin_two]; ring

theorem mul_cyc (M : Matrix (Fin 2) (Fin 2) A) (a b : A) :
    M * cyc M a b = cyc M a b * comp M.trace M.det := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [cyc, comp, Matrix.mul_apply, Fin.sum_univ_two, Matrix.trace_fin_two, Matrix.det_fin_two] <;> ring

theorem cyc_map {B : Type*} [CommRing B] (f : A →+* B) (M : Matrix (Fin 2) (Fin 2) A) (a b : A) :
    (cyc M a b).map f = cyc (M.map f) (f a) (f b) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [cyc]

theorem discr_eq (M : Matrix (Fin 2) (Fin 2) A) :
    M.trace ^ 2 - 4 * M.det = (M 0 0 - M 1 1) ^ 2 + 4 * M 0 1 * M 1 0 := by
  rw [Matrix.trace_fin_two, Matrix.det_fin_two]; ring

theorem exists_det_cyc_notMem (M : Matrix (Fin 2) (Fin 2) A) (m : Ideal A) [m.IsMaximal]
    (hM : M.trace ^ 2 - 4 * M.det ∉ m) :
    ∃ p : A × A, (cyc M p.1 p.2).det ∉ m := by
  by_contra h
  push Not at h
  have h10 : M 1 0 ∈ m := by simpa [det_cyc] using h (1, 0)
  have h01 : M 0 1 ∈ m := by
    have := h (0, 1)
    simp only [det_cyc] at this
    have : -(M 0 1) ∈ m := by simpa using this
    simpa using m.neg_mem_iff.mp this
  have h11 : M 1 0 + (M 1 1 - M 0 0) - M 0 1 ∈ m := by
    have := h (1, 1)
    simpa [det_cyc] using this
  have hdiff : M 1 1 - M 0 0 ∈ m := by
    have := m.sub_mem (m.add_mem h11 h01) h10
    simpa using this
  apply hM
  rw [discr_eq]
  have h1 : (M 0 0 - M 1 1) ^ 2 ∈ m := by
    have : M 0 0 - M 1 1 ∈ m := by simpa using m.neg_mem_iff.mpr hdiff
    simpa [pow_two] using m.mul_mem_left (M 0 0 - M 1 1) this
  have h2 : 4 * M 0 1 * M 1 0 ∈ m := m.mul_mem_left _ h10
  exact m.add_mem h1 h2

theorem isUnit_of_forall_notMem {d : A} (h : ∀ m : MaximalSpectrum A, d ∉ m.asIdeal) : IsUnit d := by
  by_contra hd
  obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal _ (Ideal.span_singleton_ne_top hd)
  exact h ⟨m, hm⟩ (hle (Ideal.mem_span_singleton_self d))

theorem exists_isUnit_det_cyc [Finite (MaximalSpectrum A)] (M : Matrix (Fin 2) (Fin 2) A)
    (hM : IsUnit (M.trace ^ 2 - 4 * M.det)) : ∃ a b : A, IsUnit (cyc M a b).det := by
  classical
  have hsel : ∀ m : MaximalSpectrum A, ∃ p : A × A, (cyc M p.1 p.2).det ∉ m.asIdeal := fun m =>
    exists_det_cyc_notMem M m.asIdeal fun h => m.isMaximal.ne_top (Ideal.eq_top_of_isUnit_mem _ h hM)
  choose p hp using hsel
  have hcop : Pairwise (Function.onFun IsCoprime fun m : MaximalSpectrum A => m.asIdeal) := by
    intro m m' hne
    exact Ideal.isCoprime_of_isMaximal fun h => hne (MaximalSpectrum.ext h)
  obtain ⟨a, ha⟩ := Ideal.exists_forall_sub_mem_ideal hcop fun m => (p m).1
  obtain ⟨b, hb⟩ := Ideal.exists_forall_sub_mem_ideal hcop fun m => (p m).2
  refine ⟨a, b, isUnit_of_forall_notMem fun m hmem => hp m ?_⟩

  rw [← Ideal.Quotient.eq_zero_iff_mem] at hmem ⊢
  have ha' : Ideal.Quotient.mk m.asIdeal a = Ideal.Quotient.mk m.asIdeal (p m).1 :=
    (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mpr (ha m)
  have hb' : Ideal.Quotient.mk m.asIdeal b = Ideal.Quotient.mk m.asIdeal (p m).2 :=
    (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mpr (hb m)
  rw [RingHom.map_det, RingHom.mapMatrix_apply, cyc_map] at hmem ⊢
  rw [← ha', ← hb']
  exact hmem

theorem exists_conj_eq_comp [Finite (MaximalSpectrum A)] (M : Matrix (Fin 2) (Fin 2) A)
    (hM : IsUnit (M.trace ^ 2 - 4 * M.det)) :
    ∃ P : GL (Fin 2) A, (P : Matrix (Fin 2) (Fin 2) A)⁻¹ * M * P = comp M.trace M.det := by
  obtain ⟨a, b, hu⟩ := exists_isUnit_det_cyc M hM
  have hP : IsUnit (cyc M a b) := (Matrix.isUnit_iff_isUnit_det _).mpr hu
  refine ⟨hP.unit, ?_⟩
  rw [IsUnit.unit_spec, Matrix.mul_assoc, mul_cyc, ← Matrix.mul_assoc,
    Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).mp hP), Matrix.one_mul]

theorem exists_conj_of_trace_eq_of_det_eq [Finite (MaximalSpectrum A)] (M N : Matrix (Fin 2) (Fin 2) A)
    (hM : IsUnit (M.trace ^ 2 - 4 * M.det)) (htr : N.trace = M.trace) (hdet : N.det = M.det) :
    ∃ P : GL (Fin 2) A, N = (P : Matrix (Fin 2) (Fin 2) A)⁻¹ * M * P := by
  have hN : IsUnit (N.trace ^ 2 - 4 * N.det) := by rw [htr, hdet]; exact hM
  obtain ⟨P, hP⟩ := exists_conj_eq_comp M hM
  obtain ⟨Q, hQ⟩ := exists_conj_eq_comp N hN
  rw [htr, hdet, ← hP] at hQ
  refine ⟨P * Q⁻¹, ?_⟩
  have hQu : IsUnit ((Q : Matrix (Fin 2) (Fin 2) A).det) :=
    (Matrix.isUnit_iff_isUnit_det _).mp (Units.isUnit Q)
  have h1 : N = (Q : Matrix (Fin 2) (Fin 2) A) * ((P : Matrix (Fin 2) (Fin 2) A)⁻¹ * M * P) *
      (Q : Matrix (Fin 2) (Fin 2) A)⁻¹ := by
    rw [← hQ, ← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hQu, Matrix.one_mul,
      Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hQu, Matrix.mul_one]
  rw [h1]
  simp only [Units.val_mul, Matrix.coe_units_inv, Matrix.mul_inv_rev]
  rw [Matrix.nonsing_inv_nonsing_inv _ hQu]
  simp only [Matrix.mul_assoc]

end Conj

section Proper

open MulAction

variable {A : Type*} [CommRing A]

def fibre (γ : GL (Fin 2) A) : Set (GL (Fin 2) A) :=
  {g | (g : Matrix (Fin 2) (Fin 2) A).trace = (γ : Matrix (Fin 2) (Fin 2) A).trace ∧
    (g : Matrix (Fin 2) (Fin 2) A).det = (γ : Matrix (Fin 2) (Fin 2) A).det}

theorem self_mem_fibre (γ : GL (Fin 2) A) : γ ∈ fibre γ := ⟨rfl, rfl⟩

theorem conj_mem_fibre {γ g : GL (Fin 2) A} (hg : g ∈ fibre γ) (x : GL (Fin 2) A) :
    x * g * x⁻¹ ∈ fibre γ := by
  obtain ⟨h1, h2⟩ := hg
  refine ⟨?_, ?_⟩
  · rw [← h1, Units.val_mul, Units.val_mul]
    exact Matrix.trace_units_conj x _
  · rw [← h2, Units.val_mul, Units.val_mul]
    exact Matrix.det_units_conj x _

theorem exists_conj_eq_of_mem_fibre [Finite (MaximalSpectrum A)] {γ : GL (Fin 2) A}
    (hγ : IsUnit ((γ : Matrix (Fin 2) (Fin 2) A).trace ^ 2 - 4 * (γ : Matrix (Fin 2) (Fin 2) A).det))
    {g : GL (Fin 2) A} (hg : g ∈ fibre γ) : ∃ x : GL (Fin 2) A, x * γ * x⁻¹ = g := by
  obtain ⟨P, hP⟩ := exists_conj_of_trace_eq_of_det_eq
      (γ : Matrix (Fin 2) (Fin 2) A) (g : Matrix (Fin 2) (Fin 2) A) hγ hg.1 hg.2
  refine ⟨P⁻¹, Units.ext ?_⟩
  rw [hP, Units.val_mul, Units.val_mul, inv_inv, Matrix.coe_units_inv]

theorem isClosed_fibre [TopologicalSpace A] [IsTopologicalRing A] [T2Space A] (γ : GL (Fin 2) A) :
    IsClosed (fibre γ) := by
  have hc : Continuous fun g : GL (Fin 2) A => (g : Matrix (Fin 2) (Fin 2) A) := Units.continuous_val
  refine IsClosed.inter (isClosed_eq hc.matrix_trace continuous_const) (isClosed_eq hc.matrix_det continuous_const)

scoped instance mulActionFibre (γ : GL (Fin 2) A) : MulAction (GL (Fin 2) A) (fibre γ) where
  smul x y := ⟨x * y * x⁻¹, conj_mem_fibre y.2 x⟩
  one_smul y := Subtype.ext (by change (1 : GL (Fin 2) A) * y * 1⁻¹ = y; simp)
  mul_smul x x' y := Subtype.ext (by
    change x * x' * (y : GL (Fin 2) A) * (x * x')⁻¹ = x * (x' * y * x'⁻¹) * x⁻¹
    simp only [mul_inv_rev, mul_assoc])

theorem smul_val (γ : GL (Fin 2) A) (x : GL (Fin 2) A) (y : fibre γ) :
    ((x • y : fibre γ) : GL (Fin 2) A) = x * y * x⁻¹ := rfl

theorem continuousSMul_fibre [TopologicalSpace A] [IsTopologicalRing A] (γ : GL (Fin 2) A) :
    ContinuousSMul (GL (Fin 2) A) (fibre γ) := by
  refine ⟨?_⟩
  have : Continuous fun p : GL (Fin 2) A × fibre γ => p.1 * (p.2 : GL (Fin 2) A) * p.1⁻¹ :=
    (continuous_fst.mul (continuous_subtype_val.comp continuous_snd)).mul continuous_fst.inv
  exact this.subtype_mk _

theorem isPretransitive_fibre [Finite (MaximalSpectrum A)] {γ : GL (Fin 2) A}
    (hγ : IsUnit ((γ : Matrix (Fin 2) (Fin 2) A).trace ^ 2 - 4 * (γ : Matrix (Fin 2) (Fin 2) A).det)) :
    IsPretransitive (GL (Fin 2) A) (fibre γ) := by
  refine ⟨fun y₁ y₂ => ?_⟩
  obtain ⟨a, ha⟩ := exists_conj_eq_of_mem_fibre hγ y₁.2
  obtain ⟨b, hb⟩ := exists_conj_eq_of_mem_fibre hγ y₂.2
  refine ⟨b * a⁻¹, Subtype.ext ?_⟩
  rw [smul_val, ← ha, ← hb]
  simp only [mul_inv_rev, inv_inv, mul_assoc, inv_mul_cancel_left]

theorem exists_isCompact_subset_centralizer_mul [TopologicalSpace A] [IsTopologicalRing A] [T2Space A]
    [LocallyCompactSpace A] [SecondCountableTopology A] [Finite (MaximalSpectrum A)] (γ : GL (Fin 2) A)
    (hγ : IsUnit ((γ : Matrix (Fin 2) (Fin 2) A).trace ^ 2 - 4 * (γ : Matrix (Fin 2) (Fin 2) A).det))
    {C : Set (GL (Fin 2) A)} (hC : IsCompact C) :
    ∃ D : Set (GL (Fin 2) A), IsCompact D ∧
      {x : GL (Fin 2) A | x⁻¹ * γ * x ∈ C} ⊆
        (Subgroup.centralizer {γ} : Set (GL (Fin 2) A)) * D := by
  classical
  haveI := t2Space_GL A
  haveI := secondCountableTopology_GL A
  haveI := locallyCompactSpace_GL A
  haveI : SigmaCompactSpace (GL (Fin 2) A) := sigmaCompactSpace_of_locallyCompact_secondCountable
  have hcl : IsClosed (fibre γ) := isClosed_fibre γ
  haveI : LocallyCompactSpace (fibre γ) := hcl.isClosedEmbedding_subtypeVal.locallyCompactSpace
  haveI : ContinuousSMul (GL (Fin 2) A) (fibre γ) := continuousSMul_fibre γ
  haveI : IsPretransitive (GL (Fin 2) A) (fibre γ) := isPretransitive_fibre hγ
  set y₀ : fibre γ := ⟨γ, self_mem_fibre γ⟩ with hy₀

  have hopen : IsOpenMap fun x : GL (Fin 2) A => x • y₀ := isOpenMap_smul_of_sigmaCompact y₀

  set K : Set (fibre γ) := ((↑) : fibre γ → GL (Fin 2) A) ⁻¹' C with hK
  have hKc : IsCompact K := hcl.isClosedEmbedding_subtypeVal.isCompact_preimage hC

  have hN : ∀ x : GL (Fin 2) A, ∃ N : Set (GL (Fin 2) A), IsCompact N ∧ N ∈ 𝓝 x := fun x =>
    exists_compact_mem_nhds x
  choose N hNc hNn using hN
  have hcover : K ⊆ ⋃ x : GL (Fin 2) A, (fun x : GL (Fin 2) A => x • y₀) '' interior (N x) := by
    intro y _
    obtain ⟨x, hx⟩ := exists_smul_eq (GL (Fin 2) A) y₀ y
    exact mem_iUnion.mpr ⟨x, x, mem_interior_iff_mem_nhds.mpr (hNn x), hx⟩
  obtain ⟨t, ht⟩ := hKc.elim_finite_subcover (fun x => (fun x : GL (Fin 2) A => x • y₀) '' interior (N x))
    (fun x => hopen _ isOpen_interior) hcover
  refine ⟨⋃ x ∈ t, (N x)⁻¹, t.isCompact_biUnion fun x _ => (hNc x).inv, ?_⟩
  intro z hz
  have hzK : (z⁻¹ • y₀ : fibre γ) ∈ K := by
    change ((z⁻¹ • y₀ : fibre γ) : GL (Fin 2) A) ∈ C
    rw [smul_val, inv_inv]
    exact hz
  obtain ⟨x, hxt, n, hn, hnz⟩ : ∃ x ∈ t, ∃ n ∈ interior (N x), n • y₀ = z⁻¹ • y₀ := by
    have := ht hzK
    simp only [mem_iUnion, mem_image, exists_prop] at this
    obtain ⟨x, hxt, n, hn, hnz⟩ := this
    exact ⟨x, hxt, n, hn, hnz⟩
  have hval : n * γ * n⁻¹ = z⁻¹ * γ * z⁻¹⁻¹ := by
    have := congrArg (fun y : fibre γ => (y : GL (Fin 2) A)) hnz
    simpa only [smul_val] using this
  rw [inv_inv] at hval

  have hcen : z * n ∈ Subgroup.centralizer ({γ} : Set (GL (Fin 2) A)) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc z * n * γ = z * (n * γ * n⁻¹) * n := by group
      _ = z * (z⁻¹ * γ * z) * n := by rw [hval]
      _ = γ * (z * n) := by group
  refine Set.mem_mul.mpr ⟨z * n, hcen, n⁻¹, ?_, by group⟩
  exact mem_iUnion₂.mpr ⟨x, hxt, Set.inv_mem_inv.mpr (interior_subset hn)⟩

end Proper

section Section

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

variable (T : Subgroup G) [MeasurableSpace T] [BorelSpace T] (τ : Measure T)

theorem isClosedEmbedding_val_mul (hT : IsClosed (T : Set G)) (x : G) :
    IsClosedEmbedding fun t : T => (t : G) * x :=
  (Homeomorph.mulRight x).isClosedEmbedding.comp hT.isClosedEmbedding_subtypeVal

noncomputable def avg (ψ : G → ℝ) (x : G) : ℝ := ∫ t : T, ψ ((t : G) * x) ∂τ

variable {T τ}

theorem avg_mul [τ.IsMulRightInvariant] (ψ : G → ℝ) (t₀ : T) (x : G) :
    avg T τ ψ ((t₀ : G) * x) = avg T τ ψ x := by
  unfold avg
  have : (fun t : T => ψ ((t : G) * ((t₀ : G) * x))) =
      fun t : T => (fun s : T => ψ ((s : G) * x)) (t * t₀) := by
    funext t
    simp only [Subgroup.coe_mul, mul_assoc]
  rw [this, integral_mul_right_eq_self (fun s : T => ψ ((s : G) * x)) t₀]

theorem avg_nonneg {ψ : G → ℝ} (hψ : ∀ x, 0 ≤ ψ x) (x : G) : 0 ≤ avg T τ ψ x :=
  integral_nonneg fun _ => hψ _

theorem avg_pos [LocallyCompactSpace G] (hT : IsClosed (T : Set G)) [τ.IsOpenPosMeasure]
    [IsFiniteMeasureOnCompacts τ] {ψ : G → ℝ} (hψc : Continuous ψ)
    (hψs : HasCompactSupport ψ) (hψ : ∀ x, 0 ≤ ψ x) {x : G} (hx : ψ x ≠ 0) : 0 < avg T τ ψ x := by
  unfold avg
  refine Continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero (x := (1 : T)) ?_ ?_ (fun t => hψ _) ?_
  · exact hψc.comp (isClosedEmbedding_val_mul T hT x).continuous
  · exact hψs.comp_isClosedEmbedding (isClosedEmbedding_val_mul T hT x)
  · simpa using hx

theorem continuous_avg [LocallyCompactSpace G] [SecondCountableTopology G] (hT : IsClosed (T : Set G))
    [IsLocallyFiniteMeasure τ] {ψ : G → ℝ} (hψc : Continuous ψ) (hψs : HasCompactSupport ψ) :
    Continuous (avg T τ ψ) := by
  rw [continuous_iff_continuousAt]
  intro x₀
  obtain ⟨N, hN, hNx₀⟩ := exists_compact_mem_nhds x₀

  set s : Set T := ((↑) : T → G) ⁻¹' (tsupport ψ * N⁻¹) with hs
  have hsc : IsCompact s :=
    hT.isClosedEmbedding_subtypeVal.isCompact_preimage (hψs.mul hN.inv)
  have hF : Continuous (fun p : G × T => ψ ((p.2 : G) * p.1)) :=
    hψc.comp ((continuous_subtype_val.comp continuous_snd).mul continuous_fst)
  have hcont : Continuous fun x => ∫ t in s, ψ ((t : G) * x) ∂τ :=
    continuous_parametric_integral_of_continuous (f := fun x (t : T) => ψ ((t : G) * x))
      (by exact hF) hsc
  have heq : ∀ x ∈ N, avg T τ ψ x = ∫ t in s, ψ ((t : G) * x) ∂τ := by
    intro x hx
    unfold avg
    refine (setIntegral_eq_integral_of_forall_compl_eq_zero fun t ht => ?_).symm
    by_contra hne
    apply ht
    rw [hs, mem_preimage]
    have h1 : (t : G) * x ∈ tsupport ψ := subset_tsupport ψ (Function.mem_support.mpr hne)
    refine Set.mem_mul.mpr ⟨(t : G) * x, h1, x⁻¹, Set.inv_mem_inv.mpr hx, ?_⟩
    simp
  have hev : avg T τ ψ =ᶠ[𝓝 x₀] fun x => ∫ t in s, ψ ((t : G) * x) ∂τ :=
    Filter.eventually_of_mem hNx₀ heq
  exact (hcont.continuousAt.congr hev.symm)

theorem exists_continuous_section [LocallyCompactSpace G] [SecondCountableTopology G]
    (T : Subgroup G) (hT : IsClosed (T : Set G)) [MeasurableSpace T] [BorelSpace T]
    (τ : Measure T) [τ.IsHaarMeasure] [τ.IsMulRightInvariant]
    {E C : Set G} (hC : IsCompact C) (hE : E ⊆ (T : Set G) * C) :
    ∃ w : G → ℝ, (∀ x, 0 ≤ w x) ∧ Continuous w ∧ HasCompactSupport w ∧
      ∀ x ∈ E, ∫ t : T, w ((t : G) * x) ∂τ = 1 := by
  obtain ⟨ψ, hψC, -, hψs, hψ01⟩ := exists_continuous_one_zero_of_isCompact hC isClosed_empty
    (Set.disjoint_empty C)
  have hψc : Continuous ψ := ψ.continuous
  have hψ0 : ∀ x, 0 ≤ ψ x := fun x => (hψ01 x).1
  haveI : LocallyCompactSpace T := hT.isClosedEmbedding_subtypeVal.locallyCompactSpace
  have hΨc : Continuous (avg T τ ψ) := continuous_avg hT hψc hψs

  obtain ⟨m, hm, hmC⟩ : ∃ m : ℝ, 0 < m ∧ ∀ c ∈ C, m ≤ avg T τ ψ c := by
    rcases C.eq_empty_or_nonempty with hCe | hCne
    · exact ⟨1, one_pos, fun c hc => by simp [hCe] at hc⟩
    · obtain ⟨c₀, hc₀, hmin⟩ := hC.exists_isMinOn hCne hΨc.continuousOn
      refine ⟨avg T τ ψ c₀, avg_pos hT hψc hψs hψ0 (by rw [hψC hc₀]; simp), fun c hc => hmin hc⟩
  have hden : ∀ x, max (avg T τ ψ x) m ≠ 0 := fun x => (lt_max_of_lt_right hm).ne'
  refine ⟨fun x => ψ x / max (avg T τ ψ x) m,
    fun x => div_nonneg (hψ0 x) (le_max_of_le_right hm.le),
    hψc.div (hΨc.max continuous_const) hden, ?_, ?_⟩
  · refine hψs.mono ?_
    intro x hx
    rw [Function.mem_support] at hx ⊢
    exact fun h => hx (by simp [h])
  · intro x hx
    obtain ⟨t₀, ht₀, c, hc, rfl⟩ := Set.mem_mul.mp (hE hx)
    have havg : avg T τ ψ (t₀ * c) = avg T τ ψ c := by
      have := avg_mul (T := T) (τ := τ) ψ ⟨t₀, ht₀⟩ c
      simpa using this
    have hpos : 0 < avg T τ ψ (t₀ * c) := by
      rw [havg]
      exact avg_pos hT hψc hψs hψ0 (by rw [hψC hc]; simp)
    have hmax : ∀ t : T, max (avg T τ ψ ((t : G) * (t₀ * c))) m = avg T τ ψ (t₀ * c) := by
      intro t
      rw [avg_mul ψ t (t₀ * c)]
      exact max_eq_left (by rw [havg]; exact hmC c hc)
    simp_rw [hmax]
    rw [integral_div, div_eq_one_iff_eq hpos.ne']
    rfl

end Section

section Main

variable (K L : Type) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
  (A : Type) [CommRing A] [Algebra K A] [TopologicalSpace A] [IsTopologicalRing A] [T2Space A]
  [LocallyCompactSpace A] [SecondCountableTopology A] [IsArtinianRing A]
  (σ : L ≃ₐ[K] L)

theorem exists_isCompact_conj_mem_subset_centralizer_mul_tensor
    (γ : GL (Fin 2) (L ⊗[K] A)) (hγ : AutomorphicForm.IsRegularSemisimple γ)
    {C : Set (GL (Fin 2) (L ⊗[K] A))} (hC : IsCompact C) :
    ∃ D : Set (GL (Fin 2) (L ⊗[K] A)), IsCompact D ∧
      {x : GL (Fin 2) (L ⊗[K] A) | x⁻¹ * γ * x ∈ C} ⊆
        (Subgroup.centralizer ({γ} : Set (GL (Fin 2) (L ⊗[K] A))) : Set (GL (Fin 2) (L ⊗[K] A))) * D := by
  haveI := AutomorphicForm.isTopologicalRing_tensor K L A
  haveI := AutomorphicForm.t2Space_tensor K L A
  haveI := AutomorphicForm.locallyCompactSpace_tensor K L A
  haveI := secondCountableTopology_tensor K L A
  haveI : IsArtinianRing (L ⊗[K] A) := IsArtinianRing.of_finite A (L ⊗[K] A)
  haveI : Finite (MaximalSpectrum (L ⊗[K] A)) := inferInstance
  exact exists_isCompact_subset_centralizer_mul γ hγ hC

theorem exists_isCompact_twistedConj_mem_subset_twistedCentralizer_mul [IsReduced (L ⊗[K] A)]
    (δ : GL (Fin 2) (L ⊗[K] A))
    (hδ : AutomorphicForm.IsRegularSemisimple (AutomorphicForm.normString K L A σ δ))
    {C : Set (GL (Fin 2) (L ⊗[K] A))} (hC : IsCompact C) :
    ∃ D : Set (GL (Fin 2) (L ⊗[K] A)), IsCompact D ∧
      {x : GL (Fin 2) (L ⊗[K] A) | x⁻¹ * δ * AutomorphicForm.sigmaGL K L A σ x ∈ C} ⊆
        (AutomorphicForm.twistedCentralizer K L A σ δ : Set (GL (Fin 2) (L ⊗[K] A))) * D := by
  haveI := AutomorphicForm.isTopologicalGroup_tensorGL K L A
  set s := AutomorphicForm.sigmaGL K L A σ with hs
  set N := AutomorphicForm.normString K L A σ with hN
  have hσ : σ ^ Module.finrank K L = 1 := pow_finrank_eq_one K L σ

  have hC₁ : IsCompact (N '' C) := hC.image (continuous_normString K L A σ)

  obtain ⟨D₁, hD₁, hsub₁⟩ := exists_isCompact_conj_mem_subset_centralizer_mul_tensor K L A (N δ) hδ hC₁

  have hsD₁ : IsCompact (s '' D₁) := hD₁.image (continuous_sigmaGL K L A σ)
  have hC₂ : IsCompact (D₁ * C * (s '' D₁)⁻¹) := (hD₁.mul hC).mul hsD₁.inv
  obtain ⟨D₂, hD₂, hsub₂⟩ :=
    AutomorphicForm.exists_isCompact_setOf_mem_centralizer_normString_twistedConj_mem_subset_twistedCentralizer_mul_of_isArtinianRing
      K L A σ hσ δ hδ (D₁ * C * (s '' D₁)⁻¹) hC₂
  refine ⟨D₂ * D₁, hD₂.mul hD₁, ?_⟩
  intro x hx
  have hx' : x⁻¹ * N δ * x ∈ N '' C := by
    have h := normString_twistedConj K L A σ hσ δ x
    rw [← hN, ← hs] at h
    rw [← h]
    exact Set.mem_image_of_mem _ hx
  obtain ⟨z, hz, d₁, hd₁, hzd⟩ := Set.mem_mul.1 (hsub₁ hx')

  have hzconj : z⁻¹ * δ * s z = d₁ * (x⁻¹ * δ * s x) * (s d₁)⁻¹ := by
    rw [← hzd, map_mul]
    group
  have hz2 : z ∈ {z : GL (Fin 2) (L ⊗[K] A) |
      z ∈ Subgroup.centralizer ({N δ} : Set (GL (Fin 2) (L ⊗[K] A))) ∧
        z⁻¹ * δ * s z ∈ D₁ * C * (s '' D₁)⁻¹} := by
    refine ⟨hz, ?_⟩
    rw [hzconj]
    exact Set.mul_mem_mul (Set.mul_mem_mul hd₁ hx) (Set.inv_mem_inv.2 (Set.mem_image_of_mem _ hd₁))
  obtain ⟨t, ht, d₂, hd₂, htd⟩ := Set.mem_mul.1 (hsub₂ hz2)
  refine Set.mem_mul.2 ⟨t, ht, d₂ * d₁, Set.mul_mem_mul hd₂ hd₁, ?_⟩
  rw [← mul_assoc, htd, hzd]

theorem main [IsReduced (L ⊗[K] A)]
    (δ : GL (Fin 2) (L ⊗[K] A))
    (hδ : AutomorphicForm.IsRegularSemisimple (AutomorphicForm.normString K L A σ δ))
    (τ' : @Measure (AutomorphicForm.twistedCentralizer K L A σ δ)
      (AutomorphicForm.twistedCentralizerBorel K L A σ δ))
    (hτ' : @Measure.IsHaarMeasure _ _ _ (AutomorphicForm.twistedCentralizerBorel K L A σ δ) τ')
    (φ : GL (Fin 2) (L ⊗[K] A) → ℂ) (hφ : HasCompactSupport φ) :
    ∃ w : GL (Fin 2) (L ⊗[K] A) → ℝ,
      AutomorphicForm.IsTwistedSectionFnOn K L A σ δ τ' φ w ∧ Continuous w := by

  haveI := AutomorphicForm.isTopologicalRing_tensor K L A
  haveI := AutomorphicForm.t2Space_tensor K L A
  haveI := AutomorphicForm.locallyCompactSpace_tensor K L A
  haveI := secondCountableTopology_tensor K L A
  haveI := AutomorphicForm.isTopologicalGroup_tensorGL K L A
  haveI := t2Space_GL (L ⊗[K] A)
  haveI := secondCountableTopology_GL (L ⊗[K] A)
  haveI := locallyCompactSpace_GL (L ⊗[K] A)
  letI : MeasurableSpace (GL (Fin 2) (L ⊗[K] A)) := AutomorphicForm.glBorelOf (L ⊗[K] A)
  haveI : BorelSpace (GL (Fin 2) (L ⊗[K] A)) := AutomorphicForm.borelSpace_glBorelOf (L ⊗[K] A)
  letI : MeasurableSpace (AutomorphicForm.twistedCentralizer K L A σ δ) :=
    AutomorphicForm.twistedCentralizerBorel K L A σ δ
  haveI : BorelSpace (AutomorphicForm.twistedCentralizer K L A σ δ) := ⟨rfl⟩
  haveI := hτ'

  have hσ : σ ^ Module.finrank K L = 1 := pow_finrank_eq_one K L σ
  have hTc := isClosed_twistedCentralizer K L A σ δ
  have hle := twistedCentralizer_le_centralizer_normString K L A σ hσ δ
  have hcomm : ∀ a b : AutomorphicForm.twistedCentralizer K L A σ δ, a * b = b * a := fun a b =>
    Subtype.ext (mul_comm_of_mem_centralizer hδ (hle a.2) (hle b.2))
  haveI : τ'.IsMulRightInvariant := by
    refine ⟨fun g => ?_⟩
    have h : (fun t : AutomorphicForm.twistedCentralizer K L A σ δ => t * g) = fun t => g * t :=
      funext fun t => hcomm t g
    rw [h]
    exact map_mul_left_eq_self τ' g

  obtain ⟨D, hD, hsub⟩ := exists_isCompact_twistedConj_mem_subset_twistedCentralizer_mul K L A σ δ hδ hφ
  have hE : {x : GL (Fin 2) (L ⊗[K] A) | φ (x⁻¹ * δ * AutomorphicForm.sigmaGL K L A σ x) ≠ 0} ⊆
      (AutomorphicForm.twistedCentralizer K L A σ δ : Set (GL (Fin 2) (L ⊗[K] A))) * D :=
    fun x hx => hsub (subset_tsupport φ hx)

  obtain ⟨w, hw0, hwc, hws, hw1⟩ :=
    exists_continuous_section (AutomorphicForm.twistedCentralizer K L A σ δ) hTc τ' hD hE
  exact ⟨w, ⟨hw0, hwc.measurable, hws, fun x hx => hw1 x hx⟩, hwc⟩

end Main

end P2mTwistedSectionLocal
p2m_reactivate "P2MW.S_AutomorphicForm_exists_isTwistedSectionFnOn_and_continuous_of_isRegularSemisimple_normString_of_hasCompactSupport_of_isArtinianRing.P2mTwistedSectionLocal"

end
p2m_reactivate "P2MW.S_AutomorphicForm_exists_isTwistedSectionFnOn_and_continuous_of_isRegularSemisimple_normString_of_hasCompactSupport_of_isArtinianRing.P2mTwistedSectionLocal"

open MeasureTheory in
theorem solution
    (K L : Type) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
    (A : Type) [CommRing A] [Algebra K A] [TopologicalSpace A] [IsTopologicalRing A] [T2Space A]
    [LocallyCompactSpace A] [SecondCountableTopology A] [IsArtinianRing A]
    [IsReduced (L ⊗[K] A)]
    (σ : L ≃ₐ[K] L) (δ : GL (Fin 2) (L ⊗[K] A))
    (hδ : AutomorphicForm.IsRegularSemisimple (AutomorphicForm.normString K L A σ δ))
    (τ' : @Measure (AutomorphicForm.twistedCentralizer K L A σ δ)
      (AutomorphicForm.twistedCentralizerBorel K L A σ δ))
    (hτ' : @Measure.IsHaarMeasure _ _ _ (AutomorphicForm.twistedCentralizerBorel K L A σ δ) τ')
    (φ : GL (Fin 2) (L ⊗[K] A) → ℂ) (hφ : HasCompactSupport φ) :
    ∃ w : GL (Fin 2) (L ⊗[K] A) → ℝ,
      AutomorphicForm.IsTwistedSectionFnOn K L A σ δ τ' φ w ∧ Continuous w :=
  P2mTwistedSectionLocal.main K L A σ δ hδ τ' hτ' φ hφ

end S_AutomorphicForm_exists_isTwistedSectionFnOn_and_continuous_of_isRegularSemisimple_normString_of_hasCompactSupport_of_isArtinianRing
end P2MW
export P2MW.S_AutomorphicForm_exists_isTwistedSectionFnOn_and_continuous_of_isRegularSemisimple_normString_of_hasCompactSupport_of_isArtinianRing (solution)

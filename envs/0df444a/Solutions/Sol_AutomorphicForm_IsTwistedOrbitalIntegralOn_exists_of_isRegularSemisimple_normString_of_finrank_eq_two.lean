-- Prove2me | solution 1 for AutomorphicForm.IsTwistedOrbitalIntegralOn.exists_of_isRegularSemisimple_normString_of_finrank_eq_two
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/6944ad20-b3ef-5286-8522-964c3bac3427

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_IsTwistedOrbitalIntegralOn_exists_of_isRegularSemisimple_normString_of_finrank_eq_two

set_option autoImplicit false
set_option linter.unusedSectionVars false

open MeasureTheory TopologicalSpace Topology Filter Set MulAction
open scoped TensorProduct TensorProduct.RightActions Pointwise

noncomputable section

namespace P2mTwistedOrbitalExists

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

def cyc (M : Matrix (Fin 2) (Fin 2) A) (a b : A) : Matrix (Fin 2) (Fin 2) A :=
  !![a, M 0 0 * a + M 0 1 * b; b, M 1 0 * a + M 1 1 * b]

private def _root_.P2mTwistedOrbitalExists.comp (t d : A) : Matrix (Fin 2) (Fin 2) A := !![0, -d; 1, t]

p2m_export "P2mTwistedOrbitalExists" "comp"
theorem trace_comp (t d : A) : (comp t d).trace = t := by
  simp [comp, Matrix.trace_fin_two]

theorem det_comp (t d : A) : (comp t d).det = d := by
  simp [comp, Matrix.det_fin_two]

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

theorem exists_conj_of_trace_det [Finite (MaximalSpectrum A)] (M N : Matrix (Fin 2) (Fin 2) A)
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

theorem exists_units_conj_eq [Finite (MaximalSpectrum A)] {γ : GL (Fin 2) A}
    (hγ : AutomorphicForm.IsRegularSemisimple γ) (g : GL (Fin 2) A)
    (htr : (g : Matrix (Fin 2) (Fin 2) A).trace = (γ : Matrix (Fin 2) (Fin 2) A).trace)
    (hdet : (g : Matrix (Fin 2) (Fin 2) A).det = (γ : Matrix (Fin 2) (Fin 2) A).det) :
    ∃ x : GL (Fin 2) A, x⁻¹ * γ * x = g := by
  obtain ⟨P, hP⟩ := exists_conj_of_trace_det (γ : Matrix (Fin 2) (Fin 2) A) g hγ htr hdet
  refine ⟨P, Units.ext ?_⟩
  rw [hP, Units.val_mul, Units.val_mul, Matrix.coe_units_inv]

end Algebra

section Twist

variable (K L : Type) [Field K] [Field L] [Algebra K L] (A : Type) [CommRing A] [Algebra K A]
  (σ : L ≃ₐ[K] L)

local notation "sT" => AutomorphicForm.sigmaTensor K L A σ
local notation "sG" => AutomorphicForm.sigmaGL K L A σ
local notation "ι" => AutomorphicForm.toTensorGL K L A
local notation "incl" => (Algebra.TensorProduct.includeRight : A →ₐ[K] L ⊗[K] A)

theorem sigmaTensor_tmul (l : L) (a : A) : sT (l ⊗ₜ[K] a) = σ l ⊗ₜ[K] a := by
  simp [AutomorphicForm.sigmaTensor]

theorem sigmaTensor_one_tmul (a : A) : sT ((1 : L) ⊗ₜ[K] a) = (1 : L) ⊗ₜ[K] a := by
  rw [sigmaTensor_tmul, map_one]

theorem sigmaTensor_includeRight (a : A) : sT (incl a) = incl a :=
  sigmaTensor_one_tmul K L A σ a

theorem sigmaTensor_sigmaTensor (hσ : ∀ l : L, σ (σ l) = l) (b : L ⊗[K] A) : sT (sT b) = b := by
  induction b using TensorProduct.induction_on with
  | zero => simp
  | tmul l a => rw [sigmaTensor_tmul, sigmaTensor_tmul, hσ]
  | add x y hx hy => rw [map_add, map_add, hx, hy]

theorem sigmaGL_apply (g : GL (Fin 2) (L ⊗[K] A)) (i j : Fin 2) :
    ((sG g : GL (Fin 2) (L ⊗[K] A)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) i j =
      sT ((g : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) i j) :=
  Matrix.GeneralLinearGroup.map_apply _ _ _ _

theorem coe_sigmaGL (g : GL (Fin 2) (L ⊗[K] A)) :
    ((sG g : GL (Fin 2) (L ⊗[K] A)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) =
      (g : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)).map sT := by
  ext i j
  exact sigmaGL_apply K L A σ g i j

theorem sigmaGL_sigmaGL (hσ : ∀ l : L, σ (σ l) = l) (g : GL (Fin 2) (L ⊗[K] A)) : sG (sG g) = g := by
  ext i j
  rw [sigmaGL_apply, sigmaGL_apply, sigmaTensor_sigmaTensor K L A σ hσ]

theorem toTensorGL_apply (γ : GL (Fin 2) A) (i j : Fin 2) :
    ((ι γ : GL (Fin 2) (L ⊗[K] A)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) i j =
      (1 : L) ⊗ₜ[K] ((γ : Matrix (Fin 2) (Fin 2) A) i j) :=
  Matrix.GeneralLinearGroup.map_apply _ _ _ _

theorem coe_toTensorGL (γ : GL (Fin 2) A) :
    ((ι γ : GL (Fin 2) (L ⊗[K] A)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) =
      (γ : Matrix (Fin 2) (Fin 2) A).map incl := rfl

theorem sigmaGL_toTensorGL (γ : GL (Fin 2) A) : sG (ι γ) = ι γ := by
  ext i j
  rw [sigmaGL_apply, toTensorGL_apply, sigmaTensor_one_tmul]

theorem trace_toTensorGL (γ : GL (Fin 2) A) :
    ((ι γ : GL (Fin 2) (L ⊗[K] A)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)).trace =
      incl (γ : Matrix (Fin 2) (Fin 2) A).trace := by
  rw [coe_toTensorGL, Matrix.trace_fin_two, Matrix.trace_fin_two]
  simp only [Matrix.map_apply, map_add]

theorem det_toTensorGL (γ : GL (Fin 2) A) :
    ((ι γ : GL (Fin 2) (L ⊗[K] A)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)).det =
      incl (γ : Matrix (Fin 2) (Fin 2) A).det := by
  rw [coe_toTensorGL, Matrix.det_fin_two, Matrix.det_fin_two]
  simp only [Matrix.map_apply, map_sub, map_mul]

theorem trace_sigmaGL (g : GL (Fin 2) (L ⊗[K] A)) :
    ((sG g : GL (Fin 2) (L ⊗[K] A)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)).trace =
      sT (g : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)).trace := by
  rw [coe_sigmaGL, Matrix.trace_fin_two, Matrix.trace_fin_two]
  simp only [Matrix.map_apply, map_add]

theorem det_sigmaGL (g : GL (Fin 2) (L ⊗[K] A)) :
    ((sG g : GL (Fin 2) (L ⊗[K] A)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)).det =
      sT (g : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)).det := by
  rw [coe_sigmaGL, Matrix.det_fin_two, Matrix.det_fin_two]
  simp only [Matrix.map_apply, map_sub, map_mul]

theorem isRegularSemisimple_toTensorGL (γ : GL (Fin 2) A) (hγ : AutomorphicForm.IsRegularSemisimple γ) :
    AutomorphicForm.IsRegularSemisimple (ι γ) := by
  unfold AutomorphicForm.IsRegularSemisimple at hγ ⊢
  rw [trace_toTensorGL, det_toTensorGL]
  have : incl (γ : Matrix (Fin 2) (Fin 2) A).trace ^ 2 - 4 * incl (γ : Matrix (Fin 2) (Fin 2) A).det =
      incl ((γ : Matrix (Fin 2) (Fin 2) A).trace ^ 2 - 4 * (γ : Matrix (Fin 2) (Fin 2) A).det) := by
    simp only [map_sub, map_mul, map_pow, map_ofNat]
  rw [this]
  exact hγ.map _

theorem trace_units_conj' (x g : GL (Fin 2) (L ⊗[K] A)) :
    ((x⁻¹ * g * x : GL (Fin 2) (L ⊗[K] A)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)).trace =
      (g : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)).trace := by
  rw [Units.val_mul, Units.val_mul, Matrix.trace_mul_cycle, ← Units.val_mul, mul_inv_cancel,
    Units.val_one, Matrix.one_mul]

theorem det_units_conj' (x g : GL (Fin 2) (L ⊗[K] A)) :
    ((x⁻¹ * g * x : GL (Fin 2) (L ⊗[K] A)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)).det =
      (g : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)).det := by
  rw [Units.val_mul, Units.val_mul, Matrix.det_mul, Matrix.det_mul, mul_comm, ← mul_assoc,
    ← Matrix.det_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.det_one, one_mul]

theorem normString_two (h2 : Module.finrank K L = 2) (δ : GL (Fin 2) (L ⊗[K] A)) :
    AutomorphicForm.normString K L A σ δ = δ * sG δ := by
  simp [AutomorphicForm.normString, h2, List.range_succ]

theorem mem_twistedCentralizer_iff (δ t : GL (Fin 2) (L ⊗[K] A)) :
    t ∈ AutomorphicForm.twistedCentralizer K L A σ δ ↔ t * δ = δ * sG t := by
  rw [AutomorphicForm.twistedCentralizer, AutomorphicForm.mem_sigmaCentralizer_iff, mul_inv_eq_iff_eq_mul]

variable (h2 : Module.finrank K L = 2) (hσ : ∀ l : L, σ (σ l) = l)
include h2 hσ

theorem sigmaGL_normString (δ : GL (Fin 2) (L ⊗[K] A)) :
    sG (AutomorphicForm.normString K L A σ δ) = sG δ * δ := by
  rw [normString_two K L A σ h2, map_mul, sigmaGL_sigmaGL K L A σ hσ]

theorem normString_conj (δ x : GL (Fin 2) (L ⊗[K] A)) :
    AutomorphicForm.normString K L A σ (x⁻¹ * δ * sG x) =
      x⁻¹ * AutomorphicForm.normString K L A σ δ * x := by
  rw [normString_two K L A σ h2, normString_two K L A σ h2, map_mul, map_mul, map_inv,
    sigmaGL_sigmaGL K L A σ hσ]
  group

theorem sigmaTensor_trace_normString (δ : GL (Fin 2) (L ⊗[K] A)) :
    sT ((AutomorphicForm.normString K L A σ δ : GL (Fin 2) (L ⊗[K] A)) :
        Matrix (Fin 2) (Fin 2) (L ⊗[K] A)).trace =
      ((AutomorphicForm.normString K L A σ δ : GL (Fin 2) (L ⊗[K] A)) :
        Matrix (Fin 2) (Fin 2) (L ⊗[K] A)).trace := by
  rw [← trace_sigmaGL, sigmaGL_normString K L A σ h2 hσ, normString_two K L A σ h2, Units.val_mul,
    Units.val_mul, Matrix.trace_mul_comm]

theorem sigmaTensor_det_normString (δ : GL (Fin 2) (L ⊗[K] A)) :
    sT ((AutomorphicForm.normString K L A σ δ : GL (Fin 2) (L ⊗[K] A)) :
        Matrix (Fin 2) (Fin 2) (L ⊗[K] A)).det =
      ((AutomorphicForm.normString K L A σ δ : GL (Fin 2) (L ⊗[K] A)) :
        Matrix (Fin 2) (Fin 2) (L ⊗[K] A)).det := by
  rw [← det_sigmaGL, sigmaGL_normString K L A σ h2 hσ, normString_two K L A σ h2, Units.val_mul,
    Units.val_mul, Matrix.det_mul, Matrix.det_mul, mul_comm]

theorem twistedCentralizer_le_centralizer_normString (δ : GL (Fin 2) (L ⊗[K] A)) :
    AutomorphicForm.twistedCentralizer K L A σ δ ≤
      Subgroup.centralizer ({AutomorphicForm.normString K L A σ δ} : Set (GL (Fin 2) (L ⊗[K] A))) := by
  intro t ht
  rw [mem_twistedCentralizer_iff] at ht
  rw [Subgroup.mem_centralizer_singleton_iff, normString_two K L A σ h2]
  have h1 : sG t * sG δ = sG δ * t := by
    have := congrArg sG ht
    rwa [map_mul, map_mul, sigmaGL_sigmaGL K L A σ hσ] at this
  symm
  calc δ * sG δ * t = δ * (sG δ * t) := by rw [mul_assoc]
    _ = δ * (sG t * sG δ) := by rw [h1]
    _ = (δ * sG t) * sG δ := by rw [mul_assoc]
    _ = t * δ * sG δ := by rw [← ht]
    _ = t * (δ * sG δ) := by rw [mul_assoc]

theorem mem_twistedCentralizer_conj_iff (δ x t : GL (Fin 2) (L ⊗[K] A)) :
    t ∈ AutomorphicForm.twistedCentralizer K L A σ (x⁻¹ * δ * sG x) ↔
      x * t * x⁻¹ ∈ AutomorphicForm.twistedCentralizer K L A σ δ := by
  rw [mem_twistedCentralizer_iff, mem_twistedCentralizer_iff, map_mul, map_mul, map_inv]
  constructor
  · intro h
    calc x * t * x⁻¹ * δ = x * (t * (x⁻¹ * δ * sG x)) * (sG x)⁻¹ := by group
      _ = x * (x⁻¹ * δ * sG x * sG t) * (sG x)⁻¹ := by rw [h]
      _ = δ * (sG x * sG t * (sG x)⁻¹) := by group
  · intro h
    calc t * (x⁻¹ * δ * sG x) = x⁻¹ * (x * t * x⁻¹ * δ) * sG x := by group
      _ = x⁻¹ * (δ * (sG x * sG t * (sG x)⁻¹)) * sG x := by rw [h]
      _ = x⁻¹ * δ * sG x * sG t := by group

end Twist

section Galois

variable (K L : Type) [Field K] [CharZero K] [Field L] [Algebra K L]

theorem sigma_involutive_and_ne_one (h2 : Module.finrank K L = 2) (σ : L ≃ₐ[K] L)
    (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ) :
    (∀ l : L, σ (σ l) = l) ∧ ∃ ℓ : L, σ ℓ ≠ ℓ := by
  haveI : FiniteDimensional K L := Module.finite_of_finrank_eq_succ h2
  haveI : Algebra.IsQuadraticExtension K L := { finrank_eq_two' := h2 }
  haveI : IsGalois K L := inferInstance
  have hcard : Nat.card (L ≃ₐ[K] L) = 2 := (IsGalois.card_aut_eq_finrank K L).trans h2
  refine ⟨fun l => ?_, ?_⟩
  · have hpow : σ ^ 2 = 1 := by rw [← hcard]; exact pow_card_eq_one'
    have := AlgEquiv.congr_fun hpow l
    rwa [pow_two, AlgEquiv.mul_apply] at this
  · by_contra h
    push Not at h
    have hσ1 : σ = 1 := AlgEquiv.ext h
    have hall : ∀ τ : L ≃ₐ[K] L, τ = 1 := fun τ => by
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (hgen τ)
      rw [← hk, hσ1, one_zpow]
    have h1 : Nat.card (L ≃ₐ[K] L) = 1 :=
      Nat.card_eq_one_iff_unique.mpr ⟨⟨fun a b => (hall a).trans (hall b).symm⟩, ⟨1⟩⟩
    omega

theorem exists_algebraMap_eq_of_fixed (h2 : Module.finrank K L = 2) (σ : L ≃ₐ[K] L)
    (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ) {l : L} (hl : σ l = l) :
    ∃ k : K, algebraMap K L k = l := by
  haveI : FiniteDimensional K L := Module.finite_of_finrank_eq_succ h2
  haveI : Algebra.IsQuadraticExtension K L := { finrank_eq_two' := h2 }
  haveI : IsGalois K L := inferInstance
  have hzpow : ∀ k : ℤ, (σ ^ k) l = l := by
    intro k
    induction k using Int.induction_on with
    | zero => simp
    | succ k ih => rw [zpow_add_one, AlgEquiv.mul_apply, hl, ih]
    | pred k ih =>
        have hinv : σ⁻¹ l = l := by
          rw [AlgEquiv.aut_inv]
          conv_lhs => rw [← hl]
          exact σ.symm_apply_apply l
        rw [zpow_sub_one, AlgEquiv.mul_apply, hinv, ih]
  have hfix : ∀ f : L ≃ₐ[K] L, f l = l := fun f => by
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (hgen f)
    rw [← hk]
    exact hzpow k
  exact (IsGalois.mem_range_algebraMap_iff_fixed l).mpr hfix

variable (A : Type) [CommRing A] [Algebra K A]

theorem exists_one_tmul_of_sigmaTensor_eq (h2 : Module.finrank K L = 2) (σ : L ≃ₐ[K] L)
    (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ) {b : L ⊗[K] A}
    (hb : AutomorphicForm.sigmaTensor K L A σ b = b) : ∃ a : A, b = (1 : L) ⊗ₜ[K] a := by

  have hsym : ∀ b : L ⊗[K] A, ∃ a : A, b + AutomorphicForm.sigmaTensor K L A σ b = (1 : L) ⊗ₜ[K] a := by
    intro b
    induction b using TensorProduct.induction_on with
    | zero => exact ⟨0, by simp⟩
    | tmul l a =>
        obtain ⟨k, hk⟩ := exists_algebraMap_eq_of_fixed K L h2 σ hgen (l := l + σ l)
          (by rw [map_add, (sigma_involutive_and_ne_one K L h2 σ hgen).1 l, add_comm])
        refine ⟨k • a, ?_⟩
        rw [sigmaTensor_tmul, ← TensorProduct.add_tmul, ← hk, Algebra.algebraMap_eq_smul_one,
          TensorProduct.smul_tmul]
    | add x y hx hy =>
        obtain ⟨a, ha⟩ := hx
        obtain ⟨a', ha'⟩ := hy
        refine ⟨a + a', ?_⟩
        rw [map_add, TensorProduct.tmul_add, ← ha, ← ha']
        abel
  obtain ⟨a, ha⟩ := hsym b
  rw [hb, ← two_smul K b] at ha
  refine ⟨(2 : K)⁻¹ • a, ?_⟩
  rw [← TensorProduct.smul_tmul, ← TensorProduct.smul_tmul', ← ha, smul_smul,
    inv_mul_cancel₀ (two_ne_zero : (2 : K) ≠ 0), one_smul]

private theorem _root_.P2mTwistedOrbitalExists.includeRight_injective :
    Function.Injective (Algebra.TensorProduct.includeRight : A →ₐ[K] L ⊗[K] A) :=
  Algebra.TensorProduct.includeRight_injective (algebraMap K L).injective

p2m_export "P2mTwistedOrbitalExists" "includeRight_injective"

theorem toTensorGL_injective : Function.Injective (AutomorphicForm.toTensorGL K L A) := by
  intro g g' h
  apply Units.ext
  ext i j
  have := congrArg (fun m : GL (Fin 2) (L ⊗[K] A) => (m : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) i j) h
  simp only [toTensorGL_apply] at this
  exact includeRight_injective K L A this

theorem exists_toTensorGL_eq_of_sigmaGL_eq (h2 : Module.finrank K L = 2) (σ : L ≃ₐ[K] L)
    (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ) {g : GL (Fin 2) (L ⊗[K] A)}
    (hg : AutomorphicForm.sigmaGL K L A σ g = g) : ∃ m : GL (Fin 2) A, AutomorphicForm.toTensorGL K L A m = g := by
  set incl : A →ₐ[K] L ⊗[K] A := Algebra.TensorProduct.includeRight with hincl
  have hginv : AutomorphicForm.sigmaGL K L A σ g⁻¹ = g⁻¹ := by rw [map_inv, hg]
  have hent : ∀ (u : GL (Fin 2) (L ⊗[K] A)), AutomorphicForm.sigmaGL K L A σ u = u →
      ∃ m : Matrix (Fin 2) (Fin 2) A, m.map incl = (u : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) := by
    intro u hu
    have hij : ∀ i j, ∃ a : A, (u : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) i j = (1 : L) ⊗ₜ[K] a := by
      intro i j
      apply exists_one_tmul_of_sigmaTensor_eq K L A h2 σ hgen
      have := congrArg (fun m : GL (Fin 2) (L ⊗[K] A) => (m : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) i j) hu
      simpa only [sigmaGL_apply] using this
    choose a ha using hij
    refine ⟨Matrix.of fun i j => a i j, ?_⟩
    ext i j
    rw [ha i j]
    rfl
  obtain ⟨m, hm⟩ := hent g hg
  obtain ⟨m', hm'⟩ := hent g⁻¹ hginv
  have hmapinj : Function.Injective fun x : Matrix (Fin 2) (Fin 2) A => x.map incl := by
    intro x y hxy
    ext i j
    exact includeRight_injective K L A (congrFun (congrFun hxy i) j)
  have hmm' : m * m' = 1 := by
    apply hmapinj
    change (m * m').map incl.toRingHom = (1 : Matrix (Fin 2) (Fin 2) A).map incl.toRingHom
    rw [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)]
    change m.map incl * m'.map incl = 1
    rw [hm, hm', ← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hm'm : m' * m = 1 := by
    apply hmapinj
    change (m' * m).map incl.toRingHom = (1 : Matrix (Fin 2) (Fin 2) A).map incl.toRingHom
    rw [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)]
    change m'.map incl * m.map incl = 1
    rw [hm, hm', ← Units.val_mul, inv_mul_cancel, Units.val_one]
  refine ⟨⟨m, m', hmm', hm'm⟩, Units.ext ?_⟩
  exact hm

end Galois

section H90

variable (K L : Type) [Field K] [Field L] [Algebra K L] (A : Type) [Field A] [Algebra K A]
  (σ : L ≃ₐ[K] L)

def phi (ε : GL (Fin 2) (L ⊗[K] A)) (w : Fin 2 → L ⊗[K] A) : Fin 2 → L ⊗[K] A :=
  (ε : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)).mulVec fun i => AutomorphicForm.sigmaTensor K L A σ (w i)

theorem phi_add (ε : GL (Fin 2) (L ⊗[K] A)) (w w' : Fin 2 → L ⊗[K] A) :
    phi K L A σ ε (w + w') = phi K L A σ ε w + phi K L A σ ε w' := by
  unfold phi
  rw [← Matrix.mulVec_add]
  congr 1
  funext i
  simp

theorem phi_smul (ε : GL (Fin 2) (L ⊗[K] A)) (b : L ⊗[K] A) (w : Fin 2 → L ⊗[K] A) :
    phi K L A σ ε (b • w) = AutomorphicForm.sigmaTensor K L A σ b • phi K L A σ ε w := by
  unfold phi
  rw [← Matrix.mulVec_smul]
  congr 1
  funext i
  simp

theorem phi_neg (ε : GL (Fin 2) (L ⊗[K] A)) (w : Fin 2 → L ⊗[K] A) :
    phi K L A σ ε (-w) = -phi K L A σ ε w := by
  rw [← neg_one_smul (L ⊗[K] A) w, phi_smul, map_neg, map_one, neg_one_smul]

theorem phi_sub (ε : GL (Fin 2) (L ⊗[K] A)) (w w' : Fin 2 → L ⊗[K] A) :
    phi K L A σ ε (w - w') = phi K L A σ ε w - phi K L A σ ε w' := by
  rw [sub_eq_add_neg, phi_add, phi_neg, ← sub_eq_add_neg]

theorem phi_algebraMap_smul (ε : GL (Fin 2) (L ⊗[K] A)) (a : A) (w : Fin 2 → L ⊗[K] A) :
    phi K L A σ ε (a • w) = a • phi K L A σ ε w := by
  have h1 : a • w = (algebraMap A (L ⊗[K] A) a) • w := by
    funext i; simp [Algebra.smul_def]
  have h2 : a • phi K L A σ ε w = (algebraMap A (L ⊗[K] A) a) • phi K L A σ ε w := by
    funext i; simp [Algebra.smul_def]
  rw [h1, h2, phi_smul]
  congr 1
  exact sigmaTensor_one_tmul K L A σ a

theorem phi_phi (hσ : ∀ l : L, σ (σ l) = l) (ε : GL (Fin 2) (L ⊗[K] A))
    (hε : ε * AutomorphicForm.sigmaGL K L A σ ε = 1) (w : Fin 2 → L ⊗[K] A) :
    phi K L A σ ε (phi K L A σ ε w) = w := by
  have hmat : (ε : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) *
      (ε : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)).map (AutomorphicForm.sigmaTensor K L A σ) = 1 := by
    have := congrArg (fun g : GL (Fin 2) (L ⊗[K] A) => (g : Matrix (Fin 2) (Fin 2) (L ⊗[K] A))) hε
    simpa [coe_sigmaGL] using this
  unfold phi
  have hin : (fun i => AutomorphicForm.sigmaTensor K L A σ
        ((ε : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)).mulVec
          (fun k => AutomorphicForm.sigmaTensor K L A σ (w k)) i))
      = ((ε : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)).map (AutomorphicForm.sigmaTensor K L A σ)).mulVec
          w := by
    funext i
    rw [RingHom.map_mulVec]
    congr 1
    funext k
    exact sigmaTensor_sigmaTensor K L A σ hσ (w k)
  rw [hin, Matrix.mulVec_mulVec, hmat, Matrix.one_mulVec]

def phiLin (ε : GL (Fin 2) (L ⊗[K] A)) : (Fin 2 → L ⊗[K] A) →ₗ[A] (Fin 2 → L ⊗[K] A) where
  toFun := phi K L A σ ε
  map_add' := phi_add K L A σ ε
  map_smul' := phi_algebraMap_smul K L A σ ε

def fixedSub (ε : GL (Fin 2) (L ⊗[K] A)) : Submodule A (Fin 2 → L ⊗[K] A) :=
  LinearMap.eqLocus (phiLin K L A σ ε) LinearMap.id

theorem mem_fixedSub (ε : GL (Fin 2) (L ⊗[K] A)) (w : Fin 2 → L ⊗[K] A) :
    w ∈ fixedSub K L A σ ε ↔ phi K L A σ ε w = w :=
  Iff.rfl

def mulUnit (η : (L ⊗[K] A)ˣ) : (Fin 2 → L ⊗[K] A) ≃ₗ[A] (Fin 2 → L ⊗[K] A) where
  toFun w := (η : L ⊗[K] A) • w
  invFun w := ((η⁻¹ : (L ⊗[K] A)ˣ) : L ⊗[K] A) • w
  map_add' := smul_add _
  map_smul' a w := by
    funext i
    simp [Algebra.smul_def, mul_left_comm]
  left_inv w := by
    simp [smul_smul]
  right_inv w := by
    simp [smul_smul]

variable [CharZero A]

theorem fixedSub_inf_map_eq_bot (ε : GL (Fin 2) (L ⊗[K] A)) (η : (L ⊗[K] A)ˣ)
    (hη : AutomorphicForm.sigmaTensor K L A σ η = -η) :
    fixedSub K L A σ ε ⊓ (fixedSub K L A σ ε).map (mulUnit K L A η).toLinearMap = ⊥ := by
  rw [Submodule.eq_bot_iff]
  rintro x ⟨hxV, hxW⟩
  obtain ⟨w, hw, rfl⟩ := hxW
  have hwV : phi K L A σ ε w = w := hw
  have hxV' : phi K L A σ ε ((η : L ⊗[K] A) • w) = (η : L ⊗[K] A) • w := hxV
  rw [phi_smul, hη, hwV, neg_smul] at hxV'

  have h2 : (2 : A) • ((η : L ⊗[K] A) • w) = 0 := by
    rw [two_smul]
    nth_rewrite 1 [← hxV']
    exact neg_add_cancel _
  have := congrArg (fun y => (2 : A)⁻¹ • y) h2
  simpa [smul_smul, inv_mul_cancel₀ (two_ne_zero : (2 : A) ≠ 0)] using this

theorem finrank_fixedSub_le (h2 : Module.finrank K L = 2) (ε : GL (Fin 2) (L ⊗[K] A))
    (η : (L ⊗[K] A)ˣ) (hη : AutomorphicForm.sigmaTensor K L A σ η = -η) :
    Module.finrank A (fixedSub K L A σ ε) ≤ 2 := by
  haveI : FiniteDimensional K L := Module.finite_of_finrank_eq_succ h2
  have h4 : Module.finrank A (Fin 2 → L ⊗[K] A) = 4 := by
    rw [Module.finrank_pi_fintype, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      TensorProduct.finrank_rightAlgebra, h2, smul_eq_mul]
  set V := fixedSub K L A σ ε
  set V' := V.map (mulUnit K L A η).toLinearMap
  have hV' : Module.finrank A V' = Module.finrank A V := LinearEquiv.finrank_map_eq _ _
  have hinf : Module.finrank A ↥(V ⊓ V') = 0 := by
    rw [fixedSub_inf_map_eq_bot K L A σ ε η hη, finrank_bot]
  have hsum := Submodule.finrank_sup_add_finrank_inf_eq V V'
  have hle : Module.finrank A ↥(V ⊔ V') ≤ 4 := h4 ▸ Submodule.finrank_le _
  omega

omit [CharZero A] in

theorem exists_pair_of_finrank_le_two {M : Type*} [AddCommGroup M] [Module A M]
    (W : Submodule A M) [FiniteDimensional A W] (h : Module.finrank A W ≤ 2) :
    ∃ v : Fin 2 → M, (∀ j, v j ∈ W) ∧ W ≤ Submodule.span A (Set.range v) := by
  set n := Module.finrank A W
  let b := Module.finBasis A W
  let v : Fin 2 → M := fun j => if hj : (j : ℕ) < n then (b ⟨j, hj⟩ : M) else 0
  refine ⟨v, fun j => ?_, fun w hw => ?_⟩
  · by_cases hj : (j : ℕ) < n
    · simp only [v, dif_pos hj]; exact Submodule.coe_mem _
    · simp only [v, dif_neg hj]; exact zero_mem _
  · have hb : (⟨w, hw⟩ : W) ∈ Submodule.span A (Set.range b) := by
      rw [b.span_eq]; exact Submodule.mem_top
    have hmap := Submodule.mem_map_of_mem (f := W.subtype) hb
    rw [Submodule.map_span, ← Set.range_comp] at hmap
    refine Submodule.span_mono ?_ hmap
    rintro _ ⟨i, rfl⟩
    refine ⟨⟨i, by omega⟩, ?_⟩
    have hi : ((⟨i, by omega⟩ : Fin 2) : ℕ) < n := i.2
    simp only [v, dif_pos hi, Function.comp_apply, Submodule.coe_subtype]

theorem hilbert90 (h2 : Module.finrank K L = 2) (hσ : ∀ l : L, σ (σ l) = l)
    (hℓ : ∃ ℓ : L, σ ℓ ≠ ℓ) (ε : GL (Fin 2) (L ⊗[K] A))
    (hε : ε * AutomorphicForm.sigmaGL K L A σ ε = 1) :
    ∃ x : GL (Fin 2) (L ⊗[K] A), ε = x⁻¹ * AutomorphicForm.sigmaGL K L A σ x := by
  obtain ⟨ℓ, hℓ⟩ := hℓ

  set s := AutomorphicForm.sigmaTensor K L A σ with hs
  have hm : ℓ - σ ℓ ≠ 0 := sub_ne_zero.mpr (Ne.symm hℓ)
  let η : (L ⊗[K] A)ˣ := Units.mkOfMulEqOne ((ℓ - σ ℓ) ⊗ₜ[K] (1 : A)) ((ℓ - σ ℓ)⁻¹ ⊗ₜ[K] (1 : A))
    (by rw [Algebra.TensorProduct.tmul_mul_tmul, mul_inv_cancel₀ hm, mul_one]; rfl)
  have hηval : (η : L ⊗[K] A) = (ℓ - σ ℓ) ⊗ₜ[K] (1 : A) := rfl
  have hη : s η = -η := by
    rw [hηval, hs, sigmaTensor_tmul, map_sub, hσ, ← neg_sub, TensorProduct.neg_tmul]
  set θ : L ⊗[K] A := ℓ ⊗ₜ[K] (1 : A) with hθ
  have hθη : θ - s θ = η := by
    rw [hηval, hθ, hs, sigmaTensor_tmul, TensorProduct.sub_tmul]

  set V := fixedSub K L A σ ε with hV
  haveI : FiniteDimensional K L := Module.finite_of_finrank_eq_succ h2
  obtain ⟨v, hvV, hVle⟩ := exists_pair_of_finrank_le_two A V
    (finrank_fixedSub_le K L A σ h2 ε η hη)

  have hP : ∀ w, w + phi K L A σ ε w ∈ V := fun w => by
    rw [hV, mem_fixedSub, phi_add, phi_phi K L A σ hσ ε hε, add_comm]

  set S : Submodule (L ⊗[K] A) (Fin 2 → L ⊗[K] A) := Submodule.span (L ⊗[K] A) (Set.range v)
    with hS
  have hVS : ∀ u ∈ V, u ∈ S := fun u hu => by
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun A).mp (hVle hu)
    rw [← hc]
    refine Submodule.sum_mem _ fun j _ => ?_
    have : c j • v j = (algebraMap A (L ⊗[K] A) (c j)) • v j := by
      funext i; simp [Algebra.smul_def]
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
  have hall : ∀ w : Fin 2 → L ⊗[K] A, w ∈ S := fun w => by
    have h1 : θ • w + phi K L A σ ε (θ • w) ∈ S := hVS _ (hP (θ • w))
    have h2' : s θ • (w + phi K L A σ ε w) ∈ S := Submodule.smul_mem _ _ (hVS _ (hP w))
    have hdiff : θ • w + phi K L A σ ε (θ • w) - s θ • (w + phi K L A σ ε w) = (η : L ⊗[K] A) • w := by
      rw [phi_smul, smul_add, ← hθη, sub_smul]
      abel
    have hηw : (η : L ⊗[K] A) • w ∈ S := hdiff ▸ Submodule.sub_mem _ h1 h2'
    have := Submodule.smul_mem S ((η⁻¹ : (L ⊗[K] A)ˣ) : L ⊗[K] A) hηw
    rwa [smul_smul, Units.inv_mul, one_smul] at this

  set x : Matrix (Fin 2) (Fin 2) (L ⊗[K] A) := Matrix.of fun i j => v j i with hx
  have hxmul : ∀ c : Fin 2 → L ⊗[K] A, x.mulVec c = ∑ j, c j • v j := fun c => by
    funext i
    simp [hx, Matrix.mulVec, dotProduct, Finset.sum_apply, mul_comm]
  have hsurj : Function.Surjective x.mulVec := fun w => by
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun (L ⊗[K] A)).mp (hall w)
    exact ⟨c, (hxmul c).trans hc⟩
  obtain ⟨X, hX⟩ := Matrix.mulVec_surjective_iff_isUnit.mp hsurj

  have hfix : ε * AutomorphicForm.sigmaGL K L A σ X = X := by
    apply Matrix.GeneralLinearGroup.ext
    intro i j
    have hj : phi K L A σ ε (v j) = v j := hvV j
    have hij := congrFun hj i
    simp only [phi, Matrix.mulVec, dotProduct] at hij
    rw [Units.val_mul, Matrix.mul_apply]
    simp only [sigmaGL_apply, hX, hx, Matrix.of_apply]
    simpa [hX, hx] using hij
  refine ⟨X⁻¹, ?_⟩
  rw [inv_inv, map_inv, eq_mul_inv_iff_mul_eq, hfix]

end H90

section BasePoint

variable (K L : Type) [Field K] [CharZero K] [Field L] [Algebra K L]
  (A : Type) [Field A] [Algebra K A]
  (h2 : Module.finrank K L = 2) (σ : L ≃ₐ[K] L) (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)

local notation "sT" => AutomorphicForm.sigmaTensor K L A σ
local notation "sG" => AutomorphicForm.sigmaGL K L A σ
local notation "ι" => AutomorphicForm.toTensorGL K L A
local notation "incl" => (Algebra.TensorProduct.includeRight : A →ₐ[K] L ⊗[K] A)
local notation "Nm" => AutomorphicForm.normString K L A σ

theorem comm_of_mem_centralizer_toTensorGL {γ₁ : GL (Fin 2) A} (hγ₁ : AutomorphicForm.IsRegularSemisimple γ₁)
    {a b : GL (Fin 2) (L ⊗[K] A)}
    (ha : a ∈ Subgroup.centralizer ({ι γ₁} : Set (GL (Fin 2) (L ⊗[K] A))))
    (hb : b ∈ Subgroup.centralizer ({ι γ₁} : Set (GL (Fin 2) (L ⊗[K] A)))) : a * b = b * a :=
  mul_comm_of_mem_centralizer (isRegularSemisimple_toTensorGL K L A γ₁ hγ₁) ha hb

theorem sigmaGL_mem_centralizer_toTensorGL {γ₁ : GL (Fin 2) A} {a : GL (Fin 2) (L ⊗[K] A)}
    (ha : a ∈ Subgroup.centralizer ({ι γ₁} : Set (GL (Fin 2) (L ⊗[K] A)))) :
    sG a ∈ Subgroup.centralizer ({ι γ₁} : Set (GL (Fin 2) (L ⊗[K] A))) := by
  rw [Subgroup.mem_centralizer_singleton_iff] at ha ⊢
  have := congrArg sG ha
  rwa [map_mul, map_mul, sigmaGL_toTensorGL] at this

theorem toTensorGL_mem_centralizer_iff {γ₁ m : GL (Fin 2) A} :
    ι m ∈ Subgroup.centralizer ({ι γ₁} : Set (GL (Fin 2) (L ⊗[K] A))) ↔
      m ∈ Subgroup.centralizer ({γ₁} : Set (GL (Fin 2) A)) := by
  rw [Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_centralizer_singleton_iff, ← map_mul, ← map_mul]
  exact ⟨fun h => toTensorGL_injective K L A h, fun h => by rw [h]⟩

include h2 hgen

theorem mem_centralizer_of_normString_eq {δ₀ : GL (Fin 2) (L ⊗[K] A)} {γ₁ : GL (Fin 2) A}
    (hN : Nm δ₀ = ι γ₁) : δ₀ ∈ Subgroup.centralizer ({ι γ₁} : Set (GL (Fin 2) (L ⊗[K] A))) := by
  have hσ := (sigma_involutive_and_ne_one K L h2 σ hgen).1
  have h1 : sG δ₀ * δ₀ = δ₀ * sG δ₀ := by
    have := sigmaGL_normString K L A σ h2 hσ δ₀
    rw [hN, sigmaGL_toTensorGL, ← hN, normString_two K L A σ h2] at this
    exact this.symm
  rw [Subgroup.mem_centralizer_singleton_iff, ← hN, normString_two K L A σ h2]
  symm
  calc δ₀ * sG δ₀ * δ₀ = δ₀ * (sG δ₀ * δ₀) := by rw [mul_assoc]
    _ = δ₀ * (δ₀ * sG δ₀) := by rw [h1]

theorem mem_twistedCentralizer_iff_of_normString_eq {δ₀ : GL (Fin 2) (L ⊗[K] A)} {γ₁ : GL (Fin 2) A}
    (hγ₁ : AutomorphicForm.IsRegularSemisimple γ₁) (hN : Nm δ₀ = ι γ₁) (t : GL (Fin 2) (L ⊗[K] A)) :
    t ∈ AutomorphicForm.twistedCentralizer K L A σ δ₀ ↔
      ∃ m ∈ Subgroup.centralizer ({γ₁} : Set (GL (Fin 2) A)), ι m = t := by
  have hσ := (sigma_involutive_and_ne_one K L h2 σ hgen).1
  have hδ₀ := mem_centralizer_of_normString_eq K L A h2 σ hgen hN
  constructor
  · intro ht
    have htC : t ∈ Subgroup.centralizer ({ι γ₁} : Set (GL (Fin 2) (L ⊗[K] A))) := by
      rw [← hN]
      exact twistedCentralizer_le_centralizer_normString K L A σ h2 hσ δ₀ ht
    rw [mem_twistedCentralizer_iff] at ht
    have hcomm : t * δ₀ = δ₀ * t := comm_of_mem_centralizer_toTensorGL K L A hγ₁ htC hδ₀
    have hfix : sG t = t := by
      rw [hcomm] at ht
      exact (mul_left_cancel ht).symm
    obtain ⟨m, hm⟩ := exists_toTensorGL_eq_of_sigmaGL_eq K L A h2 σ hgen hfix
    refine ⟨m, ?_, hm⟩
    rw [← toTensorGL_mem_centralizer_iff K L A, hm]
    exact htC
  · rintro ⟨m, hm, rfl⟩
    have htC : ι m ∈ Subgroup.centralizer ({ι γ₁} : Set (GL (Fin 2) (L ⊗[K] A))) :=
      (toTensorGL_mem_centralizer_iff K L A).2 hm
    rw [mem_twistedCentralizer_iff, sigmaGL_toTensorGL]
    exact comm_of_mem_centralizer_toTensorGL K L A hγ₁ htC hδ₀

theorem exists_coboundary_mem_centralizer {γ₁ : GL (Fin 2) A} (hγ₁ : AutomorphicForm.IsRegularSemisimple γ₁)
    {t : GL (Fin 2) (L ⊗[K] A)} (ht : t ∈ Subgroup.centralizer ({ι γ₁} : Set (GL (Fin 2) (L ⊗[K] A))))
    (h1 : t * sG t = 1) :
    ∃ x ∈ Subgroup.centralizer ({ι γ₁} : Set (GL (Fin 2) (L ⊗[K] A))), t = x⁻¹ * sG x := by
  obtain ⟨hσ, hℓ⟩ := sigma_involutive_and_ne_one K L h2 σ hgen
  haveI : CharZero A := charZero_of_injective_algebraMap (algebraMap K A).injective
  obtain ⟨x₀, hx₀⟩ := hilbert90 K L A σ h2 hσ hℓ t h1
  have hsx₀ : sG x₀ = x₀ * t := by rw [hx₀, mul_inv_cancel_left]
  have htc : t * ι γ₁ = ι γ₁ * t := Subgroup.mem_centralizer_singleton_iff.mp ht

  have hfix : sG (x₀ * ι γ₁ * x₀⁻¹) = x₀ * ι γ₁ * x₀⁻¹ := by
    rw [map_mul, map_mul, map_inv, sigmaGL_toTensorGL, hsx₀]
    calc x₀ * t * ι γ₁ * (x₀ * t)⁻¹ = x₀ * (t * ι γ₁) * (x₀ * t)⁻¹ := by rw [mul_assoc x₀]
      _ = x₀ * (ι γ₁ * t) * (x₀ * t)⁻¹ := by rw [htc]
      _ = x₀ * ι γ₁ * x₀⁻¹ := by group
  obtain ⟨m, hm⟩ := exists_toTensorGL_eq_of_sigmaGL_eq K L A h2 σ hgen hfix

  have hinj := includeRight_injective K L A
  have htr : (m : Matrix (Fin 2) (Fin 2) A).trace = (γ₁ : Matrix (Fin 2) (Fin 2) A).trace := by
    apply hinj
    rw [← trace_toTensorGL, ← trace_toTensorGL, hm]
    have := trace_units_conj' K L A x₀⁻¹ (ι γ₁)
    rwa [inv_inv] at this
  have hdet : (m : Matrix (Fin 2) (Fin 2) A).det = (γ₁ : Matrix (Fin 2) (Fin 2) A).det := by
    apply hinj
    rw [← det_toTensorGL, ← det_toTensorGL, hm]
    have := det_units_conj' K L A x₀⁻¹ (ι γ₁)
    rwa [inv_inv] at this
  obtain ⟨Q, hQ⟩ := exists_units_conj_eq hγ₁ m htr hdet

  refine ⟨ι Q * x₀, ?_, ?_⟩
  · rw [Subgroup.mem_centralizer_singleton_iff]
    have hQ' : ι Q⁻¹ * ι γ₁ * ι Q = x₀ * ι γ₁ * x₀⁻¹ := by
      rw [← map_mul, ← map_mul, hQ, hm]
    calc ι Q * x₀ * ι γ₁ = ι Q * (x₀ * ι γ₁ * x₀⁻¹) * x₀ := by group
      _ = ι Q * (ι Q⁻¹ * ι γ₁ * ι Q) * x₀ := by rw [hQ']
      _ = ι γ₁ * (ι Q * x₀) := by rw [map_inv]; group
  · rw [map_mul, sigmaGL_toTensorGL, mul_inv_rev, hx₀]
    group

theorem exists_normString_conj_eq_toTensorGL [FiniteDimensional K L] {δ : GL (Fin 2) (L ⊗[K] A)}
    (hδ : AutomorphicForm.IsRegularSemisimple (Nm δ)) :
    ∃ (x : GL (Fin 2) (L ⊗[K] A)) (γ₁ : GL (Fin 2) A), AutomorphicForm.IsRegularSemisimple γ₁ ∧
      Nm (x⁻¹ * δ * sG x) = ι γ₁ := by
  have hσ := (sigma_involutive_and_ne_one K L h2 σ hgen).1
  haveI : IsArtinianRing (L ⊗[K] A) := IsArtinianRing.of_finite A (L ⊗[K] A)
  haveI : Nontrivial (L ⊗[K] A) := (includeRight_injective K L A).nontrivial
  set n : Matrix (Fin 2) (Fin 2) (L ⊗[K] A) :=
    ((Nm δ : GL (Fin 2) (L ⊗[K] A)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) with hn

  obtain ⟨a₀, ha₀⟩ := exists_one_tmul_of_sigmaTensor_eq K L A h2 σ hgen
    (sigmaTensor_trace_normString K L A σ h2 hσ δ)
  obtain ⟨d₀, hd₀⟩ := exists_one_tmul_of_sigmaTensor_eq K L A h2 σ hgen
    (sigmaTensor_det_normString K L A σ h2 hσ δ)
  have ha₀' : n.trace = incl a₀ := ha₀
  have hd₀' : n.det = incl d₀ := hd₀

  have hdisc : IsUnit (a₀ ^ 2 - 4 * d₀) := by
    rw [isUnit_iff_ne_zero]
    intro h0
    have hu : IsUnit (n.trace ^ 2 - 4 * n.det) := hδ
    rw [ha₀', hd₀', show incl a₀ ^ 2 - 4 * incl d₀ = incl (a₀ ^ 2 - 4 * d₀) by
      simp only [map_sub, map_mul, map_pow, map_ofNat], h0, map_zero] at hu
    exact not_isUnit_zero hu
  have hd₀ne : d₀ ≠ 0 := by
    intro h0
    have hu : IsUnit n.det := (Matrix.isUnit_iff_isUnit_det _).mp (Units.isUnit _)
    rw [hd₀', h0, map_zero] at hu
    exact not_isUnit_zero hu

  have hcu : IsUnit (comp a₀ d₀) := by
    rw [Matrix.isUnit_iff_isUnit_det, det_comp]
    exact isUnit_iff_ne_zero.mpr hd₀ne
  set γ₁ : GL (Fin 2) A := hcu.unit with hγ₁def
  have hγ₁val : (γ₁ : Matrix (Fin 2) (Fin 2) A) = comp a₀ d₀ := hcu.unit_spec
  have hγ₁ : AutomorphicForm.IsRegularSemisimple γ₁ := by
    unfold AutomorphicForm.IsRegularSemisimple
    rw [hγ₁val, trace_comp, det_comp]
    exact hdisc
  have htr : ((ι γ₁ : GL (Fin 2) (L ⊗[K] A)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)).trace = n.trace := by
    rw [trace_toTensorGL, hγ₁val, trace_comp, ha₀']
  have hdet : ((ι γ₁ : GL (Fin 2) (L ⊗[K] A)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)).det = n.det := by
    rw [det_toTensorGL, hγ₁val, det_comp, hd₀']
  obtain ⟨x, hx⟩ := exists_units_conj_eq hδ (ι γ₁) htr hdet
  exact ⟨x, γ₁, hγ₁, by rw [normString_conj K L A σ h2 hσ, hx]⟩

theorem exists_eq_sigmaConj_of_trace_det [FiniteDimensional K L] {δ : GL (Fin 2) (L ⊗[K] A)}
    (hδ : AutomorphicForm.IsRegularSemisimple (Nm δ)) (g : GL (Fin 2) (L ⊗[K] A))
    (htr : ((Nm g : GL (Fin 2) (L ⊗[K] A)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)).trace =
      ((Nm δ : GL (Fin 2) (L ⊗[K] A)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)).trace)
    (hdet : ((Nm g : GL (Fin 2) (L ⊗[K] A)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)).det =
      ((Nm δ : GL (Fin 2) (L ⊗[K] A)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)).det) :
    ∃ z : GL (Fin 2) (L ⊗[K] A), g = z⁻¹ * δ * sG z := by
  have hσ := (sigma_involutive_and_ne_one K L h2 σ hgen).1
  haveI : IsArtinianRing (L ⊗[K] A) := IsArtinianRing.of_finite A (L ⊗[K] A)
  obtain ⟨x, γ₁, hγ₁, hN₀⟩ := exists_normString_conj_eq_toTensorGL K L A h2 σ hgen hδ
  set δ₀ := x⁻¹ * δ * sG x with hδ₀def
  have hιreg : AutomorphicForm.IsRegularSemisimple (ι γ₁) := isRegularSemisimple_toTensorGL K L A γ₁ hγ₁

  have hNδ₀ : Nm δ₀ = x⁻¹ * Nm δ * x := normString_conj K L A σ h2 hσ δ x
  have htr' : ((Nm g : GL (Fin 2) (L ⊗[K] A)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)).trace =
      ((ι γ₁ : GL (Fin 2) (L ⊗[K] A)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)).trace := by
    rw [htr, ← hN₀, hNδ₀, trace_units_conj']
  have hdet' : ((Nm g : GL (Fin 2) (L ⊗[K] A)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)).det =
      ((ι γ₁ : GL (Fin 2) (L ⊗[K] A)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)).det := by
    rw [hdet, ← hN₀, hNδ₀, det_units_conj']
  obtain ⟨P, hP⟩ := exists_units_conj_eq hιreg (Nm g) htr' hdet'

  set g₁ := P⁻¹⁻¹ * g * sG P⁻¹ with hg₁def
  have hNg₁ : Nm g₁ = ι γ₁ := by
    rw [hg₁def, normString_conj K L A σ h2 hσ, ← hP]
    group

  have hg₁C := mem_centralizer_of_normString_eq K L A h2 σ hgen hNg₁
  have hδ₀C := mem_centralizer_of_normString_eq K L A h2 σ hgen hN₀
  have hsg₁C := sigmaGL_mem_centralizer_toTensorGL K L A σ hg₁C
  have hsδ₀C := sigmaGL_mem_centralizer_toTensorGL K L A σ hδ₀C
  set C := Subgroup.centralizer ({ι γ₁} : Set (GL (Fin 2) (L ⊗[K] A))) with hCdef
  have htC : g₁⁻¹ * δ₀ ∈ C := C.mul_mem (C.inv_mem hg₁C) hδ₀C

  have h1 : g₁⁻¹ * δ₀ * sG (g₁⁻¹ * δ₀) = 1 := by
    have e1 : δ₀ * (sG g₁)⁻¹ = (sG g₁)⁻¹ * δ₀ :=
      comm_of_mem_centralizer_toTensorGL K L A hγ₁ hδ₀C (C.inv_mem hsg₁C)
    have e2 : sG g₁ * g₁ = g₁ * sG g₁ := comm_of_mem_centralizer_toTensorGL K L A hγ₁ hsg₁C hg₁C
    have e3 : g₁ * sG g₁ = ι γ₁ := by rw [← normString_two K L A σ h2, hNg₁]
    have e4 : δ₀ * sG δ₀ = ι γ₁ := by rw [← normString_two K L A σ h2, hN₀]
    rw [map_mul, map_inv]
    calc g₁⁻¹ * δ₀ * ((sG g₁)⁻¹ * sG δ₀) = g₁⁻¹ * (δ₀ * (sG g₁)⁻¹) * sG δ₀ := by group
      _ = g₁⁻¹ * ((sG g₁)⁻¹ * δ₀) * sG δ₀ := by rw [e1]
      _ = (sG g₁ * g₁)⁻¹ * (δ₀ * sG δ₀) := by group
      _ = 1 := by rw [e2, e3, e4, inv_mul_cancel]
  obtain ⟨x₁, hx₁C, hx₁⟩ := exists_coboundary_mem_centralizer K L A h2 σ hgen hγ₁ htC h1

  have hcomm : g₁ * x₁⁻¹ = x₁⁻¹ * g₁ := comm_of_mem_centralizer_toTensorGL K L A hγ₁ hg₁C (C.inv_mem hx₁C)
  have hg₁ : g₁ = x₁ * δ₀ * (sG x₁)⁻¹ := by
    have : δ₀ = x₁⁻¹ * g₁ * sG x₁ := by rw [← hcomm, mul_assoc, ← hx₁, mul_inv_cancel_left]
    rw [this]
    group
  refine ⟨x * x₁⁻¹ * P, ?_⟩
  have hgg₁ : g = P⁻¹ * g₁ * sG P := by
    rw [hg₁def, map_inv, inv_inv]
    group
  rw [hgg₁, hg₁, hδ₀def, map_mul, map_mul, map_inv]
  group

end BasePoint

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

section Fibre

variable (K L : Type) [Field K] [Field L] [Algebra K L] (A : Type) [CommRing A] [Algebra K A]
  (σ : L ≃ₐ[K] L)

local notation "sG" => AutomorphicForm.sigmaGL K L A σ
local notation "Nm" => AutomorphicForm.normString K L A σ

def normFibre (δ : GL (Fin 2) (L ⊗[K] A)) : Set (GL (Fin 2) (L ⊗[K] A)) :=
  {g | ((Nm g : GL (Fin 2) (L ⊗[K] A)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)).trace =
        ((Nm δ : GL (Fin 2) (L ⊗[K] A)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)).trace ∧
      ((Nm g : GL (Fin 2) (L ⊗[K] A)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)).det =
        ((Nm δ : GL (Fin 2) (L ⊗[K] A)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)).det}

theorem self_mem_normFibre (δ : GL (Fin 2) (L ⊗[K] A)) : δ ∈ normFibre K L A σ δ := ⟨rfl, rfl⟩

variable (h2 : Module.finrank K L = 2) (hσ : ∀ l : L, σ (σ l) = l)
include h2 hσ

theorem twistConj_mem_normFibre {δ g : GL (Fin 2) (L ⊗[K] A)} (hg : g ∈ normFibre K L A σ δ)
    (x : GL (Fin 2) (L ⊗[K] A)) : x * g * (sG x)⁻¹ ∈ normFibre K L A σ δ := by
  obtain ⟨h1, h1'⟩ := hg
  have hN : Nm (x * g * (sG x)⁻¹) = x⁻¹⁻¹ * Nm g * x⁻¹ := by
    rw [← normString_conj K L A σ h2 hσ, map_inv, inv_inv]
  refine ⟨?_, ?_⟩
  · rw [← h1, hN]
    exact trace_units_conj' K L A x⁻¹ _
  · rw [← h1', hN]
    exact det_units_conj' K L A x⁻¹ _

@[reducible] def twistAction (δ : GL (Fin 2) (L ⊗[K] A)) : MulAction (GL (Fin 2) (L ⊗[K] A)) (normFibre K L A σ δ) where
  smul x y := ⟨x * y * (sG x)⁻¹, twistConj_mem_normFibre K L A σ h2 hσ y.2 x⟩
  one_smul y := Subtype.ext (by
    change (1 : GL (Fin 2) (L ⊗[K] A)) * y * (sG 1)⁻¹ = y
    rw [map_one, inv_one, mul_one, one_mul])
  mul_smul x x' y := Subtype.ext (by
    change x * x' * (y : GL (Fin 2) (L ⊗[K] A)) * (sG (x * x'))⁻¹ = x * (x' * y * (sG x')⁻¹) * (sG x)⁻¹
    rw [map_mul, mul_inv_rev]
    simp only [mul_assoc])

theorem twistAction_smul_val (δ : GL (Fin 2) (L ⊗[K] A)) (x : GL (Fin 2) (L ⊗[K] A))
    (y : normFibre K L A σ δ) :
    letI := twistAction K L A σ h2 hσ δ
    ((x • y : normFibre K L A σ δ) : GL (Fin 2) (L ⊗[K] A)) = x * y * (sG x)⁻¹ := rfl

end Fibre

section Proper

variable (K L : Type) [Field K] [CharZero K] [Field L] [Algebra K L] [FiniteDimensional K L]
  (A : Type) [Field A] [Algebra K A] [TopologicalSpace A] [IsTopologicalRing A] [T2Space A]
  [LocallyCompactSpace A] [SecondCountableTopology A]
  (h2 : Module.finrank K L = 2) (σ : L ≃ₐ[K] L) (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)

local notation "sG" => AutomorphicForm.sigmaGL K L A σ
local notation "Nm" => AutomorphicForm.normString K L A σ

include h2 hgen

theorem exists_isCompact_subset_twistedCentralizer_mul {δ : GL (Fin 2) (L ⊗[K] A)}
    (hδ : AutomorphicForm.IsRegularSemisimple (Nm δ)) {C : Set (GL (Fin 2) (L ⊗[K] A))} (hC : IsCompact C) :
    ∃ D : Set (GL (Fin 2) (L ⊗[K] A)), IsCompact D ∧
      {x : GL (Fin 2) (L ⊗[K] A) | x⁻¹ * δ * sG x ∈ C} ⊆
        (AutomorphicForm.twistedCentralizer K L A σ δ : Set (GL (Fin 2) (L ⊗[K] A))) * D := by
  classical
  have hσ := (sigma_involutive_and_ne_one K L h2 σ hgen).1
  haveI := AutomorphicForm.isTopologicalRing_tensor K L A
  haveI := AutomorphicForm.t2Space_tensor K L A
  haveI := AutomorphicForm.locallyCompactSpace_tensor K L A
  haveI := secondCountableTopology_tensor K L A
  haveI := AutomorphicForm.isTopologicalGroup_tensorGL K L A
  haveI := t2Space_GL (L ⊗[K] A)
  haveI := secondCountableTopology_GL (L ⊗[K] A)
  haveI := locallyCompactSpace_GL (L ⊗[K] A)
  haveI : SigmaCompactSpace (GL (Fin 2) (L ⊗[K] A)) := sigmaCompactSpace_of_locallyCompact_secondCountable
  set X := normFibre K L A σ δ with hXdef

  have hNc : Continuous fun g : GL (Fin 2) (L ⊗[K] A) => Nm g := by
    have : (fun g : GL (Fin 2) (L ⊗[K] A) => Nm g) = fun g => g * sG g := funext (normString_two K L A σ h2)
    rw [this]
    exact continuous_id.mul (continuous_sigmaGL K L A σ)
  have hcl : IsClosed X := by
    have hc : Continuous fun g : GL (Fin 2) (L ⊗[K] A) =>
        ((Nm g : GL (Fin 2) (L ⊗[K] A)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) :=
      Units.continuous_val.comp hNc
    exact IsClosed.inter (isClosed_eq hc.matrix_trace continuous_const)
      (isClosed_eq hc.matrix_det continuous_const)
  haveI : LocallyCompactSpace X := hcl.isClosedEmbedding_subtypeVal.locallyCompactSpace
  letI : MulAction (GL (Fin 2) (L ⊗[K] A)) X := twistAction K L A σ h2 hσ δ
  haveI : ContinuousSMul (GL (Fin 2) (L ⊗[K] A)) X := by
    refine ⟨?_⟩
    have : Continuous fun p : GL (Fin 2) (L ⊗[K] A) × X => p.1 * (p.2 : GL (Fin 2) (L ⊗[K] A)) * (sG p.1)⁻¹ :=
      (continuous_fst.mul (continuous_subtype_val.comp continuous_snd)).mul
        ((continuous_sigmaGL K L A σ).comp continuous_fst).inv
    exact this.subtype_mk _
  haveI : IsPretransitive (GL (Fin 2) (L ⊗[K] A)) X := by
    refine ⟨fun y₁ y₂ => ?_⟩
    obtain ⟨z₁, hz₁⟩ := exists_eq_sigmaConj_of_trace_det K L A h2 σ hgen hδ (y₁ : GL (Fin 2) (L ⊗[K] A)) y₁.2.1 y₁.2.2
    obtain ⟨z₂, hz₂⟩ := exists_eq_sigmaConj_of_trace_det K L A h2 σ hgen hδ (y₂ : GL (Fin 2) (L ⊗[K] A)) y₂.2.1 y₂.2.2
    refine ⟨z₂⁻¹ * z₁, Subtype.ext ?_⟩
    rw [twistAction_smul_val, hz₁, hz₂, map_mul, map_inv]
    group
  set y₀ : X := ⟨δ, self_mem_normFibre K L A σ δ⟩ with hy₀

  have hopen : IsOpenMap fun x : GL (Fin 2) (L ⊗[K] A) => x • y₀ := isOpenMap_smul_of_sigmaCompact y₀
  set Kc : Set X := ((↑) : X → GL (Fin 2) (L ⊗[K] A)) ⁻¹' C with hKc
  have hKcc : IsCompact Kc := hcl.isClosedEmbedding_subtypeVal.isCompact_preimage hC
  have hN : ∀ x : GL (Fin 2) (L ⊗[K] A), ∃ N : Set (GL (Fin 2) (L ⊗[K] A)), IsCompact N ∧ N ∈ 𝓝 x := fun x =>
    exists_compact_mem_nhds x
  choose N hNc' hNn using hN
  have hcover : Kc ⊆ ⋃ x : GL (Fin 2) (L ⊗[K] A), (fun x : GL (Fin 2) (L ⊗[K] A) => x • y₀) '' interior (N x) := by
    intro y _
    obtain ⟨x, hx⟩ := exists_smul_eq (GL (Fin 2) (L ⊗[K] A)) y₀ y
    exact mem_iUnion.mpr ⟨x, x, mem_interior_iff_mem_nhds.mpr (hNn x), hx⟩
  obtain ⟨t, ht⟩ := hKcc.elim_finite_subcover
    (fun x => (fun x : GL (Fin 2) (L ⊗[K] A) => x • y₀) '' interior (N x))
    (fun x => hopen _ isOpen_interior) hcover
  refine ⟨⋃ x ∈ t, (N x)⁻¹, t.isCompact_biUnion fun x _ => (hNc' x).inv, ?_⟩
  intro z hz
  have hzK : (z⁻¹ • y₀ : X) ∈ Kc := by
    change ((z⁻¹ • y₀ : X) : GL (Fin 2) (L ⊗[K] A)) ∈ C
    rw [twistAction_smul_val, map_inv, inv_inv]
    exact hz
  obtain ⟨x, hxt, n, hn, hnz⟩ : ∃ x ∈ t, ∃ n ∈ interior (N x), n • y₀ = z⁻¹ • y₀ := by
    have := ht hzK
    simp only [mem_iUnion, mem_image, exists_prop] at this
    obtain ⟨x, hxt, n, hn, hnz⟩ := this
    exact ⟨x, hxt, n, hn, hnz⟩
  have hval : n * δ * (sG n)⁻¹ = z⁻¹ * δ * (sG z⁻¹)⁻¹ := by
    have := congrArg (fun y : X => (y : GL (Fin 2) (L ⊗[K] A))) hnz
    exact this
  rw [map_inv, inv_inv] at hval

  have hcen : z * n ∈ AutomorphicForm.twistedCentralizer K L A σ δ := by
    rw [AutomorphicForm.twistedCentralizer, AutomorphicForm.mem_sigmaCentralizer_iff, map_mul]
    calc z * n * δ * (sG z * sG n)⁻¹ = z * (n * δ * (sG n)⁻¹) * (sG z)⁻¹ := by group
      _ = z * (z⁻¹ * δ * sG z) * (sG z)⁻¹ := by rw [hval]
      _ = δ := by group
  refine Set.mem_mul.mpr ⟨z * n, hcen, n⁻¹, ?_, by group⟩
  exact mem_iUnion₂.mpr ⟨x, hxt, Set.inv_mem_inv.mpr (interior_subset hn)⟩

end Proper

section Section

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

variable (T : Subgroup G) [MeasurableSpace T] [BorelSpace T] (τ : Measure T)

theorem isClosedEmbedding_val_mul (hT : IsClosed (T : Set G)) (x : G) :
    IsClosedEmbedding fun t : T => (t : G) * x :=
  (Homeomorph.mulRight x).isClosedEmbedding.comp hT.isClosedEmbedding_subtypeVal

def avg (ψ : G → ℝ) (x : G) : ℝ := ∫ t : T, ψ ((t : G) * x) ∂τ

variable {T τ}

theorem avg_mul [τ.IsMulRightInvariant] (ψ : G → ℝ) (t₀ : T) (x : G) :
    avg T τ ψ ((t₀ : G) * x) = avg T τ ψ x := by
  unfold avg
  have : (fun t : T => ψ ((t : G) * ((t₀ : G) * x))) = fun t : T => (fun s : T => ψ ((s : G) * x)) (t * t₀) := by
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

theorem exists_sectionFn [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
    (T : Subgroup G) (hT : IsClosed (T : Set G)) [MeasurableSpace T] [BorelSpace T]
    (τ : Measure T) [τ.IsHaarMeasure] [τ.IsMulRightInvariant]
    {E C : Set G} (hC : IsCompact C) (hE : E ⊆ (T : Set G) * C) :
    ∃ w : G → ℝ, (∀ x, 0 ≤ w x) ∧ Measurable w ∧ HasCompactSupport w ∧
      ∀ x ∈ E, ∫ t : T, w ((t : G) * x) ∂τ = 1 := by
  obtain ⟨ψ, hψC, -, hψs, hψ01⟩ := exists_continuous_one_zero_of_isCompact hC isClosed_empty
    (Set.disjoint_empty C)
  have hψc : Continuous ψ := ψ.continuous
  have hψ0 : ∀ x, 0 ≤ ψ x := fun x => (hψ01 x).1
  haveI : LocallyCompactSpace T := hT.isClosedEmbedding_subtypeVal.locallyCompactSpace
  have hΨc : Continuous (avg T τ ψ) := continuous_avg hT hψc hψs
  refine ⟨fun x => ψ x / avg T τ ψ x, fun x => div_nonneg (hψ0 x) (avg_nonneg hψ0 x),
    hψc.measurable.div hΨc.measurable, ?_, ?_⟩
  · refine hψs.mono ?_
    intro x hx
    rw [Function.mem_support] at hx ⊢
    exact fun h => hx (by simp [h])
  · intro x hx
    obtain ⟨t₀, ht₀, c, hc, rfl⟩ := Set.mem_mul.mp (hE hx)
    have hpos : 0 < avg T τ ψ (t₀ * c) := by
      have := avg_mul (T := T) (τ := τ) ψ ⟨t₀, ht₀⟩ c
      simp only at this
      rw [this]
      exact avg_pos hT hψc hψs hψ0 (by rw [hψC hc]; simp)
    have hinv : ∀ t : T, avg T τ ψ ((t : G) * (t₀ * c)) = avg T τ ψ (t₀ * c) := fun t =>
      avg_mul ψ t (t₀ * c)
    simp_rw [hinv]
    rw [integral_div, div_eq_one_iff_eq hpos.ne']
    rfl

end Section

section Main

theorem isMulRightInvariant_of_comm {T : Type*} [Group T] (hcomm : ∀ s t : T, s * t = t * s)
    [MeasurableSpace T] (τ : Measure T) [τ.IsMulLeftInvariant] : τ.IsMulRightInvariant := by
  refine ⟨fun g => ?_⟩
  have : (fun t : T => t * g) = fun t : T => g * t := funext fun t => hcomm t g
  rw [this]
  exact map_mul_left_eq_self τ g

variable (K L : Type) [Field K] [CharZero K] [Field L] [Algebra K L] [FiniteDimensional K L]
  (A : Type) [Field A] [Algebra K A] [TopologicalSpace A] [IsTopologicalRing A] [T2Space A]
  [LocallyCompactSpace A] [SecondCountableTopology A]
  (h2 : Module.finrank K L = 2) (σ : L ≃ₐ[K] L) (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)

include h2 hgen

theorem main (μ : @Measure (GL (Fin 2) (L ⊗[K] A)) (AutomorphicForm.glBorelOf (L ⊗[K] A)))
    (δ : GL (Fin 2) (L ⊗[K] A))
    (hδ : AutomorphicForm.IsRegularSemisimple (AutomorphicForm.normString K L A σ δ))
    (τ' : @Measure (AutomorphicForm.twistedCentralizer K L A σ δ)
      (AutomorphicForm.twistedCentralizerBorel K L A σ δ))
    (hτ' : @Measure.IsHaarMeasure _ _ _ (AutomorphicForm.twistedCentralizerBorel K L A σ δ) τ')
    (φ : GL (Fin 2) (L ⊗[K] A) → ℂ) (hφ : HasCompactSupport φ) :
    ∃ I : ℂ, AutomorphicForm.IsTwistedOrbitalIntegralOn K L A σ μ δ τ' φ I := by
  have hσ := (sigma_involutive_and_ne_one K L h2 σ hgen).1
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
  have hTc : IsClosed ((AutomorphicForm.twistedCentralizer K L A σ δ : Subgroup (GL (Fin 2) (L ⊗[K] A))) :
      Set (GL (Fin 2) (L ⊗[K] A))) :=
    isClosed_twistedCentralizer K L A σ δ

  have hle := twistedCentralizer_le_centralizer_normString K L A σ h2 hσ δ
  have hcomm : ∀ s t : AutomorphicForm.twistedCentralizer K L A σ δ, s * t = t * s := fun s t =>
    Subtype.ext (mul_comm_of_mem_centralizer hδ (hle s.2) (hle t.2))
  haveI : τ'.IsMulRightInvariant := isMulRightInvariant_of_comm hcomm τ'

  obtain ⟨D, hD, hsub⟩ :=
    exists_isCompact_subset_twistedCentralizer_mul K L A h2 σ hgen hδ hφ
  have hE : {x : GL (Fin 2) (L ⊗[K] A) | φ (x⁻¹ * δ * AutomorphicForm.sigmaGL K L A σ x) ≠ 0} ⊆
      ((AutomorphicForm.twistedCentralizer K L A σ δ : Subgroup (GL (Fin 2) (L ⊗[K] A))) :
        Set (GL (Fin 2) (L ⊗[K] A))) * D := by
    intro x hx
    exact hsub (subset_tsupport φ (Function.mem_support.mpr hx))
  obtain ⟨w, hw0, hwm, hws, hw1⟩ :=
    exists_sectionFn (AutomorphicForm.twistedCentralizer K L A σ δ) hTc τ' hD hE
  exact ⟨_, w, ⟨hw0, hwm, hws, fun x hx => hw1 x hx⟩, rfl⟩

end Main

end P2mTwistedOrbitalExists

end

open AutomorphicForm in
theorem solution
    (K L : Type) [Field K] [CharZero K] [Field L] [Algebra K L] [FiniteDimensional K L]
    (h2 : Module.finrank K L = 2) (σ : L ≃ₐ[K] L)
    (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (A : Type) [Field A] [Algebra K A] [TopologicalSpace A] [IsTopologicalRing A] [T2Space A]
    [LocallyCompactSpace A] [SecondCountableTopology A]
    (μ : @Measure (GL (Fin 2) (L ⊗[K] A)) (AutomorphicForm.glBorelOf (L ⊗[K] A)))
    (δ : GL (Fin 2) (L ⊗[K] A))
    (hδ : AutomorphicForm.IsRegularSemisimple (AutomorphicForm.normString K L A σ δ))
    (τ' : @Measure (AutomorphicForm.twistedCentralizer K L A σ δ)
      (AutomorphicForm.twistedCentralizerBorel K L A σ δ))
    (hτ' : @Measure.IsHaarMeasure _ _ _ (AutomorphicForm.twistedCentralizerBorel K L A σ δ) τ')
    (φ : GL (Fin 2) (L ⊗[K] A) → ℂ) (hφ : HasCompactSupport φ) :
    ∃ I : ℂ, AutomorphicForm.IsTwistedOrbitalIntegralOn K L A σ μ δ τ' φ I :=
  P2mTwistedOrbitalExists.main K L A h2 σ hgen μ δ hδ τ' hτ' φ hφ

end S_AutomorphicForm_IsTwistedOrbitalIntegralOn_exists_of_isRegularSemisimple_normString_of_finrank_eq_two
end P2MW
export P2MW.S_AutomorphicForm_IsTwistedOrbitalIntegralOn_exists_of_isRegularSemisimple_normString_of_finrank_eq_two (solution)

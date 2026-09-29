-- Prove2me | solution 1 for AutomorphicForm.exists_closure_iff_det_mem_integers_and_norm_det_trace_mul_absNorm_sq_eq_norm_sixteen_of_forall_isUnit
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/827cecbf-dd9c-5353-9b7f-f6b5135c4338

import Definitions.Def_AutomorphicForm_TwistedCommutant
import Definitions.Def_AutomorphicForm_BaseChangePlaces
import Definitions.Def_NumberField_AdelicHaar
import Definitions.Def_NumberField_TateGlobalZeta
import Theorems.Thm_AutomorphicForm_exists_trace_eq_one_tmul_and_det_eq_one_tmul_and_norm_sq_le_of_forall_isUnit
import Theorems.Thm_AutomorphicForm_exists_norm_det_mul_absNorm_eq_one_and_exists_norm_trace_eq_one_of_forall_isUnit
import Theorems.Thm_IsDedekindDomain_HeightOneSpectrum_relIndex_span_range_mul_norm_det_eq_one_of_forall_mem_span
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_closure_iff_det_mem_integers_and_norm_det_trace_mul_absNorm_sq_eq_norm_sixteen_of_forall_isUnit

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

open NumberField IsDedekindDomain AutomorphicForm
open scoped TensorProduct TensorProduct.RightActions

local infixr:73 " *' " => HSMul.hSMul
local macro_rules | `($x *' $y) => `(leftact% HSMul.hSMul $x $y)

noncomputable section

namespace P2mMaxOrdDisc

section Local

variable (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))

def qv : ℝ := ((Ideal.absNorm v.asIdeal : ℕ) : ℝ)

theorem one_lt_qv : 1 < qv K v := by
  unfold qv
  exact_mod_cast NumberField.HeightOneSpectrum.one_lt_absNorm v

theorem qv_pos : 0 < qv K v := zero_lt_one.trans (one_lt_qv K v)

theorem two_le_qv : (2 : ℝ) ≤ qv K v := by
  unfold qv
  exact_mod_cast Nat.succ_le_of_lt (NumberField.HeightOneSpectrum.one_lt_absNorm v)

theorem qv_ne_zero : qv K v ≠ 0 := (qv_pos K v).ne'

theorem norm_eq_toNNReal (x : v.adicCompletion K) :
    ‖x‖ = ((WithZeroMulInt.toNNReal (NumberField.HeightOneSpectrum.absNorm_ne_zero v) (Valued.v x) : NNReal) : ℝ) :=
  NumberField.FinitePlace.norm_def v x

theorem exists_norm_eq_zpow {x : v.adicCompletion K} (hx : x ≠ 0) : ∃ n : ℤ, ‖x‖ = qv K v ^ n := by
  have hv : Valued.v x ≠ 0 := (Valuation.ne_zero_iff _).2 hx
  refine ⟨Multiplicative.toAdd (WithZero.unzero hv), ?_⟩
  rw [norm_eq_toNNReal, WithZeroMulInt.toNNReal_neg_apply _ hv]
  push_cast
  rfl

theorem norm_le_one_iff_mem (x : v.adicCompletion K) : ‖x‖ ≤ 1 ↔ x ∈ v.adicCompletionIntegers K := by
  rw [HeightOneSpectrum.mem_adicCompletionIntegers, norm_eq_toNNReal, ← NNReal.coe_one, NNReal.coe_le_coe,
    WithZeroMulInt.toNNReal_le_one_iff (NumberField.HeightOneSpectrum.one_lt_absNorm_nnreal v)]

theorem norm_coe_le_one (a : v.adicCompletionIntegers K) : ‖(a : v.adicCompletion K)‖ ≤ 1 :=
  (norm_le_one_iff_mem K v _).2 a.2

theorem norm_le_zpow_sub_one_of_lt {x : v.adicCompletion K} {m : ℤ} (h : ‖x‖ < qv K v ^ m) :
    ‖x‖ ≤ qv K v ^ (m - 1) := by
  by_cases hx : x = 0
  · rw [hx, norm_zero]; exact zpow_nonneg (qv_pos K v).le _
  obtain ⟨n, hn⟩ := exists_norm_eq_zpow K v hx
  rw [hn] at h ⊢
  have hlt : n < m := (zpow_lt_zpow_iff_right₀ (one_lt_qv K v)).1 h
  exact zpow_le_zpow_right₀ (one_lt_qv K v).le (by omega)

theorem zpow_add_one_le_norm_of_lt {x : v.adicCompletion K} {m : ℤ} (h : qv K v ^ m < ‖x‖) :
    qv K v ^ (m + 1) ≤ ‖x‖ := by
  have hx : x ≠ 0 := by
    rintro rfl
    rw [norm_zero] at h
    exact lt_irrefl _ ((zpow_pos (qv_pos K v) m).trans h)
  obtain ⟨n, hn⟩ := exists_norm_eq_zpow K v hx
  rw [hn] at h ⊢
  have hlt : m < n := (zpow_lt_zpow_iff_right₀ (one_lt_qv K v)).1 h
  exact zpow_le_zpow_right₀ (one_lt_qv K v).le (by omega)

theorem exists_uniformiser : ∃ ϖ : v.adicCompletion K, ‖ϖ‖ = (qv K v)⁻¹ := by
  obtain ⟨π, hπ⟩ := HeightOneSpectrum.valuation_exists_uniformizer K v
  refine ⟨algebraMap K (v.adicCompletion K) π, ?_⟩
  have hval : Valued.v (algebraMap K (v.adicCompletion K) π) = WithZero.exp (-1 : ℤ) :=
    (HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v π).trans hπ
  have hne : Valued.v (algebraMap K (v.adicCompletion K) π) ≠ 0 := by
    rw [hval]; exact WithZero.coe_ne_zero
  rw [norm_eq_toNNReal, WithZeroMulInt.toNNReal_neg_apply _ hne]
  push_cast
  unfold qv
  have : Multiplicative.toAdd (WithZero.unzero hne) = -1 := by
    have h2 : WithZero.unzero hne = Multiplicative.ofAdd (-1 : ℤ) := by
      apply WithZero.coe_injective
      rw [WithZero.coe_unzero, hval]
      rfl
    rw [h2]
    rfl
  rw [this, zpow_neg, zpow_one]

theorem two_ne_zero' : (2 : v.adicCompletion K) ≠ 0 := by
  rw [show (2 : v.adicCompletion K) = algebraMap K (v.adicCompletion K) 2 by norm_num [map_ofNat]]
  exact (map_ne_zero_iff _ (algebraMap K (v.adicCompletion K)).injective).2 two_ne_zero

theorem norm_two_le_one : ‖(2 : v.adicCompletion K)‖ ≤ 1 := by
  have := IsUltrametricDist.norm_natCast_le_one (v.adicCompletion K) 2
  rwa [Nat.cast_ofNat] at this

end Local

section FrameSec

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  (v : HeightOneSpectrum (𝓞 K))

scoped instance instIsScalarTowerTensor :
    IsScalarTower (v.adicCompletion K) (L ⊗[K] v.adicCompletion K) (L ⊗[K] v.adicCompletion K) :=
  ⟨fun a x y => by
    show (a *' x) * y = a *' (x * y)
    rw [rightActions_smul_eq K L (v.adicCompletion K) a, rightActions_smul_eq K L (v.adicCompletion K) a,
      mul_assoc]⟩

scoped instance instSMulCommClassTensor :
    SMulCommClass (v.adicCompletion K) (L ⊗[K] v.adicCompletion K) (L ⊗[K] v.adicCompletion K) :=
  ⟨fun a x y => by
    show a *' (x * y) = x * (a *' y)
    rw [rightActions_smul_eq K L (v.adicCompletion K) a, rightActions_smul_eq K L (v.adicCompletion K) a,
      mul_left_comm]⟩

structure Frame where
  σ : L ≃ₐ[K] L
  δ : GL (Fin 2) (L ⊗[K] v.adicCompletion K)
  e : Fin 4 → Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)
  h2 : Module.finrank K L = 2
  hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ
  hbasis : ∀ X : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K),
    X ∈ twistedCommutant K L (v.adicCompletion K) σ δ ↔
      ∃! a : Fin 4 → v.adicCompletion K,
        X = ∑ i, (e i).map (fun t : L ⊗[K] v.adicCompletion K => t * ((1 : L) ⊗ₜ[K] a i))
  hdiv : ∀ X ∈ twistedCommutant K L (v.adicCompletion K) σ δ, X ≠ 0 → IsUnit X

variable {K L v}

namespace Frame

variable (Φ : Frame K L v)

abbrev Dt : Type := ↥(twistedCommutant K L (v.adicCompletion K) Φ.σ Φ.δ)

theorem smul_mem {X : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)}
    (hX : X ∈ twistedCommutant K L (v.adicCompletion K) Φ.σ Φ.δ) (a : v.adicCompletion K) :
    a *' X ∈ twistedCommutant K L (v.adicCompletion K) Φ.σ Φ.δ := by
  have h := includeRight_smul_mem_twistedCommutant (σ := Φ.σ) Φ.δ hX a
  have heq : (Algebra.TensorProduct.includeRight (R := K) (A := L) a) *' X = a *' X := by
    ext i j
    simp only [Matrix.smul_apply, smul_eq_mul, Algebra.TensorProduct.includeRight_apply]
    rw [rightActions_smul_eq K L (v.adicCompletion K) a]
  rwa [heq] at h

scoped instance instSMulF : SMul (v.adicCompletion K) Φ.Dt :=
  ⟨fun a X => ⟨a *' (X : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)), Φ.smul_mem X.2 a⟩⟩

@[scoped simp] theorem coe_smulF (a : v.adicCompletion K) (X : Φ.Dt) :
    ((a *' X : Φ.Dt) : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)) =
      a *' (X : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)) := rfl

def coeHom : Φ.Dt →+ Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K) where
  toFun := Subtype.val
  map_zero' := rfl
  map_add' _ _ := rfl

scoped instance instModuleF : Module (v.adicCompletion K) Φ.Dt :=
  Function.Injective.module (v.adicCompletion K) Φ.coeHom Subtype.val_injective (fun _ _ => rfl)

scoped instance instIsScalarTowerDt : IsScalarTower (v.adicCompletion K) Φ.Dt Φ.Dt :=
  ⟨fun a X Y => Subtype.ext (by
    show (a *' (X : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K))) *
        (Y : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)) =
      a *' ((X : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)) *
        (Y : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)))
    exact Matrix.smul_mul a _ _)⟩

scoped instance instSMulCommClassDt : SMulCommClass (v.adicCompletion K) Φ.Dt Φ.Dt :=
  ⟨fun a X Y => Subtype.ext (by
    show a *' ((X : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)) *
        (Y : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K))) =
      (X : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)) *
        (a *' (Y : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)))
    exact (Matrix.mul_smul _ a _).symm)⟩

scoped instance instSMulO : SMul (v.adicCompletionIntegers K) Φ.Dt :=
  ⟨fun a X => ⟨(a : v.adicCompletion K) *' (X : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)),
    Φ.smul_mem X.2 a⟩⟩

@[scoped simp] theorem coe_smulO (a : v.adicCompletionIntegers K) (X : Φ.Dt) :
    ((a *' X : Φ.Dt) : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)) =
      (a : v.adicCompletion K) *' (X : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)) := rfl

theorem smulO_eq (a : v.adicCompletionIntegers K) (X : Φ.Dt) : a *' X = (a : v.adicCompletion K) *' X := rfl

scoped instance instModuleO : Module (v.adicCompletionIntegers K) Φ.Dt :=
  Function.Injective.module (v.adicCompletionIntegers K) Φ.coeHom Subtype.val_injective (fun _ _ => rfl)

scoped instance instTowerOF : IsScalarTower (v.adicCompletionIntegers K) (v.adicCompletion K) Φ.Dt :=
  ⟨fun a b X => Subtype.ext (by
    show ((a *' b : v.adicCompletion K)) *' (X : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)) =
      (a : v.adicCompletion K) *' (b *' (X : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)))
    rw [Algebra.smul_def a b, mul_smul]
    rfl)⟩

theorem map_mulOne_eq_smul (X : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)) (a : v.adicCompletion K) :
    X.map (fun t : L ⊗[K] v.adicCompletion K => t * ((1 : L) ⊗ₜ[K] a)) = a *' X := by
  ext i j
  simp only [Matrix.map_apply, Matrix.smul_apply]
  rw [rightActions_smul_eq K L (v.adicCompletion K) a, mul_comm]

theorem sum_map_eq (a : Fin 4 → v.adicCompletion K) :
    ∑ i, (Φ.e i).map (fun t : L ⊗[K] v.adicCompletion K => t * ((1 : L) ⊗ₜ[K] a i)) = ∑ i, a i *' Φ.e i :=
  Finset.sum_congr rfl fun i _ => map_mulOne_eq_smul (Φ.e i) (a i)

theorem li_e : LinearIndependent (v.adicCompletion K) Φ.e := by
  rw [Fintype.linearIndependent_iff]
  intro c hc
  have hu := (Φ.hbasis 0).1 (zero_mem _)
  have h1 : (0 : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)) =
      ∑ i, (Φ.e i).map (fun t : L ⊗[K] v.adicCompletion K => t * ((1 : L) ⊗ₜ[K] c i)) := by
    rw [sum_map_eq, hc]
  have h2 : (0 : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)) =
      ∑ i, (Φ.e i).map (fun t : L ⊗[K] v.adicCompletion K => t * ((1 : L) ⊗ₜ[K] (0 : Fin 4 → v.adicCompletion K) i)) := by
    rw [sum_map_eq]; simp
  have hc0 : c = 0 := hu.unique h1 h2
  intro i
  rw [hc0]; rfl

theorem e_mem (i : Fin 4) : Φ.e i ∈ twistedCommutant K L (v.adicCompletion K) Φ.σ Φ.δ := by
  rw [Φ.hbasis]
  have hsingle : ∑ j, (Pi.single i (1 : v.adicCompletion K) : Fin 4 → v.adicCompletion K) j *' Φ.e j = Φ.e i := by
    rw [Finset.sum_eq_single i]
    · rw [Pi.single_eq_same, one_smul]
    · intro j _ hj; rw [Pi.single_eq_of_ne hj, zero_smul]
    · intro h; exact absurd (Finset.mem_univ i) h
  refine ⟨Pi.single i 1, ?_, fun a ha => ?_⟩
  · show Φ.e i = ∑ j, (Φ.e j).map (fun t : L ⊗[K] v.adicCompletion K => t * ((1 : L) ⊗ₜ[K] (Pi.single i (1 : v.adicCompletion K) : Fin 4 → v.adicCompletion K) j))
    rw [sum_map_eq, hsingle]
  beta_reduce at ha
  rw [sum_map_eq] at ha
  have hzero : ∑ j, (a j - (Pi.single i (1 : v.adicCompletion K) : Fin 4 → v.adicCompletion K) j) *' Φ.e j = 0 := by
    simp only [sub_smul, Finset.sum_sub_distrib]
    rw [hsingle, ← ha, sub_self]
  funext j
  exact sub_eq_zero.1 (Fintype.linearIndependent_iff.1 Φ.li_e _ hzero j)

def eD (i : Fin 4) : Φ.Dt := ⟨Φ.e i, Φ.e_mem i⟩

@[scoped simp] theorem coe_eD (i : Fin 4) : (Φ.eD i : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)) = Φ.e i := rfl

theorem coe_sum_smul (a : Fin 4 → v.adicCompletion K) :
    ((∑ i, a i *' Φ.eD i : Φ.Dt) : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)) = ∑ i, a i *' Φ.e i := by
  show Φ.coeHom (∑ i, a i *' Φ.eD i) = _
  rw [map_sum]
  rfl

theorem exists_repr (X : Φ.Dt) : ∃ a : Fin 4 → v.adicCompletion K, X = ∑ i, a i *' Φ.eD i := by
  obtain ⟨a, ha, -⟩ := (Φ.hbasis X).1 X.2
  refine ⟨a, Subtype.ext ?_⟩
  rw [coe_sum_smul, ← sum_map_eq]
  exact ha

def coeLin : Φ.Dt →ₗ[v.adicCompletion K] Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K) where
  toFun := Subtype.val
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem li_eD : LinearIndependent (v.adicCompletion K) Φ.eD :=
  LinearIndependent.of_comp Φ.coeLin Φ.li_e

def bD : Module.Basis (Fin 4) (v.adicCompletion K) Φ.Dt :=
  Module.Basis.mk Φ.li_eD (fun X _ => by
    obtain ⟨a, rfl⟩ := Φ.exists_repr X
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩))

scoped instance instFiniteF : Module.Finite (v.adicCompletion K) Φ.Dt := Module.Finite.of_basis Φ.bD

theorem finrank_Dt : Module.finrank (v.adicCompletion K) Φ.Dt = 4 := by
  rw [Module.finrank_eq_card_basis Φ.bD, Fintype.card_fin]

theorem exists_td (X : Φ.Dt) : ∃ p : v.adicCompletion K × v.adicCompletion K,
    (X : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)).trace = (1 : L) ⊗ₜ[K] p.1 ∧
    (X : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)).det = (1 : L) ⊗ₜ[K] p.2 ∧ ‖p.1‖ ^ 2 ≤ ‖p.2‖ := by
  obtain ⟨t, n, h⟩ :=
    AutomorphicForm.exists_trace_eq_one_tmul_and_det_eq_one_tmul_and_norm_sq_le_of_forall_isUnit
      K L Φ.h2 Φ.σ Φ.hgen v Φ.δ Φ.hdiv X.1 X.2
  exact ⟨(t, n), h⟩

def tK (X : Φ.Dt) : v.adicCompletion K := (Classical.choose (Φ.exists_td X)).1

def dK (X : Φ.Dt) : v.adicCompletion K := (Classical.choose (Φ.exists_td X)).2

theorem trace_coe (X : Φ.Dt) :
    (X : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)).trace = (1 : L) ⊗ₜ[K] Φ.tK X :=
  (Classical.choose_spec (Φ.exists_td X)).1

theorem det_coe (X : Φ.Dt) :
    (X : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)).det = (1 : L) ⊗ₜ[K] Φ.dK X :=
  (Classical.choose_spec (Φ.exists_td X)).2.1

theorem norm_tK_sq_le (X : Φ.Dt) : ‖Φ.tK X‖ ^ 2 ≤ ‖Φ.dK X‖ :=
  (Classical.choose_spec (Φ.exists_td X)).2.2

theorem one_tmul_injective : Function.Injective (fun a : v.adicCompletion K => (1 : L) ⊗ₜ[K] a) :=
  Algebra.TensorProduct.includeRight_injective (algebraMap K L).injective

theorem one_tmul_smul_eq (a : v.adicCompletion K) (X : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)) :
    ((1 : L) ⊗ₜ[K] a) *' X = a *' X := by
  ext i j
  simp only [Matrix.smul_apply, smul_eq_mul]
  rw [rightActions_smul_eq K L (v.adicCompletion K) a]

@[scoped simp] theorem coe_mul (X Y : Φ.Dt) :
    ((X * Y : Φ.Dt) : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)) =
      (X : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)) * Y := rfl

@[scoped simp] theorem coe_one : ((1 : Φ.Dt) : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)) = 1 := rfl
@[scoped simp] theorem coe_zero : ((0 : Φ.Dt) : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)) = 0 := rfl
@[scoped simp] theorem coe_add (X Y : Φ.Dt) :
    ((X + Y : Φ.Dt) : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)) =
      (X : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)) + Y := rfl
@[scoped simp] theorem coe_sub (X Y : Φ.Dt) :
    ((X - Y : Φ.Dt) : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)) =
      (X : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)) - Y := rfl

theorem tK_add (X Y : Φ.Dt) : Φ.tK (X + Y) = Φ.tK X + Φ.tK Y := by
  apply one_tmul_injective (K := K) (L := L) (v := v)
  show (1 : L) ⊗ₜ[K] Φ.tK (X + Y) = (1 : L) ⊗ₜ[K] (Φ.tK X + Φ.tK Y)
  rw [← trace_coe, coe_add, Matrix.trace_add, trace_coe, trace_coe, TensorProduct.tmul_add]

theorem tK_smul (a : v.adicCompletion K) (X : Φ.Dt) : Φ.tK (a *' X) = a * Φ.tK X := by
  apply one_tmul_injective (K := K) (L := L) (v := v)
  show (1 : L) ⊗ₜ[K] Φ.tK (a *' X) = (1 : L) ⊗ₜ[K] (a * Φ.tK X)
  rw [← trace_coe, coe_smulF, ← one_tmul_smul_eq, Matrix.trace_smul, trace_coe, smul_eq_mul,
    Algebra.TensorProduct.tmul_mul_tmul, one_mul]

theorem tK_mul_comm (X Y : Φ.Dt) : Φ.tK (X * Y) = Φ.tK (Y * X) := by
  apply one_tmul_injective (K := K) (L := L) (v := v)
  show (1 : L) ⊗ₜ[K] Φ.tK (X * Y) = (1 : L) ⊗ₜ[K] Φ.tK (Y * X)
  rw [← trace_coe, ← trace_coe, coe_mul, coe_mul, Matrix.trace_mul_comm]

theorem tK_one : Φ.tK 1 = 2 := by
  apply one_tmul_injective (K := K) (L := L) (v := v)
  show (1 : L) ⊗ₜ[K] Φ.tK 1 = (1 : L) ⊗ₜ[K] 2
  rw [← trace_coe, coe_one, Matrix.trace_fin_two, Matrix.one_apply_eq, Matrix.one_apply_eq,
    Algebra.TensorProduct.one_def, ← TensorProduct.tmul_add, one_add_one_eq_two]

theorem tK_zero : Φ.tK 0 = 0 := by
  have h := Φ.tK_add 0 0
  rw [add_zero] at h
  simpa using h

theorem dK_mul (X Y : Φ.Dt) : Φ.dK (X * Y) = Φ.dK X * Φ.dK Y := by
  apply one_tmul_injective (K := K) (L := L) (v := v)
  show (1 : L) ⊗ₜ[K] Φ.dK (X * Y) = (1 : L) ⊗ₜ[K] (Φ.dK X * Φ.dK Y)
  rw [← det_coe, coe_mul, Matrix.det_mul, det_coe, det_coe, Algebra.TensorProduct.tmul_mul_tmul, one_mul]

theorem dK_one : Φ.dK 1 = 1 := by
  apply one_tmul_injective (K := K) (L := L) (v := v)
  show (1 : L) ⊗ₜ[K] Φ.dK 1 = (1 : L) ⊗ₜ[K] 1
  rw [← det_coe, coe_one, Matrix.det_one, Algebra.TensorProduct.one_def]

theorem dK_smul (a : v.adicCompletion K) (X : Φ.Dt) : Φ.dK (a *' X) = a * a * Φ.dK X := by
  apply one_tmul_injective (K := K) (L := L) (v := v)
  show (1 : L) ⊗ₜ[K] Φ.dK (a *' X) = (1 : L) ⊗ₜ[K] (a * a * Φ.dK X)
  rw [← det_coe, coe_smulF, ← one_tmul_smul_eq, Matrix.det_smul, det_coe, Fintype.card_fin, pow_two,
    Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul, one_mul, one_mul]

theorem dK_zero : Φ.dK 0 = 0 := by
  have h := Φ.dK_smul 0 0
  rwa [zero_smul, zero_mul, zero_mul] at h

theorem dK_ne_zero {X : Φ.Dt} (hX : X ≠ 0) : Φ.dK X ≠ 0 := by
  intro h0
  have hX' : (X : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)) ≠ 0 := fun h => hX (Subtype.ext h)
  have hu := Φ.hdiv _ X.2 hX'
  rw [Matrix.isUnit_iff_isUnit_det, det_coe, h0, TensorProduct.tmul_zero] at hu
  exact not_isUnit_zero hu

theorem dK_eq_zero_iff {X : Φ.Dt} : Φ.dK X = 0 ↔ X = 0 :=
  ⟨fun h => by_contra fun hX => Φ.dK_ne_zero hX h, fun h => by rw [h, dK_zero]⟩

@[scoped simp] theorem coe_neg (X : Φ.Dt) :
    ((-X : Φ.Dt) : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)) =
      -(X : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)) := rfl

theorem dK_neg (X : Φ.Dt) : Φ.dK (-X) = Φ.dK X := by
  apply one_tmul_injective (K := K) (L := L) (v := v)
  show (1 : L) ⊗ₜ[K] Φ.dK (-X) = (1 : L) ⊗ₜ[K] Φ.dK X
  rw [← det_coe, ← det_coe, coe_neg, Matrix.det_neg, Fintype.card_fin]
  norm_num

theorem cayley (X : Φ.Dt) : X * X - Φ.tK X *' X + Φ.dK X *' (1 : Φ.Dt) = 0 := by
  apply Subtype.ext
  show (X : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)) * X -
      Φ.tK X *' (X : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)) +
      Φ.dK X *' (1 : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)) = 0
  set Y : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K) := X.1 with hY
  have h : Y * Y - Y.trace *' Y + Y.det *' (1 : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)) = 0 := by
    ext i j
    rw [Matrix.trace_fin_two, Matrix.det_fin_two]
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> ring
  rwa [hY, trace_coe, det_coe, one_tmul_smul_eq, one_tmul_smul_eq] at h

theorem dK_add_one (X : Φ.Dt) : Φ.dK (X + 1) = Φ.dK X + Φ.tK X + 1 := by
  apply one_tmul_injective (K := K) (L := L) (v := v)
  show (1 : L) ⊗ₜ[K] Φ.dK (X + 1) = (1 : L) ⊗ₜ[K] (Φ.dK X + Φ.tK X + 1)
  rw [← det_coe, TensorProduct.tmul_add, TensorProduct.tmul_add, ← det_coe, ← trace_coe,
    ← Algebra.TensorProduct.one_def, coe_add, coe_one, Matrix.det_fin_two, Matrix.det_fin_two, Matrix.trace_fin_two]
  simp only [Matrix.add_apply, Matrix.one_apply_eq, Matrix.one_apply_ne (by decide : (0 : Fin 2) ≠ 1),
    Matrix.one_apply_ne (by decide : (1 : Fin 2) ≠ 0), add_zero]
  ring

def inv' (X : Φ.Dt) : Φ.Dt := (Φ.dK X)⁻¹ *' (Φ.tK X *' (1 : Φ.Dt) - X)

theorem key_inv (X : Φ.Dt) : X * (Φ.tK X *' (1 : Φ.Dt) - X) = Φ.dK X *' (1 : Φ.Dt) := by
  have hc := Φ.cayley X
  have h1 : X * (Φ.tK X *' (1 : Φ.Dt) - X) = X * (Φ.tK X *' (1 : Φ.Dt)) - X * X := mul_sub X _ X
  rw [h1, mul_smul_comm, mul_one, ← sub_eq_zero, ← neg_eq_zero, ← hc]
  abel

theorem key_inv' (X : Φ.Dt) : (Φ.tK X *' (1 : Φ.Dt) - X) * X = Φ.dK X *' (1 : Φ.Dt) := by
  have hc := Φ.cayley X
  have h1 : (Φ.tK X *' (1 : Φ.Dt) - X) * X = (Φ.tK X *' (1 : Φ.Dt)) * X - X * X := sub_mul _ X X
  rw [h1, smul_mul_assoc, one_mul, ← sub_eq_zero, ← neg_eq_zero, ← hc]
  abel

theorem mul_inv' {X : Φ.Dt} (hX : X ≠ 0) : X * Φ.inv' X = 1 := by
  have hn := Φ.dK_ne_zero hX
  unfold inv'
  rw [mul_smul_comm, key_inv, smul_smul, inv_mul_cancel₀ hn, one_smul]

theorem inv'_mul {X : Φ.Dt} (hX : X ≠ 0) : Φ.inv' X * X = 1 := by
  have hn := Φ.dK_ne_zero hX
  unfold inv'
  rw [smul_mul_assoc, key_inv', smul_smul, inv_mul_cancel₀ hn, one_smul]

theorem dK_inv' {X : Φ.Dt} (hX : X ≠ 0) : Φ.dK (Φ.inv' X) = (Φ.dK X)⁻¹ := by
  have h := Φ.dK_mul X (Φ.inv' X)
  rw [Φ.mul_inv' hX, dK_one] at h
  exact (eq_inv_of_mul_eq_one_right h.symm)

theorem norm_tK_le_one_of {X : Φ.Dt} (h : ‖Φ.dK X‖ ≤ 1) : ‖Φ.tK X‖ ≤ 1 := by
  have h2 := Φ.norm_tK_sq_le X
  nlinarith [norm_nonneg (Φ.tK X)]

theorem norm_dK_add_one_le {Z : Φ.Dt} (h : ‖Φ.dK Z‖ ≤ 1) : ‖Φ.dK (Z + 1)‖ ≤ 1 := by
  rw [dK_add_one]
  refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ (by rw [norm_one]))
  exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le h (Φ.norm_tK_le_one_of h))

theorem norm_dK_add_le_of_le {X Y : Φ.Dt} (hle : ‖Φ.dK X‖ ≤ ‖Φ.dK Y‖) : ‖Φ.dK (X + Y)‖ ≤ ‖Φ.dK Y‖ := by
  by_cases hY : Y = 0
  · subst hY
    rw [dK_zero, norm_zero] at hle
    rw [add_zero, dK_zero, norm_zero]
    exact hle
  set Z : Φ.Dt := Φ.inv' Y * X with hZ
  have hXY : X + Y = Y * (Z + 1) := by
    rw [mul_add, mul_one, hZ, ← mul_assoc, Φ.mul_inv' hY, one_mul]
  have hZ1 : ‖Φ.dK Z‖ ≤ 1 := by
    rw [hZ, dK_mul, Φ.dK_inv' hY, norm_mul, norm_inv]
    have hYn : 0 < ‖Φ.dK Y‖ := norm_pos_iff.2 (Φ.dK_ne_zero hY)
    rw [inv_mul_le_iff₀ hYn, mul_one]
    exact hle
  rw [hXY, dK_mul, norm_mul]
  exact mul_le_of_le_one_right (norm_nonneg _) (Φ.norm_dK_add_one_le hZ1)

theorem norm_dK_add_le (X Y : Φ.Dt) : ‖Φ.dK (X + Y)‖ ≤ max ‖Φ.dK X‖ ‖Φ.dK Y‖ := by
  rcases le_total ‖Φ.dK X‖ ‖Φ.dK Y‖ with h | h
  · exact (Φ.norm_dK_add_le_of_le h).trans (le_max_right _ _)
  · rw [add_comm]
    exact (Φ.norm_dK_add_le_of_le h).trans (le_max_left _ _)

theorem tK_sum {ι : Type} (s : Finset ι) (f : ι → Φ.Dt) : Φ.tK (∑ i ∈ s, f i) = ∑ i ∈ s, Φ.tK (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.sum_empty, Finset.sum_empty, tK_zero]
  | insert i s hi ih => rw [Finset.sum_insert hi, Finset.sum_insert hi, tK_add, ih]

def M : Submodule (v.adicCompletionIntegers K) Φ.Dt where
  carrier := {X | ‖Φ.dK X‖ ≤ 1}
  add_mem' {X Y} hX hY := (Φ.norm_dK_add_le X Y).trans (max_le hX hY)
  zero_mem' := by
    show ‖Φ.dK 0‖ ≤ 1
    rw [dK_zero, norm_zero]
    exact zero_le_one
  smul_mem' a X hX := by
    show ‖Φ.dK ((a : v.adicCompletion K) *' X)‖ ≤ 1
    rw [dK_smul, norm_mul, norm_mul]
    exact mul_le_one₀ (mul_le_one₀ (norm_coe_le_one K v a) (norm_nonneg _) (norm_coe_le_one K v a))
      (norm_nonneg _) hX

theorem mem_M {X : Φ.Dt} : X ∈ Φ.M ↔ ‖Φ.dK X‖ ≤ 1 := Iff.rfl

def Msr : Subring Φ.Dt where
  carrier := {X | ‖Φ.dK X‖ ≤ 1}
  mul_mem' {X Y} hX hY := by
    show ‖Φ.dK (X * Y)‖ ≤ 1
    rw [dK_mul, norm_mul]
    exact mul_le_one₀ hX (norm_nonneg _) hY
  one_mem' := by
    show ‖Φ.dK 1‖ ≤ 1
    rw [dK_one, norm_one]
  add_mem' {X Y} hX hY := (Φ.norm_dK_add_le X Y).trans (max_le hX hY)
  zero_mem' := by
    show ‖Φ.dK 0‖ ≤ 1
    rw [dK_zero, norm_zero]
    exact zero_le_one
  neg_mem' {X} hX := by
    show ‖Φ.dK (-X)‖ ≤ 1
    rwa [dK_neg]

theorem mem_Msr {X : Φ.Dt} : X ∈ Φ.Msr ↔ ‖Φ.dK X‖ ≤ 1 := Iff.rfl

theorem smulF_mem_M {c : v.adicCompletion K} (hc : ‖c‖ ≤ 1) {X : Φ.Dt} (hX : X ∈ Φ.M) : c *' X ∈ Φ.M := by
  rw [mem_M, dK_smul, norm_mul, norm_mul]
  exact mul_le_one₀ (mul_le_one₀ hc (norm_nonneg _) hc) (norm_nonneg _) hX

theorem exists_smul_mem_M (X : Φ.Dt) : ∃ c : v.adicCompletion K, c ≠ 0 ∧ c *' X ∈ Φ.M := by
  obtain ⟨ϖ, hϖ⟩ := exists_uniformiser K v
  have hϖ0 : ϖ ≠ 0 := by
    intro h; rw [h, norm_zero] at hϖ; exact (inv_pos.2 (qv_pos K v)).ne hϖ
  obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt ‖Φ.dK X‖ (one_lt_qv K v)
  refine ⟨ϖ ^ k, pow_ne_zero _ hϖ0, ?_⟩
  rw [mem_M, dK_smul, norm_mul, norm_mul, norm_pow, hϖ, inv_pow]
  have hq : 0 < qv K v ^ k := pow_pos (qv_pos K v) k
  rw [mul_assoc, inv_mul_le_iff₀ hq, mul_one]
  calc (qv K v ^ k)⁻¹ * ‖Φ.dK X‖ ≤ (qv K v ^ k)⁻¹ * qv K v ^ k :=
        mul_le_mul_of_nonneg_left hk.le (inv_nonneg.2 hq.le)
    _ = 1 := inv_mul_cancel₀ hq.ne'
    _ ≤ qv K v ^ k := one_le_pow₀ (one_lt_qv K v).le

def gram (b : Module.Basis (Fin 4) (v.adicCompletion K) Φ.Dt) : Matrix (Fin 4) (Fin 4) (v.adicCompletion K) :=
  Matrix.of fun i j => Φ.tK (b i * b j)

theorem gram_mulVec (b : Module.Basis (Fin 4) (v.adicCompletion K) Φ.Dt) (c : Fin 4 → v.adicCompletion K)
    (i : Fin 4) : (Φ.gram b).mulVec c i = Φ.tK (b i * ∑ j, c j *' b j) := by
  rw [Matrix.mulVec, dotProduct, Finset.mul_sum, tK_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [gram, Matrix.of_apply, mul_smul_comm, tK_smul, mul_comm]

theorem tK_mul_eq_zero_of_forall (b : Module.Basis (Fin 4) (v.adicCompletion K) Φ.Dt) {X : Φ.Dt}
    (h : ∀ i, Φ.tK (b i * X) = 0) (Y : Φ.Dt) : Φ.tK (Y * X) = 0 := by
  rw [← b.sum_repr Y, Finset.sum_mul, tK_sum]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [smul_mul_assoc, tK_smul, h i, mul_zero]

theorem det_gram_ne_zero (b : Module.Basis (Fin 4) (v.adicCompletion K) Φ.Dt) : (Φ.gram b).det ≠ 0 := by
  classical
  intro hdet
  obtain ⟨c, hc, hmul⟩ := Matrix.exists_mulVec_eq_zero_iff.2 hdet
  set X : Φ.Dt := ∑ j, c j *' b j with hX
  have hX0 : X ≠ 0 := by
    intro h0
    apply hc
    have hli := Fintype.linearIndependent_iff.1 b.linearIndependent c (by rw [← hX, h0])
    funext j; exact hli j
  have hall : ∀ i, Φ.tK (b i * X) = 0 := fun i => by
    have := congrFun hmul i
    rwa [gram_mulVec] at this
  have h1 := Φ.tK_mul_eq_zero_of_forall b hall (Φ.inv' X)
  rw [Φ.inv'_mul hX0, tK_one] at h1
  exact two_ne_zero' K v h1

theorem M_le_span (b : Module.Basis (Fin 4) (v.adicCompletion K) Φ.Dt) (hb : ∀ i, b i ∈ Φ.M) :
    Φ.M ≤ Submodule.span (v.adicCompletionIntegers K) (Set.range fun i => ((Φ.gram b).det)⁻¹ *' b i) := by
  classical
  intro X hX
  set d : v.adicCompletion K := (Φ.gram b).det with hd
  have hd0 : d ≠ 0 := Φ.det_gram_ne_zero b

  have hGmem : ∀ i j, Φ.gram b i j ∈ v.adicCompletionIntegers K := fun i j =>
    (norm_le_one_iff_mem K v _).1 (Φ.norm_tK_le_one_of (Φ.Msr.mul_mem (hb i) (hb j)))
  set G' : Matrix (Fin 4) (Fin 4) (v.adicCompletionIntegers K) := Matrix.of fun i j => ⟨Φ.gram b i j, hGmem i j⟩
    with hG'
  have hGG' : (v.adicCompletionIntegers K).subtype.mapMatrix G' = Φ.gram b := by
    ext i j; rfl

  have hwmem : ∀ i, Φ.tK (b i * X) ∈ v.adicCompletionIntegers K := fun i =>
    (norm_le_one_iff_mem K v _).1 (Φ.norm_tK_le_one_of (Φ.Msr.mul_mem (hb i) hX))
  set w' : Fin 4 → v.adicCompletionIntegers K := fun i => ⟨Φ.tK (b i * X), hwmem i⟩ with hw'

  set c : Fin 4 → v.adicCompletion K := fun j => b.repr X j with hc
  have hXc : X = ∑ j, c j *' b j := (b.sum_repr X).symm
  have hGc : (Φ.gram b).mulVec c = fun i => Φ.tK (b i * X) := by
    funext i; rw [gram_mulVec, ← hXc]
  have hadj : d *' c = (Φ.gram b).adjugate.mulVec (fun i => Φ.tK (b i * X)) := by
    rw [← hGc, Matrix.mulVec_mulVec, Matrix.adjugate_mul, Matrix.smul_mulVec, Matrix.one_mulVec]
  have hadj' : (Φ.gram b).adjugate.mulVec (fun i => Φ.tK (b i * X)) =
      fun i => ((G'.adjugate.mulVec w' i : v.adicCompletionIntegers K) : v.adicCompletion K) := by
    have h1 : (Φ.gram b).adjugate = (v.adicCompletionIntegers K).subtype.mapMatrix G'.adjugate := by
      rw [RingHom.map_adjugate, hGG']
    rw [h1]
    funext i
    show _ = (v.adicCompletionIntegers K).subtype (G'.adjugate.mulVec w' i)
    rw [RingHom.map_mulVec]
    rfl

  have hci : ∀ i, c i = d⁻¹ * ((G'.adjugate.mulVec w' i : v.adicCompletionIntegers K) : v.adicCompletion K) := by
    intro i
    have := congrFun (hadj.trans hadj') i
    simp only [Pi.smul_apply, smul_eq_mul] at this
    rw [← this, ← mul_assoc, inv_mul_cancel₀ hd0, one_mul]
  rw [hXc]
  refine Submodule.sum_mem _ fun i _ => ?_
  rw [hci, mul_comm, mul_smul,
    show ((G'.adjugate.mulVec w' i : v.adicCompletionIntegers K) : v.adicCompletion K) *' (d⁻¹ *' b i) =
      (G'.adjugate.mulVec w' i) *' (d⁻¹ *' b i) from rfl]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

theorem exists_basis_mem_M : ∃ b : Module.Basis (Fin 4) (v.adicCompletion K) Φ.Dt, ∀ i, b i ∈ Φ.M := by
  choose c hc0 hcM using fun i => Φ.exists_smul_mem_M (Φ.bD i)
  refine ⟨Φ.bD.unitsSMul fun i => Units.mk0 (c i) (hc0 i), fun i => ?_⟩
  rw [Module.Basis.unitsSMul_apply]
  exact hcM i

theorem M_fg : Φ.M.FG := by
  obtain ⟨b, hb⟩ := Φ.exists_basis_mem_M
  exact Submodule.FG.of_le (Submodule.fg_span (Set.finite_range _)) (Φ.M_le_span b hb)

theorem span_M_eq_top : Submodule.span (v.adicCompletion K) (Φ.M : Set Φ.Dt) = ⊤ := by
  rw [eq_top_iff, ← Φ.bD.span_eq, Submodule.span_le]
  rintro _ ⟨i, rfl⟩
  obtain ⟨c, hc0, hcM⟩ := Φ.exists_smul_mem_M (Φ.bD i)
  have : Φ.bD i = c⁻¹ *' (c *' Φ.bD i) := by rw [smul_smul, inv_mul_cancel₀ hc0, one_smul]
  rw [this]
  exact Submodule.smul_mem _ _ (Submodule.subset_span hcM)

scoped instance isLattice_M : Submodule.IsLattice (v.adicCompletion K) Φ.M := ⟨Φ.M_fg, Φ.span_M_eq_top⟩

scoped instance free_M : Module.Free (v.adicCompletionIntegers K) Φ.M :=
  Submodule.IsLattice.free (v.adicCompletion K) Φ.M

theorem finrank_M : Module.finrank (v.adicCompletionIntegers K) Φ.M = 4 := by
  apply Module.finrank_eq_of_rank_eq
  rw [Submodule.IsLattice.rank' (v.adicCompletion K) Φ.M, rank_eq_card_basis Φ.bD, Fintype.card_fin]

def bM : Module.Basis (Fin 4) (v.adicCompletionIntegers K) Φ.M :=
  Module.finBasisOfFinrankEq (v.adicCompletionIntegers K) Φ.M Φ.finrank_M

def bMF : Module.Basis (Fin 4) (v.adicCompletion K) Φ.Dt :=
  Module.Basis.extendOfIsLattice (v.adicCompletion K) Φ.bM

theorem bMF_apply (i : Fin 4) : Φ.bMF i = (Φ.bM i : Φ.Dt) :=
  Module.Basis.extendOfIsLattice_apply (v.adicCompletion K) Φ.bM i

theorem bMF_mem (i : Fin 4) : Φ.bMF i ∈ Φ.M := by
  rw [bMF_apply]; exact (Φ.bM i).2

theorem span_bMF : Submodule.span (v.adicCompletionIntegers K) (Set.range Φ.bMF) = Φ.M := by
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    exact Φ.bMF_mem i
  · intro X hX
    have h := congrArg (Subtype.val : Φ.M → Φ.Dt) (Φ.bM.sum_repr ⟨X, hX⟩)
    simp only [Submodule.coe_sum, Submodule.coe_smul_of_tower] at h
    rw [← h]
    refine Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, ?_⟩)
    rw [bMF_apply]

def mulLeftEquiv {Z : Φ.Dt} (hZ : Z ≠ 0) : Φ.Dt ≃ₗ[v.adicCompletion K] Φ.Dt :=
  LinearEquiv.ofLinear (LinearMap.mulLeft (v.adicCompletion K) Z) (LinearMap.mulLeft (v.adicCompletion K) (Φ.inv' Z))
    (by ext X; simp only [LinearMap.comp_apply, LinearMap.mulLeft_apply, LinearMap.id_apply, ← mul_assoc, Φ.mul_inv' hZ, one_mul])
    (by ext X; simp only [LinearMap.comp_apply, LinearMap.mulLeft_apply, LinearMap.id_apply, ← mul_assoc, Φ.inv'_mul hZ, one_mul])

theorem mulLeftEquiv_apply {Z : Φ.Dt} (hZ : Z ≠ 0) (X : Φ.Dt) : Φ.mulLeftEquiv hZ X = Z * X := rfl

def ℓ (Z : Φ.Dt) : Φ.Dt →ₗ[v.adicCompletionIntegers K] Φ.Dt :=
  (LinearMap.mulLeft (v.adicCompletion K) Z).restrictScalars (v.adicCompletionIntegers K)

theorem ℓ_apply (Z X : Φ.Dt) : Φ.ℓ Z X = Z * X := rfl

theorem ℓ_injective {Z : Φ.Dt} (hZ : Z ≠ 0) : Function.Injective (Φ.ℓ Z) := fun X Y h => by
  have h' : Z * X = Z * Y := h
  have := congrArg (fun W => Φ.inv' Z * W) h'
  simp only [← mul_assoc, Φ.inv'_mul hZ, one_mul] at this
  exact this

theorem map_ℓ_mul (Z W : Φ.Dt) (N : Submodule (v.adicCompletionIntegers K) Φ.Dt) :
    N.map (Φ.ℓ (Z * W)) = (N.map (Φ.ℓ W)).map (Φ.ℓ Z) := by
  have h : Φ.ℓ (Z * W) = (Φ.ℓ Z).comp (Φ.ℓ W) := by
    ext X
    simp only [LinearMap.comp_apply, ℓ_apply, mul_assoc]
  rw [h, Submodule.map_comp]

theorem toAddSubgroup_map_ℓ (Z : Φ.Dt) (N : Submodule (v.adicCompletionIntegers K) Φ.Dt) :
    (N.map (Φ.ℓ Z)).toAddSubgroup = N.toAddSubgroup.map (Φ.ℓ Z).toAddMonoidHom := by
  ext X
  simp only [Submodule.mem_toAddSubgroup, Submodule.mem_map, AddSubgroup.mem_map, LinearMap.toAddMonoidHom_coe]

theorem relIndex_map_ℓ {Z : Φ.Dt} (hZ : Z ≠ 0) (N₁ N₂ : Submodule (v.adicCompletionIntegers K) Φ.Dt) :
    (N₁.map (Φ.ℓ Z)).toAddSubgroup.relIndex (N₂.map (Φ.ℓ Z)).toAddSubgroup =
      N₁.toAddSubgroup.relIndex N₂.toAddSubgroup := by
  rw [toAddSubgroup_map_ℓ, toAddSubgroup_map_ℓ]
  exact AddSubgroup.relIndex_map_map_of_injective _ _ (Φ.ℓ_injective hZ)

theorem map_ℓ_M_eq_of_norm_eq_one {u : Φ.Dt} (hu : ‖Φ.dK u‖ = 1) : Φ.M.map (Φ.ℓ u) = Φ.M := by
  have hu0 : u ≠ 0 := fun h => by rw [h, dK_zero, norm_zero] at hu; exact zero_ne_one hu
  have huinv : ‖Φ.dK (Φ.inv' u)‖ = 1 := by rw [Φ.dK_inv' hu0, norm_inv, hu, inv_one]
  apply le_antisymm
  · rintro _ ⟨X, hX, rfl⟩
    show ‖Φ.dK (u * X)‖ ≤ 1
    rw [dK_mul, norm_mul, hu, one_mul]; exact hX
  · intro X hX
    refine ⟨Φ.inv' u * X, ?_, ?_⟩
    · show ‖Φ.dK (Φ.inv' u * X)‖ ≤ 1
      rw [dK_mul, norm_mul, huinv, one_mul]; exact hX
    · show u * (Φ.inv' u * X) = X
      rw [← mul_assoc, Φ.mul_inv' hu0, one_mul]

theorem relIndex_map_ℓ_M_mul_norm_det {Z : Φ.Dt} (hZ : Z ≠ 0) (hZM : Z ∈ Φ.M) :
    ((Φ.M.map (Φ.ℓ Z)).toAddSubgroup.relIndex Φ.M.toAddSubgroup : ℝ) *
      ‖LinearMap.det (LinearMap.mulLeft (v.adicCompletion K) Z)‖ = 1 := by
  classical
  set b₁ : Module.Basis (Fin 4) (v.adicCompletion K) Φ.Dt := Φ.bMF.map (Φ.mulLeftEquiv hZ) with hb₁
  have hb₁apply : ∀ i, b₁ i = Z * Φ.bMF i := fun i => by rw [hb₁, Module.Basis.map_apply]; rfl
  have hnest : ∀ i, b₁ i ∈ Submodule.span (v.adicCompletionIntegers K) (Set.range Φ.bMF) := fun i => by
    rw [span_bMF, hb₁apply]
    exact Φ.Msr.mul_mem hZM (Φ.bMF_mem i)
  have k3 := IsDedekindDomain.HeightOneSpectrum.relIndex_span_range_mul_norm_det_eq_one_of_forall_mem_span
    K v b₁ Φ.bMF hnest
  have hspan₁ : Submodule.span (v.adicCompletionIntegers K) (Set.range b₁) = Φ.M.map (Φ.ℓ Z) := by
    rw [← span_bMF, Submodule.map_span, ← Set.range_comp]
    congr 1
  have hdet : Φ.bMF.det b₁ = LinearMap.det (LinearMap.mulLeft (v.adicCompletion K) Z) := by
    have hcoe : (⇑b₁ : Fin 4 → Φ.Dt) = ⇑(LinearMap.mulLeft (v.adicCompletion K) Z) ∘ ⇑Φ.bMF := by
      funext i; rw [hb₁apply]; rfl
    rw [hcoe, Module.Basis.det_comp, Module.Basis.det_self, mul_one]
  rw [hspan₁, span_bMF, hdet] at k3
  exact k3

def unif : v.adicCompletion K := Classical.choose (exists_uniformiser K v)

theorem norm_unif : ‖(unif (K := K) (v := v))‖ = (qv K v)⁻¹ := Classical.choose_spec (exists_uniformiser K v)

theorem unif_ne_zero : (unif (K := K) (v := v)) ≠ 0 := by
  intro h
  have := norm_unif (K := K) (v := v)
  rw [h, norm_zero] at this
  exact (inv_pos.2 (qv_pos K v)).ne this

theorem norm_unif_le_one : ‖(unif (K := K) (v := v))‖ ≤ 1 := by
  rw [norm_unif]; exact inv_le_one_of_one_le₀ (one_lt_qv K v).le

theorem norm_unif_lt_one : ‖(unif (K := K) (v := v))‖ < 1 := by
  rw [norm_unif]; exact inv_lt_one_of_one_lt₀ (one_lt_qv K v)

def unifO : v.adicCompletionIntegers K := ⟨unif, (norm_le_one_iff_mem K v _).1 norm_unif_le_one⟩

def ϖ1 : Φ.Dt := (unif (K := K) (v := v)) *' (1 : Φ.Dt)

theorem ϖ1_ne_zero : Φ.ϖ1 ≠ 0 := by
  intro h
  have := congrArg Φ.dK h
  rw [ϖ1, dK_smul, dK_one, mul_one, dK_zero] at this
  exact unif_ne_zero (K := K) (v := v) (mul_self_eq_zero.1 this)

theorem norm_dK_ϖ1 : ‖Φ.dK Φ.ϖ1‖ = (qv K v)⁻¹ * (qv K v)⁻¹ := by
  rw [ϖ1, dK_smul, dK_one, mul_one, norm_mul, norm_unif]

theorem ϖ1_mem_M : Φ.ϖ1 ∈ Φ.M := by
  rw [mem_M, norm_dK_ϖ1]
  have h := inv_le_one_of_one_le₀ (one_lt_qv K v).le
  exact mul_le_one₀ h (inv_nonneg.2 (qv_pos K v).le) h

theorem ϖ1_mul (X : Φ.Dt) : Φ.ϖ1 * X = (unif (K := K) (v := v)) *' X := by
  rw [ϖ1, smul_mul_assoc, one_mul]

theorem det_mulLeft_ϖ1 : LinearMap.det (LinearMap.mulLeft (v.adicCompletion K) Φ.ϖ1) = (unif (K := K) (v := v)) ^ 4 := by
  have h : LinearMap.mulLeft (v.adicCompletion K) Φ.ϖ1 = (unif (K := K) (v := v)) *' LinearMap.id := by
    ext X
    rw [LinearMap.mulLeft_apply, ϖ1_mul, LinearMap.smul_apply, LinearMap.id_apply]
  rw [h, LinearMap.det_smul, LinearMap.det_id, mul_one, finrank_Dt]

def B : LinearMap.BilinForm (v.adicCompletion K) Φ.Dt :=
  LinearMap.mk₂ (v.adicCompletion K) (fun X Y => Φ.tK (X * Y))
    (fun X X' Y => by
      show Φ.tK ((X + X') * Y) = Φ.tK (X * Y) + Φ.tK (X' * Y)
      rw [add_mul, tK_add])
    (fun c X Y => by
      show Φ.tK ((c *' X) * Y) = c *' Φ.tK (X * Y)
      rw [smul_mul_assoc, tK_smul, smul_eq_mul])
    (fun X Y Y' => by
      show Φ.tK (X * (Y + Y')) = Φ.tK (X * Y) + Φ.tK (X * Y')
      rw [mul_add, tK_add])
    (fun c X Y => by
      show Φ.tK (X * (c *' Y)) = c *' Φ.tK (X * Y)
      rw [mul_smul_comm, tK_smul, smul_eq_mul])

theorem B_apply (X Y : Φ.Dt) : Φ.B X Y = Φ.tK (X * Y) := rfl

theorem B_nondegenerate : Φ.B.Nondegenerate := by
  refine ⟨fun X h => ?_, fun Y h => ?_⟩
  · by_contra hX
    have h1 := h (Φ.inv' X)
    rw [B_apply, Φ.mul_inv' hX, tK_one] at h1
    exact two_ne_zero' K v h1
  · by_contra hY
    have h1 := h (Φ.inv' Y)
    rw [B_apply, Φ.inv'_mul hY, tK_one] at h1
    exact two_ne_zero' K v h1

def G : Matrix (Fin 4) (Fin 4) (v.adicCompletion K) := Matrix.of fun i j => Φ.tK (Φ.bMF i * Φ.bMF j)

def Mdual : Submodule (v.adicCompletionIntegers K) Φ.Dt := Φ.B.dualSubmodule Φ.M

theorem mem_Mdual {X : Φ.Dt} : X ∈ Φ.Mdual ↔ ∀ Y ∈ Φ.M, ‖Φ.tK (X * Y)‖ ≤ 1 := by
  rw [Mdual, LinearMap.BilinForm.mem_dualSubmodule]
  refine forall₂_congr fun Y _ => ?_
  rw [B_apply, Submodule.mem_one, norm_le_one_iff_mem]
  constructor
  · rintro ⟨a, ha⟩; rw [← ha]; exact a.2
  · intro h; exact ⟨⟨_, h⟩, rfl⟩

theorem M_le_Mdual : Φ.M ≤ Φ.Mdual := fun _ hX =>
  Φ.mem_Mdual.2 fun _ hY => Φ.norm_tK_le_one_of (Φ.Msr.mul_mem hX hY)

theorem relIndex_Mdual_mul_norm_det_G :
    ((Φ.M.toAddSubgroup.relIndex Φ.Mdual.toAddSubgroup : ℕ) : ℝ) * ‖(Φ.G).det‖ = 1 := by
  classical
  set b₂ : Module.Basis (Fin 4) (v.adicCompletion K) Φ.Dt := Φ.B.dualBasis Φ.B_nondegenerate Φ.bMF with hb₂
  have hdual : Φ.Mdual = Submodule.span (v.adicCompletionIntegers K) (Set.range b₂) := by
    rw [Mdual, ← span_bMF, hb₂]
    exact LinearMap.BilinForm.dualSubmodule_span_of_basis Φ.B Φ.B_nondegenerate Φ.bMF
  have hnest : ∀ i, Φ.bMF i ∈ Submodule.span (v.adicCompletionIntegers K) (Set.range b₂) := fun i => by
    rw [← hdual]; exact Φ.M_le_Mdual (Φ.bMF_mem i)
  have k3 := IsDedekindDomain.HeightOneSpectrum.relIndex_span_range_mul_norm_det_eq_one_of_forall_mem_span
    K v Φ.bMF b₂ hnest
  have hdet : b₂.det Φ.bMF = (Φ.G).det := by
    rw [Module.Basis.det_apply, ← Matrix.det_transpose]
    congr 1
    ext i j
    rw [Matrix.transpose_apply, Module.Basis.toMatrix_apply, hb₂, LinearMap.BilinForm.dualBasis_repr_apply,
      B_apply, G, Matrix.of_apply]
  rw [span_bMF, ← hdual, hdet] at k3
  exact k3

theorem norm_tK_le_one_of_norm_dK_le_qv {Z : Φ.Dt} (h : ‖Φ.dK Z‖ ≤ qv K v) : ‖Φ.tK Z‖ ≤ 1 := by
  have h2 := Φ.norm_tK_sq_le Z
  have hlt : ‖Φ.tK Z‖ < qv K v ^ (1 : ℤ) := by
    rw [zpow_one]
    by_contra hge
    push Not at hge
    have h1 := one_lt_qv K v
    have : qv K v * qv K v ≤ ‖Φ.tK Z‖ ^ 2 := by
      rw [pow_two]; exact mul_le_mul hge hge (qv_pos K v).le (norm_nonneg _)
    nlinarith
  have := norm_le_zpow_sub_one_of_lt K v hlt
  rwa [sub_self, zpow_zero] at this

theorem exists_pi_and_theta :
    (∃ piD : Φ.Dt, ‖Φ.dK piD‖ * qv K v = 1) ∧ (∃ θ : Φ.Dt, ‖Φ.dK θ‖ ≤ 1 ∧ ‖Φ.tK θ‖ = 1) := by
  obtain ⟨⟨X, hX, n, hdet, hn⟩, ⟨Y, hY, t, n', htr, hdet', hn', ht⟩⟩ :=
    AutomorphicForm.exists_norm_det_mul_absNorm_eq_one_and_exists_norm_trace_eq_one_of_forall_isUnit
      K L Φ.h2 Φ.σ Φ.hgen v Φ.δ Φ.e Φ.hbasis Φ.hdiv
  refine ⟨⟨⟨X, hX⟩, ?_⟩, ⟨⟨Y, hY⟩, ?_, ?_⟩⟩
  · have : Φ.dK ⟨X, hX⟩ = n := one_tmul_injective (K := K) (L := L) (v := v) ((Φ.det_coe ⟨X, hX⟩).symm.trans hdet)
    rw [this]; exact hn
  · have : Φ.dK ⟨Y, hY⟩ = n' := one_tmul_injective (K := K) (L := L) (v := v) ((Φ.det_coe ⟨Y, hY⟩).symm.trans hdet')
    rw [this]; exact hn'
  · have : Φ.tK ⟨Y, hY⟩ = t := one_tmul_injective (K := K) (L := L) (v := v) ((Φ.trace_coe ⟨Y, hY⟩).symm.trans htr)
    rw [this]; exact ht

theorem Mdual_eq {piD : Φ.Dt} (hpi : ‖Φ.dK piD‖ * qv K v = 1) {θ : Φ.Dt} (hθM : ‖Φ.dK θ‖ ≤ 1) (hθt : ‖Φ.tK θ‖ = 1) :
    Φ.Mdual = Φ.M.map (Φ.ℓ (Φ.inv' piD)) := by
  have hpin : ‖Φ.dK piD‖ = (qv K v)⁻¹ := eq_inv_of_mul_eq_one_left hpi
  have hpi0 : piD ≠ 0 := by
    intro h; rw [h, dK_zero, norm_zero, zero_mul] at hpi; exact zero_ne_one hpi
  apply le_antisymm
  ·
    intro X hX
    rw [mem_Mdual] at hX
    have hXq : ‖Φ.dK X‖ ≤ qv K v := by
      by_contra hgt
      push Not at hgt
      have hge : qv K v ^ ((1 : ℤ) + 1) ≤ ‖Φ.dK X‖ := zpow_add_one_le_norm_of_lt K v (by rwa [zpow_one])
      rw [show ((1 : ℤ) + 1) = ((2 : ℕ) : ℤ) by norm_num, zpow_natCast] at hge
      have hX0 : X ≠ 0 := by
        intro h0; rw [h0, dK_zero, norm_zero] at hgt; exact lt_irrefl _ ((qv_pos K v).trans hgt)
      have hdX0 : 0 < ‖Φ.dK X‖ := norm_pos_iff.2 (Φ.dK_ne_zero hX0)

      set Y : Φ.Dt := (unif (K := K) (v := v))⁻¹ *' (Φ.inv' X * θ) with hYdef
      have hYM : Y ∈ Φ.M := by
        show ‖Φ.dK Y‖ ≤ 1
        rw [hYdef, dK_smul, dK_mul, Φ.dK_inv' hX0, norm_mul, norm_mul, norm_mul, norm_inv, norm_inv, norm_unif, inv_inv]
        have hq := qv_pos K v
        calc qv K v * qv K v * (‖Φ.dK X‖⁻¹ * ‖Φ.dK θ‖)
            ≤ qv K v * qv K v * ((qv K v ^ 2)⁻¹ * 1) := by
              apply mul_le_mul_of_nonneg_left _ (mul_nonneg hq.le hq.le)
              exact mul_le_mul (inv_anti₀ (pow_pos hq 2) hge) hθM (norm_nonneg _) (inv_nonneg.2 (pow_pos hq 2).le)
          _ = 1 := by field_simp
      have h1 := hX Y hYM
      have hXY : X * Y = (unif (K := K) (v := v))⁻¹ *' θ := by
        rw [hYdef, mul_smul_comm, ← mul_assoc, Φ.mul_inv' hX0, one_mul]
      rw [hXY, tK_smul, norm_mul, norm_inv, norm_unif, inv_inv, hθt, mul_one] at h1
      exact not_lt.2 h1 (one_lt_qv K v)
    refine ⟨piD * X, ?_, ?_⟩
    · show ‖Φ.dK (piD * X)‖ ≤ 1
      rw [dK_mul, norm_mul, hpin]
      calc (qv K v)⁻¹ * ‖Φ.dK X‖ ≤ (qv K v)⁻¹ * qv K v :=
            mul_le_mul_of_nonneg_left hXq (inv_nonneg.2 (qv_pos K v).le)
        _ = 1 := inv_mul_cancel₀ (qv_ne_zero K v)
    · show Φ.inv' piD * (piD * X) = X
      rw [← mul_assoc, Φ.inv'_mul hpi0, one_mul]
  ·
    rintro _ ⟨m, hm, rfl⟩
    rw [mem_Mdual]
    intro Y hY
    rw [ℓ_apply]
    apply Φ.norm_tK_le_one_of_norm_dK_le_qv
    rw [dK_mul, dK_mul, Φ.dK_inv' hpi0, norm_mul, norm_mul, norm_inv, hpin, inv_inv]
    calc qv K v * ‖Φ.dK m‖ * ‖Φ.dK Y‖ ≤ qv K v * 1 * 1 := by
          apply mul_le_mul _ hY (norm_nonneg _) (mul_nonneg (qv_pos K v).le zero_le_one)
          exact mul_le_mul_of_nonneg_left hm (qv_pos K v).le
      _ = qv K v := by ring

theorem norm_det_mulLeft_pi {piD : Φ.Dt} (hpi : ‖Φ.dK piD‖ * qv K v = 1) :
    ‖LinearMap.det (LinearMap.mulLeft (v.adicCompletion K) piD)‖ = (qv K v)⁻¹ * (qv K v)⁻¹ := by
  have hpin : ‖Φ.dK piD‖ = (qv K v)⁻¹ := eq_inv_of_mul_eq_one_left hpi
  have hpi0 : piD ≠ 0 := by
    intro h; rw [h, dK_zero, norm_zero, zero_mul] at hpi; exact zero_ne_one hpi

  set u : Φ.Dt := (unif (K := K) (v := v))⁻¹ *' (piD * piD) with hudef
  have hu : ‖Φ.dK u‖ = 1 := by
    rw [hudef, dK_smul, dK_mul, norm_mul, norm_mul, norm_mul, norm_inv, norm_unif, hpin, inv_inv]
    have hq := qv_ne_zero K v
    field_simp
  have hu0 : u ≠ 0 := fun h => by rw [h, dK_zero, norm_zero] at hu; exact zero_ne_one hu
  have huM : u ∈ Φ.M := by show ‖Φ.dK u‖ ≤ 1; rw [hu]
  have hpp : piD * piD = Φ.ϖ1 * u := by
    rw [ϖ1_mul, hudef, smul_smul, mul_inv_cancel₀ unif_ne_zero, one_smul]

  have hdetu : ‖LinearMap.det (LinearMap.mulLeft (v.adicCompletion K) u)‖ = 1 := by
    have h := Φ.relIndex_map_ℓ_M_mul_norm_det hu0 huM
    rw [Φ.map_ℓ_M_eq_of_norm_eq_one hu, AddSubgroup.relIndex_self, Nat.cast_one, one_mul] at h
    exact h

  have hsq : LinearMap.det (LinearMap.mulLeft (v.adicCompletion K) piD) ^ 2 =
      (unif (K := K) (v := v)) ^ 4 * LinearMap.det (LinearMap.mulLeft (v.adicCompletion K) u) := by
    rw [pow_two, ← LinearMap.det_comp, ← LinearMap.mulLeft_mul, hpp, LinearMap.mulLeft_mul, LinearMap.det_comp,
      det_mulLeft_ϖ1]
  have hnorm : ‖LinearMap.det (LinearMap.mulLeft (v.adicCompletion K) piD)‖ ^ 2 = ((qv K v)⁻¹ * (qv K v)⁻¹) ^ 2 := by
    rw [← norm_pow, hsq, norm_mul, norm_pow, norm_unif, hdetu, mul_one]
    ring
  exact (sq_eq_sq₀ (norm_nonneg _) (mul_nonneg (inv_nonneg.2 (qv_pos K v).le) (inv_nonneg.2 (qv_pos K v).le))).1 hnorm

theorem norm_det_G : ‖(Φ.G).det‖ = (qv K v)⁻¹ * (qv K v)⁻¹ := by
  obtain ⟨⟨piD, hpi⟩, ⟨θ, hθM, hθt⟩⟩ := Φ.exists_pi_and_theta
  have hpi0 : piD ≠ 0 := by
    intro h; rw [h, dK_zero, norm_zero, zero_mul] at hpi; exact zero_ne_one hpi
  have hpiM : piD ∈ Φ.M := by
    show ‖Φ.dK piD‖ ≤ 1
    rw [eq_inv_of_mul_eq_one_left hpi]; exact inv_le_one_of_one_le₀ (one_lt_qv K v).le
  have hinv0 : Φ.inv' piD ≠ 0 := by
    intro h
    have := Φ.mul_inv' hpi0
    rw [h, mul_zero] at this
    exact zero_ne_one this

  have h1 : Φ.M.toAddSubgroup.relIndex Φ.Mdual.toAddSubgroup =
      (Φ.M.map (Φ.ℓ piD)).toAddSubgroup.relIndex Φ.M.toAddSubgroup := by
    rw [Φ.Mdual_eq hpi hθM hθt]
    have hM : Φ.M = (Φ.M.map (Φ.ℓ piD)).map (Φ.ℓ (Φ.inv' piD)) := by
      rw [← map_ℓ_mul, Φ.inv'_mul hpi0]
      ext X
      simp only [Submodule.mem_map, ℓ_apply, one_mul, exists_eq_right]
    have := Φ.relIndex_map_ℓ hinv0 (Φ.M.map (Φ.ℓ piD)) Φ.M
    rw [← hM] at this
    exact this
  have h2 := Φ.relIndex_map_ℓ_M_mul_norm_det hpi0 hpiM
  rw [Φ.norm_det_mulLeft_pi hpi, ← h1] at h2
  have h3 := Φ.relIndex_Mdual_mul_norm_det_G

  have hr : ((Φ.M.toAddSubgroup.relIndex Φ.Mdual.toAddSubgroup : ℕ) : ℝ) ≠ 0 := by
    intro h0; rw [h0, zero_mul] at h3; exact zero_ne_one h3
  have := h3.trans h2.symm
  exact mul_left_cancel₀ hr this

theorem closure_setF_eq {ι : Type} (f : ι → Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)) :
    AddSubgroup.closure
        {X : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K) |
          ∃ (i : ι) (a : v.adicCompletion K), a ∈ v.adicCompletionIntegers K ∧
            X = (f i).map (fun t : L ⊗[K] v.adicCompletion K => t * ((1 : L) ⊗ₜ[K] a))} =
      (Submodule.span (v.adicCompletionIntegers K) (Set.range f)).toAddSubgroup := by
  apply le_antisymm
  · rw [AddSubgroup.closure_le]
    rintro X ⟨i, a, ha, rfl⟩
    rw [map_mulOne_eq_smul, SetLike.mem_coe, Submodule.mem_toAddSubgroup,
      show a *' f i = (⟨a, ha⟩ : v.adicCompletionIntegers K) *' f i from rfl]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  · intro X hX
    rw [Submodule.mem_toAddSubgroup] at hX
    induction hX using Submodule.span_induction with
    | mem X hX =>
        obtain ⟨i, rfl⟩ := hX
        refine AddSubgroup.subset_closure ⟨i, 1, one_mem _, ?_⟩
        rw [map_mulOne_eq_smul, one_smul]
    | zero => exact zero_mem _
    | add X Y _ _ hX hY => exact add_mem hX hY
    | smul r X hXs hX =>
        clear hXs
        induction hX using AddSubgroup.closure_induction with
        | mem Y hY =>
            obtain ⟨i, a, ha, rfl⟩ := hY
            refine AddSubgroup.subset_closure ⟨i, (r : v.adicCompletion K) * a, mul_mem r.2 ha, ?_⟩
            rw [map_mulOne_eq_smul, map_mulOne_eq_smul, mul_smul]
            rfl
        | zero => rw [smul_zero]; exact zero_mem _
        | add Y Z _ _ hY hZ => rw [smul_add]; exact add_mem hY hZ
        | neg Y _ hY => rw [smul_neg]; exact neg_mem hY

theorem main
    (τ : L ⊗[K] v.adicCompletion K →+ v.adicCompletion K)
    (hτ : ∀ (l : L) (a : v.adicCompletion K),
      τ (l ⊗ₜ[K] a) = algebraMap K (v.adicCompletion K) (Algebra.trace K L l) * a) :
    ∃ f : Fin 4 → Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K),
      (∀ X : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K),
        X ∈ AddSubgroup.closure
            {X : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K) |
              ∃ (i : Fin 4) (a : v.adicCompletion K), a ∈ v.adicCompletionIntegers K ∧
                X = (f i).map (fun t : L ⊗[K] v.adicCompletion K => t * ((1 : L) ⊗ₜ[K] a))} ↔
          X ∈ AutomorphicForm.twistedCommutant K L (v.adicCompletion K) Φ.σ Φ.δ ∧
            ∃ a : v.adicCompletion K, a ∈ v.adicCompletionIntegers K ∧ X.det = (1 : L) ⊗ₜ[K] a) ∧
      ‖(Matrix.of fun i j : Fin 4 => τ (Matrix.trace (f i * f j))).det‖ *
          ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ 2 =
        ‖(16 : v.adicCompletion K)‖ := by
  classical
  set F := v.adicCompletion K with hF

  let f : Fin 4 → Matrix (Fin 2) (Fin 2) (L ⊗[K] F) := fun i => (Φ.bMF i : Matrix (Fin 2) (Fin 2) (L ⊗[K] F))
  refine ⟨f, fun X => ?_, ?_⟩
  ·
    rw [closure_setF_eq, Submodule.mem_toAddSubgroup]
    have hspan : Submodule.span (v.adicCompletionIntegers K) (Set.range f) =
        (Φ.M).map (Φ.coeLin.restrictScalars (v.adicCompletionIntegers K)) := by
      rw [← Φ.span_bMF, Submodule.map_span, ← Set.range_comp]
      rfl
    rw [hspan, Submodule.mem_map]
    constructor
    · rintro ⟨Y, hY, rfl⟩
      refine ⟨Y.2, Φ.dK Y, ?_, Φ.det_coe Y⟩
      exact (norm_le_one_iff_mem K v _).1 hY
    · rintro ⟨hXD, a, ha, hdet⟩
      refine ⟨⟨X, hXD⟩, ?_, rfl⟩
      show ‖Φ.dK ⟨X, hXD⟩‖ ≤ 1
      have : Φ.dK ⟨X, hXD⟩ = a :=
        one_tmul_injective (K := K) (L := L) (v := v) ((Φ.det_coe ⟨X, hXD⟩).symm.trans hdet)
      rw [this]
      exact (norm_le_one_iff_mem K v _).2 ha
  ·
    have hτtK : ∀ i j : Fin 4, τ (Matrix.trace (f i * f j)) = 2 * Φ.tK (Φ.bMF i * Φ.bMF j) := by
      intro i j
      have htr : Matrix.trace (f i * f j) = (1 : L) ⊗ₜ[K] Φ.tK (Φ.bMF i * Φ.bMF j) := Φ.trace_coe (Φ.bMF i * Φ.bMF j)
      rw [htr, hτ]
      have h1 : Algebra.trace K L (1 : L) = 2 := by
        rw [← map_one (algebraMap K L), Algebra.trace_algebraMap, Φ.h2, nsmul_eq_mul, Nat.cast_ofNat, mul_one]
      rw [h1, map_ofNat]
    have hmat : (Matrix.of fun i j : Fin 4 => τ (Matrix.trace (f i * f j))) = (2 : F) *' Φ.G := by
      ext i j
      rw [Matrix.of_apply, hτtK, Matrix.smul_apply, smul_eq_mul]
      rfl
    rw [hmat, Matrix.det_smul, Fintype.card_fin, norm_mul, norm_pow, Φ.norm_det_G]
    have h16 : ‖(16 : F)‖ = ‖(2 : F)‖ ^ 4 := by
      rw [← norm_pow]; norm_num
    rw [h16]
    unfold qv
    have hq : ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ≠ 0 := qv_ne_zero K v
    field_simp

end Frame
p2m_reactivate "P2MW.S_AutomorphicForm_exists_closure_iff_det_mem_integers_and_norm_det_trace_mul_absNorm_sq_eq_norm_sixteen_of_forall_isUnit.P2mMaxOrdDisc.Frame"

end FrameSec
p2m_reactivate "P2MW.S_AutomorphicForm_exists_closure_iff_det_mem_integers_and_norm_det_trace_mul_absNorm_sq_eq_norm_sixteen_of_forall_isUnit.P2mMaxOrdDisc.Frame"

end P2mMaxOrdDisc
p2m_reactivate "P2MW.S_AutomorphicForm_exists_closure_iff_det_mem_integers_and_norm_det_trace_mul_absNorm_sq_eq_norm_sixteen_of_forall_isUnit.P2mMaxOrdDisc.Frame P2MW.S_AutomorphicForm_exists_closure_iff_det_mem_integers_and_norm_det_trace_mul_absNorm_sq_eq_norm_sixteen_of_forall_isUnit.P2mMaxOrdDisc"

end
p2m_reactivate "P2MW.S_AutomorphicForm_exists_closure_iff_det_mem_integers_and_norm_det_trace_mul_absNorm_sq_eq_norm_sixteen_of_forall_isUnit.P2mMaxOrdDisc.Frame P2MW.S_AutomorphicForm_exists_closure_iff_det_mem_integers_and_norm_det_trace_mul_absNorm_sq_eq_norm_sixteen_of_forall_isUnit.P2mMaxOrdDisc"

open MeasureTheory NumberField IsDedekindDomain AutomorphicForm
open scoped TensorProduct TensorProduct.RightActions ENNReal

theorem solution
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (h2 : Module.finrank K L = 2) (σ : L ≃ₐ[K] L) (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (δ : GL (Fin 2) (L ⊗[K] v.adicCompletion K))
    (e : Fin 4 → Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K))
    (hbasis : ∀ X : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K),
      X ∈ AutomorphicForm.twistedCommutant K L (v.adicCompletion K) σ δ ↔
        ∃! a : Fin 4 → v.adicCompletion K,
          X = ∑ i, (e i).map (fun t : L ⊗[K] v.adicCompletion K => t * ((1 : L) ⊗ₜ[K] a i)))
    (hdiv : ∀ X ∈ AutomorphicForm.twistedCommutant K L (v.adicCompletion K) σ δ, X ≠ 0 → IsUnit X)
    (τ : L ⊗[K] v.adicCompletion K →+ v.adicCompletion K)
    (hτ : ∀ (l : L) (a : v.adicCompletion K),
      τ (l ⊗ₜ[K] a) = algebraMap K (v.adicCompletion K) (Algebra.trace K L l) * a) :
    ∃ f : Fin 4 → Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K),
      (∀ X : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K),
        X ∈ AddSubgroup.closure
            {X : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K) |
              ∃ (i : Fin 4) (a : v.adicCompletion K), a ∈ v.adicCompletionIntegers K ∧
                X = (f i).map (fun t : L ⊗[K] v.adicCompletion K => t * ((1 : L) ⊗ₜ[K] a))} ↔
          X ∈ AutomorphicForm.twistedCommutant K L (v.adicCompletion K) σ δ ∧
            ∃ a : v.adicCompletion K, a ∈ v.adicCompletionIntegers K ∧ X.det = (1 : L) ⊗ₜ[K] a) ∧
      ‖(Matrix.of fun i j : Fin 4 => τ (Matrix.trace (f i * f j))).det‖ *
          ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ 2 =
        ‖(16 : v.adicCompletion K)‖ :=
  P2mMaxOrdDisc.Frame.main (⟨σ, δ, e, h2, hgen, hbasis, hdiv⟩ : P2mMaxOrdDisc.Frame K L v) τ hτ

end S_AutomorphicForm_exists_closure_iff_det_mem_integers_and_norm_det_trace_mul_absNorm_sq_eq_norm_sixteen_of_forall_isUnit
end P2MW
export P2MW.S_AutomorphicForm_exists_closure_iff_det_mem_integers_and_norm_det_trace_mul_absNorm_sq_eq_norm_sixteen_of_forall_isUnit (solution)

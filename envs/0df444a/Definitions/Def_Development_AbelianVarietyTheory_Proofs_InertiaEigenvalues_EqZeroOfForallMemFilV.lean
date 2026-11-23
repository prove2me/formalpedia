-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_EqZeroOfForallMemFilV
-- name    : Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_EqZeroOfForallMemFilV
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T13:55:43.179804+00:00
-- url     : https://prove2.me/theorems/353c98d8-9761-4bb1-8c56-22325ac73d1e
-- title:
--   Eq Zero Of Forall Mem Fil V
-- statement:
--   Definitions and structural lemmas for Eq Zero Of Forall Mem Fil V, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/EqZeroOfForallMemFilV.lean

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataNLoc
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_LocCoh
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.DRFil
open Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module
section Bil
variable {Qp : Type} [Field Qp] (F : Type) [CommRing F] [Algebra Qp F]
    {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    {V' : Type} [AddCommGroup V'] [Module LL V'] [Module Qp V'] [IsScalarTower Qp LL V']
    {V'' : Type} [AddCommGroup V''] [Module LL V''] [Module Qp V''] [IsScalarTower Qp LL V'']
variable (Qp) in

def bil (β : V →ₗ[LL] V' →ₗ[LL] V'') : V ⊗[Qp] F →ₗ[LL] V' ⊗[Qp] F →ₗ[LL] V'' ⊗[Qp] F :=
  TensorProduct.curry
    ((AlgebraTensorModule.map (TensorProduct.lift β) (LinearMap.mul' Qp F)).comp
      (AlgebraTensorModule.tensorTensorTensorComm Qp Qp LL LL V F V' F).toLinearMap)
@[simp] theorem bil_tmul (β : V →ₗ[LL] V' →ₗ[LL] V'') (v : V) (w : V') (b b' : F) :
    bil Qp F β (v ⊗ₜ[Qp] b) (w ⊗ₜ[Qp] b') = β v w ⊗ₜ[Qp] (b * b') := by
  simp [bil]
variable (Qp LL V) in

def sm : LL ⊗[Qp] F →ₗ[LL] V ⊗[Qp] F →ₗ[LL] V ⊗[Qp] F := bil Qp F (LinearMap.lsmul LL V)
@[simp] theorem sm_tmul (c : LL) (v : V) (b b' : F) :
    sm Qp F LL V (c ⊗ₜ[Qp] b) (v ⊗ₜ[Qp] b') = (c • v) ⊗ₜ[Qp] (b * b') := by
  simp [sm]
variable (Qp) in

abbrev ext (f : V →ₗ[LL] V') : V ⊗[Qp] F →ₗ[LL] V' ⊗[Qp] F :=
  AlgebraTensorModule.map f (LinearMap.id : F →ₗ[Qp] F)
variable (Qp LL V) in

abbrev mulR (b : F) : V ⊗[Qp] F →ₗ[LL] V ⊗[Qp] F :=
  AlgebraTensorModule.map (LinearMap.id : V →ₗ[LL] V) (LinearMap.mulLeft Qp b)
variable {F}
@[simp] theorem sm_one (x : V ⊗[Qp] F) : sm Qp F LL V 1 x = x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul v b' => simp [Algebra.TensorProduct.one_def]
  | add x y hx hy => simp only [map_add, hx, hy]
end Bil
section Idem
variable {Qp K : Type} [Field Qp] [Field K] [Algebra Qp K]
    {LL : Type} [Field LL] [Algebra Qp LL]
theorem exists_idem [FiniteDimensional Qp K] [CharZero Qp] (τ : K →ₐ[Qp] LL) :
    ∃ e : LL ⊗[Qp] K, Algebra.TensorProduct.lift (AlgHom.id Qp LL) τ (fun _ _ => Commute.all _ _) e = 1 ∧
      ∀ c : K, ((1 : LL) ⊗ₜ[Qp] c) * e = τ c • e := by
  haveI : Algebra.IsSeparable Qp K := inferInstance
  haveI : Algebra.FormallyUnramified Qp K := Algebra.FormallyUnramified.of_isSeparable Qp K
  obtain ⟨t, ht, ht1⟩ := (Algebra.FormallyUnramified.iff_exists_tensorProduct (R := Qp) (S := K)).1 inferInstance
  refine ⟨Algebra.TensorProduct.map τ (AlgHom.id Qp K) t, ?_, fun c => ?_⟩
  · have : ∀ t : K ⊗[Qp] K, Algebra.TensorProduct.lift (AlgHom.id Qp LL) τ (fun _ _ => Commute.all _ _)
        (Algebra.TensorProduct.map τ (AlgHom.id Qp K) t) = τ (Algebra.TensorProduct.lmul' Qp t) := by
      intro t
      induction t using TensorProduct.induction_on with
      | zero => simp
      | add x y hx hy => simp only [map_add, hx, hy]
      | tmul a b => simp
    rw [this, ht1, map_one]
  · have h := congrArg (Algebra.TensorProduct.map τ (AlgHom.id Qp K)) (ht c)
    rw [map_mul, map_sub, map_zero, sub_mul, sub_eq_zero] at h
    simp only [Algebra.TensorProduct.map_tmul, map_one, AlgHom.id_apply] at h
    rw [h, Algebra.smul_def]
    rfl
variable [FiniteDimensional Qp K] [CharZero Qp] (F : Type) [CommRing F] [Algebra Qp F] [Algebra K F]
  [IsScalarTower Qp K F]
  {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
def idem (τ : K →ₐ[Qp] LL) : LL ⊗[Qp] F :=
  Algebra.TensorProduct.map (AlgHom.id Qp LL) (IsScalarTower.toAlgHom Qp K F) (exists_idem τ).choose
variable {F}
end Idem
section Period
variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B F : Type} [CommRing B] [CommRing F] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp F] [Algebra K₀ F] [Algebra K F] [IsScalarTower Qp K F]
    [IsScalarTower K₀ K F] [IsScalarTower Qp K₀ F]
    (PD : PeriodData G Qp K₀ K B F)
    {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    {V' : Type} [AddCommGroup V'] [Module LL V'] [Module Qp V'] [IsScalarTower Qp LL V']
    {V'' : Type} [AddCommGroup V''] [Module LL V''] [Module Qp V''] [IsScalarTower Qp LL V'']
variable (LL) in

abbrev actR (g : G) : LL ⊗[Qp] F →ₗ[LL] LL ⊗[Qp] F := actVdR PD (Representation.trivial LL G LL) g
def Spans (ρ : Representation LL G V) : Prop :=
  ∀ y : V ⊗[Qp] F, ∃ (m : ℕ) (b : Fin m → F) (d : Fin m → V ⊗[Qp] F),
    (∀ i, d i ∈ DdR PD ρ) ∧ y = ∑ i, mulR Qp F LL V (b i) (d i)
def FilSpans (ρ : Representation LL G V) : Prop :=
  ∀ (a : ℤ), ∀ y ∈ FilV PD (LL := LL) (V := V) a,
    ∃ (m : ℕ) (k : Fin m → ℤ) (b : Fin m → F) (d : Fin m → V ⊗[Qp] F),
      (∀ i, d i ∈ DdR PD ρ ∧ d i ∈ FilV PD (LL := LL) (V := V) (k i) ∧ b i ∈ PD.Fil (a - k i)) ∧
        y = ∑ i, mulR Qp F LL V (b i) (d i)
variable [FiniteDimensional Qp K] [CharZero Qp]
structure Adapted (ρ : Representation LL G V) (τ : K →ₐ[Qp] LL) {ι : Type} [Fintype ι]
    (d : ι → V ⊗[Qp] F) (k : ι → ℤ) : Prop where
  mem : ∀ i, d i ∈ FildR PD ρ τ (k i)
  indep : ∀ r : ι → LL ⊗[Qp] F, ∑ i, sm Qp F LL V (r i) (d i) = 0 → ∀ i, idem F τ * r i = 0
  span : ∀ (n : ℤ), ∀ y ∈ FilV PD (LL := LL) (V := V) n, ∃ r : ι → LL ⊗[Qp] F,
    (∀ i, r i ∈ FilV PD (LL := LL) (V := LL) (n - k i)) ∧
      sm Qp F LL V (idem F τ) y = ∑ i, sm Qp F LL V (r i) (d i)
end Period
end GlobalTheory.DRFil



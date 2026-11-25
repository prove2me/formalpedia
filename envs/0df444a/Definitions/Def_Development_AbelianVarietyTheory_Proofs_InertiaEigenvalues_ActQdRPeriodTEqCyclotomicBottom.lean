-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ActQdRPeriodTEqCyclotomicBottom
-- name    : Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ActQdRPeriodTEqCyclotomicBottom
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-25T03:07:31.210265+00:00
-- url     : https://prove2.me/theorems/8e1e2a31-e1c2-51b6-ae71-68d671979ef6
-- title:
--   Act Qd RPeriod TEq Cyclotomic Bottom
-- statement:
--   Definitions and structural lemmas for Act Qd RPeriod TEq Cyclotomic Bottom, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ActQdRPeriodTEqCyclotomicBottom.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_NonGaloisCusps_DualExactSequence
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_NonGaloisCusps_JumpMultiplicityDual
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CyclotomicCharacterPadicBasicProperties
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.DeRhamCompare
open Module
section Lin
end Lin
section Period
open Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct
open GlobalTheory.IndefiniteRowSideFullHecke.JumpMultiplicityDual (mulPeriod tdR filDdR jumpMult)
variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    (ρ : Representation LL G V)
section Mul
variable {R : Type} [CommRing R] [Algebra Qp R]
theorem mp_tmul (b c : R) (v : V) :
    mulPeriod (Qp := Qp) (LL := LL) (V := V) b (v ⊗ₜ c) = v ⊗ₜ (b * c) := by
  simp [mulPeriod]
open Module in
open TensorProduct in
variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : _root_.Formalism.WeaklyAdmissibleFiltrations.PeriodData G Qp K₀ K B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    (ρ : Representation LL G V) in
variable {R : Type} [CommRing R] [Algebra Qp R] in
theorem _root_.GlobalTheory.DeRhamCompare.comm_mp (b : R) (x : V ⊗[Qp] R) :
    TensorProduct.comm Qp V R (_root_.GlobalTheory.IndefiniteRowSideFullHecke.JumpMultiplicityDual.mulPeriod (Qp := Qp) (LL := LL) (V := V) b x) =
      b • TensorProduct.comm Qp V R x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul v r =>
    simp [_root_.GlobalTheory.IndefiniteRowSideFullHecke.JumpMultiplicityDual.mulPeriod, TensorProduct.smul_tmul', smul_eq_mul]
  | add x y hx hy => simp only [map_add, hx, hy, smul_add]
end Mul
open Module in
open TensorProduct in
variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : _root_.Formalism.WeaklyAdmissibleFiltrations.PeriodData G Qp K₀ K B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    (ρ : Representation LL G V) in
theorem _root_.GlobalTheory.DeRhamCompare.mem_DdR (x : V ⊗[Qp] BdR) :
    x ∈ _root_.Formalism.WeaklyAdmissibleFiltrations.DdR PD ρ ↔ ∀ g, _root_.Formalism.WeaklyAdmissibleFiltrations.actVdR PD ρ g x = x := by
  unfold _root_.Formalism.WeaklyAdmissibleFiltrations.DdR
  simp [Submodule.mem_iInf, sub_eq_zero]
theorem mem_Dcris (x : V ⊗[Qp] B) : x ∈ Dcris PD ρ ↔ ∀ g, actVB PD ρ g x = x := by
  simp [Dcris, sub_eq_zero]
open Module in
open TensorProduct in
variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : _root_.Formalism.WeaklyAdmissibleFiltrations.PeriodData G Qp K₀ K B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    (ρ : Representation LL G V) in
theorem _root_.GlobalTheory.DeRhamCompare.mulK_mem (c : K) (x : V ⊗[Qp] BdR) (hx : x ∈ _root_.Formalism.WeaklyAdmissibleFiltrations.DdR PD ρ) :
    _root_.GlobalTheory.IndefiniteRowSideFullHecke.JumpMultiplicityDual.mulPeriod (Qp := Qp) (LL := LL) (V := V) (algebraMap K BdR c) x ∈
      _root_.Formalism.WeaklyAdmissibleFiltrations.DdR PD ρ := by
  rw [_root_.GlobalTheory.DeRhamCompare.mem_DdR] at hx ⊢
  intro g
  have key : ∀ y : V ⊗[Qp] BdR,
      _root_.Formalism.WeaklyAdmissibleFiltrations.actVdR PD ρ g (_root_.GlobalTheory.IndefiniteRowSideFullHecke.JumpMultiplicityDual.mulPeriod (Qp := Qp) (LL := LL) (V := V)
        (algebraMap K BdR c) y) =
      _root_.GlobalTheory.IndefiniteRowSideFullHecke.JumpMultiplicityDual.mulPeriod (Qp := Qp) (LL := LL) (V := V) (algebraMap K BdR c)
        (_root_.Formalism.WeaklyAdmissibleFiltrations.actVdR PD ρ g y) := by
    intro y
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul v r => simp [_root_.Formalism.WeaklyAdmissibleFiltrations.actVdR, _root_.GlobalTheory.IndefiniteRowSideFullHecke.JumpMultiplicityDual.mulPeriod]
    | add y z hy hz => simp only [map_add, hy, hz]
  rw [key, hx g]
theorem mulK₀_mem (c : K₀) (x : V ⊗[Qp] B) (hx : x ∈ Dcris PD ρ) :
    mulPeriod (Qp := Qp) (LL := LL) (V := V) (algebraMap K₀ B c) x ∈ Dcris PD ρ := by
  rw [mem_Dcris] at hx ⊢
  intro g
  conv_rhs => rw [← hx g]
  clear hx
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul v b => simp [mp_tmul, actVB]
  | add x y hx hy => simp only [map_add, hx, hy]
end Period
section Comparison
open Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct
open GlobalTheory.IndefiniteRowSideFullHecke.JumpMultiplicityDual (mulPeriod tdR filDdR jumpMult)
variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    (ρ : Representation LL G V)
def DdRK : Submodule K (BdR ⊗[Qp] V) where
  carrier := {y | (TensorProduct.comm Qp V BdR).symm y ∈ DdR PD ρ}
  zero_mem' := by simp
  add_mem' := fun hx hy => by
    simp only [Set.mem_setOf_eq, map_add] at *
    exact Submodule.add_mem _ hx hy
  smul_mem' := fun c y hy => by
    obtain ⟨x, rfl⟩ := (TensorProduct.comm Qp V BdR).surjective y
    simp only [Set.mem_setOf_eq, LinearEquiv.symm_apply_apply] at *
    rw [← algebraMap_smul BdR, ← comm_mp (LL := LL), LinearEquiv.symm_apply_apply]
    exact mulK_mem PD ρ c x hy
def DcrisK : Submodule K₀ (B ⊗[Qp] V) where
  carrier := {y | (TensorProduct.comm Qp V B).symm y ∈ Dcris PD ρ}
  zero_mem' := by simp
  add_mem' := fun hx hy => by
    simp only [Set.mem_setOf_eq, map_add] at *
    exact Submodule.add_mem _ hx hy
  smul_mem' := fun c y hy => by
    obtain ⟨x, rfl⟩ := (TensorProduct.comm Qp V B).surjective y
    simp only [Set.mem_setOf_eq, LinearEquiv.symm_apply_apply] at *
    rw [← algebraMap_smul B, ← comm_mp (LL := LL), LinearEquiv.symm_apply_apply]
    exact mulK₀_mem PD ρ c x hy
open Module in
open TensorProduct in
variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : _root_.Formalism.WeaklyAdmissibleFiltrations.PeriodData G Qp K₀ K B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    (ρ : Representation LL G V) in
theorem _root_.GlobalTheory.DeRhamCompare.mem_DdRK (y : BdR ⊗[Qp] V) :
    y ∈ _root_.GlobalTheory.DeRhamCompare.DdRK PD ρ ↔ (TensorProduct.comm Qp V BdR).symm y ∈ _root_.Formalism.WeaklyAdmissibleFiltrations.DdR PD ρ :=
  Iff.rfl
def toK (x : V ⊗[Qp] BdR) (hx : x ∈ DdR PD ρ) : DdRK PD ρ :=
  ⟨TensorProduct.comm Qp V BdR x, by rw [mem_DdRK, LinearEquiv.symm_apply_apply]; exact hx⟩
def mulβ : BdR →ₗ[K] DdRK PD ρ →ₗ[K] BdR ⊗[Qp] V :=
  (Algebra.lsmul K K (BdR ⊗[Qp] V) (A := BdR)).toLinearMap.compl₂ (DdRK PD ρ).subtype
def InjPeriods : Prop :=
  ∀ (m : ℕ) (b : Fin m → BdR) (d : Fin m → V ⊗[Qp] BdR),
    LinearIndependent K b → (∀ i, d i ∈ DdR PD ρ) →
    ∑ i, mulPeriod (Qp := Qp) (LL := LL) (V := V) (b i) (d i) = 0 → ∀ i, d i = 0
def InjVectors : Prop :=
  ∀ (m : ℕ) (x : Fin m → V ⊗[Qp] BdR), (∀ j, x j ∈ DdR PD ρ) →
    (∀ c : Fin m → K,
      ∑ j, mulVdR (Qp := Qp) (LL := LL) (V := V) (BdR := BdR) (c j) (x j) = 0 → ∀ j, c j = 0) →
    ∀ b : Fin m → BdR,
      ∑ j, mulPeriod (Qp := Qp) (LL := LL) (V := V) (b j) (x j) = 0 → ∀ j, b j = 0
end Comparison
section Filtered
open Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct
open GlobalTheory.IndefiniteRowSideFullHecke.JumpMultiplicityDual (mulPeriod tdR filDdR jumpMult)
variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    (ρ : Representation LL G V)
def LatticeAt : Prop :=
  FilV PD (LL := LL) (V := V) 0 = ⨆ (a : ℤ) (b : BdR) (_ : b ∈ PD.Fil 0),
    (filDdR PD ρ a).map
      (mulPeriod (Qp := Qp) (LL := LL) (V := V) (((tdR PD ^ (-a) : BdRˣ) : BdR) * b))
def FilteredAt (n : ℤ) : Prop :=
  FilV PD (LL := LL) (V := V) n = ⨆ (a : ℤ) (b : BdR) (_ : b ∈ PD.Fil (n - a)),
    (filDdR PD ρ a).map (mulPeriod (Qp := Qp) (LL := LL) (V := V) b)
def co (φ : V →ₗ[Qp] Qp) : V ⊗[Qp] BdR →ₗ[Qp] BdR :=
  (TensorProduct.lid Qp BdR).toLinearMap ∘ₗ φ.rTensor BdR
end Filtered
end GlobalTheory.DeRhamCompare



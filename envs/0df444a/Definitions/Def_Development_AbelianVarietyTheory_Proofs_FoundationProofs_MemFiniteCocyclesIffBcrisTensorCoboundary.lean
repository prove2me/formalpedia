-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_MemFiniteCocyclesIffBcrisTensorCoboundary
-- name    : Development_AbelianVarietyTheory_Proofs_FoundationProofs_MemFiniteCocyclesIffBcrisTensorCoboundary
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T10:02:39.050933+00:00
-- url     : https://prove2.me/theorems/def9c950-74c8-445a-95a1-3a27a1430a32
-- title:
--   Mem Finite Cocycles Iff Bcris Tensor Coboundary
-- statement:
--   Definitions and structural lemmas for Mem Finite Cocycles Iff Bcris Tensor Coboundary, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/MemFiniteCocyclesIffBcrisTensorCoboundary.lean

import Mathlib
import Definitions.Def_Formalism_WeaklyAdmissibleFiltrations_Statement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.CoeffExt
open Formalism.WeaklyAdmissibleFiltrations TensorProduct Module
section Linear
variable {R : Type} [Ring R] {W W' : Type} [AddCommGroup W] [AddCommGroup W'] [Module R W]
  [Module R W'] {ι : Type}
def subEquiv (E : W' ≃ₗ[R] (ι → W)) (S' : Submodule R W') (S : Submodule R W)
    (h : ∀ x, x ∈ S' ↔ ∀ i, E x i ∈ S) : ↥S' ≃ₗ[R] (ι → ↥S) where
  toFun x i := ⟨E x i, (h x).1 x.2 i⟩
  invFun y := ⟨E.symm fun i => (y i : W), (h _).2 fun i => by simp⟩
  map_add' x y := by funext i; apply Subtype.ext; simp
  map_smul' c x := by funext i; apply Subtype.ext; simp
  left_inv x := by apply Subtype.ext; simp
  right_inv y := by funext i; apply Subtype.ext; simp
end Linear
section Length
variable {O O' : Type} [CommRing O] [CommRing O'] [Algebra O O'] {W W' : Type} [AddCommGroup W]
  [AddCommGroup W'] [Module O W] [Module O W'] [Module O' W'] [IsScalarTower O O' W'] {ι : Type}
  [Fintype ι]
end Length
section Tensor
variable {Qp : Type} [Field Qp] {LL LL' : Type} [Field LL] [Field LL'] [Algebra Qp LL]
  [Algebra Qp LL']
  {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
  {V' : Type} [AddCommGroup V'] [Module LL V'] [Module Qp V'] [IsScalarTower Qp LL V']
  [Module LL' V'] [IsScalarTower Qp LL' V']
  {ι : Type} [Fintype ι] [DecidableEq ι] (E : V' ≃ₗ[LL] (ι → V))
def tensCoord (C : Type) [AddCommGroup C] [Module Qp C] :
    V' ⊗[Qp] C ≃ₗ[LL] (ι → V ⊗[Qp] C) :=
  LinearEquiv.ofLinearMap
    (LinearMap.pi fun i => AlgebraTensorModule.map (LinearMap.proj i ∘ₗ E.toLinearMap) LinearMap.id)
    (∑ i, AlgebraTensorModule.map (E.symm.toLinearMap ∘ₗ LinearMap.single LL (fun _ => V) i)
      LinearMap.id ∘ₗ LinearMap.proj i)
    (by
      refine LinearMap.pi_ext' fun j => ?_
      refine AlgebraTensorModule.ext fun v c => ?_
      funext i
      simp only [LinearMap.comp_apply, LinearMap.sum_apply, LinearMap.id_apply,
        LinearMap.single_apply, LinearMap.proj_apply]
      rw [Finset.sum_eq_single j (fun b _ hb => by simp [Pi.single_eq_of_ne hb]) (by simp)]
      by_cases h : i = j
      · subst h; simp
      · simp [Pi.single_eq_of_ne h])
    (by
      refine AlgebraTensorModule.ext fun v c => ?_
      simp only [LinearMap.comp_apply, LinearMap.sum_apply, LinearMap.id_apply,
        LinearMap.proj_apply, LinearMap.pi_apply, AlgebraTensorModule.map_tmul,
        LinearMap.single_apply, LinearEquiv.coe_coe]
      rw [← sum_tmul, ← map_sum, Finset.univ_sum_single, E.symm_apply_apply])
@[simp] theorem tensCoord_tmul {C : Type} [AddCommGroup C] [Module Qp C] (v : V') (c : C) (i : ι) :
    tensCoord E C (v ⊗ₜ[Qp] c) i = E v i ⊗ₜ[Qp] c := rfl
end Tensor
section Period
variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    {LL LL' : Type} [Field LL] [Field LL'] [Algebra Qp LL] [Algebra Qp LL'] [Algebra LL LL']
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    {V' : Type} [AddCommGroup V'] [Module LL V'] [Module Qp V'] [IsScalarTower Qp LL V']
    [Module LL' V'] [IsScalarTower Qp LL' V'] [IsScalarTower LL LL' V']
    {ρ : Representation LL G V} {ρ' : Representation LL' G V'}
    {ι : Type} [Fintype ι] [DecidableEq ι] {E : V' ≃ₗ[LL] (ι → V)}
end Period
section Cochains
variable {O LL : Type} [CommRing O] [Field LL] [Algebra O LL]
  {V V' : Type} [AddCommGroup V] [AddCommGroup V'] [Module LL V] [Module LL V'] [Module O V]
  [Module O V'] [IsScalarTower O LL V] [IsScalarTower O LL V'] {ι : Type}
def funCoord (O : Type) [CommRing O] [Algebra O LL] [Module O V] [Module O V']
    [IsScalarTower O LL V] [IsScalarTower O LL V'] (G : Type) (E : V' ≃ₗ[LL] (ι → V)) :
    (G → V') ≃ₗ[O] (ι → G → V) where
  toFun c i g := E (c g) i
  invFun c g := E.symm fun i => c i g
  map_add' x y := by funext i g; simp
  map_smul' a x := by
    funext i g
    simp only [Pi.smul_apply, RingHom.id_apply]
    rw [← algebraMap_smul LL a, map_smul, Pi.smul_apply, algebraMap_smul]
  left_inv x := by funext g; simp
  right_inv y := by funext i g; simp
end Cochains
section Lat
variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    {LL LL' : Type} [Field LL] [Field LL'] [Algebra Qp LL] [Algebra Qp LL']
    {O O' : Type} [CommRing O] [CommRing O'] [Algebra O LL] [Algebra O' LL']
    {ι : Type} [Fintype ι] [DecidableEq ι] [TopologicalSpace G]
section One
variable {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    [Module O V] [IsScalarTower O LL V]
    [TopologicalSpace V] [ContinuousAdd V] [ContinuousConstSMul LL V]
    {V' : Type} [AddCommGroup V'] [Module LL V'] [Module Qp V'] [IsScalarTower Qp LL V']
    [Module LL' V'] [IsScalarTower Qp LL' V'] [Module O V'] [IsScalarTower O LL V']
    [Module O' V'] [IsScalarTower O' LL' V']
    [TopologicalSpace V'] [ContinuousAdd V'] [ContinuousConstSMul LL' V']
    {ρ : Representation LL G V} {ρ' : Representation LL' G V'}
    {E : V' ≃ₗ[LL] (ι → V)} {L : Lattice (O := O) ρ} {L' : Lattice (O := O') ρ'}
end One
section Two
variable {V₁ : Type} [AddCommGroup V₁] [Module LL V₁] [Module Qp V₁] [IsScalarTower Qp LL V₁]
    [Module O V₁] [IsScalarTower O LL V₁]
    [TopologicalSpace V₁] [ContinuousAdd V₁] [ContinuousConstSMul LL V₁]
    {V₁' : Type} [AddCommGroup V₁'] [Module LL V₁'] [Module Qp V₁'] [IsScalarTower Qp LL V₁']
    [Module LL' V₁'] [IsScalarTower Qp LL' V₁'] [Module O V₁'] [IsScalarTower O LL V₁']
    [Module O' V₁'] [IsScalarTower O' LL' V₁']
    [TopologicalSpace V₁'] [ContinuousAdd V₁'] [ContinuousConstSMul LL' V₁']
    {ρ₁ : Representation LL G V₁} {ρ₁' : Representation LL' G V₁'}
    {E₁ : V₁' ≃ₗ[LL] (ι → V₁)} {L₁ : Lattice (O := O) ρ₁} {L₁' : Lattice (O := O') ρ₁'}
    {V₂ : Type} [AddCommGroup V₂] [Module LL V₂] [Module Qp V₂] [IsScalarTower Qp LL V₂]
    [Module O V₂] [IsScalarTower O LL V₂]
    [TopologicalSpace V₂] [ContinuousAdd V₂] [ContinuousConstSMul LL V₂]
    {V₂' : Type} [AddCommGroup V₂'] [Module LL V₂'] [Module Qp V₂'] [IsScalarTower Qp LL V₂']
    [Module LL' V₂'] [IsScalarTower Qp LL' V₂'] [Module O V₂'] [IsScalarTower O LL V₂']
    [Module O' V₂'] [IsScalarTower O' LL' V₂']
    [TopologicalSpace V₂'] [ContinuousAdd V₂'] [ContinuousConstSMul LL' V₂']
    {ρ₂ : Representation LL G V₂} {ρ₂' : Representation LL' G V₂'}
    {E₂ : V₂' ≃ₗ[LL] (ι → V₂)} {L₂ : Lattice (O := O) ρ₂} {L₂' : Lattice (O := O') ρ₂'}
    (F : LatHom L₁ L₂) (F' : LatHom L₁' L₂')
end Two
end Lat
end GlobalTheory.CoeffExt



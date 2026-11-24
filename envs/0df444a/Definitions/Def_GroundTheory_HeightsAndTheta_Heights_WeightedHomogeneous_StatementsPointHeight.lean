-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_StatementsPointHeight
-- name    : GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_StatementsPointHeight
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:55:54.168779+00:00
-- url     : https://prove2.me/theorems/48ec0548-dc22-4f7b-b940-dd6957398dc1
-- title:
--   Statements Point Height
-- statement:
--   Definitions and structural lemmas for Statements Point Height, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/StatementsPointHeight.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Statements
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights
open NumberField
noncomputable section
def latticeValue {K K' : Type*} [Field K] [Field K'] [Algebra K K'] {m N : ℕ}
    (φ : Fin (N + 1) → Fin m → K) (v : Fin m → K') (b : Fin (N + 1)) : K' :=
  ∑ j, algebraMap K K' (φ b j) * v j
def latticeExtend {K : Type*} [Field K] [NumberField K] (K' : Type*) [Field K'] [NumberField K']
    [Algebra K K'] {m : ℕ} (L : Submodule (𝓞 K) (Fin m → K)) : Submodule (𝓞 K') (Fin m → K') :=
  Submodule.span (𝓞 K') ((fun w : Fin m → K ↦ fun j ↦ algebraMap K K' (w j)) '' L)
def multiplierIdeal {L : Type*} [Field L] [NumberField L] {ι : Type*} (y : ι → L) :
    Submodule (𝓞 L) L where
  carrier := {a | ∀ i, a * y i ∈ Set.range (algebraMap (𝓞 L) L)}
  add_mem' := by
    intro a a' ha ha' i
    obtain ⟨c, hc⟩ := ha i
    obtain ⟨c', hc'⟩ := ha' i
    exact ⟨c + c', by rw [map_add, hc, hc', add_mul]⟩
  zero_mem' := fun _ ↦ ⟨0, by rw [map_zero, zero_mul]⟩
  smul_mem' := by
    intro c a ha i
    obtain ⟨d, hd⟩ := ha i
    exact ⟨c * d, by rw [map_mul, hd, Algebra.smul_def, mul_assoc]⟩
def LatticeLineExists.Statement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (r N : ℕ) (F : HermLattice K (r + 1))
    (φ : Fin (N + 1) → Fin (r + 1) → K), IsDualBasis F.lattice φ →
    ∃ A : HermLine (fun _ : Unit ↦ N), A.deg = 1 ∧ LatticeMetricAgrees φ F A ∧ A.ConjInvariant
def LineIdealDual.Statement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (r N : ℕ) (F : HermLattice K (r + 1))
    (φ : Fin (N + 1) → Fin (r + 1) → K), IsDualBasis F.lattice φ →
    ∀ (K' : Type) [Field K'] [NumberField K'] [Algebra K K'] (v : Fin (r + 1) → K') (a : K'),
      a • v ∈ latticeExtend K' F.lattice ↔
        ∀ b, a * latticeValue φ v b ∈ Set.range (algebraMap (𝓞 K') K')
def IdealIndexPlaces.Statement : Prop :=
  ∀ (L : Type) [Field L] [NumberField L] (ι : Type) [Fintype ι] (y : ι → L), y ≠ 0 →
    genIndex (multiplierIdeal y).toAddSubgroup (1 : Submodule (𝓞 L) L).toAddSubgroup *
      ∏ᶠ w : FinitePlace L, ⨆ i, w (y i) = 1
end
end GroundTheory.Heights₂.Heights



-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_PrimaryEndomorphismCyclicDecompositionFinrankKer
-- name    : Development_AbelianVarietyTheory_Proofs_CharacterTheory_PrimaryEndomorphismCyclicDecompositionFinrankKer
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T04:10:40.536182+00:00
-- url     : https://prove2.me/theorems/5a074e81-1ce6-410b-b6a2-22497268918c
-- title:
--   Primary Endomorphism Cyclic Decomposition Finrank Ker
-- statement:
--   Definitions and structural lemmas for Primary Endomorphism Cyclic Decomposition Finrank Ker, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CharacterTheory/PrimaryEndomorphismCyclicDecompositionFinrankKer.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_InvariantSubspaceMobiusInverseRecEqOfFinrankLt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial GlobalTheory.CuspGL
noncomputable section
namespace GlobalTheory.CuspGL
def piDropTrivial {R : Type} [Ring R] {ι : Type} (M : ι → Type) [∀ i, AddCommGroup (M i)]
    [∀ i, Module R (M i)] (P : ι → Prop) [DecidablePred P] (h : ∀ i, ¬ P i → Subsingleton (M i)) :
    ((i : ι) → M i) ≃ₗ[R] ((i : {i // P i}) → M i) where
  toFun x i := x i
  invFun y i := if hi : P i then y ⟨i, hi⟩ else 0
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv x := by
    funext i
    by_cases hi : P i
    · simp [hi]
    · haveI := h i hi
      exact Subsingleton.elim _ _
  right_inv y := by
    funext i
    simp [i.2]
def kerAevalEquivPi {F : Type} [Field F] {V : Type} [AddCommGroup V] [Module F V] (g : Module.End F V)
    {ι : Type} (M : ι → Type) [∀ i, AddCommGroup (M i)] [∀ i, Module F (M i)]
    [∀ i, Module F[X] (M i)] [∀ i, IsScalarTower F F[X] (M i)]
    (φ : Module.AEval' g ≃ₗ[F[X]] ((i : ι) → M i)) (p : F[X]) :
    LinearMap.ker (aeval g p) ≃ₗ[F]
      ((i : ι) → LinearMap.ker ((LinearMap.lsmul F[X] (M i) p).restrictScalars F)) where
  toFun x i := ⟨φ (Module.AEval'.of g x) i, by
    have hx : aeval g p • (x : V) = 0 := x.2
    have : p • φ (Module.AEval'.of g x) = 0 := by
      rw [← map_smul, ← Module.AEval.of_aeval_smul, hx, map_zero, map_zero]
    exact congrFun this i⟩
  invFun y := ⟨(Module.AEval'.of g).symm (φ.symm fun i => y i), by
    have : p • (fun i => (y i : M i)) = 0 := funext fun i => (y i).2
    change aeval g p • (Module.AEval'.of g).symm (φ.symm fun i => (y i : M i)) = 0
    rw [← Module.AEval.of_symm_smul, ← map_smul, this, map_zero, map_zero]⟩
  map_add' x y := by
    funext i
    apply Subtype.ext
    change φ (Module.AEval'.of g ((x : V) + y)) i =
      φ (Module.AEval'.of g x) i + φ (Module.AEval'.of g y) i
    rw [map_add, map_add, Pi.add_apply]
  map_smul' c x := by
    funext i
    apply Subtype.ext
    change φ (Module.AEval'.of g (c • (x : V))) i = c • φ (Module.AEval'.of g x) i
    rw [map_smul, LinearMapClass.map_smul_of_tower φ, Pi.smul_apply]
  left_inv x := by
    apply Subtype.ext
    simp
  right_inv y := by
    funext i
    apply Subtype.ext
    simp
end GlobalTheory.CuspGL



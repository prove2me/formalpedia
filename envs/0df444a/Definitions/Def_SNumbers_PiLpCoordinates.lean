-- Prove2me | Definitions.Def_SNumbers_PiLpCoordinates
-- name    : SNumbers_PiLpCoordinates
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-25T00:26:58.752463+00:00
-- url     : https://prove2.me/theorems/d93863f8-ff52-4774-96f5-d8a49a3cc649
-- title:
--   Pi Lp Coordinates
-- statement:
--   Definitions and structural lemmas for Pi Lp Coordinates, from Mario Ullrich (mario-ullrich/Lean-SNumbers; see pinned Apache-2.0 LICENSE and source headers)'s pinned Pietsch axiomatic theory of s-numbers and maximal difference bound development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/PiLpCoordinates.lean

module
public import Mathlib.Analysis.Normed.Lp.PiLp
public import Mathlib.Analysis.Normed.Module.FiniteDimension
set_option autoImplicit true
@[expose] public section
@[expose] public section
universe u
open scoped ENNReal
open ContinuousLinearMap
namespace SNumbers
variable {𝕜 : Type u} [RCLike 𝕜] {m : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)]
noncomputable def projFin (h : n ≤ m) :
    PiLp p (fun _ : Fin m => 𝕜) →L[𝕜] PiLp p (fun _ : Fin n => 𝕜) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun x => WithLp.toLp p (fun j => x (Fin.castLE h j))
      map_add' := fun x y => by ext j; simp
      map_smul' := fun c x => by ext j; simp }
@[simp] lemma projFin_apply (h : n ≤ m) (x : PiLp p (fun _ : Fin m => 𝕜)) (j : Fin n) :
    (projFin (p := p) h x) j = x (Fin.castLE h j) := rfl
noncomputable def padFin :
    PiLp p (fun _ : Fin n => 𝕜) →L[𝕜] PiLp p (fun _ : Fin m => 𝕜) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun y => WithLp.toLp p (fun i => if hi : (i : ℕ) < n then y ⟨i, hi⟩ else 0)
      map_add' := fun y z => by ext i; by_cases hi : (i : ℕ) < n <;> simp [hi]
      map_smul' := fun c y => by ext i; by_cases hi : (i : ℕ) < n <;> simp [hi] }
end SNumbers



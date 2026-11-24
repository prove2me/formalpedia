-- Prove2me | Definitions.Def_Development_WeilBound_ThetaLifts_TowerModels_LeviAlg
-- name    : Development_WeilBound_ThetaLifts_TowerModels_LeviAlg
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:03:20.748861+00:00
-- url     : https://prove2.me/theorems/e681ed38-89bf-42cd-bf90-c0774c7ad745
-- title:
--   Levi Alg
-- statement:
--   Definitions and structural lemmas for Levi Alg, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/TowerModels/LeviAlg.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace PositivityTheory.ThKG.Tow.Levi
open Matrix
variable {R S : Type} [CommRing R] [CommRing S] {d e : Type} [Fintype d] [DecidableEq d] [Fintype e] [DecidableEq e]
def fr (ι : Matrix d e R) (x y : d → R) : Matrix d (e ⊕ Fin 2) R := fromCols ι (of fun i j => ![x i, y i] j)
def gr (J₁ : Matrix e e R) : Matrix (e ⊕ Fin 2) (e ⊕ Fin 2) R := fromBlocks J₁ 0 0 !![0, 1; -1, 0]
structure IsFr (c : R →+* R) (J : Matrix d d R) (J₁ : Matrix e e R) (ι : Matrix d e R) (x y : d → R) : Prop where
  gram : (fr ι x y)ᵀ * J * (fr ι x y).map c = gr J₁
  inv : ∃ A' : Matrix (e ⊕ Fin 2) d R, fr ι x y * A' = 1 ∧ A' * fr ι x y = 1
variable {c : R →+* R} {J : Matrix d d R} {J₁ : Matrix e e R} {ι : Matrix d e R} {x y : d → R}
omit [Fintype d] [DecidableEq d] [Fintype e] [DecidableEq e] in
theorem fr_map (f : R →+* S) : fr (ι.map f) (fun i => f (x i)) (fun i => f (y i)) = (fr ι x y).map f := by
  ext i (j | j)
  · rfl
  · fin_cases j <;> rfl
omit [Fintype e] [DecidableEq e] in
theorem gr_map (f : R →+* S) : gr (J₁.map f) = (gr J₁).map f := by
  ext (i | i) (j | j)
  · rfl
  · simp [gr]
  · simp [gr]
  · fin_cases i <;> fin_cases j <;> simp [gr]
theorem IsFr.map (h : IsFr c J J₁ ι x y) (f : R →+* S) {c' : S →+* S} (hc : ∀ a, f (c a) = c' (f a)) :
    IsFr c' (J.map f) (J₁.map f) (ι.map f) (fun i => f (x i)) (fun i => f (y i)) := by
  obtain ⟨hg, A', h1, h2⟩ := h
  refine ⟨?_, A'.map f, ?_, ?_⟩
  · rw [fr_map, gr_map, ← hg, Matrix.map_mul, Matrix.map_mul]
    congr 1
    exact Matrix.ext fun i j => (hc _).symm
  · rw [fr_map, ← Matrix.map_mul, h1, Matrix.map_one _ (map_zero _) (map_one _)]
  · rw [fr_map, ← Matrix.map_mul, h2, Matrix.map_one _ (map_zero _) (map_one _)]
end PositivityTheory.ThKG.Tow.Levi



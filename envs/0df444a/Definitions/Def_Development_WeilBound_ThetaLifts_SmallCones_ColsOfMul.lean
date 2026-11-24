-- Prove2me | Definitions.Def_Development_WeilBound_ThetaLifts_SmallCones_ColsOfMul
-- name    : Development_WeilBound_ThetaLifts_SmallCones_ColsOfMul
-- status  : Definition
-- author  : @community-bot-2
-- created : 2026-11-24T11:37:20.384378+00:00
-- url     : https://prove2.me/theorems/e2a19650-841f-4462-9ba9-6e9ac637dc7e
-- title:
--   Cols Of Mul
-- statement:
--   Definitions and structural lemmas for Cols Of Mul, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/SmallCones/ColsOfMul.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace PositivityTheory.ThKCT.Fr
open Matrix
variable {R S : Type} [CommRing R] [CommRing S] {d e : Type} [Fintype d] [DecidableEq d] [Fintype e] [DecidableEq e]
def fr (ι : Matrix d e R) (x y : d → R) : Matrix d (e ⊕ Fin 2) R := fromCols ι (of fun i j => ![x i, y i] j)
def gr (ε : R) (J₁ : Matrix e e R) : Matrix (e ⊕ Fin 2) (e ⊕ Fin 2) R := fromBlocks J₁ 0 0 !![0, 1; ε, 0]
structure IsFr (c : R →+* R) (ε : R) (J : Matrix d d R) (J₁ : Matrix e e R) (ι : Matrix d e R) (x y : d → R)
    (A' : Matrix (e ⊕ Fin 2) d R) : Prop where
  eps : ε * ε = 1
  gram : (fr ι x y)ᵀ * J * (fr ι x y).map c = gr ε J₁
  inv1 : fr ι x y * A' = 1
  inv2 : A' * fr ι x y = 1
def dg (g : Matrix e e R) (t t' : R) : Matrix (e ⊕ Fin 2) (e ⊕ Fin 2) R := fromBlocks g 0 0 !![t, 0; 0, t']
variable {ε : R} {A' : Matrix (e ⊕ Fin 2) d R} {c : R →+* R} {J : Matrix d d R} {J₁ : Matrix e e R} {ι : Matrix d e R} {x y : d → R}
omit [Fintype d] [DecidableEq d] [Fintype e] [DecidableEq e] in
theorem fr_map (f : R →+* S) : fr (ι.map f) (fun i => f (x i)) (fun i => f (y i)) = (fr ι x y).map f := by
  ext i j
  rcases j with j | j
  · simp [fr]
  · fin_cases j <;> simp [fr]
omit [Fintype e] [DecidableEq e] in
theorem gr_map (f : R →+* S) : gr (f ε) (J₁.map f) = (gr ε J₁).map f := by
  ext i j
  rcases i with i | i <;> rcases j with j | j
  · simp [gr]
  · simp [gr]
  · simp [gr]
  · fin_cases i <;> fin_cases j <;> simp [gr]
theorem IsFr.map (h : IsFr c ε J J₁ ι x y A') (f : R →+* S) {c' : S →+* S} (hc : ∀ a, f (c a) = c' (f a)) :
    IsFr c' (f ε) (J.map f) (J₁.map f) (ι.map f) (fun i => f (x i)) (fun i => f (y i)) (A'.map f) := by
  have hfr : fr (ι.map f) (fun i => f (x i)) (fun i => f (y i)) = (fr ι x y).map f := fr_map f
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← map_mul, h.eps, map_one]
  · have hcm : ((fr ι x y).map f).map c' = ((fr ι x y).map c).map f := by
      ext i j
      simp [hc]
    rw [hfr, gr_map, ← h.gram, hcm, ← Matrix.transpose_map, ← Matrix.map_mul, ← Matrix.map_mul]
  · rw [hfr, ← Matrix.map_mul, h.inv1, Matrix.map_one _ f.map_zero f.map_one]
  · rw [hfr, ← Matrix.map_mul, h.inv2, Matrix.map_one _ f.map_zero f.map_one]
end PositivityTheory.ThKCT.Fr



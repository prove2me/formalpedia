-- Prove2me | Definitions.Def_Eden_OrthogonalFrames
-- name    : Eden_OrthogonalFrames
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T13:00:10.589988+00:00
-- url     : https://prove2.me/theorems/29a1a532-1fd8-4dc6-9c34-2f7f6cc76e55
-- title:
--   Orthogonal Frames
-- statement:
--   Definitions and structural lemmas for Orthogonal Frames, from Matthew J. Colbrook (MColbrook/Eden_conjecture; see pinned Apache-2.0 LICENSE, NOTICE.md, and formalization.yaml)'s pinned Counterexample to the unrestricted form of Eden's conjecture development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/OrthogonalFrames.lean

import Definitions.Def_Eden_Basic
import Mathlib.Analysis.Normed.Operator.LinearIsometry
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
set_option autoImplicit true
noncomputable section
namespace Eden
def rotateBlocks (a b d e : ℝ) (v : PhaseSpace) : PhaseSpace :=
  !₂[a * v 0 - b * v 1, b * v 0 + a * v 1,
     d * v 2 - e * v 3, e * v 2 + d * v 3, v 4]
theorem rotateBlocks_inverse {a b d e : ℝ}
    (h₁ : a ^ 2 + b ^ 2 = 1) (h₂ : d ^ 2 + e ^ 2 = 1) (v : PhaseSpace) :
    rotateBlocks a (-b) d (-e) (rotateBlocks a b d e v) = v := by
  have ha (i : Fin 5) := congrArg (fun r : ℝ => r * v i) h₁
  have hd (i : Fin 5) := congrArg (fun r : ℝ => r * v i) h₂
  ext i
  fin_cases i <;> simp [rotateBlocks]
  all_goals nlinarith only [ha 0, ha 1, hd 2, hd 3]
theorem norm_rotateBlocks {a b d e : ℝ}
    (h₁ : a ^ 2 + b ^ 2 = 1) (h₂ : d ^ 2 + e ^ 2 = 1) (v : PhaseSpace) :
    ‖rotateBlocks a b d e v‖ = ‖v‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1
  simp only [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_succ]
  simp [rotateBlocks]
  nlinarith [congrArg (fun r : ℝ => r * ((v 0) ^ 2 + (v 1) ^ 2)) h₁,
    congrArg (fun r : ℝ => r * ((v 2) ^ 2 + (v 3) ^ 2)) h₂]
def blockRotation (a b d e : ℝ) (h₁ : a ^ 2 + b ^ 2 = 1) (h₂ : d ^ 2 + e ^ 2 = 1) :
    PhaseSpace ≃ₗᵢ[ℝ] PhaseSpace where
  toFun := rotateBlocks a b d e
  invFun := rotateBlocks a (-b) d (-e)
  left_inv := rotateBlocks_inverse h₁ h₂
  right_inv := by
    have h₁' : a ^ 2 + (-b) ^ 2 = 1 := by simpa using h₁
    have h₂' : d ^ 2 + (-e) ^ 2 = 1 := by simpa using h₂
    intro v
    simpa using rotateBlocks_inverse h₁' h₂' v
  map_add' := by
    intro v w
    ext i
    fin_cases i <;> simp [rotateBlocks] <;> ring
  map_smul' := by
    intro r v
    ext i
    fin_cases i <;> simp [rotateBlocks, smul_eq_mul] <;> ring
  norm_map' := norm_rotateBlocks h₁ h₂
end Eden



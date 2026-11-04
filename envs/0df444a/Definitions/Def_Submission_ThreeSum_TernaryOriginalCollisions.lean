-- Prove2me | Definitions.Def_Submission_ThreeSum_TernaryOriginalCollisions
-- name    : Submission_ThreeSum_TernaryOriginalCollisions
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T07:18:06.264891+00:00
-- url     : https://prove2.me/theorems/cc53855e-dd44-4dc6-9992-0e24fca026b6
-- title:
--   Ternary Original Collisions
-- statement:
--   Definitions and structural lemmas for Ternary Original Collisions, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryOriginalCollisions.lean

import Definitions.Def_Submission_ThreeSum_TernaryOriginalRowMenu
set_option autoImplicit false
noncomputable section
namespace ThreeSum.TernaryOriginalCollisions
open Finset TernaryOriginalRowMenu
open scoped BigOperators
attribute [local instance] Classical.propDecidable
variable {K E B W : Type*} [Field K] [Fintype K] [DecidableEq K]
  [Field E] [Algebra K E] [Fintype E] [DecidableEq E]
  [Fintype B] [DecidableEq B] [DecidableEq W]
def collisionPairs (hash : B → W) : Finset (B × B) :=
  univ.filter fun ab => ab.1 ≠ ab.2 ∧ hash ab.1 = hash ab.2
def deleted (hash : B → W) : Finset B :=
  univ.filter fun a => ∃ b, a ≠ b ∧ hash a = hash b
def nextCollisions {Λ : ℕ} (ℓ : E →ₗ[K] K) (v : B → Fin Λ → K)
    (hash : B → W) (seed : E × E) : ℕ :=
  ((collisionPairs hash).filter fun ab => row Λ ℓ seed (v ab.1) = row Λ ℓ seed (v ab.2)).card
end ThreeSum.TernaryOriginalCollisions



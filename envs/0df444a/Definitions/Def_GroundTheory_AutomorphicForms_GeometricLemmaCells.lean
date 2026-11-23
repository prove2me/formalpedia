-- Prove2me | Definitions.Def_GroundTheory_AutomorphicForms_GeometricLemmaCells
-- name    : GroundTheory_AutomorphicForms_GeometricLemmaCells
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T16:17:31.162426+00:00
-- url     : https://prove2.me/theorems/063c5451-f2ba-4896-b91d-de7272620dfb
-- title:
--   Geometric Lemma Cells
-- statement:
--   Definitions and structural lemmas for Geometric Lemma Cells, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GeometricLemmaCells.lean

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_FiniteBruhat
import Definitions.Def_GroundTheory_AutomorphicForms_InductionParabolicGroups
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
namespace GroundTheory.Automorphic
namespace Parabolic
open Matrix Iwasawa Topology Set DoubleCoset
section Rank
variable {K : Type*} [Field K] {m l : Type*} [Fintype m] [Fintype l] [DecidableEq m]
variable [TopologicalSpace K] [IsTopologicalRing K] [T1Space K]
end Rank
variable {F : Type*} [Field F] {n : ℕ}
section Invariants
variable (β γ : Fin n → ℕ)
def cellRank (g : GL (Fin n) F) (a b : ℕ) : ℕ :=
  ((g : Matrix (Fin n) (Fin n) F).submatrix (fun i : {i : Fin n // a ≤ β i} => (i : Fin n))
    (fun j : {j : Fin n // γ j ≤ b} => (j : Fin n))).rank
variable {β γ}
end Invariants
section Permutations
variable {β γ : Fin n → ℕ}
end Permutations
section Height
variable (β γ : Fin n → ℕ)
def cellHeight (g : GL (Fin n) F) : ℕ :=
  ∑ a ∈ Finset.range (Finset.univ.sup β + 2), ∑ b ∈ Finset.range (Finset.univ.sup γ + 1),
    cellRank β γ g a b
variable {β γ}
variable [TopologicalSpace F] [IsTopologicalRing F] [T1Space F]
end Height
end Parabolic
end GroundTheory.Automorphic



-- Prove2me | Definitions.Def_ReciprocityTheory_GroupCohomology_ReverseA
-- name    : ReciprocityTheory_GroupCohomology_ReverseA
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T16:58:33.289899+00:00
-- url     : https://prove2.me/theorems/0ae955e0-616f-4aa6-bd2d-e84a3ca8dfbc
-- title:
--   Reverse A
-- statement:
--   Definitions and structural lemmas for Reverse A, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GroupCohomology/ReverseA.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.Coh.RevCh
open Finsupp
noncomputable section
abbrev Ch (m : ℕ) (S : Type*) := (Fin (m + 1) → S) →₀ ℤ
variable {S T U : Type*}
def bd (m : ℕ) : Ch (m + 1) S →ₗ[ℤ] Ch m S :=
  linearCombination ℤ fun t => ∑ i : Fin (m + 2), ((-1 : ℤ) ^ (i : ℕ)) • single (t ∘ i.succAbove) (1 : ℤ)
def mp (f : S → T) (m : ℕ) : Ch m S →ₗ[ℤ] Ch m T := lmapDomain ℤ ℤ fun t => f ∘ t
def eps (m : ℕ) : ℤ := (-1) ^ (m * (m + 1) / 2)
def rv (m : ℕ) : Ch m S →ₗ[ℤ] Ch m S := eps m • lmapDomain ℤ ℤ fun t : Fin (m + 1) → S => t ∘ Fin.rev
def cone (v : S) (m : ℕ) : Ch m S →ₗ[ℤ] Ch (m + 1) S :=
  lmapDomain ℤ ℤ fun t : Fin (m + 1) → S => (Fin.cons v t : Fin (m + 2) → S)
def HHof (k : ℕ) (w : Ch (k + 1) (Fin (k + 1))) : Ch k S →ₗ[ℤ] Ch (k + 1) S :=
  linearCombination ℤ fun t => mp t (k + 1) w
def uu : (k : ℕ) → Ch (k + 1) (Fin (k + 1))
  | 0 => 0
  | k + 1 => cone (0 : Fin (k + 2)) (k + 1)
      (rv (k + 1) (single (id : Fin (k + 2) → Fin (k + 2)) 1) - single id 1 -
        HHof k (uu k) (bd k (single (id : Fin (k + 2) → Fin (k + 2)) 1)))
abbrev HH (k : ℕ) : Ch k S →ₗ[ℤ] Ch (k + 1) S := HHof k (uu k)
def Q (k : ℕ) : Prop :=
  bd (k + 1) (uu (k + 1)) + HH k (bd k (single (id : Fin (k + 2) → Fin (k + 2)) 1)) =
    rv (k + 1) (single (id : Fin (k + 2) → Fin (k + 2)) 1) - single id 1
end
end ReciprocityTheory.Coh.RevCh



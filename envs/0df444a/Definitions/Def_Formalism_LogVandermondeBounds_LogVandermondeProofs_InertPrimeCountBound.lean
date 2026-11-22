-- Prove2me | Definitions.Def_Formalism_LogVandermondeBounds_LogVandermondeProofs_InertPrimeCountBound
-- name    : Formalism_LogVandermondeBounds_LogVandermondeProofs_InertPrimeCountBound
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T18:42:37.003506+00:00
-- url     : https://prove2.me/theorems/84ac89be-26c0-4917-82f7-8a39b90a0621
-- title:
--   Inert Prime Count Bound
-- statement:
--   Definitions and structural lemmas for Inert Prime Count Bound, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LogVandermondeBounds/LogVandermondeProofs/InertPrimeCountBound.lean

import Definitions.Def_Formalism_LogVandermondeBounds_LogVandermondeVariationUnbounded
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace Formalism.LogVandermondeBounds.StandardLattice
open Finset
section Inert
variable {L : Type} [Field L] [Fintype L] [DecidableEq L] {q : ℕ}
def Sfix (L : Type) [Field L] [Fintype L] [DecidableEq L] (q : ℕ) : Finset L :=
  univ.filter (fun c : L => c ≠ 0 ∧ c ^ q = c)
def fib (q : ℕ) (d : L) : Finset L := (univ.erase 0).filter (fun u : L => u ^ (q + 1) = d)
def Ncnt (q M : ℕ) (c : L) : ℕ := Fintype.card {x : Fin M → L // ∑ i, x i ^ (q + 1) = c}
def Az (q M : ℕ) : ℤ := (q : ℤ) ^ M * ((q : ℤ) ^ M - (-1) ^ M)
def Zz (q M : ℕ) : ℤ := (q : ℤ) ^ (2 * M) + (-1) ^ M * ((q : ℤ) ^ (M + 1) - (q : ℤ) ^ M)
end Inert
end Formalism.LogVandermondeBounds.StandardLattice



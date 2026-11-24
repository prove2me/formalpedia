-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Lattice
-- name    : GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Lattice
-- status  : Definition
-- author  : @community-bot-5
-- created : 2026-11-24T18:06:06.401905+00:00
-- url     : https://prove2.me/theorems/ae408e2c-f999-413e-a6ca-79aa93fdb917
-- title:
--   Lattice
-- statement:
--   Definitions and structural lemmas for Lattice, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/Lattice.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_AltCoeff
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.RestTerms.Comb
open MvPolynomial Finset Equiv
noncomputable section
open scoped Classical
variable {m : ℕ}
def pcnt {n : ℕ} (w : Fin n → Fin m) (t : ℕ) (i : Fin m) : ℕ :=
  (univ.filter (fun s : Fin n => (s : ℕ) < t ∧ w s = i)).card
def IsLattice {n : ℕ} (w : Fin n → Fin m) : Prop :=
  ∀ t ≤ n, ∀ i j : Fin m, i ≤ j → pcnt w t j ≤ pcnt w t i
def latticeWords (n : ℕ) (lam : Fin m → ℕ) : Finset (Fin n → Fin m) :=
  univ.filter (fun w => IsLattice w ∧ ∀ i, pcnt w n i = lam i)
end
end GroundTheory.Heights₂.Heights.RestTerms.Comb



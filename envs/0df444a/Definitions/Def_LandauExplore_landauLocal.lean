-- Prove2me | Definitions.Def_LandauExplore_landauLocal
-- name    : LandauExplore_landauLocal
-- status  : Definition
-- author  : @pitimespi
-- created : 2026-11-01T00:30:16.092177+00:00
-- url     : https://prove2.me/theorems/47dae953-cd78-4b1c-8569-51d6ca98f89a
-- title:
--   Landau function as a permutation-order supremum
-- statement:
--   For a natural number $n$, $\mathrm{landauLocal}(n)$ is the largest order of any permutation of an $n$-element set, realized as the supremum of $\mathrm{orderOf}(\sigma)$ over all permutations $\sigma$ of $\mathrm{Fin}\, n$. This is the mirror of the platform's Landau function $g(n)$, provided as a standalone definition so that the sup/max bookkeeping for Landau's function can be stated and proved against it.

import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.GCDMonoid.FinsetLemmas
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.GroupTheory.Perm.Cycle.Type
import Mathlib.GroupTheory.Perm.Cycle.PossibleTypes

namespace LandauExplore

/-- Mirror of the platform Landau function: the largest order of a permutation of Fin n, as a Finset sup over all permutations. -/
noncomputable def landauLocal (n : ℕ) : ℕ :=
  Finset.univ.sup (fun σ : Equiv.Perm (Fin n) => orderOf σ)

end LandauExplore



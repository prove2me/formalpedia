-- Prove2me | Definitions.Def_ComplementComponent
-- name    : ComplementComponent
-- status  : Definition
-- author  : @xuanji
-- created : 2026-09-27T23:45:28.805587+00:00
-- url     : https://prove2.me/theorems/4d7034aa-645f-4368-85d0-c9099e9d6e5e
-- title:
--   ComplementComponent
-- statement:
--   A connected component of the complement of a set: a nonempty connected subset of the complement that is maximal among nonempty connected subsets of that complement.
-- source:
--   https://github.com/wpegden/crossing-consequences/blob/8769d142033fce042f502bf2857afb6b1375b5c3/Tablet/ComplementComponent.lean#L1-8

import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Set.Finite.Basic
import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Basic

-- [TABLET NODE: ComplementComponent]
-- Source: https://github.com/wpegden/crossing-consequences/blob/8769d142033fce042f502bf2857afb6b1375b5c3/Tablet/ComplementComponent.lean#L1-8
def ComplementComponent (K F : Set (EuclideanSpace ℝ (Fin 2))) : Prop :=
  F.Nonempty ∧ F ⊆ Kᶜ ∧ IsConnected F ∧
    ∀ C : Set (EuclideanSpace ℝ (Fin 2)),
      C.Nonempty → C ⊆ Kᶜ → IsConnected C → F ⊆ C → C ⊆ F



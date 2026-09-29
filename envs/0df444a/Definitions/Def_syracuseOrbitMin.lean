-- Prove2me | Definitions.Def_syracuseOrbitMin
-- name    : syracuseOrbitMin
-- status  : Definition
-- author  : @mysticflounder
-- created : 2026-09-09T02:50:36.030658+00:00
-- url     : https://prove2.me/theorems/136d2e7b-5229-431a-9aa3-80a9ba5b3611
-- title:
--   Minimum of the forward Syracuse orbit
-- statement:
--   The least value in the full forward Syracuse orbit of n, including the initial value at iterate zero. The orbit is indexed by all natural iteration counts, not a finite cutoff. The natural-number infimum of this nonempty set is attained. The definition is total on natural inputs; Tao's applications restrict the initial input to positive odd integers.
-- source:
--   Terence Tao, Almost all orbits of the Collatz map attain almost bounded values, arXiv:1909.03562v7, Section 1, Syracuse orbit minimum preceding Theorem 1.6; used in Theorem 3.1. https://arxiv.org/html/1909.03562v7

/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under GPL-3.0-or-later as described in the file LICENSE.
Authors: Adam McKenna
-/
import Mathlib.Logic.Function.Iterate
import Mathlib.Order.Lattice.Nat
import Definitions.Def_syracuseStep

noncomputable def syracuseOrbitMin (n : ℕ) : ℕ :=
  sInf (Set.range (fun k : ℕ => syracuseStep^[k] n))



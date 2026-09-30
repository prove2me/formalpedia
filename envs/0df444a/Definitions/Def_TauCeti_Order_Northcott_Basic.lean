-- Prove2me | Definitions.Def_TauCeti_Order_Northcott_Basic
-- name    : TauCeti_Order_Northcott_Basic
-- status  : Definition
-- author  : @riccardo.brasca
-- created : 2026-09-29T19:37:39.662602+00:00
-- url     : https://prove2.me/theorems/d426bff4-09d9-4338-aeaa-8e0ef4951e91
-- title:
--   Finite real-cutoff carriers for Northcott functions
-- statement:
--   Let $N:A\to\mathbb N$ have finite bounded sublevel sets and let $w$ be a weight on $A$. For real $x$, define
--
--   $$
--   A_{\leq x}=\{a\in A:N(a)\leq x\},\qquad W(x)=\sum_{a\in A_{\leq x}}w(a).
--   $$
--
--   These inclusive finite cutoffs provide the common summation convention.
--
--   **Formalization Note.** These foundational declarations are transplanted from the Tau Ceti contributors' [original source](https://github.com/TauCetiProject/TauCeti/blob/948fe4751b1fe528b6d580c522ca5d743d47f185/TauCeti/Order/Northcott/Basic.lean) (Apache-2.0, commit `948fe4751b1fe528b6d580c522ca5d743d47f185`), with compatibility adaptations for Lean 4.33.1. Mathematical proofs requiring separate theorem nodes are published separately.
-- source:
--   https://github.com/TauCetiProject/TauCeti/blob/948fe4751b1fe528b6d580c522ca5d743d47f185/TauCeti/Order/Northcott/Basic.lean

/- Transplanted from https://github.com/TauCetiProject/TauCeti at 948fe4751b1fe528b6d580c522ca5d743d47f185.
Original source copyright/license notices are retained below.
Generated exclusively from compiler declaration, command, and reference facts. -/
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Data.Set.Card
import Mathlib.Order.Filter.AtTopBot.Finset
import Mathlib.Order.Northcott
import Mathlib.Topology.Algebra.Order.Floor
import Mathlib.Topology.UniformSpace.Real

section
set_option autoImplicit true
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
/-!
# Finite real-cutoff carriers for Northcott functions

This file packages the finite carrier selected by a real cutoff for a natural-valued Northcott
function, together with generic summatory functions over that carrier. The carrier depends only
on the integer part of the cutoff, and for a nonnegative cutoff it agrees with the one selected by
its natural floor.
-/

 section

namespace TauCeti

open Filter
open scoped Topology

variable {ι : Type*} (N : ι → ℕ) [Northcott N]

/-- Only finitely many indices have `N`-value at most a fixed real number, because the `N`-value
is a natural number and `N` is Northcott. -/
theorem finite_setOf_natCast_le (x : ℝ) : {i : ι | (N i : ℝ) ≤ x}.Finite :=
  (Northcott.finite_le (h := N) ⌊x⌋₊).subset fun _ hi ↦ Nat.le_floor hi

/-- The finite set of indices whose `N`-value is at most the real cutoff `x`. The cutoff is
inclusive: an index with `N i = x` belongs to `normLE N x`. -/
 noncomputable def normLE (x : ℝ) : Finset ι :=
  (finite_setOf_natCast_le N x).toFinset



















/-! ### Generic summatory functions -/

/-- The inclusive summatory function of a weight `w`: the sum of `w` over all indices of
`N`-value at most `x`. -/
 noncomputable def summatory {M : Type*} [AddCommMonoid M]
    (w : ι → M) (x : ℝ) : M :=
  ∑ i ∈ normLE N x, w i































end TauCeti

end
end



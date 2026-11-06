-- Prove2me | Definitions.Def_MethodFulfillment_Run
-- name    : MethodFulfillment_Run
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T20:10:07.534208+00:00
-- url     : https://prove2.me/theorems/d19088da-8cdc-4950-b1fb-86db6c5a7aa2
-- title:
--   One period and one run of the online process of Algorithm 1
-- statement:
--   A **step** of the online process records three things for one period: the arrival (an order type, or none), the method $m$ drawn in step 1 of Algorithm 1, and the set $A$ of item–facility pairs that the method-acceptance strategy makes available in step 2. The pairs actually used are $m\cap A$: the method is accepted when $m\subseteq A$, and otherwise the submethod $m\cap A\subsetneq m$ is used and the other items of the order are served from the dummy facility. A **run** is one step per period of the horizon.
-- source:
--   Amil, Makhdoumi & Wei, Multi-Item Order Fulfillment Revisited: LP Formulation and Prophet Inequality, manuscript (PDF sha256 197c13b9…), Algorithm 1, p.13

import Mathlib

namespace MethodFulfillment

/-- One period of the online process of Algorithm 1 (Amil, Makhdoumi & Wei, manuscript, PDF
sha256 197c13b9…, Algorithm 1, p.13): the arrival (`none` if no order arrives), the method `m`
drawn in step 1, and the set `A` of (item, facility) pairs made available by the
method-acceptance strategy in step 2. The pairs used in the period are `m ∩ A`; the method is
accepted when `m ⊆ A`, and otherwise the submethod `m ∩ A ⊊ m` is used, its remaining items being
served from the dummy facility. -/
abbrev Step (I K Q : Type) : Type :=
  Option Q × Finset (I × K) × Finset (I × K)

/-- A run of the online process over the horizon: one `Step` per (0-based) period. -/
abbrev Run (I K Q : Type) (T : ℕ) : Type :=
  Fin T → Step I K Q

end MethodFulfillment



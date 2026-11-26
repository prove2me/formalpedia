-- Prove2me | Definitions.Def_CollatzEndpointTransport_Linear_FixedTotalCriticalMoment
-- name    : CollatzEndpointTransport_Linear_FixedTotalCriticalMoment
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T08:23:46.6496+00:00
-- url     : https://prove2.me/theorems/02e843af-1a05-5786-8996-fd5d238e4900
-- title:
--   Fixed Total Critical Moment
-- statement:
--   Definitions and structural lemmas for Fixed Total Critical Moment, from Idris Ali Shaik (shaikidris/CollatzEndpointTransport-Palomar; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Refined arbitrary-target transport through Collatz endpoints development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/FixedTotalCriticalMoment.lean

import Definitions.Def_CollatzEndpointTransport_Linear_FixedTotalQuotientOrder
import Definitions.Def_CollatzEndpointTransport_Linear_FixedTotalFirstMoment
import Mathlib.Algebra.Order.Chebyshev
set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace CollatzEndpointTransport
namespace FixedTotal
open Nat Finset
noncomputable section
local instance compositionDecidableEq (N : ℕ) :
    DecidableEq (Composition N) :=
  Classical.decEq _
def fixedSet (N s : ℕ) : Finset (Composition N) :=
  (Finset.univ : Finset (Composition N)).filter fun c => c.length = s
def fixedFiberCard (N s : ℕ) (a : Fin (3 ^ s)) : ℕ :=
  (residueFiber (fixedSet N s) syracuseNumerator (3 ^ s) a).card
def fixedCriticalNumerator (N s : ℕ) : ℝ :=
  Real.sqrt (3 ^ s) *
    ∑ a : Fin (3 ^ s),
      (fixedFiberCard N s a : ℝ) * Real.sqrt (fixedFiberCard N s a)
def fixedCriticalContribution (N s : ℕ) : ℝ :=
  fixedCriticalNumerator N s / Real.sqrt (fixedSet N s).card
def fixedCriticalAverage (N : ℕ) : ℝ :=
  (∑ s ∈ Finset.Icc 1 N, fixedCriticalContribution N s) /
    (2 ^ (N - 1) : ℝ)
end
end FixedTotal
end CollatzEndpointTransport



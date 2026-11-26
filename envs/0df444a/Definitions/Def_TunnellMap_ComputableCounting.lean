-- Prove2me | Definitions.Def_TunnellMap_ComputableCounting
-- name    : TunnellMap_ComputableCounting
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T16:06:03.864638+00:00
-- url     : https://prove2.me/theorems/33c8a222-6296-47d3-92dc-6cd94d3dd50d
-- title:
--   Computable Counting
-- statement:
--   Definitions and structural lemmas for Computable Counting, from Aakash Gurung (GrgAakash/tunnell-two-to-one-map; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Two-to-one executable map between Tunnell representation sets development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/ComputableCounting.lean

import Definitions.Def_TunnellMap_ComputableTargetRoster
set_option autoImplicit true
namespace TunnellMap
instance bRepDecidableEq (n : ℤ) : DecidableEq (BRep n) :=
  inferInstanceAs (DecidableEq {p : Triple // bForm p = n})
instance bOddRepDecidableEq (n : ℤ) : DecidableEq (BOddRep n) :=
  inferInstanceAs (DecidableEq {p : Triple // bForm p = n ∧ Odd p.z})
instance bResidualDecidableEq' (n : ℤ) : DecidableEq (BResidual n) :=
  inferInstanceAs (DecidableEq {p : BOddRep n // ¬ DirectSourceUsed p})
def bRepList (n : ℤ) : List (BRep n) :=
  (sourceTriples n).filterMap fun w => if h : bForm w = n then some ⟨w, h⟩ else none
def aRepList (n : ℤ) : List (ARep n) :=
  (targetTriples n).filterMap fun w => if h : aForm w = n then some ⟨w, h⟩ else none
def bEvenTriples (n : ℤ) : List Triple :=
  (sourceTriples n).filter fun w => !decide (Odd w.z)
def bDirectTriples (n : ℤ) : List Triple :=
  (sourceTriples n).filter fun w => decide (Odd w.z) && decide (SourceUsedTriple w)
def bResidualTriples (n : ℤ) : List Triple :=
  (sourceTriples n).filter fun w => decide (Odd w.z) && !decide (SourceUsedTriple w)
def aDirectTriples (n : ℤ) : List Triple :=
  (targetTriples n).filter fun w => decide (ImageUsedTriple w)
def aResidualTriples (n : ℤ) : List Triple :=
  (targetTriples n).filter fun w => !decide (ImageUsedTriple w)
end TunnellMap



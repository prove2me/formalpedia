-- Prove2me | Definitions.Def_MatchingDual
-- name    : MatchingDual
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T08:44:10.131245+00:00
-- url     : https://prove2.me/theorems/bdfde166-a271-4135-8880-ac598becf8c6
-- title:
--   MatchingDual definitions
-- statement:
--   Weak duality and optimality certificates for finite weighted matching.
--
--   [Original Lean source](https://github.com/CrocSwap/integer-mult-bounds/blob/7c49fe32c55de02c2c873655c804b16e4c3fef0a/research/matrix-exponent-synthesis/MatchingDual.lean). Imported from CrocSwap/integer-mult-bounds at `7c49fe32c55d`. Original work by Alejandro Zarzuelo Urdiales, with the assistance and predecessor credits recorded in the source provenance. [Attribution notice](https://github.com/CrocSwap/integer-mult-bounds/blob/7c49fe32c55de02c2c873655c804b16e4c3fef0a/NOTICE). Apache-2.0. Imported by marwahaha using lean-splitter.
-- source:
--   https://github.com/CrocSwap/integer-mult-bounds/blob/7c49fe32c55de02c2c873655c804b16e4c3fef0a/research/matrix-exponent-synthesis/MatchingDual.lean | Apache-2.0 | CrocSwap contributors; see pinned NOTICE | lean-splitter import, independently validated on Hetzner

import Std
set_option autoImplicit true
namespace MatrixMatchingDual
structure Edge where
  cost : Int
  rowPrice : Int
  columnPrice : Int
def costSum (edges : List Edge) : Int := (edges.map Edge.cost).sum
def rowSum (edges : List Edge) : Int := (edges.map Edge.rowPrice).sum
def selectedSum (edges : List Edge) : Int := (edges.map Edge.columnPrice).sum
end MatrixMatchingDual



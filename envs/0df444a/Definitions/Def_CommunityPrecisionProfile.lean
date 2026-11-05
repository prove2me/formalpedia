-- Prove2me | Definitions.Def_CommunityPrecisionProfile
-- name    : CommunityPrecisionProfile
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T08:44:10.131245+00:00
-- url     : https://prove2.me/theorems/939c9849-58f0-4d36-9579-aba614fd3485
-- title:
--   CommunityPrecisionProfile definitions
-- statement:
--   Precision accounting for arbitrary finite profiles of Gaussian-integer operations.
--
--   [Original Lean source](https://github.com/CrocSwap/integer-mult-bounds/blob/7c49fe32c55de02c2c873655c804b16e4c3fef0a/research/gaussian-parity-synthesis/CommunityPrecisionProfile.lean). Imported from CrocSwap/integer-mult-bounds at `7c49fe32c55d`. Original work by Alejandro Zarzuelo Urdiales, with the assistance and predecessor credits recorded in the source provenance. [Attribution notice](https://github.com/CrocSwap/integer-mult-bounds/blob/7c49fe32c55de02c2c873655c804b16e4c3fef0a/NOTICE). Apache-2.0. Imported by marwahaha using lean-splitter.
-- source:
--   https://github.com/CrocSwap/integer-mult-bounds/blob/7c49fe32c55de02c2c873655c804b16e4c3fef0a/research/gaussian-parity-synthesis/CommunityPrecisionProfile.lean | Apache-2.0 | CrocSwap contributors; see pinned NOTICE | lean-splitter import, independently validated on Hetzner

import Std
set_option autoImplicit true
namespace CommunityPrecision
def ceilHalf (n : Nat) : Nat := (n+1)/2
def profile : List (Nat × Nat) :=
  [(1,540572760), (2,336785904), (3,161899920), (4,117097344),
   (5,93051504), (6,64779624), (7,52822224), (8,70243992),
   (9,32150664), (10,50699376), (11,22728888), (12,47580624),
   (13,26208000), (14,44907408), (15,24714144), (16,49192416),
   (17,20815704), (18,52501176), (19,22624056), (20,46348848),
   (21,37759176), (22,58961448), (23,40773096), (24,38781288),
   (25,2208024), (26,3741192), (27,43112160),
   (729,21464352), (756,516232080)]
def rankMass (xs : List (Nat × Nat)) : Nat :=
  (xs.map fun x => x.1*x.2).sum
def precisionCharge (xs : List (Nat × Nat)) (f : Nat) : Nat :=
  (xs.map fun x => ceilHalf (x.1*f)*x.2).sum
def oddMultiplicity (xs : List (Nat × Nat)) : Nat :=
  (xs.map fun x => (x.1%2)*x.2).sum
end CommunityPrecision



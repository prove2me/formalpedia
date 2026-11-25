-- Prove2me | Definitions.Def_proofs_OptimalAffinity_SourceBridge
-- name    : proofs_OptimalAffinity_SourceBridge
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-25T21:02:46.614801+00:00
-- url     : https://prove2.me/theorems/72d33e2c-9206-549d-93ce-897be5c63cb2
-- title:
--   Source Bridge
-- statement:
--   Definitions and structural lemmas for Source Bridge, from mmislan (mmislan/palomar-p004-optimal-affinity-counterexample; see pinned Apache-2.0 LICENSE and README.md)'s pinned A two-reaction counterexample to the gross-amplification affinity bound development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/mmislan/palomar-p004-optimal-affinity-counterexample/blob/50199f4bc2999fb43a0486dcb7571f9dfd333ff2/proofs/OptimalAffinity/SourceBridge.lean

module
public import Definitions.Def_proofs_OptimalAffinity_Affinity
set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace OptimalAffinity
noncomputable section
def reactantDet (N : Network) : ℤ :=
  (N.xReactant 0 : ℤ) * (N.yReactant 1 : ℤ) -
    (N.xReactant 1 : ℤ) * (N.yReactant 0 : ℤ)
def stationaryY (x : ℝ) : ℝ :=
  (6*x^2 - 2 + Real.sqrt ((6*x^2 - 2)^2 + 84*x)) / 14
end
end OptimalAffinity



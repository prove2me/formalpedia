-- Prove2me | Definitions.Def_Submission_ThreeSum_Histograms
-- name    : Submission_ThreeSum_Histograms
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T07:09:39.444199+00:00
-- url     : https://prove2.me/theorems/2ea708ca-15b5-42aa-8091-6a3572f286e8
-- title:
--   Histograms
-- statement:
--   Definitions and structural lemmas for Histograms, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/Histograms.lean

import Definitions.Def_Submission_ThreeSum_Balancing
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Finset.Prod
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Abel
set_option autoImplicit false
namespace ThreeSum.Histograms
open Finset
open scoped BigOperators
variable {ι τ ν G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
def histogram (I : Finset ι) (key : ι → G) (weight : ι → ℕ) (k : G) : ℕ :=
  ∑ i ∈ I, if key i = k then weight i else 0
def pairMass (I : Finset ι) (J : Finset τ) (left : ι → G) (right : τ → G)
    (weightL : ι → ℕ) (weightR : τ → ℕ) (d : G) : ℕ :=
  ∑ i ∈ I, ∑ j ∈ J, if right j - left i = d then weightL i * weightR j else 0
def tripleMass (A : Finset ι) (B : Finset τ) (C : Finset ν)
    (a : ι → G) (b : τ → G) (c : ν → G)
    (wa : ι → ℕ) (wb : τ → ℕ) (wc : ν → ℕ) : ℕ :=
  ∑ i ∈ A, ∑ j ∈ B, ∑ k ∈ C,
    if a i + b j = c k then wa i * wb j * wc k else 0
end ThreeSum.Histograms



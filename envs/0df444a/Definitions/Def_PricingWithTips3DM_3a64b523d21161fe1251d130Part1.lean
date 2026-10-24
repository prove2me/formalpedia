-- Prove2me | Definitions.Def_PricingWithTips3DM_3a64b523d21161fe1251d130Part1
-- name    : PricingWithTips3DM_3a64b523d21161fe1251d130Part1
-- status  : Definition
-- author  : @qmaai2907271020
-- created : 2026-10-23T06:31:56.307979+00:00
-- url     : https://prove2.me/theorems/de6ea285-98b8-4ca2-885a-952eeb3dbda3
-- title:
--   PricingWithTips 3DM dependency: Scratch_PricingWithTips_FixedShape3DM.Part1
-- statement:
--   A private, kernel-checked dependency module used by the formal NP-hardness proof for three-dimensional matching and Theorems 4.1 and 4.2 of arXiv:2507.10872.
-- source:
--   https://arxiv.org/abs/2507.10872

import Definitions.Def_PricingWithTips3DM_36f8af72b5600c8711e12fba
import Definitions.Def_PricingWithTips3DM_df394fdb8c18e941ef8d63ad
import Definitions.Def_PricingWithTips3DM_e7e44ed57595d80dbeb263ea
import Definitions.Def_PricingWithTips3DM_3b6a88d9be5918e3cb96dca9
import Theorems.Thm_PricingWithTips_finset3DM_iff_allocation3DM
import Definitions.Def_PricingWithTips3DM_b96f43df0f03fac823d4c3fd
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false

/-!
A fixed-shape variant of the Garey--Johnson SAT-to-3DM gadget.

For a raw CLRS 3-CNF word of length `L`, we use exactly the variables
`0, ..., L-1` and pad the decoded formula to exactly `L` clauses with a
tautology.  Thus every loop bound and the final 3DM dimension are fixed
polynomials in `L`; neither variable deduplication nor a data-dependent clause
count remains in the target encoder.
-/

namespace PricingWithTips.FixedShape3DM

open Hardness Hardness.Cert Hardness.Sat3dm

abbrev CNF := Hardness.CNF ℕ

def baseCNF (input : List CLRS.Chapter34.CNFSym) : CNF :=
  Hardness.Cert.decodeCNF (CLRS3CNFBridge.guardedCertCNF input)

def tautClause : Hardness.Clause ℕ :=
  [⟨0, true⟩, ⟨0, false⟩]

def paddedCNF (input : List CLRS.Chapter34.CNFSym) : CNF :=
  baseCNF input ++ List.replicate (input.length - (baseCNF input).length) tautClause

def variableList (input : List CLRS.Chapter34.CNFSym) : List ℕ :=
  List.range input.length

theorem baseCNF_length_le (input : List CLRS.Chapter34.CNFSym) :
    (baseCNF input).length ≤ input.length := by
  by_cases h : CLRS.Chapter34.isThreeCNFBool
      (CLRS.Chapter34.decodeCNF input) = true
  · have hlen : (baseCNF input).length =
        (CLRS.Chapter34.decodeCNF input).length := by
      simp [baseCNF, CLRS3CNFBridge.guardedCertCNF, h,
        Hardness.Cert.length_decodeCNF, CLRS3CNFBridge.certCNF]
    rw [hlen]
    have hs := CLRS.Chapter34.decodeCNF_storedSize_le input
    omega
  · have hpos : 0 < input.length := by
      cases input with
      | nil => simp [CLRS.Chapter34.isThreeCNFBool,
          CLRS.Chapter34.decodeCNF] at h
      | cons a as => simp
    simp [baseCNF, CLRS3CNFBridge.guardedCertCNF, h,
      Hardness.Cert.length_decodeCNF]
    exact hpos

theorem paddedCNF_length (input : List CLRS.Chapter34.CNFSym) :
    (paddedCNF input).length = input.length := by
  simp [paddedCNF, baseCNF_length_le]
end PricingWithTips.FixedShape3DM



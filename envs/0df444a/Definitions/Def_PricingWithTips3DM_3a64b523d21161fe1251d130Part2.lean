-- Prove2me | Definitions.Def_PricingWithTips3DM_3a64b523d21161fe1251d130Part2
-- name    : PricingWithTips3DM_3a64b523d21161fe1251d130Part2
-- status  : Definition
-- author  : @qmaai2907271020
-- created : 2026-10-23T06:39:21.442336+00:00
-- url     : https://prove2.me/theorems/7104fca3-7df2-4a62-b2ab-8b6ef11313ce
-- title:
--   PricingWithTips 3DM dependency: Scratch_PricingWithTips_FixedShape3DM.Part2
-- statement:
--   A private, kernel-checked dependency module used by the formal NP-hardness proof for three-dimensional matching and Theorems 4.1 and 4.2 of arXiv:2507.10872.
-- source:
--   https://arxiv.org/abs/2507.10872

import Definitions.Def_PricingWithTips3DM_3a64b523d21161fe1251d130Part1
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false

namespace PricingWithTips.FixedShape3DM

open Hardness Hardness.Cert Hardness.Sat3dm

theorem tautClause_sat (σ : ℕ → Bool) :
    Hardness.Clause.Sat σ tautClause := by
  cases h : σ 0 <;> simp [tautClause, Hardness.Clause.Sat,
    Hardness.Literal.Holds, h]

theorem paddedCNF_satisfiable_iff (input : List CLRS.Chapter34.CNFSym) :
    (paddedCNF input).Satisfiable ↔ (baseCNF input).Satisfiable := by
  constructor
  · rintro ⟨σ, hσ⟩
    exact ⟨σ, fun c hc => hσ c (List.mem_append_left _ hc)⟩
  · rintro ⟨σ, hσ⟩
    refine ⟨σ, ?_⟩
    intro c hc
    rw [paddedCNF, List.mem_append] at hc
    rcases hc with hc | hc
    · exact hσ c hc
    · have : c = tautClause := by
        simpa using (List.eq_of_mem_replicate hc)
      simpa [this] using tautClause_sat σ

theorem threeCNFSat_iff_paddedCNF (input : List CLRS.Chapter34.CNFSym) :
    input ∈ CLRS.Chapter34.ThreeCNFSat ↔ (paddedCNF input).Satisfiable := by
  rw [paddedCNF_satisfiable_iff]
  exact CLRS3CNFBridge.threeCNFSat_iff_guardedCertSAT input
end PricingWithTips.FixedShape3DM



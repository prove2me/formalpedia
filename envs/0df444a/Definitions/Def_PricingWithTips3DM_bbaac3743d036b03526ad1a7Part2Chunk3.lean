-- Prove2me | Definitions.Def_PricingWithTips3DM_bbaac3743d036b03526ad1a7Part2Chunk3
-- name    : PricingWithTips3DM_bbaac3743d036b03526ad1a7Part2Chunk3
-- status  : Definition
-- author  : @qmaai2907271020
-- created : 2026-10-22T22:10:05.127073+00:00
-- url     : https://prove2.me/theorems/2c590da8-86f0-4042-a1e1-cf91dd6f94d9
-- title:
--   PricingWithTips 3DM dependency: CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorValidityRowTailSource.Part2.Chunk3
-- statement:
--   A private, kernel-checked dependency module used by the formal NP-hardness proof for three-dimensional matching and Theorems 4.1 and 4.2 of arXiv:2507.10872.
-- source:
--   https://github.com/tanktechnology/CLRS-Lean

import Definitions.Def_PricingWithTips3DM_bbaac3743d036b03526ad1a7Part2Chunk2
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CLRS.Chapter34.Turing.CookLevin

open PolyBuilder

/-- The compact one-hot invocation payload never contains the outer row
boundary symbol. -/
theorem affineExactlyOneOutputInvocationFamily_no_frameEnd
    (frames : List AffineExactlyOneFrame) :
    ∀ symbol ∈ encodeAffineExactlyOneOutputSourceInvocationFamily frames,
      symbol ≠ UnaryFrameSym.frameEnd := by
  intro symbol hsymbol
  rw [encodeAffineExactlyOneOutputSourceInvocationFamily,
    List.mem_flatMap] at hsymbol
  rcases hsymbol with ⟨frame, hframe, hsymbol⟩
  rw [encodeAffineExactlyOneOutputSourceInvocation, encodeUnaryFrame,
    List.mem_flatMap] at hsymbol
  rcases hsymbol with ⟨value, hvalue, hsymbol⟩
  simp [encodeUnaryFrameBlock] at hsymbol
  rcases hsymbol with ⟨_, rfl⟩ | rfl <;> simp
end CLRS.Chapter34.Turing.CookLevin



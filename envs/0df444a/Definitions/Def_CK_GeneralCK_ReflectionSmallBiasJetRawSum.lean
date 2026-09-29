-- Prove2me | Definitions.Def_CK_GeneralCK_ReflectionSmallBiasJetRawSum
-- name    : CK_GeneralCK_ReflectionSmallBiasJetRawSum
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-28T16:09:21.834439+00:00
-- url     : https://prove2.me/theorems/4b0b1dac-058d-457f-bab3-1ad2e77d0b10
-- title:
--   Courtade–Kumar proof module `GeneralCK.ReflectionSmallBiasJetRawSum` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.ReflectionSmallBiasJetRawSum` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.ReflectionSmallBiasJetRawSum` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.ReflectionSmallBiasJetRawSum (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/ReflectionSmallBiasJetRawSum.lean)

import Definitions.Def_CK_GeneralCK_ReflectionSmallBiasJetReplay

-- ===== source module GeneralCK.ReflectionSmallBiasJetRawSum =====
section

/-! Append finite Taylor sums without repeatedly normalizing intermediate lists. -/

namespace GeneralCK.Reflection.SmallBiasJet.Approximates

open SmallBiasPolynomial

theorem addAppend {n : ℕ} {k : ℂ} {f g : ℂ × ℂ → ℂ} {p q : List Term}
    (hf : Approximates n k f p) (hg : Approximates n k g q) :
    Approximates n k (fun z => f z + g z) (p ++ q) := by
  refine ⟨hf.analytic.add hg.analytic, ?_⟩
  apply (hf.error.add hg.error).congr_left
  intro z
  rw [eval_append]
  ring

end GeneralCK.Reflection.SmallBiasJet.Approximates


end



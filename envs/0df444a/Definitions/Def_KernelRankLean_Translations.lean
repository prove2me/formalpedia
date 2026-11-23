-- Prove2me | Definitions.Def_KernelRankLean_Translations
-- name    : KernelRankLean_Translations
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-23T01:49:20.5828+00:00
-- url     : https://prove2.me/theorems/86c63ab4-3d47-4cc2-884d-9348f1c8707c
-- title:
--   Translations
-- statement:
--   Definitions and structural lemmas for Translations, from Olli Niemitalo's pinned Finite separable rank of radial kernels development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/OlliNiemitalo/kernel-rank-lean/blob/a406bf6714fea09066eb0ef896d01df205145675/KernelRankLean/Translations.lean

import Definitions.Def_KernelRankLean_RowSpan
set_option autoImplicit true
open NNReal
namespace KernelRank
def translateSpan {𝕜 : Type*} [Field 𝕜] (φ : ℝ → 𝕜) : Submodule 𝕜 (ℝ≥0 → 𝕜) :=
  Submodule.span 𝕜 (Set.range fun (t : ℝ≥0) (u : ℝ≥0) => φ (u + t))
end KernelRank



-- Prove2me | Definitions.Def_KernelRankLean_RowSpan
-- name    : KernelRankLean_RowSpan
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-23T01:48:26.624866+00:00
-- url     : https://prove2.me/theorems/7f294ae7-3401-4549-ab50-84ca58f2a453
-- title:
--   Row Span
-- statement:
--   Definitions and structural lemmas for Row Span, from Olli Niemitalo's pinned Finite separable rank of radial kernels development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/OlliNiemitalo/kernel-rank-lean/blob/a406bf6714fea09066eb0ef896d01df205145675/KernelRankLean/RowSpan.lean

import Definitions.Def_KernelRankLean_Defs
set_option autoImplicit true
namespace KernelRank
variable {𝕜 α : Type*}
def fin2Vec (x y : α) : Fin 2 → α
  | 0 => x
  | 1 => y
variable [Field 𝕜]
def rowSpan (K : (Fin 2 → α) → 𝕜) : Submodule 𝕜 (α → 𝕜) :=
  Submodule.span 𝕜 (Set.range fun (y : α) (x : α) => K (fin2Vec x y))
end KernelRank



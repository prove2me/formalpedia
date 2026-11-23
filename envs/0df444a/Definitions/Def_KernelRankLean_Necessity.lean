-- Prove2me | Definitions.Def_KernelRankLean_Necessity
-- name    : KernelRankLean_Necessity
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-23T02:05:27.317306+00:00
-- url     : https://prove2.me/theorems/d804478c-f1d1-4d6d-bf09-eff0b3ab0708
-- title:
--   Necessity
-- statement:
--   Definitions and structural lemmas for Necessity, from Olli Niemitalo's pinned Finite separable rank of radial kernels development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/OlliNiemitalo/kernel-rank-lean/blob/a406bf6714fea09066eb0ef896d01df205145675/KernelRankLean/Necessity.lean

import Definitions.Def_KernelRankLean_TranslationSemigroup
import Definitions.Def_KernelRankLean_Representation
set_option autoImplicit true
open Complex Polynomial NNReal
namespace KernelRank
attribute [local instance] translateNormedAddCommGroup translateNormedSpace
  translateUniformSpace translateCompleteSpace
section Exp
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
end Exp
end KernelRank



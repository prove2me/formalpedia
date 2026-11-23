-- Prove2me | Definitions.Def_Experiments_Translation
-- name    : Experiments_Translation
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-23T02:05:46.599934+00:00
-- url     : https://prove2.me/theorems/b9cdb830-be89-409c-bbd7-195993e0ed81
-- title:
--   Translation
-- statement:
--   Definitions and structural lemmas for Translation, from Olli Niemitalo's pinned Finite separable rank of radial kernels development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/OlliNiemitalo/kernel-rank-lean/blob/a406bf6714fea09066eb0ef896d01df205145675/Experiments/Translation.lean

import Definitions.Def_Experiments_FiniteDifferenceSemigroup
import Definitions.Def_Experiments_NonstandardSemigroup
import Definitions.Def_KernelRankLean_TranslationSemigroup
set_option autoImplicit true
namespace Experiments
open KernelRank
attribute [local instance] translateNormedAddCommGroup translateNormedSpace
  translateUniformSpace translateCompleteSpace
end Experiments



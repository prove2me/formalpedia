-- Prove2me | Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_ZBrauerNesbittAlg
-- name    : Formalism_PadicSubsetSums_StableGradedCounts_ZBrauerNesbittAlg
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T18:15:58.252068+00:00
-- url     : https://prove2.me/theorems/f23544f2-afea-4d5e-8f5c-9d7a5f0258d6
-- title:
--   ZBrauer Nesbitt Alg
-- statement:
--   Definitions and structural lemmas for ZBrauer Nesbitt Alg, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PadicSubsetSums/StableGradedCounts/ZBrauerNesbittAlg.lean

import Definitions.Def_Formalism_PadicSubsetSums_CentralIdempotents_PrimitiveRootFifteenSubOneUnit
import Definitions.Def_Lemmata_GeneralBFactSecondVersion_Imports
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Polynomial
namespace Formalism.IrreducibleCountingLemmas.Z.BN
def cp (k : Type) {A : Type} (V : Type) [Field k] [Ring A] [Algebra k A] [AddCommGroup V]
    [Module k V] [Module A V] [IsScalarTower k A V] [FiniteDimensional k V] (a : A) : k[X] :=
  (Algebra.lsmul k k V a).charpoly
section
variable {k A : Type} [Field k] [Ring A] [Algebra k A]
variable {V W S : Type} [AddCommGroup V] [Module k V] [Module A V] [IsScalarTower k A V]
  [AddCommGroup W] [Module k W] [Module A W] [IsScalarTower k A W]
  [AddCommGroup S] [Module A S]
instance (N : Submodule A V) [FiniteDimensional k V] : FiniteDimensional k N :=
  Module.Finite.of_injective (N.subtype.restrictScalars k) N.subtype_injective
instance (N : Submodule A V) [FiniteDimensional k V] : FiniteDimensional k (V ⧸ N) :=
  Module.Finite.of_surjective (N.mkQ.restrictScalars k) N.mkQ_surjective
end
end Formalism.IrreducibleCountingLemmas.Z.BN
namespace Formalism.IrreducibleCountingLemmas.Z
end Formalism.IrreducibleCountingLemmas.Z



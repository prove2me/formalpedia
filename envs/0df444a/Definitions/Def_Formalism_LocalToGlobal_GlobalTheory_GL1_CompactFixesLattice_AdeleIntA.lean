-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_GlobalTheory_GL1_CompactFixesLattice_AdeleIntA
-- name    : Formalism_LocalToGlobal_GlobalTheory_GL1_CompactFixesLattice_AdeleIntA
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T01:27:21.500698+00:00
-- url     : https://prove2.me/theorems/d64fc94c-2fe9-48d4-bcfd-ea51d4f352a2
-- title:
--   Adele Int A
-- statement:
--   Definitions and structural lemmas for Adele Int A, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/GlobalTheory/GL1/CompactFixesLattice/AdeleIntA.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace Formalism.L2.GlobalTheoryTheory.FiltrationBoundaryCriterion.CompactFixesLatticeTheory.AdeleIntA
open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
variable {R : Type*} [CommRing R] [IsDedekindDomain R] {K : Type*} [Field K] [Algebra R K]
  [IsFractionRing R K]
def IsInt (b : FiniteAdeleRing R K) : Prop := ∀ v, b v ∈ v.adicCompletionIntegers K
end Formalism.L2.GlobalTheoryTheory.FiltrationBoundaryCriterion.CompactFixesLatticeTheory.AdeleIntA



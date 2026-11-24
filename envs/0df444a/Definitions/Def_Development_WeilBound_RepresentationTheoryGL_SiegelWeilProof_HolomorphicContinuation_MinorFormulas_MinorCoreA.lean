-- Prove2me | Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MinorFormulas_MinorCoreA
-- name    : Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MinorFormulas_MinorCoreA
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:03:59.52206+00:00
-- url     : https://prove2.me/theorems/8890d4b9-4c41-4fb2-a415-5bdb35c5b785
-- title:
--   Minor Core A
-- statement:
--   Definitions and structural lemmas for Minor Core A, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/MinorFormulas/MinorCoreA.lean

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MinorFormulas_MinorB
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial Matrix
namespace PositivityTheory.Rg.Sw.SP.Mi
variable {R : Type} [CommRing R]
def gens (α : R) (ρ : ℕ) : Set (Module.End R (Pm R ρ)) := Set.range fun pq : Fin ρ × Fin ρ => opE α pq.1 pq.2
end PositivityTheory.Rg.Sw.SP.Mi



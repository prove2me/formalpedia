-- Prove2me | Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MinorFormulas_MinorCore
-- name    : Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MinorFormulas_MinorCore
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:14:45.288802+00:00
-- url     : https://prove2.me/theorems/3ec6b44b-d7ee-4eb5-8621-62e0b1638c79
-- title:
--   Minor Core
-- statement:
--   Definitions and structural lemmas for Minor Core, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/MinorFormulas/MinorCore.lean

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MinorFormulas_MinorCoreA
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
def Aop (α : R) (ρ : ℕ) : Matrix (Fin ρ) (Fin ρ) (Algebra.adjoin R (gens α ρ)) :=
  fun p q => ⟨opE α p q, Algebra.subset_adjoin ⟨(p, q), rfl⟩⟩
end PositivityTheory.Rg.Sw.SP.Mi



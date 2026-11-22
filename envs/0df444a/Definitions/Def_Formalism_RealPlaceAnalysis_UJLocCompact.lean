-- Prove2me | Definitions.Def_Formalism_RealPlaceAnalysis_UJLocCompact
-- name    : Formalism_RealPlaceAnalysis_UJLocCompact
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T16:48:09.880746+00:00
-- url     : https://prove2.me/theorems/443c77e5-245e-486c-b993-3e1bb917e634
-- title:
--   UJLoc Compact
-- statement:
--   Definitions and structural lemmas for UJLoc Compact, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RealPlaceAnalysis/UJLocCompact.lean

import Definitions.Def_Formalism_RealPlaceAnalysis_Complexify
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace Formalism.REAL
def UJEmb : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool),
    Topology.IsClosedEmbedding (fun g : UJ ε => ((g : (Matrix (Fin n) (Fin n) ℂ)ˣ) :
      Matrix (Fin n) (Fin n) ℂ)) ∧
    Set.range (fun g : UJ ε => ((g : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ)) =
      {g | inUJ ε g}
def UJLocCompact : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool), LocallyCompactSpace (UJ ε)
end Formalism.REAL



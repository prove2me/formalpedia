-- Prove2me | Definitions.Def_Formalism_SubspaceCounting_SubspaceCountingProofs_LengthLayers
-- name    : Formalism_SubspaceCounting_SubspaceCountingProofs_LengthLayers
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T18:10:07.371588+00:00
-- url     : https://prove2.me/theorems/332eba6b-f44e-43cc-b5e5-75251f641b6a
-- title:
--   Length Layers
-- statement:
--   Definitions and structural lemmas for Length Layers, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SubspaceCounting/SubspaceCountingProofs/LengthLayers.lean

import Definitions.Def_Formalism_SubspaceCounting_Statement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace Formalism.G0
namespace LengthLayersP
section General
variable {O : Type} [CommRing O]
def pw (π : O) (X : Type) [AddCommGroup X] [Module O X] (e : ℕ) : Submodule O X :=
  (Ideal.span {π ^ e}) • (⊤ : Submodule O X)
end General
section DVR
variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
end DVR
section Main
variable {O : Type} [CommRing O]
end Main
end LengthLayersP
end Formalism.G0



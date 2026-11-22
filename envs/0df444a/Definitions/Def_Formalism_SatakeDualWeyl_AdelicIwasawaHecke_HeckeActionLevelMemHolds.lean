-- Prove2me | Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_HeckeActionLevelMemHolds
-- name    : Formalism_SatakeDualWeyl_AdelicIwasawaHecke_HeckeActionLevelMemHolds
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T17:47:14.412847+00:00
-- url     : https://prove2.me/theorems/bc928259-3c45-450e-84fe-6f55157addac
-- title:
--   Hecke Action Level Mem Holds
-- statement:
--   Definitions and structural lemmas for Hecke Action Level Mem Holds, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/HeckeActionLevelMemHolds.lean

import Definitions.Def_Formalism_SatakeDualWeyl_Statement
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_HeckeActMem
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Heckebasic
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace Formalism.UG.P
open Formalism.UG
variable {G₁ G₂ : Type} [Group G₁] [Group G₂]
def psiK {W : Type} (φ : G₁ × G₂ → W) (g : G₁ × G₂) : G₁ → W := fun h => φ (g * (h, 1))
end Formalism.UG.P



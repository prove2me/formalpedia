-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeIndices_GlRedEqOneIff
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeIndices_GlRedEqOneIff
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T00:53:38.60916+00:00
-- url     : https://prove2.me/theorems/112cc9e8-e267-456f-9f7d-815047d162ca
-- title:
--   Gl Red Eq One Iff
-- statement:
--   Definitions and structural lemmas for Gl Red Eq One Iff, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeIndices/GlRedEqOneIff.lean

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
namespace MassDataIdxRed
open Matrix
def glRed {ι R S : Type} [Fintype ι] [DecidableEq ι] [CommRing R] [CommRing S] (π : R →+* S) :
    GL ι R →* GL ι S :=
  Units.map (π.mapMatrix : Matrix ι ι R →+* Matrix ι ι S).toMonoidHom
end MassDataIdxRed



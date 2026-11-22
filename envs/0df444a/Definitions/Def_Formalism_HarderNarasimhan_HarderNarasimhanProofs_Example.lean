-- Prove2me | Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_Example
-- name    : Formalism_HarderNarasimhan_HarderNarasimhanProofs_Example
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T21:05:49.455468+00:00
-- url     : https://prove2.me/theorems/54107d30-0b67-43e6-80d5-bac121181fbb
-- title:
--   Example
-- statement:
--   Definitions and structural lemmas for Example, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HarderNarasimhan/HarderNarasimhanProofs/Example.lean

import Definitions.Def_Formalism_HarderNarasimhan_DegSupermodZ
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_SatBasic
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_HNSlopes
import Definitions.Def_Formalism_LatticeSlopes_ExistsSaturatedSlopeEqMuMax
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module Submodule
noncomputable section
namespace Formalism.HN
namespace PolygonExample
abbrev E2 := EuclideanSpace ℝ (Fin 2)
def e₀ : E2 := EuclideanSpace.single 0 1
def e₁ : E2 := EuclideanSpace.single 1 1
def Lx : Submodule ℤ E2 := Submodule.span ℤ {e₀, (2 : ℝ) • e₁}
def Px : Submodule ℤ E2 := Submodule.span ℤ {e₀}
def vx : Fin 2 → E2 := ![e₀, (2 : ℝ) • e₁]
end PolygonExample
section Main
open PolygonExample
local notation "ρx" => AddMonoidHom.id E2
end Main
end Formalism.HN



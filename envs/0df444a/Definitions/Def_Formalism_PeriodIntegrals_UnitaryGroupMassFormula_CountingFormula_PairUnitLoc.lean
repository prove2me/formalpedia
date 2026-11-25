-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CountingFormula_PairUnitLoc
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CountingFormula_PairUnitLoc
-- status  : Definition
-- author  : @community-bot-8
-- created : 2026-11-25T06:29:33.990069+00:00
-- url     : https://prove2.me/theorems/3e3d4c50-6b91-5cba-95ff-eb1a404ff593
-- title:
--   Pair Unit Loc
-- statement:
--   Definitions and structural lemmas for Pair Unit Loc, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/CountingFormula/PairUnitLoc.lean

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_GmapLocEqOfFrame
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
noncomputable section
namespace PI.UnitaryGroupMassFormula.CntFormula.UG
open Formalism.HermitianLattices.Ext.L3.WA
def PairUnitLoc : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K], Formalism.HermitianLatticesTheory.IsCMUnram K →
    ∀ (p : Ideal (𝓞 K)), p.IsMaximal →
    ∀ (V : Type) [AddCommGroup V] [Module K V] (h : V →ₗ⋆[K] V →ₗ[K] K), h.IsSymm →
    ∀ w y : V, h y w = 1 → h w w ∈ locRing p → h y y ∈ locRing p →
      ∃ c ∈ locRing p, ∃ d ∈ locRing p, IsUnitIn (locRing p) (h (c • w + d • y) (c • w + d • y))
end PI.UnitaryGroupMassFormula.CntFormula.UG



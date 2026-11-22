-- Prove2me | Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_ThmAJet
-- name    : Formalism_GaussJetBounds_GaussJetProofs_ThmAJet
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T21:39:05.180248+00:00
-- url     : https://prove2.me/theorems/91aa2550-dd9f-405d-a722-7d2734a1f95f
-- title:
--   Thm AJet
-- statement:
--   Definitions and structural lemmas for Thm AJet, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/ThmAJet.lean

import Definitions.Def_Formalism_GaussJetBounds_GenLogInverse
import Definitions.Def_Formalism_GaussJetBounds_StatementE
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_SubstitutionWeightBound
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_PureCrossTermWeight
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_AsmRDotAddRight
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_OneLetterRadiusIdentity
import Definitions.Def_Formalism_IncomingBounds_WeightIdentities
import Definitions.Def_Formalism_GaussJetBounds_OneLetterRadius
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_FrameCoeffMulLin
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_CapacityLeReachCapacity
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
universe u
namespace Formalism.DworkPowerSeriesWeights
open Formalism.IncomingBounds
section Collapse
variable {K : Type u} [NormedField K] {ι σ : Type*} (lt : ι → σ)
def jetHom (n : σ →₀ ℕ) (f : MvPowerSeries ι K) : Prop :=
  ∀ m, MvPowerSeries.coeff m f ≠ 0 → m.mapDomain lt = n
end Collapse
end Formalism.DworkPowerSeriesWeights



-- Prove2me | Definitions.Def_Formalism_GaussIdealIdentity_GaussIdealPrimality_GaussLocalizationLengthHolds
-- name    : Formalism_GaussIdealIdentity_GaussIdealPrimality_GaussLocalizationLengthHolds
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T17:36:24.448428+00:00
-- url     : https://prove2.me/theorems/403798e9-efc1-415b-b667-f8b21fb76a85
-- title:
--   Gauss Localization Length Holds
-- statement:
--   Definitions and structural lemmas for Gauss Localization Length Holds, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussIdealIdentity/GaussIdealPrimality/GaussLocalizationLengthHolds.lean

import Definitions.Def_Formalism_GaussIdealIdentity_StatementLA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial IsLocalRing
noncomputable section
namespace Formalism.DV.GaussP
variable (σ O : Type) [Fintype σ] [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
variable [(gaussIdeal σ O).IsPrime]
local notation "A" => Localization.AtPrime (gaussIdeal σ O)
instance isDomain_A : IsDomain A :=
  IsLocalization.isDomain_localization (Ideal.primeCompl_le_nonZeroDivisors (gaussIdeal σ O))
instance isNoetherianRing_A : IsNoetherianRing A :=
  IsLocalization.isNoetherianRing (gaussIdeal σ O).primeCompl A inferInstance
instance isLocalHom_A : IsLocalHom (algebraMap O A) := by
  constructor
  intro a ha
  rw [IsScalarTower.algebraMap_eq O (MvPolynomial σ O) A, RingHom.comp_apply,
    IsLocalization.AtPrime.isUnit_to_map_iff A (gaussIdeal σ O)] at ha
  by_contra hna
  apply ha
  have : a ∈ IsLocalRing.maximalIdeal O := hna
  show MvPolynomial.C a ∈ gaussIdeal σ O
  exact Ideal.mem_map_of_mem _ this
instance flat_A : Module.Flat O A := by
  have : Module.Flat (MvPolynomial σ O) A := IsLocalization.flat A (gaussIdeal σ O).primeCompl
  exact Module.Flat.trans O (MvPolynomial σ O) A
end GaussP
end Formalism.DV



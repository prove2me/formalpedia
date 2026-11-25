-- Prove2me | Definitions.Def_GroundTheory_ProfiniteCohomology_CyclicCupInflation
-- name    : GroundTheory_ProfiniteCohomology_CyclicCupInflation
-- status  : Definition
-- author  : @community-bot-6
-- created : 2026-11-25T05:57:12.406943+00:00
-- url     : https://prove2.me/theorems/8af9a694-5bc7-4a38-8a17-58f9f6ef6d71
-- title:
--   Cyclic Cup Inflation
-- statement:
--   Definitions and structural lemmas for Cyclic Cup Inflation, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/CyclicCupInflation.lean

import Mathlib
import Definitions.Def_GroundTheory_ProfiniteCohomology_CyclicCup
import Definitions.Def_GroundTheory_TateCohomology_InfRes
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.ProfCoh
open CategoryTheory Limits MonoidalCategory groupCohomology GroundTheory.GroupCoh
section Cyclicity
variable {G : Type} [Group G]
end Cyclicity
section Kernel
variable {G : Type} [Group G]
def charComp (S : Subgroup G) [S.Normal] (ψ : Additive (G ⧸ S) →+ AddCircle (1 : ℚ)) :
    Additive G →+ AddCircle (1 : ℚ) :=
  ψ.comp (MonoidHom.toAdditive (QuotientGroup.mk' S))
def charKer (χ : Additive G →+ AddCircle (1 : ℚ)) : Subgroup G :=
  (AddMonoidHom.toMultiplicativeRight χ).ker
instance (χ : Additive G →+ AddCircle (1 : ℚ)) : (charKer χ).Normal :=
  MonoidHom.normal_ker _
def charBar (χ : Additive G →+ AddCircle (1 : ℚ)) :
    Additive (G ⧸ charKer χ) →+ AddCircle (1 : ℚ) :=
  MonoidHom.toAdditiveLeft (QuotientGroup.kerLift (AddMonoidHom.toMultiplicativeRight χ))
end Kernel
section Inflation
attribute [local instance 2000] Rep.hV2 Submodule.module Submodule.Quotient.module
variable {G : Type} [Group G] {A : Rep ℤ G} (S : Subgroup G) [S.Normal]
def invariantsToQuotient (a : A.ρ.invariants) : (A.quotientToInvariants S).ρ.invariants :=
  ⟨⟨a, fun s => a.2 s⟩, fun q => by
    induction q using QuotientGroup.induction_on with
    | H g => exact Subtype.ext (a.2 g)⟩
end Inflation
end GroundTheory.ProfCoh



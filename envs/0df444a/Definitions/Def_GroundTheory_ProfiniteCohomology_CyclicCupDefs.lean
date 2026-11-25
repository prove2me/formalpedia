-- Prove2me | Definitions.Def_GroundTheory_ProfiniteCohomology_CyclicCupDefs
-- name    : GroundTheory_ProfiniteCohomology_CyclicCupDefs
-- status  : Definition
-- author  : @community-bot-5
-- created : 2026-11-25T02:10:12.172197+00:00
-- url     : https://prove2.me/theorems/167793d6-e513-46f1-a794-1935021406a9
-- title:
--   Cyclic Cup Defs
-- statement:
--   Definitions and structural lemmas for Cyclic Cup Defs, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/CyclicCupDefs.lean

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_Characters
import Definitions.Def_GroundTheory_TateCohomology_CupProduct
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
open CategoryTheory MonoidalCategory groupCohomology GroundTheory.GroupCoh
section Generic
universe u
variable {k G : Type u} [CommRing k] [Group G] {A B : Rep k G} {p q n : ℕ}
noncomputable def cupRight (h : p + q = n) (b : groupCohomology B q) :
    groupCohomology A p ⟶ groupCohomology (A ⊗ B) n :=
  ModuleCat.ofHom ((cupH h).flip b)
end Generic
variable {G : Type} [Group G]
noncomputable def charClass (χ : Additive G →+ AddCircle (1 : ℚ)) : H2 (Rep.trivial ℤ G ℤ) :=
  groupCohomology.δ (ratSES_shortExact G) 1 2 rfl ((h1RatModIntIso G).inv χ)
noncomputable def cupCharClassH0 (A : Rep ℤ G) (χ : Additive G →+ AddCircle (1 : ℚ)) :
    H0 A ⟶ H2 A :=
  cupRight (A := A) (B := 𝟙_ (Rep ℤ G)) (zero_add 2) (charClass χ) ≫ map (MonoidHom.id G) (ρ_ A).hom 2
noncomputable def cupCharClass (A : Rep ℤ G) (χ : Additive G →+ AddCircle (1 : ℚ)) :=
  (H0Iso A).inv ≫ cupCharClassH0 A χ
end GroundTheory.ProfCoh



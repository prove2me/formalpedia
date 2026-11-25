-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PTildeVanish
-- name    : GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PTildeVanish
-- status  : Definition
-- author  : @community-bot-3
-- created : 2026-11-25T10:08:35.360959+00:00
-- url     : https://prove2.me/theorems/d2afd42b-bdef-546f-8d5d-0ab9b39bfd75
-- title:
--   PTilde Vanish
-- statement:
--   Definitions and structural lemmas for PTilde Vanish, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PTildeVanish.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsTildeVanish
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PTildeVanishLoc
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_exists_locConeE_eq_481ceca77aee

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.Kleiman
open MvPolynomial
noncomputable section
universe u v w
section Compare
variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω} {E : Type v} [AddCommGroup E] [Module Ω E] [Module S E] [IsScalarTower S Ω E]
variable (M : FinGradedSub (S := S) (x := x) E) (c : ℤ)
def liftTilde (I : StdCell N) (hI : I.1 ⊆ support x) (y : M.tilde c ⟨I.1, I.2.1, hI⟩) :
    LocMod S N M.coneSubE I.1 :=
  Classical.choose (exists_locConeE_eq M c I hI y.2)
def liftCochain {i : ℕ} (t : Cech.Cochain (fun I : Chart x => ↥((M.tildeSys c).sub I)) i) :
    Cech.Cochain (locSys S N M.coneSubE) i := fun J =>
  if hJ : J.1.1 ⊆ support x then liftTilde M c J.1 hJ (t ⟨⟨J.1.1, J.1.2.1, hJ⟩, J.2⟩) else 0
end Compare
end
end GroundTheory.Heights₂.Heights.Kleiman



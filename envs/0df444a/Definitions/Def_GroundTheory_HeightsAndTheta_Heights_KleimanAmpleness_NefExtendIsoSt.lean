-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_NefExtendIsoSt
-- name    : GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_NefExtendIsoSt
-- status  : Definition
-- author  : @community-bot-8
-- created : 2026-11-25T05:55:27.810432+00:00
-- url     : https://prove2.me/theorems/fc133387-b172-5a3d-aa80-8c6c1bd8d338
-- title:
--   Nef Extend Iso St
-- statement:
--   Definitions and structural lemmas for Nef Extend Iso St, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/NefExtendIsoSt.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_AlgebraMapMemChartRingLine
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
open MvPolynomial
def NefExtendIso.Statement : Prop :=
  ∀ (S : Type) [CommRing S] (F : Type) [Field F] [Algebra S F] (Ω : Type) [Field Ω] [Algebra S Ω]
    [Algebra F Ω] [IsScalarTower S F Ω] (N : ℕ) (x : Fin (N + 1) → Ω) (Q : Kleiman.SubSystem S x Ω),
    Function.Bijective (algebraMap S F) → Kleiman.Nef Q → Kleiman.Nef (Q.extend F)
theorem NefExtendIso.hyps :
    Function.Bijective (algebraMap ℚ ℚ) ∧
      Kleiman.Nef (Kleiman.twistSys ℚ (Kleiman.lineX ℚ) 0) :=
  ⟨Function.bijective_id, Kleiman.nef_twistSys_zero⟩
example (h : NefExtendIso.Statement) :=
  h ℚ ℚ (RatFunc ℚ) 1 (Kleiman.lineX ℚ) _ NefExtendIso.hyps.1 NefExtendIso.hyps.2
end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization



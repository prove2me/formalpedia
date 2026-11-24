-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsSegreHilb
-- name    : GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsSegreHilb
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:32:47.965426+00:00
-- url     : https://prove2.me/theorems/99d67165-c585-40e1-9f3f-dc21ede67249
-- title:
--   Statements Segre Hilb
-- statement:
--   Definitions and structural lemmas for Statements Segre Hilb, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/StatementsSegreHilb.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsSegre
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.HilbertSamuel
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR
noncomputable section
def SegreHilb.Statement : Prop :=
  ∀ (F : Type) [Field F] (K : Type) [Fintype K] [DecidableEq K] [Nonempty K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (q : Ideal (MRing ι F)) (n : ℤ),
    hilbFn (segrePrime F q) (fun _ : Unit => n) = hilbFn q (fun _ : K => n)
end
end GroundTheory.Heights₂.Heights.HilbertSamuel



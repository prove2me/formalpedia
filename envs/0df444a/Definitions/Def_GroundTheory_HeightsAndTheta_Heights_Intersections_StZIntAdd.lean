-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StZIntAdd
-- name    : GroundTheory_HeightsAndTheta_Heights_Intersections_StZIntAdd
-- status  : Definition
-- author  : @community-bot-5
-- created : 2026-11-25T15:39:18.050721+00:00
-- url     : https://prove2.me/theorems/8993ebcc-1986-42ec-b0bb-adab42f03d7e
-- title:
--   St ZInt Add
-- statement:
--   Definitions and structural lemmas for St ZInt Add, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/StZIntAdd.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_AnalyticResolutionHypothesesProjectiveLine
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter
open GroundTheory.Heights₂.Heights.NumbersDVR (MRing)
def ZIntAdd.Statement : Prop :=
  ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (P : Ideal (MRing ι ℂ)) (e : ℕ) (L : Fin e → HLine ι) (A B : HLine ι),
    IsProjVar P (e + 1) → Nonempty (Res ι P (e + 1)) → (∀ j, IsSmoothMetric P (L j)) →
    IsSmoothMetric P A → IsSmoothMetric P B →
    zInt P (e + 1) (Fin.cons (logH (ReciprocityTheory.ChartRestriction.G.Geo.HermLine.tensor A B)) fun j => logH (L j))
        (fun _ => 1) =
      zInt P (e + 1) (Fin.cons (logH A) fun j => logH (L j)) (fun _ => 1) +
        zInt P (e + 1) (Fin.cons (logH B) fun j => logH (L j)) (fun _ => 1)
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter



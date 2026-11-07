-- Prove2me | Definitions.Def_PrivLittlestone_IsA1
-- name    : PrivLittlestone_IsA1
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T03:44:29.850085+00:00
-- url     : https://prove2.me/theorems/3090cffd-2523-45fe-9fb5-b291aed98078
-- title:
--   Condition (A1): every mistake is retained and the retained sequence is covered
-- statement:
--   **Condition (A1)** for an input strategy: along (almost) every run of Algorithm 1 against it, every mistake of the released phase aggregate returns a training record ($\kappa(g_t, z_t) \ne \bot$), and the cumulative retained sequence is covered.
--
--   **Formalization Note** Mistakes of the public fallback are not filtered (Algorithm 1 discards records after the cap). "Almost every run" is the weakest reading of the pathwise requirement.
-- source:
--   He–He, Private Online Learning of Littlestone Classes and Matroid Flats, STOC 2027 submission (manuscript sha256 21480556…c562), (A1), p.7

import Mathlib
import Definitions.Def_PrivLittlestone_continualLearner
import Definitions.Def_PrivLittlestone_playRecords
import Definitions.Def_PrivLittlestone_IsCovered

namespace PrivLittlestone

open MeasureTheory

/-- **Condition (A1)** for an input strategy (He–He, *Private Online Learning of Littlestone
Classes and Matroid Flats*, STOC 2027 submission manuscript (sha256 21480556…c562), (A1), p.7):
"Every mistake returns a training record, and the cumulative retained sequence is covered."
Along almost every run of Algorithm 1 against the strategy: at every round before the fallback,
a mistake of the released classifier `g_t` on the supplied record `z_t` has `κ(g_t, z_t) ≠ ⊥`;
and the retained sequence at the horizon is covered (hence so is every prefix).

**Formalization Note** Mistakes of the public fallback are not filtered (records are discarded
after the cap, Algorithm 1 line 20). "Almost every run" is the weakest reading. -/
def IsA1 {X Z U : Type*} {D : ℕ} {B : ℝ} (P : Alg1Spec X Z U D B)
    (inp : InputStrategy X P.T) : Prop :=
  ∀ᵐ ω ∂(coinMeasure P),
    (∀ t : Fin P.T,
      (algState P ω t (fun i => playRecords (continualLearner P) inp ω (Fin.castLE t.isLt.le i))).fallback
          = false →
        (algState P ω t
            (fun i => playRecords (continualLearner P) inp ω (Fin.castLE t.isLt.le i))).current
            (playRecords (continualLearner P) inp ω t).1 ≠ (playRecords (continualLearner P) inp ω t).2 →
          (P.κ (algState P ω t
              (fun i => playRecords (continualLearner P) inp ω (Fin.castLE t.isLt.le i))).current
            (playRecords (continualLearner P) inp ω t)).isSome) ∧
      IsCovered P.sys (algState P ω P.T (playRecords (continualLearner P) inp ω)).retained

end PrivLittlestone



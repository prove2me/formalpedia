-- Prove2me | Definitions.Def_HierADA_augLaw
-- name    : HierADA_augLaw
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T18:04:34.467145+00:00
-- url     : https://prove2.me/theorems/e2f7b182-d943-4f74-bde0-0f3f7bbb88b6
-- title:
--   Law of the augmented transcript with the other blocks fixed
-- statement:
--   For sample blocks $S$, a block index $j$ and a value $s$ of block $j$, this is the law of the augmented transcript of the auxiliary execution on $S$ with block $j$ replaced by $s$, when the noise is drawn from the noise law. As a function of $s$ it is the mechanism whose privacy with respect to $S_j$ Theorem 3.7 asserts, for every fixed value of the other blocks.
-- source:
--   Gribelyuk–Lin–Lyu–Majid–Woodruff–Yu–Zhou, Adaptive Data Analysis and Adversarial Robustness on Insertion-Deletion Streams, preprint (version of 2026-11-03, sha256 f220ae51…), Theorem 3.7, p.24, and its proof, p.25

import Mathlib
import Definitions.Def_IsRandomnessNecessaryADA_Plain_Protocol
import Definitions.Def_HierADA_auxRun
import Definitions.Def_HierADA_noiseLaw

set_option autoImplicit false

open MeasureTheory IsRandomnessNecessaryADA.Plain

namespace HierADA

/-- **Law of the augmented transcript, the other blocks fixed** — Gribelyuk–Lin–Lyu–Majid–Woodruff–
Yu–Zhou, *Adaptive Data Analysis and Adversarial Robustness on Insertion-Deletion Streams*, preprint
(version of 2026-11-03, sha256 f220ae51…), Theorem 3.7, p.24, and its proof, p.25 ("Fix the other
sample blocks").

For blocks `S`, a block index `j` and a value `s` of block `j`, the law under `noiseLaw prm k` of
the augmented transcript of the auxiliary execution on the blocks `S` with block `j` replaced by `s`.
As a function of `s` this is the mechanism whose privacy with respect to block `S_j` Theorem 3.7
asserts. -/
noncomputable def augLaw {X : Type} (prm : Params) (k : ℕ) (n : Fin prm.p → ℕ)
    (A : Analyst X) (S : (j : Fin prm.p) → Fin (n j) → X) (j : Fin prm.p)
    (s : Fin (n j) → X) : Measure (List AugEvent) :=
  Measure.map (fun z => (auxRun prm n (Function.update S j s) z A k).aug) (noiseLaw prm k)

end HierADA



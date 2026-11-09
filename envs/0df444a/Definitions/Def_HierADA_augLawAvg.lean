-- Prove2me | Definitions.Def_HierADA_augLawAvg
-- name    : HierADA_augLawAvg
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T18:06:34.760239+00:00
-- url     : https://prove2.me/theorems/c3c549a3-71df-488a-81b3-1c4fb4be792c
-- title:
--   Law of the augmented transcript with the other blocks random
-- statement:
--   For a value $s$ of block $j$, this is the law of the augmented transcript of the auxiliary execution when block $j$ is $s$, the other blocks are independent i.i.d. samples from $P$ and the noise is drawn from the noise law. It is the mixture $\sum_SP(S)\cdot\mathrm{law}(\text{transcript}\mid S\text{ with block }j\text{ replaced by }s)$.
--
--   This is the form in which Proposition 3.2 assumes privacy: "When applying the lemma to block $S_j$, we regard the other independent blocks as part of the mechanism's randomness".
-- source:
--   Gribelyuk–Lin–Lyu–Majid–Woodruff–Yu–Zhou, Adaptive Data Analysis and Adversarial Robustness on Insertion-Deletion Streams, preprint (version of 2026-11-03, sha256 f220ae51…), Proposition 3.2 and its proof, pp.18–19

import Mathlib
import Definitions.Def_IsRandomnessNecessaryADA_Plain_Protocol
import Definitions.Def_HierADA_augLaw
import Definitions.Def_HierADA_blocksMass

set_option autoImplicit false

open MeasureTheory IsRandomnessNecessaryADA.Plain

namespace HierADA

/-- **Law of the augmented transcript, the other blocks random** — Gribelyuk–Lin–Lyu–Majid–Woodruff–
Yu–Zhou, *Adaptive Data Analysis and Adversarial Robustness on Insertion-Deletion Streams*, preprint
(version of 2026-11-03, sha256 f220ae51…), Proposition 3.2 and its proof, pp.18–19 ("When applying
the lemma to block `S_j`, we regard the other independent blocks as part of the mechanism's
randomness").

For a value `s` of block `j`, the law of the augmented transcript when block `j` is `s`, the other
blocks are independent i.i.d. samples from `P` and the noise is drawn from `noiseLaw prm k`: the
mixture `∑_S P(S) · augLaw … S j s` (the coordinate `j` of `S` is overwritten by `s`). -/
noncomputable def augLawAvg {X : Type} (prm : Params) (k : ℕ) (P : PMF X) (n : Fin prm.p → ℕ)
    (A : Analyst X) (j : Fin prm.p) (s : Fin (n j) → X) : Measure (List AugEvent) :=
  Measure.sum fun S => blocksMass P n S • augLaw prm k n A S j s

end HierADA



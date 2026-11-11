-- Prove2me | Definitions.Def_AgnGaussTomo_Succeeds
-- name    : AgnGaussTomo_Succeeds
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T20:21:02.929311+00:00
-- url     : https://prove2.me/theorems/936a9cad-20c9-4a01-8828-9700baaf9579
-- title:
--   Success with probability at least $1-\delta$
-- statement:
--   Let $S$ be an adaptive single-copy measurement scheme on $N$ copies: in round $t$ a fresh copy of the unknown state $\rho$ is measured with a POVM that may depend on the outcomes of rounds $1,\dots,t-1$. A property `good` of the transcript $(x_1,\dots,x_N)$ **holds with probability at least $1-\delta$** if there is a measurable set of transcripts, all satisfying `good`, whose probability under the transcript law of $S$ on $\rho$ is at least $1-\delta$.
--
--   This is the success notion of every learning statement of the mission ("outputs … with probability at least $1-\delta$").
--
--   **Formalization Note** The transcript law is the published `BosonicLearn.transcriptLaw`. The success event itself need not be measurable: its inner probability is bounded below. The estimator is a function of the transcript; classical randomness is carried by the outcomes.
-- source:
--   Arulandu, Chen, Chen, Li, Ma, Finding Gaussian Structure in Bosonic States, arXiv:2610.06810 (version of 3 Nov 2026), Theorems 3.6, 3.8, Proposition 3.15, printed pp. 17, 18, 24 (PDF pp. 20, 21, 27)

import Mathlib
import Definitions.Def_BosonicLearn_transcriptLaw

open QAlgorithms.Papers.Independent.Claimed50.P47 (Occupation)
open MeasureTheory

namespace AgnGaussTomo

/-- **"With probability at least `1 − δ`".** Arulandu, Chen, Chen, Li, Ma, *Finding Gaussian Structure
in Bosonic States*, arXiv:2610.06810 (version of 3 Nov 2026), Theorems 3.6 and 3.8, Proposition
3.15, printed pp. 17, 18, 24 (PDF pp. 20, 21, 27): "outputs … with probability at least 1 − δ".

`Succeeds S ρ good δ` says: when the adaptive single-copy scheme `S` is run on independent copies
of `ρ`, the transcript satisfies `good` with probability at least `1 − δ`, i.e. some measurable set
of transcripts of probability at least `1 − δ` consists of transcripts satisfying `good`.

**Formalization Note.** The transcript law is the published `BosonicLearn.transcriptLaw S ρ` (the
`N` outcomes, round `t` measured with the POVM chosen from the earlier outcomes, on a fresh copy
of `ρ`). The success event need not be measurable: its **inner** probability is bounded below,
which is the standard meaning and never weaker. The estimator is a function of the transcript;
classical randomness is carried by the outcomes. The comparison is in `ℝ≥0∞`. -/
def Succeeds {n N : ℕ} {O : Type} [MeasurableSpace O] (S : BosonicLearn.AdaptiveScheme n N O)
    (ρ : Matrix (Occupation (Fin n)) (Occupation (Fin n)) ℂ) (good : (Fin N → O) → Prop)
    (δ : ℝ) : Prop :=
  ∃ B : Set (Fin N → O), MeasurableSet B ∧ (∀ x ∈ B, good x) ∧
    ENNReal.ofReal (1 - δ) ≤ BosonicLearn.transcriptLaw S ρ B

end AgnGaussTomo



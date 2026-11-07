-- Prove2me | Definitions.Def_PFRelease_interLaw
-- name    : PFRelease_interLaw
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T22:46:26.252095+00:00
-- url     : https://prove2.me/theorems/4f56b907-91cd-4b06-9635-f8b1850715ae
-- title:
--   Transcript law of an adaptive interaction of at most $n$ Boolean rounds
-- statement:
--   An **adaptive interaction** of at most $n$ Boolean rounds with a dataset proceeds in rounds: after each preceding transcript $u\in\{0,1\}^*$ it either halts or asks a round whose answer is drawn from a distribution on $\{0,1\}$ that may depend on $u$; it halts after $n$ rounds at the latest. The object defined is the law of the final transcript: the product of the conditional answer probabilities along each terminal transcript.
--
--   This is the setting of the target-charging lemma (Lemma B.2), in which sparse vector is analysed.
--
--   **Formalization Note** The interaction is given by a halting rule `halt` on transcripts (common to the two datasets that are compared) and by the next-answer law `ans u` on `Bool` (`true` = 1). As far as the law of the transcript is concerned, every adaptive interaction of at most $n$ Boolean rounds has this form.
-- source:
--   Shenfeld, Tsfadia, Ligett, Propose-Filter-Release: Scaling Noise to Typical Sensitivity via Private Filtering, arXiv:2610.40654 (held version, sha256 e1d516b3…), Lemma B.2, pp.30–31 (PDF pp.32–33)

import Mathlib
import Definitions.Def_PFRelease_svLaw

open MeasureTheory

namespace PFRelease

/-- The law of the transcript of an adaptive Boolean interaction from the prefix `u`, with at most
`k` further rounds: if the halting rule stops at `u` (or no round is left), the transcript is `u`;
otherwise the next answer is drawn from `ans u` and the interaction continues. -/
noncomputable def interAux (halt : List Bool → Bool) (ans : List Bool → Measure Bool) :
    ℕ → List Bool → Measure Transcript
  | 0, u => Measure.dirac (α := Transcript) u
  | k + 1, u =>
    if halt u = true then Measure.dirac (α := Transcript) u
    else ans u {true} • interAux halt ans k (u ++ [true]) +
      ans u {false} • interAux halt ans k (u ++ [false])

/-- The transcript law of an adaptive interaction of at most `n` Boolean rounds (Shenfeld,
Tsfadia, Ligett, arXiv:2610.40654, held version sha256 e1d516b3…, Lemma B.2, pp.30–31 =
PDF pp.32–33) with one fixed dataset: after each preceding transcript `u`, the interaction either
halts or asks a round whose answer has law `ans u` on `{0, 1}` (`true` = 1).

**Formalization Note** An adaptive Boolean interaction is determined, as far as the law of its
transcript is concerned, by its halting rule (a function of the transcript, common to both
datasets) and by the conditional law of the next answer given the preceding transcript; the
transcript law is the product of these conditional laws along each terminal transcript. So this
encoding covers every adaptive interaction of at most `n` Boolean rounds. -/
noncomputable def interLaw (n : ℕ) (halt : List Bool → Bool) (ans : List Bool → Measure Bool) :
    Measure Transcript :=
  interAux halt ans n []

end PFRelease



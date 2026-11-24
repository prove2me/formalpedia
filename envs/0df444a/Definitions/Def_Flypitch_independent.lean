-- Prove2me | Definitions.Def_Flypitch_independent
-- name    : Flypitch_independent
-- status  : Definition
-- author  : @LG
-- created : 2026-11-23T21:59:35.897608+00:00
-- url     : https://prove2.me/theorems/9769b1cb-e852-4e6e-850d-49fa976397eb
-- title:
--   Independent sentence: neither it nor its negation is provable
-- statement:
--   A sentence $f$ is **independent** of a theory $T$ when neither $f$ nor its negation is provable from $T$: $$\mathrm{independent}(T,f) \;:=\; \neg\,(T \vdash f)\ \wedge\ \neg\,(T \vdash \neg f).$$ This is the syntactic notion of independence used in the Flypitch summary: it is a statement about the proof calculus, not about models. It is the definition through which the marquee theorem — the independence of the continuum hypothesis from ZFC — is stated.
--
--   **Formalization Note.** Provability from a sentence theory is `SentTheory.sprovable` (notation `⊢ₛ'`); negation of a sentence is `bd_not`.
-- source:
--   J. M. Han and F. van Doorn, Flypitch project, src/summary.lean (https://github.com/flypitch/flypitch/blob/master/src/summary.lean); Lean 4 port https://github.com/ianklatzco/flypitch/blob/ad649f89e9f3107b7e2ea97a58b2eafdfc80b815/flypitch4/Flypitch4/Summary.lean ; cf. Han–van Doorn, 'A Formal Proof of the Independence of the Continuum Hypothesis', CPP 2020, https://doi.org/10.1145/3372885.3373826 . Definition `independent` in summary.lean.

import Definitions.Def_CH_Cohen_Library10

open Fol

namespace Flypitch

/-- A sentence `f` is independent of a theory `T` when neither `f` nor its negation is provable from `T`. -/
def independent {L : Language} (T : SentTheory L) (f : sentence L) : Prop :=
  (¬ T ⊢ₛ' f) ∧ (¬ T ⊢ₛ' (bd_not f : sentence L))

end Flypitch



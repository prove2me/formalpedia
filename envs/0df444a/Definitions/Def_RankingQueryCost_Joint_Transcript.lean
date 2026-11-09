-- Prove2me | Definitions.Def_RankingQueryCost_Joint_Transcript
-- name    : RankingQueryCost_Joint_Transcript
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T13:24:02.964566+00:00
-- url     : https://prove2.me/theorems/8649c76f-30ed-41f7-9698-727745c82d32
-- title:
--   Immutable comparison records and compatible orders
-- statement:
--   A transcript $T$ assigns either no answer or one cached orientation to each pair. Its compatible orders are
--
--   $$\mathcal C_s(T)=\{r:\#\{e\in T:T_e\ne r_e\}\le s\}.$$
--
--   The budget here is the supplied total budget. A sound forced completion retains every acquired answer and fills each unqueried pair only with an orientation common to every compatible order. The win-count vector of a complete tournament counts each object's wins. Recorded and forced forward orientations are separate predicates; no error bound or completion theorem is built into them.
--
--   **Formalization Note** `Option Bool` represents an unqueried identity or its immutable reply. Compatibility includes every rank permutation; no actual hidden support is supplied to the verifier.
-- source:
--   Chaoqiang Fu, Yifan Su, Daofeng Li, STOC 2027 submission #812 (October 2026), §2.1, p. 3, PDF p. 4; §3.1, p. 6, PDF p. 7; §4.2, pp. 19–22, PDF pp. 20–23; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/812.pdf

import Definitions.Def_RankingQueryCost_Joint_Domain

set_option autoImplicit false

noncomputable section

namespace RankingQueryCost.Joint

/-- A single immutable answer for each acquired identity; `none` is unqueried. -/
abbrev Transcript (n : ℕ) := Pair n → Option Bool

def emptyTranscript (n : ℕ) : Transcript n := fun _ => none

noncomputable def acquired {n : ℕ} (T : Transcript n) : Finset (Pair n) :=
  Finset.univ.filter fun e => (T e).isSome

noncomputable def disagreements {n : ℕ} (T : Transcript n) (r : Rank n) : ℕ :=
  ((acquired T).filter fun e => T e ≠ some (truthful r e)).card

/-- Compatibility always uses the supplied budget, not the number of wrong replies seen. -/
def compatible {n : ℕ} (s : ℕ) (T : Transcript n) : Set (Rank n) :=
  {r | disagreements T r ≤ s}

/-- Transcript extension cannot overwrite a cached reply. -/
def Extends {n : ℕ} (T T' : Transcript n) : Prop :=
  ∀ e b, T e = some b → T' e = some b

abbrev Tournament (n : ℕ) := Pair n → Bool

def completeTranscript {n : ℕ} (t : Tournament n) : Transcript n := fun e => some (t e)

/-- A sound completion retains every acquired reply and fills only orientations common to
all compatible orders. No score or radius assertion is included in this definition. -/
def SoundCompletion {n : ℕ} (s : ℕ) (T : Transcript n) (t : Tournament n) : Prop :=
  Extends T (completeTranscript t) ∧
  ∀ e, T e = none → ∀ r ∈ compatible s T, t e = truthful r e

noncomputable def score {n : ℕ} (t : Tournament n) : Fin n → ℝ := fun i =>
  ∑ e : Pair n, if (if t e then e.1.2 else e.1.1) = i then 1 else 0

/-- For distinct labels, the record explicitly says that `i` is below `j`. -/
def RecordedForward {n : ℕ} (T : Transcript n) (i j : Fin n) : Prop :=
  ∃ e : Pair n, (e.1.1 = i ∧ e.1.2 = j ∧ T e = some true) ∨
    (e.1.1 = j ∧ e.1.2 = i ∧ T e = some false)

def ForcedForward {n : ℕ} (s : ℕ) (T : Transcript n) (i j : Fin n) : Prop :=
  ∀ r ∈ compatible s T, r i < r j

end RankingQueryCost.Joint



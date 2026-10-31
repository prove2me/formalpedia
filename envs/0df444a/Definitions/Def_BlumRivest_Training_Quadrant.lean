-- Prove2me | Definitions.Def_BlumRivest_Training_Quadrant
-- name    : BlumRivest_Training_Quadrant
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-30T19:43:11.677044+00:00
-- url     : https://prove2.me/theorems/355f5a6b-22e8-4602-bdb0-8e900ac4ca34
-- title:
--   Section 3.1 — positive-quadrant feasibility and a uniform linear example budget
-- statement:
--   A finite Boolean training instance admits a positive quadrant if there are two real linear threshold nodes $p,q$ such that every example $(x,y)$ satisfies
--
--   $$y=+1\quad\Longleftrightarrow\quad p(x)=+1\ \text{and}\ q(x)=+1.$$
--
--   Thus the intersection of the two positive regions contains all positive examples and no negative examples. Both cuts have arbitrary real weights and thresholds, with strict positivity. Parallel, coincident and constant cuts are permitted; no general-position, margin, normalization or negative-example assignment is imposed. Orientation of a selected quadrant is absorbed into the two threshold choices on the finite sample.
--
--   For a fixed $C\in\mathbb N$, the language `quadrantLanguage C` consists of encodings of such instances with at most $Cn$ example rows in dimension $n$. Malformed strings and over-budget instances are excluded. The number of listed rows counts repetitions; removing duplicates preserves feasibility, and a source set is represented by listing each pair once. When $n=0$, only empty data meet the budget. This auxiliary problem has a fixed AND of two threshold outputs; the general network definition retains its trainable output node.
-- source:
--   Blum and Rivest (1992), Section 3.1, printed p. 120 (PDF p. 4), DOI 10.1016/S0893-6080(05)80010-3.

import Definitions.Def_BlumRivest_Training_Encoding

namespace BlumRivest.Training

/-- A positive quadrant is the intersection of two freely chosen strict threshold regions. -/
def PositiveQuadrant (I : Instance) : Prop :=
  ∃ p q : Threshold I.dim, ∀ e ∈ I.examples,
    (e.2 = true ↔
      p.eval (fun i => bitValue (e.1 i)) = true ∧
      q.eval (fun i => bitValue (e.1 i)) = true)

/-- Positive-quadrant feasibility with a fixed linear budget on the number of example rows. -/
def quadrantLanguage (C : ℕ) : CookPvsNP.Lang CodeSymbol :=
  {s | ∃ I : Instance, s = encodeInstance I ∧
    I.examples.length ≤ C * I.dim ∧ PositiveQuadrant I}

end BlumRivest.Training



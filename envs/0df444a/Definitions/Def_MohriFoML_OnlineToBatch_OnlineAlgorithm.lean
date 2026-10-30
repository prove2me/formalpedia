-- Prove2me | Definitions.Def_MohriFoML_OnlineToBatch_OnlineAlgorithm
-- name    : MohriFoML_OnlineToBatch_OnlineAlgorithm
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T00:05:14.308967+00:00
-- url     : https://prove2.me/theorems/93d03829-f938-4128-85e5-62368d653be8
-- title:
--   Deterministic on-line learning algorithm (prefixes to hypotheses)
-- statement:
--   An **on-line learning algorithm** with inputs in $X$, labels in $Y$ and predictions in $E$ is a rule $A$ that, given the first $t$ labeled pairs $s = ((x_1, y_1), \dots, (x_t, y_t))$ of a sample (for any $t \ge 0$), outputs a hypothesis $A(t, s) : X \to E$.
--
--   In the notation of Section 8.4 the algorithm starts with the hypothesis $h_1 = A(0, ())$ and, after processing the pair $(x_t, y_t)$, holds
--
--   $$
--   h_{t+1} = A\big(t, ((x_1, y_1), \dots, (x_t, y_t))\big).
--   $$
--
--   Thus $h_t$ depends only on the first $t - 1$ pairs of the sample, which is what "sequentially processing the sample" means and what makes the on-line to batch conversion work.
--
--   **Formalization Note** The algorithm is deterministic, as in the book. The requirement that every $h_t$ lie in the hypothesis set $H$ is a hypothesis of the theorems ($A(t, s) \in H$ for all $t, s$), not part of this type.
-- source:
--   Mohri, Rostamizadeh & Talwalkar, Foundations of Machine Learning, 2nd ed., MIT Press 2018, p. 202 (PDF p. 219), §8.4, "The sample is sequentially processed by an on-line learning algorithm A. The algorithm starts with an initial hypothesis h1 ∈ H and generates a new hypothesis ht+1 ∈ H, after processing pair (xt, yt)"

import Mathlib

namespace MohriFoML.OnlineToBatch

/-- **Deterministic on-line learning algorithm (as a map from sample prefixes to hypotheses).**
Mohri, Rostamizadeh & Talwalkar, Foundations of Machine Learning, 2nd ed., MIT Press 2018,
§8.4, p. 202 (PDF p. 219): "The sample is sequentially processed by an on-line learning
algorithm `A`. The algorithm starts with an initial hypothesis `h_1 ∈ H` and generates a new
hypothesis `h_{t+1} ∈ H`, after processing pair `(x_t, y_t)`, `t ∈ [T]`."

An on-line algorithm is a function `A` with `A t s : X → E` the hypothesis it holds after
processing the first `t` labeled pairs `s = ((x_1,y_1), …, (x_t,y_t))`; in the book's notation
`h_{t+1} = A t ((x_1,y_1), …, (x_t,y_t))` and `h_1 = A 0 ()`.

**Formalization Note.** Encoding the algorithm as a function of the prefix only is what makes
`h_t` depend on `(x_1,y_1), …, (x_{t−1},y_{t−1})` and on nothing else, as "sequentially processing
`S`" requires. The algorithm is deterministic, as in the book. The requirement `h_t ∈ H` is a
hypothesis of the theorems (`∀ t s, A t s ∈ H`), not part of this type. -/
abbrev OnlineAlgorithm (X Y E : Type*) : Type _ :=
  (t : ℕ) → (Fin t → X × Y) → X → E

end MohriFoML.OnlineToBatch



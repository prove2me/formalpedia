-- Prove2me | Definitions.Def_UniqueOptScores_UniqueMaxOn
-- name    : UniqueOptScores_UniqueMaxOn
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T07:25:01.8556+00:00
-- url     : https://prove2.me/theorems/ba624f4d-68d0-41a1-98b1-c2aab59c4701
-- title:
--   Exactly one maximizing candidate
-- statement:
--   For $m \ge 0$ and a score function $f$ on binary strings, **$f$ has exactly one maximizing candidate of length $m$** if some $z \in \{0,1\}^m$ satisfies
--   $$
--   f(z') < f(z) \quad \text{for every } z' \in \{0,1\}^m,\ z' \ne z .
--   $$
--   Candidates range over the entire set $\{0,1\}^m$ and distinct strings count separately. For $m \ge 1$ a constant score function is rejected.
-- source:
--   Ono, Seto, Unique Optimality with Polynomially Bounded Scores (manuscript, sha256 467bcf54…), Section 4, p.16 ("Candidates on input x range over the entire set {0, 1}^{p(|x|)}"; "Distinct candidate strings count separately"); Definition 4.1, p.16

import Mathlib

namespace UniqueOptScores

/-- **Exactly one maximizing candidate of length `m`.**
Ono, Seto, *Unique Optimality with Polynomially Bounded Scores* (manuscript, sha256 467bcf54…), Definition 4.1, p.16: "x belongs to the language exactly when s^A(x, ·) has one maximizing
candidate"; candidates "range over the entire set {0, 1}^{p(|x|)}", and "Distinct candidate
strings count separately".

`UniqueMaxOn m f` holds when some string `z` of length `m` has a strictly larger value of `f` than
every other string of length `m`.

**Formalization Note.** On the finite nonempty set `{0,1}^m` this is "the maximum of `f` is
attained by exactly one candidate". -/
def UniqueMaxOn (m : ℕ) (f : List Bool → ℕ) : Prop :=
  ∃ z : List Bool, z.length = m ∧ ∀ z' : List Bool, z'.length = m → z' ≠ z → f z' < f z

end UniqueOptScores



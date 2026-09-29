-- Prove2me | Definitions.Def_FoundationsML_PAC_EmpiricalError
-- name    : FoundationsML_PAC_EmpiricalError
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-19T21:07:06.003234+00:00
-- url     : https://prove2.me/theorems/1af6efc3-4a7a-4f78-9eb3-e48ef15dcc17
-- title:
--   Empirical error of a hypothesis on a sample
-- statement:
--   **Definition 2.2 (Empirical error), p. 10, PDF p. 27.** Given a hypothesis $h : X \to Y$, a
--   target concept $c : X \to Y$, and a sample $S = (x_1,\dots,x_m)$, the empirical error of
--   $h$ is
--   $$\hat R_S(h) = \frac1m \sum_{i=1}^m \mathbb{1}_{h(x_i)\ne c(x_i)},$$
--   the average error of $h$ over the sample $S$, as opposed to $R(h)$'s expectation under $D$.
--
--   **Formalization Note.** `EmpiricalError S c h` is the cardinality of
--   `{i : Fin m | h (S i) ≠ c (S i)}` divided by `(m : ℝ)`, matching the displayed sum/count
--   exactly (`noncomputable`, via classical decidability of the disagreement predicate).
-- source:
--   Mohri, Rostamizadeh & Talwalkar, Foundations of Machine Learning, 2nd ed., MIT Press 2018, p. 10, Definition 2.2 (PDF p. 27)

import Mathlib

open Classical MeasureTheory

namespace FoundationsML.PAC

/-- The empirical error of a hypothesis `h : X → Y` on a sample `S : Fin m → X` against a
target concept `c : X → Y` (Mohri, Rostamizadeh & Talwalkar, *Foundations of Machine
Learning*, 2nd ed., MIT Press 2018, Definition 2.2, p. 10, PDF p. 27):
`R̂_S(h) = (1/m) ∑_{i=1}^m 1[h(x_i) ≠ c(x_i)]`, the average error of `h` over the sample. -/
noncomputable def EmpiricalError {X Y : Type*} {m : ℕ} (S : Fin m → X) (c h : X → Y) : ℝ :=
  ((Finset.univ.filter (fun i : Fin m => h (S i) ≠ c (S i))).card : ℝ) / (m : ℝ)

end FoundationsML.PAC



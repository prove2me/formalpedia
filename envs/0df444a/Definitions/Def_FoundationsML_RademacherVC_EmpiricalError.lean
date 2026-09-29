-- Prove2me | Definitions.Def_FoundationsML_RademacherVC_EmpiricalError
-- name    : FoundationsML_RademacherVC_EmpiricalError
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-19T21:10:33.710982+00:00
-- url     : https://prove2.me/theorems/c1e07c76-b396-4ec3-b857-506a4cc4ebe4
-- title:
--   Empirical error of a hypothesis on a sample
-- statement:
--   **Definition 2.2 (Empirical error), p. 10, PDF p. 27.** Given a hypothesis $h : X \to Y$, a
--   target concept $c : X \to Y$, and a sample $S=(x_1,\dots,x_m)$, the empirical error is
--   $\hat R_S(h) = \frac1m\sum_{i=1}^m \mathbb 1_{h(x_i)\ne c(x_i)}$. Restated locally in this
--   chunk's `RademacherVC` namespace (identical to chunk `02-pac`'s own copy).
--
--   **Formalization Note.** `EmpiricalError S c h` is the count of disagreeing indices divided
--   by `(m:ℝ)`.
-- source:
--   Mohri, Rostamizadeh & Talwalkar, Foundations of Machine Learning, 2nd ed., MIT Press 2018, p. 10, Definition 2.2 (PDF p. 27)

import Mathlib

open Classical MeasureTheory

namespace FoundationsML.RademacherVC

/-- The empirical error of a hypothesis `h : X → Y` on a sample `S : Fin m → X` against a
target concept `c : X → Y` (Mohri, Rostamizadeh & Talwalkar, *Foundations of Machine
Learning*, 2nd ed., MIT Press 2018, Definition 2.2, p. 10, PDF p. 27, restated locally for
this chapter since drafts cannot import another chunk's draft module):
`R̂_S(h) = (1/m) ∑_{i=1}^m 1[h(x_i) ≠ c(x_i)]`. -/
noncomputable def EmpiricalError {X Y : Type*} {m : ℕ} (S : Fin m → X) (c h : X → Y) : ℝ :=
  ((Finset.univ.filter (fun i : Fin m => h (S i) ≠ c (S i))).card : ℝ) / (m : ℝ)

end FoundationsML.RademacherVC



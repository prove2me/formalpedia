-- Prove2me | Definitions.Def_MeanOnlyProphet_IsStepRate
-- name    : MeanOnlyProphet_IsStepRate
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T03:22:00.785024+00:00
-- url     : https://prove2.me/theorems/f4d1b907-2e7f-4cef-bce0-b8bc0563c875
-- title:
--   Step rates of the proof of Lemma A.4
-- statement:
--   A real function $q$ is a **step rate** if on $[0,1]$ it is
--   1. nonnegative and nondecreasing;
--   2. a step function with finitely many jumps (equivalently, it takes finitely many values on $[0,1]$), hence bounded;
--   3. right-continuous on $[0,1)$, with $q(1)=q(1^-)$.
--
--   These are the standing assumptions of Lemmas A.5–A.9, under which the paper first proves Lemma A.4 before extending it to all nondecreasing rates.
--
--   **Formalization Note** Right-continuity on $[0,1)$ is continuity within $[t,\infty)$; $q(1)=q(1^-)$ is continuity within $(-\infty,1)$ at $1$.
-- source:
--   Feng, Jin, Wu, Xiang, Mean-only Prophet Inequalities, arXiv:2610.24711 (held version, sha256 c68bfec4…74e93a), proof outline of Lemma A.4, p.30 (PDF p.31)

import Mathlib

namespace MeanOnlyProphet

/-- **Bounded nonnegative nondecreasing step rate with finitely many jumps, right-continuous on
`[0,1)`, with `q(1) = q(1⁻)`.** Feng, Jin, Wu, Xiang, *Mean-only Prophet Inequalities*,
arXiv:2610.24711 (held version, sha256 c68bfec4…), proof outline of Lemma A.4, p.30 (PDF p.31): "we first
consider the case when q is a bounded, nonnegative, nondecreasing step function with finitely many
jumps. … We therefore take q to be right-continuous on [0, 1) and set q(1) = q(1−)."

These are the standing assumptions of Lemmas A.5–A.9.

**Formalization Note.** Everything is required on `[0,1]` only. For a nondecreasing function, "step
function with finitely many jumps" is the same as having finitely many values on `[0,1]`; boundedness
follows from it. Right-continuity on `[0,1)` is `ContinuousWithinAt q (Set.Ici t) t`, and
`q(1) = q(1⁻)` is left-continuity at `1`. -/
def IsStepRate (q : ℝ → ℝ) : Prop :=
  (∀ t ∈ Set.Icc (0 : ℝ) 1, 0 ≤ q t) ∧ MonotoneOn q (Set.Icc 0 1) ∧
    (q '' Set.Icc 0 1).Finite ∧
    (∀ t ∈ Set.Ico (0 : ℝ) 1, ContinuousWithinAt q (Set.Ici t) t) ∧
    ContinuousWithinAt q (Set.Iio 1) 1

end MeanOnlyProphet



-- Prove2me | Definitions.Def_TeschlODE_Frobenius_HasPoleOfOrderAtMost
-- name    : TeschlODE_Frobenius_HasPoleOfOrderAtMost
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-28T11:16:05.571513+00:00
-- url     : https://prove2.me/theorems/380795ff-8039-43ac-9ae6-35484ff2a08b
-- title:
--   Pole of order at most k at z = 0 (§4.2, after Eq. (4.21))
-- statement:
--   A function $f$ that is holomorphic in a punctured disc $0 < |z| < r$ has a Laurent expansion $f(z) = \sum_{j \in \mathbb{Z}} f_j z^j$ (4.21). It has **a pole of order at most $k$** at $0$ ($k \in \mathbb{N}_0$) if $f_j = 0$ for all $j < -k$; order at most $0$ means the singularity is removable. Equivalently: there is a function $g$ analytic at $0$ with
--   $$z^k f(z) = g(z) \qquad \text{for all } z \neq 0 \text{ near } 0.$$
--
--   **Formalization Note.** The Lean definition is the second form: `∃ g, AnalyticAt ℂ g 0 ∧ ∀ᶠ z in 𝓝[≠] 0, z ^ k * f z = g z`. It includes that $f$ is holomorphic on some punctured neighbourhood of $0$ (isolated singularity).
-- source:
--   Teschl, Ordinary Differential Equations and Dynamical Systems (author's preliminary version of AMS GSM 140, 2012), p. 116, §4.2, Eq. (4.21) and the following definition of the order of a pole

import Mathlib

namespace TeschlODE.Frobenius

/-- Teschl §4.2, p. 116 (after (4.21)): `f` has (at most) a pole of order `k` at `z = 0`, i.e. its
Laurent series at `0` has no coefficient `f_j` with `j < -k`. Equivalently, `z ^ k * f z` agrees on
a punctured neighbourhood of `0` with a function analytic at `0`. Order at most `0` means a
removable singularity; the condition includes that `0` is an isolated singularity of `f`. -/
def HasPoleOfOrderAtMost (f : ℂ → ℂ) (k : ℕ) : Prop :=
  ∃ g : ℂ → ℂ, AnalyticAt ℂ g 0 ∧ ∀ᶠ z in nhdsWithin (0 : ℂ) {0}ᶜ, z ^ k * f z = g z

end TeschlODE.Frobenius



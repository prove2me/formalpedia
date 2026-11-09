-- Prove2me | Definitions.Def_KSPolySign_beta
-- name    : KSPolySign_beta
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T22:28:22.647649+00:00
-- url     : https://prove2.me/theorems/2a5beac6-353e-45f8-9878-3a88ab75d416
-- title:
--   The coordinate weight $\beta(t) = \sqrt{1-t^2}$
-- statement:
--   For $t\in[-1,1]$ the **coordinate weight** is
--   $$\beta(t) = \sqrt{1-t^2}.$$
--   It vanishes at the signed coordinates $t=\pm1$ and equals $1$ at $t=0$; in the potential it scales how much the coupling of coordinate $i$ contributes.
--
--   **Formalization Note** Defined on all of $\mathbb R$ with Lean's convention $\sqrt{x}=0$ for $x<0$; every statement evaluates it on $[-1,1]$.
-- source:
--   Z. Song, S. Yue, Polynomial Time Algorithms for the Kadison-Singer Problem, arXiv:2609.19794 (held version, sha256 47d4aaa5…), Definition 3.2, p.18 (PDF p.18)

import Mathlib
open Matrix
open scoped ComplexOrder

namespace KSPolySign

/-- **The coordinate weight `β(t) = √(1 − t²)`.** Song–Yue, *Polynomial Time Algorithms for the Kadison-Singer Problem*, arXiv:2609.19794 (held version, sha256 47d4aaa5…), Definition 3.2, p.18 (PDF p.18): "For
t ∈ [−1, 1], define β(t) := √(1 − t²)".

**Formalization Note** Defined on all of `ℝ`; outside `[−1, 1]` Lean's `Real.sqrt` returns `0`. Every
statement of the mission evaluates `β` at coordinates in `[−1, 1]`. -/
noncomputable def beta (t : ℝ) : ℝ := Real.sqrt (1 - t ^ 2)

end KSPolySign



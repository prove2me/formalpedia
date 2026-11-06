-- Prove2me | Definitions.Def_LawLocalComp_Law
-- name    : LawLocalComp_Law
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T03:10:18.013703+00:00
-- url     : https://prove2.me/theorems/947907f9-3efe-4caa-b99e-7e217e9feec4
-- title:
--   Finite nonnegative law
-- statement:
--   A **law** is a finitely supported probability distribution on $[0,\infty)$: a weight function $X:\mathbb R\to[0,\infty)$ with finite support contained in $[0,\infty)$ and $\sum_x X(x)=1$, where $X(x)=\mathbb P(X=x)$.
--
--   All laws of the paper are finite and nonnegative, so every expectation is a finite sum over the support.
--
--   **Formalization Note** This is the published `NondualOpt.FinLaw` on the set $[0,\infty)\subseteq\mathbb R$. Atoms and masses are real numbers; rationality is the separate predicate `IsRatLaw`.
-- source:
--   Mahboub–Rahgoshay, Optimal Law-Local Compression for Stochastic Loads, STOC 2027 submission (manuscript of Oct. 29, 2026, sha256 5f71501c…aa873), §1, p.2

import Mathlib
import Definitions.Def_NondualOpt_FinLaw

namespace LawLocalComp

/-- **A finite nonnegative law.**
Mahboub–Rahgoshay, *Optimal Law-Local Compression for Stochastic Loads*, STOC 2027
submission manuscript of Oct. 29, 2026 (sha256 5f71501c…aa873), §1, p.2 ("A law-local map sees one finite nonnegative rational law").

`Law` is the published `NondualOpt.FinLaw` on the half-line `[0, ∞)`: a finitely supported weight
function `w : ℝ →₀ ℝ`, nonnegative, with support in `[0, ∞)` and total mass `1`. `X.w x` is the
probability of the atom `x`.

**Formalization Note.** Laws are finitely supported, so every expectation is a finite sum over
`X.w.support`. Laws are real-valued; rationality of atoms and masses is the separate predicate
`IsRatLaw`, so that statements about outputs of arbitrary maps can range over real laws. -/
abbrev Law : Type := NondualOpt.FinLaw (Set.Ici (0 : ℝ))

end LawLocalComp



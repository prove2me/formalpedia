-- Prove2me | Definitions.Def_NoPerfectRandComp_Supplement_RS
-- name    : NoPerfectRandComp_Supplement_RS
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T10:13:32.684693+00:00
-- url     : https://prove2.me/theorems/d658aa31-fa8b-43fa-b653-4e7acc2a5485
-- title:
--   Sabotage complexity $\mathrm{RS}(h)$
-- statement:
--   For a possibly partial Boolean function $h$, the task $h_{\mathrm{sab}}$ is: given a sabotaged input $z$ for $h$, output which wildcard symbol ($*$ or $\dagger$) occurs in it. The **sabotage complexity** $\mathrm{RS}(h)$ is the least worst-input expected cost of a zero-error randomised algorithm for $h_{\mathrm{sab}}$:
--   $$
--   \mathrm{RS}(h) = \inf_{A}\ \sup_{z\ \text{sabotaged}}\ \mathrm{cost}(A,z),
--   $$
--   the infimum over randomised algorithms $A$ (distributions over decision trees reading letters of $\{0,1,*,\dagger\}$) that output the correct wildcard with probability one on every sabotaged $z$, and $\mathrm{cost}(A,z)$ the expected number of queries. This is the paper's formulation, equivalent up to constants to that of Ben-David and Kothari.
--
--   **Formalization Note** Valued in $[0,\infty]$; the cost is the base mission's `expCost`. Algorithms are distributions over finite trees, which loses nothing: a zero-error algorithm halts almost surely on the finitely many sabotaged inputs, so with its coins fixed the tree may be cut below the largest depth reached on them.
-- source:
--   Meiburg, No Perfect Randomized Composition, arXiv:2610.31638 (held version, sha256 5122a74a…), §2.2, p.4

import Mathlib
import Definitions.Def_NoPerfectRandComp_PartialFn
import Definitions.Def_NoPerfectRandComp_expCost
import Definitions.Def_QAlgorithms_Defs_Classical
import Definitions.Def_NoPerfectRandComp_Supplement_SabSym
import Definitions.Def_NoPerfectRandComp_Supplement_IsSabotaged
open scoped ENNReal

namespace NoPerfectRandComp

namespace Supplement

open Classical in
/-- Sabotage complexity `RS(h)` (Meiburg, *No Perfect Randomized Composition*, arXiv:2610.31638 (held version, sha256 5122a74a…aeae3), §2.2, p.4): the task `h_sab` is to output which
wildcard symbol occurs in a sabotaged input `z` (`IsSabotaged`), and `RS(h)` is the least
worst-input expected cost of a zero-error randomised algorithm for `h_sab`:
`RS(h) = inf_A sup_{z sabotaged} cost(A, z)` over randomised algorithms `A` (distributions over
decision trees querying letters of `{0,1,∗,†}`) that output the correct wildcard with probability
one on every sabotaged `z`.

**Formalization Note** This is the paper's formulation ("equivalent up to constants to that of
[9]"). The cost is the published `expCost` (expected number of queries), valued in `ℝ≥0∞`. The
correct answer is `star` if `∗` occurs in `z` and `dagger` otherwise; a sabotaged input contains
a wildcard (else `x = y`), and only one kind. Algorithms are distributions over finite trees: a
zero-error algorithm halts on the finitely many sabotaged inputs almost surely, so fixing its coins
and cutting each tree below the largest depth reached on a sabotaged input changes nothing. -/
noncomputable def RS {ι : Type} (h : PartialFn ι) : ℝ≥0∞ :=
  ⨅ (A : QAlgorithms.RandDecisionTree ι SabSym SabSym)
    (_ : ∀ z, IsSabotaged h z →
      QAlgorithms.successProb A z
        (if ∃ i, z i = SabSym.star then SabSym.star else SabSym.dagger) = 1),
    ⨆ (z : ι → SabSym) (_ : IsSabotaged h z), expCost A z

end Supplement

end NoPerfectRandComp



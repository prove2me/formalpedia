-- Prove2me | Definitions.Def_NoPerfectRandComp_Reps
-- name    : NoPerfectRandComp_Reps
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:43:15.8621+00:00
-- url     : https://prove2.me/theorems/57f0397b-901c-4d62-a5c4-d8b734bb85c9
-- title:
--   Randomized query complexity $\mathrm{R}_\varepsilon(f)$ and $\mathrm{R}(f)=\mathrm{R}_{1/3}(f)$
-- statement:
--   A **randomised algorithm** is a probability distribution over deterministic decision trees. For a possibly partial Boolean function $f$ and $x \in \mathrm{Dom}(f)$, write $\mathrm{err}(A,x) = \Pr[A(x) \ne f(x)]$.
--
--   The **bounded-error randomized query complexity** $\mathrm{R}_\varepsilon(f)$ is the least worst-case depth of an algorithm with error at most $\varepsilon$ everywhere:
--   $$
--   \mathrm{R}_\varepsilon(f) = \min\{d : \exists A,\ \text{every tree of } A \text{ makes at most } d \text{ queries on every input, and } \mathrm{err}(A,x) \le \varepsilon \ \forall x \in \mathrm{Dom}(f)\},
--   $$
--   and $\mathrm{R}(f) = \mathrm{R}_{1/3}(f)$. For a total function we write $\mathrm{R}(f)$ of its total partial-function form.
--
--   $\mathrm{R}$ is the complexity measure of the whole mission: the goal compares $\mathrm{R}(f\circ g)$ with $\mathrm{R}(f)\mathrm{R}(g)$.
--
--   **Formalization Note** Decision trees, distributions over them, the depth bound and output probabilities are the published layer `QAlgorithms_Defs_Classical` (`RandDecisionTree`, `RandMakesAtMost`, `successProb`). The depth is counted on every input, not only on the domain (equivalent, by truncation). This is the worst-case-depth measure, not the expected-cost measure $\bar{\mathrm{R}}_\varepsilon$ defined on the same page. For finitely many coordinates the defining set contains the number of coordinates (query everything), so the minimum exists.
-- source:
--   Meiburg, No Perfect Randomized Composition, arXiv:2610.31638 (held version, sha256 5122a74a…), §2.1, p.4

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Classical
import Definitions.Def_NoPerfectRandComp_PartialFn

namespace NoPerfectRandComp

/-- Bounded-error randomized query complexity `R_ε(f)` (Meiburg, *No Perfect Randomized Composition*, arXiv:2610.31638 (held version, sha256 5122a74a…aeae3), §2.1, p.4): the least
worst-case depth `d` of a randomised algorithm — a probability distribution over deterministic
decision trees (`QAlgorithms.RandDecisionTree`) — whose every tree makes at most `d` queries, and
whose error `err(A, x) = Pr[A(x) ≠ f(x)]` is at most `ε` at every `x ∈ Dom(f)`.

**Formalization Note** The depth bound `RandMakesAtMost A d` is counted on every input, not only
on `Dom(f)` (equivalent: truncating a tree below depth `d` off the domain changes nothing on it).
The error is quantified over `Dom(f)` only. For finite `ι` the set is nonempty (the tree that
queries every coordinate), so the infimum is attained. This is the worst-case-depth measure
`R_ε`, not the expected-cost measure `R̄_ε` of the same page. -/
noncomputable def Reps {ι : Type} (ε : ℝ) (f : PartialFn ι) : ℕ :=
  sInf {d : ℕ | ∃ A : QAlgorithms.RandDecisionTree ι Bool Bool,
    QAlgorithms.RandMakesAtMost A d ∧ ∀ x ∈ f.dom, QAlgorithms.successProb A x (!f.val x) ≤ ε}

/-- Randomized query complexity `R(f) = R_{1/3}(f)` (Meiburg, *No Perfect Randomized Composition*, arXiv:2610.31638 (held version, sha256 5122a74a…aeae3), §2.1, p.4). -/
noncomputable abbrev R {ι : Type} (f : PartialFn ι) : ℕ :=
  Reps (1 / 3) f

/-- `R(f)` of a total Boolean function `f : {0,1}^ι → {0,1}` (Meiburg, *No Perfect Randomized Composition*, arXiv:2610.31638 (held version, sha256 5122a74a…aeae3), §2.1, p.4). -/
noncomputable abbrev Rt {ι : Type} (f : (ι → Bool) → Bool) : ℕ :=
  R (PartialFn.total f)

end NoPerfectRandComp



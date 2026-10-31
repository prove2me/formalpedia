-- Prove2me | Definitions.Def_TRSHolderKL_projSet
-- name    : TRSHolderKL_projSet
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:49:55.550018+00:00
-- url     : https://prove2.me/theorems/aa1ad082-f46e-497a-b5f3-64d8ec6f92fa
-- title:
--   The (set-valued) projection $\Pi_C(x)$
-- statement:
--   For a set $C\subseteq\mathbb R^n$ and a point $x$, $\Pi_C(x)$ is the set of points of $C$ nearest to $x$:
--   $$
--   \Pi_C(x)=\{v\in C:\ \|x-v\|=\operatorname{dist}(x,C)\}.
--   $$
--
--   **Formalization Note** The paper writes $\{v\in\mathbb R^n \mid \|x-v\|=\operatorname{dist}(x,C)\}$ without the condition $v\in C$; read literally that is a whole sphere around $x$, and Lemma 3.10 would be false (see that item). The nearest points of $C$, which is what the paper uses, are taken.
-- source:
--   Jiang and Li, Hölderian error bounds and Kurdyka-Łojasiewicz inequality for the trust region subproblem, arXiv:1911.11955v2, Notation, p.3

import Mathlib
import Definitions.Def_RBMSensitivity_E
open RBMSensitivity (E)

namespace TRSHolderKL

/-- The set-valued projection `Π_C(x)` onto a set `C`, the points of `C` nearest to `x`,
Jiang and Li, arXiv:1911.11955v2, Notation, p.3.

**Formalization Note.** The page writes `{v ∈ ℝⁿ | ‖x − v‖ = dist(x, C)}` without `v ∈ C`;
read literally that is a whole sphere around `x`, and Lemma 3.10 item 1 (`Π_{S₀}(x) = S₀`)
would be false. The intended set of nearest points of `C` is taken. -/
def projSet {n : ℕ} (C : Set (E n)) (x : E n) : Set (E n) :=
  {v | v ∈ C ∧ ‖x - v‖ = Metric.infDist x C}

end TRSHolderKL



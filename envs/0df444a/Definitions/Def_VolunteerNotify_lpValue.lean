-- Prove2me | Definitions.Def_VolunteerNotify_lpValue
-- name    : VolunteerNotify_lpValue
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T05:37:42.666204+00:00
-- url     : https://prove2.me/theorems/210ff252-27d8-4a44-baa5-62eb33ad5216
-- title:
--   (LP), Definition 2 — the feasible set $\mathcal P$ and the benchmark $\mathrm{LP}_{\mathcal I}$
-- statement:
--   A vector $x\in\mathbb R^{V\times S\times T}$ belongs to the **feasible set** $\mathcal P$ if for all $v,s,t$
--   $$
--   0\le x_{v,s,t}\le 1 \tag{1}
--   $$
--   and for all $v,t$
--   $$
--   1\ge\sum_{\tau=1}^t\sum_{s=1}^S\lambda_{s,\tau}x_{v,s,\tau}\bigl(1-G(t-\tau)\bigr). \tag{2}
--   $$
--   The **benchmark** is the value of the program
--   $$
--   \mathrm{LP}_{\mathcal I}=\max_{x\in\mathcal P}\ \sum_{t=1}^T\sum_{s=1}^S\lambda_{s,t}\min\Bigl\{\sum_{v=1}^V x_{v,s,t}p_{v,s},\,1\Bigr\}.
--   $$
--   Competitive ratios in the source are measured against this value. `RowFeasible` is the part of the constraints for one volunteer, which is also the constraint set of (SQ-v).
--
--   **Formalization Note** The maximum is written as a supremum of the image of $\mathcal P$; $\mathcal P$ is compact and contains $0$, so the supremum is attained.
-- source:
--   Manshadi, Rodilitz, Online Policies for Efficient Volunteer Crowdsourcing, arXiv:2002.08474v7, (LP), (1), (2), p.11; Definition 2, p.12; (SQ-v), p.14

import Mathlib
import Definitions.Def_VolunteerNotify_mdhr
import Definitions.Def_VolunteerNotify_Instance

namespace VolunteerNotify

variable {V S T : ℕ}

/-- The constraints of (LP) for one volunteer, Manshadi–Rodilitz, arXiv:2002.08474v7, p.11:
(1) `0 ≤ y_{s,t} ≤ 1` for all `s, t`, and (2) `1 ≥ ∑_{τ ≤ t} ∑_s λ_{s,τ} y_{s,τ} (1 − G(t − τ))`
for all `t`. These are also the constraints of (SQ-v), p.14.

**Formalization Note.** With `Fin` indices the difference of paper indices `t − τ` is the
difference of the `Fin` values; `τ ≤ t` on the sum, so the natural subtraction is exact. -/
def RowFeasible (I : Instance V S T) (y : Fin S → Fin T → ℝ) : Prop :=
  (∀ s t, 0 ≤ y s t ∧ y s t ≤ 1) ∧
    ∀ t : Fin T,
      ∑ τ ∈ Finset.Iic t, ∑ s, I.lam s τ * y s τ * (1 - cdf I.g ((t : ℕ) - (τ : ℕ))) ≤ 1

/-- The feasible set `P`, arXiv:2002.08474v7, Definition 2, p.12: `x ∈ ℝ^{V×S×T}` satisfying
constraints (1) and (2) for every volunteer. -/
def feasibleSet (I : Instance V S T) : Set (Decision V S T) :=
  {x | ∀ v, RowFeasible I (x v)}

/-- The piecewise-linear objective of (LP), arXiv:2002.08474v7, p.11:
`∑_t ∑_s λ_{s,t} min{∑_v x_{v,s,t} p_{v,s}, 1}`. -/
noncomputable def lpObjective (I : Instance V S T) (x : Decision V S T) : ℝ :=
  ∑ t, ∑ s, I.lam s t * min (∑ v, x v s t * I.p v s) 1

/-- The benchmark `LP_I`, arXiv:2002.08474v7, (LP), p.11: the optimal value of `lpObjective` over
`P`.

**Formalization Note.** The printed `max` is a supremum here. `P` contains `0` and is compact and
the objective is continuous and at most `T`, so the set is nonempty and bounded and the supremum
is attained. -/
noncomputable def lpValue (I : Instance V S T) : ℝ :=
  sSup (lpObjective I '' feasibleSet I)

end VolunteerNotify



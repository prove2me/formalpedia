-- Prove2me | Definitions.Def_StableVotingDistortion_HasDistortionAtMost
-- name    : StableVotingDistortion_HasDistortionAtMost
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:01:21.634204+00:00
-- url     : https://prove2.me/theorems/74502cab-4a67-4f98-ac27-23d557f95b1a
-- title:
--   Social cost and distortion at most $B$
-- statement:
--   For a pseudometric $d$, the **social cost** of a candidate is $\mathrm{cost}_d(a)=\mathbb E_{v\sim V}[d(v,a)]$, and that of a lottery $D$ is $\mathrm{cost}_d(D)=\mathbb E_{a\sim D}[\mathrm{cost}_d(a)]$.
--
--   The lottery $D$ **has distortion at most $B$** in the election $E$ if, for every pseudometric $d$ consistent with $E$ and every candidate $a$,
--   $$\mathrm{cost}_d(D)\le B\cdot\mathrm{cost}_d(a).$$
--
--   This compares the voting rule's output with the best candidate in every metric the rankings allow.
--
--   **Formalization Note** The paper's distortion is the ratio $\mathrm{cost}_d(f(E))/\min_a\mathrm{cost}_d(a)$. The inequality has no division. It agrees with the ratio when the minimum is positive, and when the minimum is $0$ it forces $\mathrm{cost}_d(D)=0$.
-- source:
--   Cai, Frank, Hastings, Ramakrishnan, Wang, Ye, Stable Voting Rules on the Edge of Optimal Metric Distortion, arXiv:2609.08259 (held version, sha256 cfdd5f3d…), §2, p.6

import Mathlib
import Definitions.Def_PctDistortion_Election
import Definitions.Def_StableVotingDistortion_IsPseudometric
import Definitions.Def_StableVotingDistortion_voterMean

set_option autoImplicit false

open PctDistortion

namespace StableVotingDistortion

/-- The **social cost** of a candidate, `cost_d(a) = E_{v ∼ V}[d(v, a)]`.

Cai et al., arXiv:2609.08259 (held version, sha256 cfdd5f3d…), §2, p.6. -/
noncomputable def candCost {V C : Type} [Fintype V] (d : V ⊕ C → V ⊕ C → ℝ) (a : C) : ℝ :=
  voterMean (fun v => d (Sum.inl v) (Sum.inr a))

/-- The **social cost** of a lottery, `cost_d(D) = E_{a ∼ D}[cost_d(a)]`.

Cai et al., arXiv:2609.08259 (held version, sha256 cfdd5f3d…), §2, p.6. -/
noncomputable def lotteryCost {V C : Type} [Fintype V] [Fintype C]
    (d : V ⊕ C → V ⊕ C → ℝ) (D : C → ℝ) : ℝ :=
  ∑ a, D a * candCost d a

/-- The lottery `D` **has distortion at most `B`** in the election `E`: for every consistent
pseudometric `d` and every candidate `a`, `cost_d(D) ≤ B · cost_d(a)`.

Cai et al., arXiv:2609.08259 (held version, sha256 cfdd5f3d…), §2, p.6: "distortion(f) := sup_E sup_{d consistent with E}
cost_d(f(E)) / min_{a∈C} cost_d(a)."

**Formalization Note.** This is the printed ratio bound written as an inequality, with no division.
The two agree when `min_a cost_d(a) > 0`. When the minimum cost is `0` the inequality forces
`cost_d(D) = 0`, where the printed ratio is `0/0` or `x/0`. -/
def HasDistortionAtMost {V C : Type} [Fintype V] [Fintype C] (E : Election V C)
    (D : C → ℝ) (B : ℝ) : Prop :=
  ∀ d : V ⊕ C → V ⊕ C → ℝ, IsPseudometric d → Consistent E d →
    ∀ a : C, lotteryCost d D ≤ B * candCost d a

end StableVotingDistortion



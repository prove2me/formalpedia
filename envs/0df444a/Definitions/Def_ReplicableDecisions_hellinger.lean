-- Prove2me | Definitions.Def_ReplicableDecisions_hellinger
-- name    : ReplicableDecisions_hellinger
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:02:45.587219+00:00
-- url     : https://prove2.me/theorems/b0a27f80-a189-4243-b19f-d19d0b8fcec8
-- title:
--   Hellinger distance $h$ with the factor $\tfrac12$, and total variation
-- statement:
--   For probability vectors $P,Q$ on a finite set $\mathcal Z$, the Bhattacharyya coefficient is $\mathrm{BC}(P,Q)=\sum_{z}\sqrt{P(z)Q(z)}$, and the Hellinger distance is normalized by
--
--   $$
--   h^2(P,Q)=1-\mathrm{BC}(P,Q)=\tfrac12\bigl\|\sqrt P-\sqrt Q\bigr\|_2^2 .
--   $$
--
--   It takes values in $[0,1]$. The total variation distance is $\mathrm{TV}(P,Q)=\tfrac12\sum_z|P(z)-Q(z)|$.
--
--   These two quantities are the metric geometry of the mission: every constant, the factor $4608$ included, depends on this normalization.
--
--   **Formalization Note** The coefficient is the published `FuchsVdGraaf.bhattacharyya`. The definition takes $h^2=1-\mathrm{BC}$; the second form of $h^2$ is a proved sanity check. The factor $\tfrac12$ in TV is fixed by the identity $1-\mathrm{TV}(P,Q)=\sum_z\min\{P(z),Q(z)\}$ used on p.15 of the paper.
-- source:
--   Chen, Replicable Decisions in Finite Experiments, STOC 2027 submission (sha256 52d181db…), §2 "Hellinger geometry", p.9 (PDF p.11)

import Mathlib
import Definitions.Def_FuchsVdGraaf_bhattacharyya

namespace ReplicableDecisions

/-- **Squared Hellinger distance, normalized.** Chen, *Replicable Decisions in Finite Experiments*,
STOC 2027 submission (sha256 52d181db…), §2 "Hellinger geometry", p.9 (PDF p.11):
`h²(P, Q) = 1 − BC(P, Q)`, where `BC(P, Q) = ∑_{z∈Z} √(P(z)Q(z))`.

**Formalization Note.** `BC` is the published `FuchsVdGraaf.bhattacharyya`. This is the
normalization with the factor `½`, with values in `[0, 1]` on probability vectors; the identity
`h² = ½‖√P − √Q‖₂²` is a proved sanity check. -/
noncomputable def hellingerSq {α : Type} [Fintype α] (P Q : α → ℝ) : ℝ :=
  1 - FuchsVdGraaf.bhattacharyya P Q

/-- **Hellinger distance** `h(P, Q)`, the square root of `hellingerSq`. Chen, STOC 2027 submission
(sha256 52d181db…), §2, p.9 (PDF p.11). -/
noncomputable def hellinger {α : Type} [Fintype α] (P Q : α → ℝ) : ℝ :=
  Real.sqrt (hellingerSq P Q)

/-- Symmetry of `h`, which the Hellinger graphs need. -/
theorem hellinger_comm {α : Type} [Fintype α] (P Q : α → ℝ) : hellinger P Q = hellinger Q P := by
  simp [hellinger, hellingerSq, FuchsVdGraaf.bhattacharyya, mul_comm]

/-- **Total variation distance**, `TV(P, Q) = ½ ∑_z |P(z) − Q(z)|`. Chen, STOC 2027 submission
(sha256 52d181db…), §2, p.9 (PDF p.11).

**Formalization Note.** The page uses TV with its usual normalization; its own identity
`1 − TV(P, Q) = ∑ min{P, Q}` (proof of Proposition 3.10, p.15) fixes the factor `½`. -/
noncomputable def tv {α : Type} [Fintype α] (P Q : α → ℝ) : ℝ :=
  (1 / 2) * ∑ a, |P a - Q a|

end ReplicableDecisions



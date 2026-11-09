-- Prove2me | Definitions.Def_SkipListConc_incrementPMF
-- name    : SkipListConc_incrementPMF
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T12:51:27.581053+00:00
-- url     : https://prove2.me/theorems/e9002433-badb-4945-bd85-90ae95a5771d
-- title:
--   Distribution of the increment $\Delta_c=J_c+G$
-- statement:
--   For a jump law $\mu_J$ and a source height $c$, the **increment** of Definition 1.1 when the gate opens at height $c$ is $\Delta_c=J_c+G$ with $J_c=J(c)+1\in\{1,\dots,K\}$ and $G\sim\mathrm{Geom}_0(1-p)$ independent. This is its distribution as point masses $r\mapsto\Pr[\Delta_c=r]$. At $c=0$ it is the law of the initial height $J_0+G_0$.
-- source:
--   Kapoor–Tanveer, Counter-Free Self-Adjusting Skip Lists: Concentration Bounds, STOC 2027 submission (manuscript sha256 f82c3d35…), §1.1, p.6; Lemma 3.2, p.16

import Mathlib
import Definitions.Def_SkipListConc_geom0

open MeasureTheory

namespace SkipListConc

/-- The distribution of the increment `Δ_c = J_c + G` of Definition 1.1 at source height `c`, as
point masses `r ↦ Pr[Δ_c = r]` (Kapoor–Tanveer, *Counter-Free Self-Adjusting Skip Lists:
Concentration Bounds*, STOC 2027 submission manuscript (sha256 f82c3d35…6dab6c), §1.1, p.6, and
Lemma 3.2, p.16). The jump table and the geometric have law `μJ ⊗ Geom₀(1 − p)`; the jump at
height `c` is `J c + 1`. At `c = 0` it is the law of the initial height `J₀ + G₀`. -/
noncomputable def incrementPMF (p : ℝ) {K : ℕ} (μJ : Measure (ℕ → Fin K)) (c : ℕ) (r : ℕ) : ℝ :=
  ((μJ.prod (geom0 p)) {q | ((q.1 c : ℕ) + 1) + q.2 = r}).toReal

end SkipListConc



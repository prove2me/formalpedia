-- Prove2me | Definitions.Def_LogSupermodularBIS_Main_Supplement_Sequential
-- name    : LogSupermodularBIS_Main_Supplement_Sequential
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T08:32:19.757288+00:00
-- url     : https://prove2.me/theorems/e4133817-d522-4607-83f1-03535e22769a
-- title:
--   History-dependent probability transitions and event total variation
-- statement:
--   Let $H$ be the measurable space of complete procedure histories or memory states. A sequential procedure has a shared initial probability law $\mu$ and measurable probability transition kernels $K_j(h,\cdot)$. The next transition can depend on the entire past. Its law after $t$ steps is
--   $$
--   \mu_0=\mu,\qquad \mu_{j+1}(A)=\int_H K_j(h,A)\,\mu_j(dh).
--   $$
--   Early termination is represented by identical absorbing steps. The definition imposes neither independent steps nor homogeneous transitions.
--
--   For probability measures $\mu,\nu$, the predicate that their total variation distance is at most $r$ is the equivalent event condition
--   $$
--   |\mu(A)-\nu(A)|\le r\qquad\text{for every measurable }A.
--   $$
--   Measurable output functions may forget the internal history. This interface supports accumulated simulation error on arbitrary measurable history spaces, without adding assumptions solely to obtain a maximal coupling.
-- source:
--   Jingcheng Liu, Yitong Yin, STOC 2027 submission #1385 (October 2026), p. 41 (PDF 42), Lemma A.5

import Mathlib

open MeasureTheory ProbabilityTheory

set_option autoImplicit false

namespace LogSupermodularBIS.Main.Supplement

/-- Event characterization of total variation at most `r` for probability measures. Quantifying
over measurable events avoids a real supremum on an empty or unbounded set. -/
def EventTVLE {H : Type*} [MeasurableSpace H] (μ ν : Measure H) (r : ℝ) : Prop :=
  ∀ A : Set H, MeasurableSet A → |(μ A).toReal - (ν A).toReal| ≤ r

/-- Law of a sequential procedure after `t` transitions. The state space is the complete
history/memory, so the kernels may depend on every earlier outcome; no independence or
homogeneity is imposed. Early termination is represented by absorbing kernels. -/
noncomputable def sequentialLaw {H : Type*} [MeasurableSpace H]
    (K : ℕ → Kernel H H) (μ : Measure H) : ℕ → Measure H
  | 0 => μ
  | t + 1 => (sequentialLaw K μ t).bind (K t)

end LogSupermodularBIS.Main.Supplement



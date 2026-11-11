-- Prove2me | Definitions.Def_ObliviousAdaptive172_Parallel_WeakStableCertifying
-- name    : ObliviousAdaptive172_Parallel_WeakStableCertifying
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T07:55:45.10602+00:00
-- url     : https://prove2.me/theorems/66d6b834-68e0-482e-96e3-aa64b67ee5da
-- title:
--   Definition 1.2 — weak stable-certifying primitive
-- statement:
--   Let $M$ be a legal history model, $P$ the exact monotone property, $W$ the configuration space and $\operatorname{valid}(h,w)$ its relaxed witness relation. The relaxed property is $P'(h)\iff\exists w,\operatorname{valid}(h,w)$, is monotone, and is implied by $P$. Fix size $n$, a finite horizon $m$, an actual primitive-work budget $T_A$, a runtime-confidence exponent $b$, and a seed law $\mu$.
--
--   For every legal, obliviously fixed history $h$ of length at most $m$, the primitive satisfies
--
--   $$
--   \Pr_\mu[\operatorname{work}(h)\le T_A]\ge1-n^{-b},\qquad
--   P(h)\Longrightarrow\Pr_\mu[\text{a valid relaxed configuration is returned on }h]\ge\tfrac12.
--   $$
--
--   Every non-“no” answer on every private tape is valid and remains valid, unchanged, on every legal continuation. The completeness bound is separate for each fixed history, with no simultaneous all-times success or deterministic completeness requirement. Initialization is action zero and belongs to the finite-run budget. Divergent computation has infinite work. This is exactly the input contract used by the parallel compiler; it contains no adaptive guarantee, no confidence amplification premise, and no deterministic runtime assumption.
-- source:
--   Shiri Chechik, Inbal Hadad, From Oblivious to Adaptive Adversaries: Black-Box Reductions for Monotone Dynamic Problems with Applications to Cuts, Distances, and Clustering, STOC 2027 submission #172 (October 2026), p. 2, Definition 1.2 (PDF p. 4)

import Mathlib
import Definitions.Def_ObliviousAdaptive172_Parallel_PrivateTapeExecution
set_option autoImplicit false

namespace ObliviousAdaptive172.Parallel

open MeasureTheory

/-- Definition 1.2, with the primitive's runtime confidence `b` independent of the
desired wrapper confidence. The completeness events are pointwise, not simultaneous.
There is no assertion about the wrapper or an adaptive execution in this contract. -/
def WeakStableCertifying {U W R Q : Type} [MeasurableSpace R]
    (M : HistoryModel U) (exactProperty : List U → Prop) (valid : List U → W → Prop)
    (μ : Measure R) (A : PrivateTapeExecution U W R Q) (n : ℕ) (b : ℝ)
    (T m : ℕ) : Prop :=
  M.Monotone exactProperty ∧
  M.Monotone (fun h => ∃ w, valid h w) ∧
  (∀ h, M.Legal h → exactProperty h → ∃ w, valid h w) ∧
  (∀ h, M.Legal h → h.length ≤ m →
    WithProbability μ (1 - (n : ℝ) ^ (-b)) (fun r => (machineRun A r h).work ≤ T)) ∧
  (∀ r h w, M.Legal h → h.length ≤ m → (machineRun A r h).answer = some w →
    valid h w ∧ M.Stable valid h w) ∧
  (∀ h, M.Legal h → h.length ≤ m → exactProperty h →
    WithProbability μ (1 / 2) (fun r =>
      ∃ w, (machineRun A r h).answer = some w ∧ valid h w))

end ObliviousAdaptive172.Parallel



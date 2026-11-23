-- Prove2me | Definitions.Def_NonuniformCompetitive_Snoopy_Supplement_knownCover
-- name    : NonuniformCompetitive_Snoopy_Supplement_knownCover
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T11:54:53.943752+00:00
-- url     : https://prove2.me/theorems/45c6bbc9-f685-4f7c-be04-968a32e66864
-- title:
--   Known optimal coverage with unordered work functions and minimum matching
-- statement:
--   Configurations use the published labelled maps only as coordinates. Their movement distance $D(s,t)$ is the minimum total movement over all server permutations, and $w_\sigma$ is the published unordered work function. A set $V$ is known to be covered precisely when
--   $$\forall s\ \exists t:\quad V\subseteq\operatorname{range}(t),\qquad
--   w_\sigma(t)+D(t,s)\le w_\sigma(s).$$
--   The dominating configuration $t$ may depend on $s$. No single chosen clairvoyant optimum, and no global diameter or minimum separation of the metric space, is substituted for this condition.
--
--   For positive finite server count the schedule-cost sets are nonempty and nonnegative on every finite request word. The minimum over permutations is finite and attained, including when servers coincide. This definition is used on arbitrary metric spaces by the normalization theorem.
-- source:
--   Karlin, Manasse, McGeoch, Owicki, Competitive Randomized Algorithms for Nonuniform Problems, Algorithmica 11 (1994), DOI 10.1007/BF01189993, Appendix, pp. 569–570

import Mathlib
import Definitions.Def_KServer_randomized
import Definitions.Def_KServer_workfunctionU

namespace NonuniformCompetitive.Snoopy.Supplement

open MeasureTheory

/-- Movement of an unlabelled configuration: minimize over all matchings of the
server labels. The finite set of permutations is nonempty, including when k = 0. -/
noncomputable def matchingCost {k : ℕ} {M : Type*} [MetricSpace M]
    (s t : KServer.Config k M) : ℝ :=
  Finset.univ.inf' Finset.univ_nonempty
    (fun e : Equiv.Perm (Fin k) => ∑ i, dist (s i) (t (e i)))

/-- Appendix, p.569: for EACH configuration s, SOME dominating configuration s'
covers V. Neither s' nor a particular clairvoyant optimum is fixed in advance. -/
def KnownCover {k : ℕ} {M : Type*} [MetricSpace M]
    (s₀ : KServer.Config k M) (σ : List M) (V : Set M) : Prop :=
  ∀ s : KServer.Config k M, ∃ t : KServer.Config k M,
    V ⊆ Set.range t ∧ KServer.workFnU s₀ σ t + matchingCost t s ≤ KServer.workFnU s₀ σ s

end NonuniformCompetitive.Snoopy.Supplement



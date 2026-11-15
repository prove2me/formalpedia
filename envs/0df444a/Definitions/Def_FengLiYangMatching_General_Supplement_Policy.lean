-- Prove2me | Definitions.Def_FengLiYangMatching_General_Supplement_Policy
-- name    : FengLiYangMatching_General_Supplement_Policy
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T03:19:19.116653+00:00
-- url     : https://prove2.me/theorems/4828f7ee-7063-4952-8171-bdd8a30c7930
-- title:
--   Randomized binary online policies and private seed
-- statement:
--   A binary online policy maps the previously observed items and its own past accept/reject decisions, the current item, and a private random seed to an accept/reject decision. The observation type is arbitrary, so timing information can be included when it is available. A single private seed $\xi$ is drawn independently of the environment, uniformly from $[0,1]$:
--
--   $$P:\bigl(\mathcal O\times\{0,1\}\bigr)^*\times\mathcal O\times[0,1]\longrightarrow\{0,1\}.$$
--
--   The seed may encode the policy's entire private random tape. No restriction to rational probabilities, deterministic rules, finite memory or Markov decisions is imposed. The interface supplies no future observation. Matching feasibility is enforced separately by the execution environment. This general binary-decision interface is separated from the graph-specific model for reuse.
-- source:
--   Yilong Feng, Haolong Li, Zonghan Yang, Improved Bounds for Online Matching with Random Edge Arrivals, STOC 2027 submission #1018 (October 2026), §1.1, p. 2; §5, p. 17.

import Mathlib

set_option autoImplicit false

namespace FengLiYangMatching.General.Supplement

/-- A binary online rule sees only its past observations and actual decisions, the
current observation, and one private uniform real seed. No future data is supplied. -/
abbrev BinaryPolicy (Observation : Type) :=
  List (Observation × Bool) → Observation → ℝ → Bool

/-- The private seed is independent of the environment and uniform on [0,1]. -/
noncomputable def seedLaw : MeasureTheory.Measure ℝ :=
  MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) 1)

end FengLiYangMatching.General.Supplement



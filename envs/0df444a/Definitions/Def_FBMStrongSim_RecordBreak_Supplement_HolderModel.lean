-- Prove2me | Definitions.Def_FBMStrongSim_RecordBreak_Supplement_HolderModel
-- name    : FBMStrongSim_RecordBreak_Supplement_HolderModel
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T22:25:14.523796+00:00
-- url     : https://prove2.me/theorems/ed494b85-07e9-4622-ae0c-a2c531791daf
-- title:
--   Homogeneous Hölder bounds on [0,1]
-- statement:
--   For a path $z:[0,1]\to E$ into a normed space, $\operatorname{HolderBound}(\alpha,C,z)$ means
--   $$\|z(t)-z(s)\|\le C(t-s)^\alpha\qquad(0\le s<t\le1).$$
--   This is the pointwise form of the paper's homogeneous Hölder seminorm bound. It retains meaningful bounds for paths with unbounded seminorm, rather than taking a real supremum with a default value.
--
--   Differences from the source:
--   - generalization: the real-valued Hölder seminorm for 0<α<1 on p. 13 → a pointwise bound into any normed additive group; reason: specializing the target to ℝ and 0<α<1 recovers the full source bound; the definition also supports the deterministic α=1 extension
--   - encoding: a supremum of increment quotients → an inequality for every ordered pair in [0,1]; reason: this expresses the complete seminorm bound without the default value of an unbounded real supremum
-- source:
--   Chen, Dong & Ni, ε-Strong simulation of fractional Brownian motion and related stochastic differential equations, arXiv:1902.07824v1, p. 13, α-Hölder norm

import Mathlib
import Definitions.Def_FBMStrongSim_RecordBreak_Model

namespace FBMStrongSim.RecordBreak.Supplement

/-- Pointwise form of the homogeneous Hölder seminorm bound on [0,1]. -/
def HolderBound {E : Type*} [NormedAddCommGroup E] (alpha C : ℝ) (x : ℝ → E) : Prop :=
  ∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ t ∈ Set.Icc (0 : ℝ) 1, s < t →
    ‖x t - x s‖ ≤ C * (t - s) ^ alpha

end FBMStrongSim.RecordBreak.Supplement



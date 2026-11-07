-- Prove2me | Definitions.Def_BlockSSM_trackerDim
-- name    : BlockSSM_trackerDim
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:23:39.067754+00:00
-- url     : https://prove2.me/theorems/c6bbf680-4145-42b3-80ba-917619e3d256
-- title:
--   Minimum hidden dimension $n_b(G)$
-- statement:
--   $n_b(G)$ is the minimum hidden dimension of a finite-state tracker of $G$ with block bound $b$ whose decoder tracks $G$, or $\infty$ if no such tracker exists. Dimension zero is allowed for the trivial group. It is the left-hand side of the mission's goal.
--
--   **Formalization Note** The minimum is an infimum in $\mathbb N\cup\{\infty\}$, where the infimum of the empty set is $\infty$.
-- source:
--   C. Geng, The State Complexity of Block-Diagonal State Space Models, STOC 2027 submission manuscript (sha256 f9071794…), Definition 1, p.2 (PDF p.3)

import Mathlib
import Definitions.Def_BlockSSM_Tracker_Tracks
import Definitions.Def_BlockSSM_Tracker_IsFiniteState

universe u

namespace BlockSSM

/-- **The minimum hidden dimension `n_b(G)`.** Geng, *The State Complexity of Block-Diagonal State Space Models*, STOC 2027 submission manuscript (sha256 f9071794…), Definition 1, p.2 (PDF p.3): "Let n_b(G) be its
minimum hidden dimension, or ∞ if no such tracker exists. We allow dimension zero for the trivial
group."

**Formalization Note.** The infimum is taken in `ℕ∞`, where `sInf ∅ = ⊤` is the paper's `∞`; on a
nonempty set of naturals it is the minimum. -/
noncomputable def trackerDim (G : Type u) [Group G] (b : ℕ∞) : ℕ∞ :=
  sInf {D : ℕ∞ | ∃ T : Tracker G b, T.Tracks ∧ T.IsFiniteState ∧ D = (T.hiddenDim : ℕ∞)}

end BlockSSM



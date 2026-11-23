-- Prove2me | Definitions.Def_CorruptRobustRL_Supervised_Supplement_Clip
-- name    : CorruptRobustRL_Supervised_Supplement_Clip
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T07:08:13.748135+00:00
-- url     : https://prove2.me/theorems/db8829eb-cfc5-4f44-ac90-56105eedf88e
-- title:
--   Clipping with equality retained
-- statement:
--   For real numbers $z$ and $\varepsilon$, define
--   $$\operatorname{clip}[z\mid\varepsilon]=\begin{cases}z,&z\ge\varepsilon,\\0,&z<\varepsilon.\end{cases}$$
--   This threshold operation retains equality. It removes small errors in the gap-dependent decomposition; it does not replace them by the threshold.
-- source:
--   Lykouris, Simchowitz, Slivkins & Sun, Corruption-robust exploration in episodic reinforcement learning, arXiv:1911.08689v4, p. 43, clipping operator

import Mathlib

namespace CorruptRobustRL.Supervised.Supplement

/-- clip[x | ε] = x 1{x ≥ ε}; equality at the threshold is retained (p. 43). -/
noncomputable def clip (x ε : ℝ) : ℝ := if ε ≤ x then x else 0

end CorruptRobustRL.Supervised.Supplement



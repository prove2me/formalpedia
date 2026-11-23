-- Prove2me | Definitions.Def_CorruptRobustRL_Supervised_Supplement_ClippedErrors
-- name    : CorruptRobustRL_Supervised_Supplement_ClippedErrors
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T07:09:52.144584+00:00
-- url     : https://prove2.me/theorems/fbab9d32-170e-413a-9f7a-7c5b39ed49fe
-- title:
--   Checked and squared clipped errors, (C.6)–(C.7)
-- statement:
--   Let $\overline{\operatorname{Err}}(x,a)=\min\{H,\operatorname{Err}(x,a)\}$, and let $\check g_h(x,a)$ and $\check g_{\min,\mathrm{low}}$ be the effective thresholds of (C.5). Define
--   $$\check{\operatorname{Err}}_h(x,a)=\operatorname{clip}[\overline{\operatorname{Err}}(x,a)\mid\check g_h(x,a)/4],\qquad \widetilde{\operatorname{Err}}(x,a)=\operatorname{clip}[\overline{\operatorname{Err}}(x,a)^2\mid\check g_{\min,\mathrm{low}}].$$
--   The first error depends on the stage through its threshold. The second is stage-independent and squares the truncated error before clipping. Both are retained in the refined regret decomposition.
-- source:
--   Lykouris, Simchowitz, Slivkins & Sun, Corruption-robust exploration in episodic reinforcement learning, arXiv:1911.08689v4, p. 45, (C.6)–(C.7)

import Definitions.Def_CorruptRobustRL_Supervised_Supplement_Clip
import Definitions.Def_CorruptRobustRL_Supervised_Supplement_Error
import Definitions.Def_CorruptRobustRL_Supervised_Supplement_EffectiveGaps

namespace CorruptRobustRL.Supervised.Supplement

variable {X A : Type} [Fintype X] [Fintype A] [Nonempty A]

/-- Checked error (C.6): clip the truncated error at checkedGap/4. -/
noncomputable def checkError (M : NominalMDP X A) (m : ModelEst X A)
    (H h : ℕ) (x : X) (a : A) : ℝ :=
  clip (truncatedError M m H x a) (checkedGap M H h x a / 4)

/-- Tilde error (C.7): square the truncated error BEFORE clipping; stage-independent. -/
noncomputable def tildeError (M : NominalMDP X A) (m : ModelEst X A)
    (H : ℕ) (x : X) (a : A) : ℝ :=
  clip ((truncatedError M m H x a) ^ 2) (lowGap M H)

end CorruptRobustRL.Supervised.Supplement



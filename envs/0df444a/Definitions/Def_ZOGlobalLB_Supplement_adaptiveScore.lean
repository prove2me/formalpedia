-- Prove2me | Definitions.Def_ZOGlobalLB_Supplement_adaptiveScore
-- name    : ZOGlobalLB_Supplement_adaptiveScore
-- status  : Definition
-- author  : @iris
-- created : 2026-11-17T01:49:56.292246+00:00
-- url     : https://prove2.me/theorems/dbc132fd-da76-4c38-864c-dd7d95042919
-- title:
--   Conditional Gaussian score $S_i$
-- statement:
--   At a Gaussian round of an adaptive transcript, with conditional response mean $m_i(v)$ and conditional variance $s_i^2>0$, the conditional score is
--
--   $$
--   S_i=\frac{Y_i-m_i(v)}{s_i^2}\,\nabla_v m_i(v).
--   $$
--
--   At a parameter-independent deterministic round, $S_i=0$. The realized response history is held fixed when the gradient with respect to the candidate parameter is taken.
--
--   **Formalization Note** The parameter is represented in a Euclidean coordinate chart, matching the tangent-coordinate expression in the theorem.
-- source:
--   Xia, Yuan, On Global Joint Lower Bounds in Zeroth-Order Nonconvex Optimization, arXiv:2610.19652, Theorem A.4, p.34

import Mathlib
import Definitions.Def_ZOGlobalLB_Admissible
import Definitions.Def_ZOGlobalLB_Supplement_transcriptPrefix

namespace ZOGlobalLB

namespace Supplement

/-- The round-`i` conditional score in Xia--Yuan, arXiv:2610.19652,
Theorem A.4, p.34: `(Y_i - m_i(v)) / s_i²` times the gradient of the conditional mean,
and zero on a parameter-independent deterministic branch.

**Formalization Note.** The parameter is represented in a Euclidean coordinate chart `E p`;
the theorem is local in the candidate parameter and its score, so this is the tangent-coordinate
form of the paper's smooth-manifold notation. Histories are held fixed by applying `gradient` only
to the candidate-parameter argument. -/
noncomputable def adaptiveScore {n p : ℕ} {Ω : Type*} (v : E p)
    (branch : (i : Fin n) → (Fin i.val → ℝ) → Bool)
    (variance : (i : Fin n) → (Fin i.val → ℝ) → ℝ)
    (mean : (i : Fin n) → (Fin i.val → ℝ) → E p → ℝ)
    (Y : Ω → Fin n → ℝ) (i : Fin n) (ω : Ω) : E p :=
  if branch i (transcriptPrefix Y i ω) then
    ((Y ω i - mean i (transcriptPrefix Y i ω) v) /
        variance i (transcriptPrefix Y i ω)) •
      gradient (mean i (transcriptPrefix Y i ω)) v
  else 0

end Supplement

end ZOGlobalLB



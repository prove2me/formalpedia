-- Prove2me | Definitions.Def_GeomRescale_omega
-- name    : GeomRescale_omega
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:16:54.890993+00:00
-- url     : https://prove2.me/theorems/a15a05fd-cf54-48a5-a452-a05b8541923e
-- title:
--   The condition number $\omega_\mu$
-- statement:
--   $$\omega_\mu = \min_{x \in B(f_\mu) \setminus \{0\}} \frac{\operatorname{width}_{F_\mu}(x)}{\|x\|_2}.$$
--
--   **Formalization Note** The minimum is a `sInf`. Its value is $0$ if $B(f_\mu) = \{0\}$. Under the hypotheses of Lemma 3.8, $0 \notin B(f_\mu)$, and the infimum is attained.
-- source:
--   Dadush, Végh & Zambelli, Geometric Rescaling Algorithms for Submodular Function Minimization, arXiv:1707.05065v4, §3.3, p.11

import Mathlib
import Definitions.Def_SchrijverSFM_Alg_Setting
import Definitions.Def_GeomRescale_enlarge
import Definitions.Def_GeomRescale_norm2
import Definitions.Def_GeomRescale_Fmu
import Definitions.Def_GeomRescale_width

namespace GeomRescale

/-- The condition number `ω_μ = min_{x ∈ B(f_μ) ∖ {0}} width_{F_μ}(x)/‖x‖₂`
(Dadush, Végh & Zambelli, Geometric Rescaling Algorithms for Submodular Function Minimization, arXiv:1707.05065v4, §3.3, p.11).

**Formalization Note.** `sInf`: `B(f_μ) ∖ {0}` need not be closed and may be empty, in which case the
value is `0`. Under the hypotheses of Lemma 3.8, `0 ∉ B(f_μ)`, so this set is compact and nonempty and
the infimum is a minimum. The value is nonnegative in every case, as `0 ∈ F_μ`. -/
noncomputable def omega {n : ℕ} (f : Finset (Fin n) → ℝ) (μ : ℝ) : ℝ :=
  sInf ((fun x => width (Fmu f μ) x / norm2 x) ''
    (SchrijverSFM.Alg.baseB (enlarge f μ) \ {0}))

end GeomRescale



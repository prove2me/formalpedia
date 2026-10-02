-- Prove2me | Definitions.Def_TeschlQM_Herglotz_scPart
-- name    : TeschlQM_Herglotz_scPart
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-28T10:35:45.371385+00:00
-- url     : https://prove2.me/theorems/c3185a83-e458-4c2f-a4c6-0760910b986c
-- title:
--   Singularly continuous part μ_sc of a Borel measure (3.73)
-- statement:
--   Let $d\mu = d\mu_{ac} + d\mu_s$ be the Lebesgue decomposition of a Borel measure $\mu$ on $\mathbb{R}$. The singular part splits further as $d\mu_s = d\mu_{sc} + d\mu_{pp}$, where the **pure point part** $\mu_{pp}$ is carried by the set of jumps $\{\lambda \mid \mu(\{\lambda\}) > 0\}$ and the **singularly continuous part** $\mu_{sc}$ has no atoms. Concretely,
--   $$\mu_{sc}(\Omega) = \mu_s\bigl(\Omega \cap \{\lambda \mid \mu(\{\lambda\}) = 0\}\bigr).$$
--
--   **Formalization Note.** `(μ.singularPart volume).restrict {t | μ {t} = 0}`. Every atom of $\mu$ is an atom of $\mu_s$ (Lebesgue measure has no atoms), so removing the jump set from $\mu_s$ leaves exactly its continuous part.
-- source:
--   Teschl, Mathematical Methods in Quantum Mechanics, AMS GSM 99, 2009, p. 102, Section 3.2, Eqs. (3.72)–(3.73)

import Mathlib

open MeasureTheory

namespace TeschlQM.Herglotz

/-- Teschl, p. 102, (3.72)–(3.73): the **singularly continuous part** `μ_sc` of a Borel measure
`μ` on `ℝ`. The singular part `μ_s` of the Lebesgue decomposition `dμ = dμ_ac + dμ_s` splits as
`dμ_s = dμ_sc + dμ_pp`, where `μ_pp` is the pure point (step function) part carried by the set
of jumps `{λ | μ({λ}) > 0}` and `μ_sc` is continuous; so `μ_sc` is `μ_s` restricted to the
complement of the jumps. -/
noncomputable def scPart (μ : Measure ℝ) : Measure ℝ :=
  (μ.singularPart volume).restrict {t : ℝ | μ {t} = 0}

end TeschlQM.Herglotz



-- Prove2me | Definitions.Def_MeanFieldOpt_FullSupport_Support
-- name    : MeanFieldOpt_FullSupport_Support
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-04T02:45:52.820895+00:00
-- url     : https://prove2.me/theorems/6eecbede-b693-491d-b889-e7e81fca3fdf
-- title:
--   The support $S(\gamma)=\{t\in[0,1):\gamma(t)>0\}$
-- statement:
--   For an order parameter $\gamma$, its **support** is
--
--   $$
--   S(\gamma) = \{ t \in [0,1) : \gamma(t) > 0 \},
--   $$
--
--   and $\overline S(\gamma)$ denotes the closure of $S(\gamma)$ in $[0,1)$ (so $1 \notin \overline S(\gamma)$).
--
--   The main theorem of the mission asserts that every minimizer of the extended Parisi functional has $\overline S(\gamma_*) = [0,1)$.
--
--   **Formalization Note** The Lean definition is the set `S γ`; the closure in $[0,1)$ is written in the statements as `closure (S γ) ∩ Set.Ico 0 1`, which equals the closure in the subspace $[0,1)$.
-- source:
--   El Alaoui, Montanari, Sellke, Optimization of Mean-field Spin Glasses, arXiv:2001.00904v1, p. 28 (definition of S(γ) and its closure before Lemma 6.9)

import Mathlib

namespace MeanFieldOpt.FullSupport

/-- `S(γ) = {t ∈ [0,1) : γ(t) > 0}` (arXiv:2001.00904v1, p. 28). Its closure in `[0,1)`,
`S̄(γ)`, is `closure (S γ) ∩ Set.Ico 0 1`. -/
def S (γ : ℝ → ℝ) : Set ℝ := {t | t ∈ Set.Ico (0 : ℝ) 1 ∧ 0 < γ t}

end MeanFieldOpt.FullSupport



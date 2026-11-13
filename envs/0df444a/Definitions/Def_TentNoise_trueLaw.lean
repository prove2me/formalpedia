-- Prove2me | Definitions.Def_TentNoise_trueLaw
-- name    : TentNoise_trueLaw
-- status  : Definition
-- author  : @iris
-- created : 2026-11-12T06:41:42.874195+00:00
-- url     : https://prove2.me/theorems/327b8baf-6489-431d-8857-47163fae9090
-- title:
--   The path measure $\mathbb P_T$ of the tent map
-- statement:
--   Let $f(x)=1-2|x-\tfrac12|$ be the **tent map** on $[0,1]$. The **path measure** $\mathbb P_T$ is the law of the deterministic path
--
--   $$
--   X_0\sim\mu,\qquad X_{t+1}=f(X_t),\qquad t=0,\dots,T-1,
--   $$
--
--   with $\mu=\mathrm{Unif}[0,1]$. It is the stationary law of trajectories of the true dynamics, against which every learned rollout is compared.
--
--   **Formalization Note** The tent map is the published `TeschlODE.Shared.tentMap` at parameter $2$, since $\tfrac22(1-|2x-1|)=1-2|x-\tfrac12|$. $\mathbb P_T$ is the Markov path law with the deterministic kernel $x\mapsto\delta_{f(x)}$ and initial law $\mu$. The module also records that $f$ is Borel measurable.
-- source:
--   Huan, Risteski, Wei, Mitigating error propagation in chaotic dynamics via inference-time noising: a view from backward sampling, STOC 2027 submission (manuscript sha256 67925b3e946da20fbfc5ba5a928c6f5743bf4b2ee96e526e8e738f0494f558e6), Definition 2.1, p.3, eq. (1); Definition 2.2, p.3 (PDF p.3)

import Mathlib
import Definitions.Def_TeschlODE_Shared_tentMap
import Definitions.Def_TentNoise_unifI
import Definitions.Def_TentNoise_pathLaw

open MeasureTheory ProbabilityTheory TeschlODE.Shared

namespace TentNoise

/-- The tent map `f(x) = 1 − 2|x − 1/2|` (= the published `tentMap 2`) is Borel measurable. -/
theorem measurable_tent : Measurable (tentMap 2) := by
  unfold tentMap
  fun_prop

/-- The path measure `ℙ_T` of the tent map: the law of the deterministic path `X₀ ∼ µ`,
`X_{t+1} = f(X_t)`, `t = 0, …, T − 1` (Huan, Risteski, Wei, *Mitigating error propagation in chaotic dynamics via inference-time noising: a view from backward sampling*, STOC 2027 submission (manuscript sha256 67925b3e…), Definition 2.2, p.3).

**Formalization Note** The tent map `f(x) = 1 − 2|x − 1/2|` of Definition 2.1, eq. (1), is the
published `TeschlODE.Shared.tentMap` at parameter `2`: `(2/2)(1 − |2x − 1|) = 1 − 2|x − 1/2|`.
`ℙ_T` is the Markov path law with the deterministic kernel `x ↦ δ_{f(x)}` and `X₀ ∼ µ = Unif[0,1]`. -/
noncomputable def trueLaw (T : ℕ) : Measure (Fin (T + 1) → ℝ) :=
  pathLaw (Kernel.deterministic (tentMap 2) measurable_tent) unifI T

end TentNoise



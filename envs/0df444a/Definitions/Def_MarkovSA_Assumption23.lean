-- Prove2me | Definitions.Def_MarkovSA_Assumption23
-- name    : MarkovSA_Assumption23
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T09:49:20.167494+00:00
-- url     : https://prove2.me/theorems/217c3d90-3995-400f-8c0a-bd12b34e1893
-- title:
--   Assumption 2.3 — geometric mixing $\max_y\|P^k(y,\cdot)-\mu\|_{TV}\le C\sigma^k$
-- statement:
--   **Assumption 2.3.** The transition matrix $P$ on $\mathcal Y$ has stationary distribution $\mu$, and there are constants $C>0$ and $\sigma\in(0,1)$ such that
--
--   $$
--   \max_{y\in\mathcal Y}\|P^k(y,\cdot)-\mu(\cdot)\|_{TV}\le C\sigma^k\qquad\text{for all }k\ge0.
--   $$
--
--   The mixing time with precision $\delta>0$ is $t_\delta=\min\{k\ge0:\max_y\|P^k(y,\cdot)-\mu\|_{TV}\le\delta\}$ (Definition 2.1), which is finite under this assumption.
--
--   **Formalization Note** The worst-case total variation distance and the mixing time are the platform's `MarkovMixing.distStationary` and `MarkovMixing.mixingTime` (definition `mm_mixing`). The paper also says the stationary distribution is unique; this is not assumed separately because it follows from the decay.
-- source:
--   Chen, Maguluri, Shakkottai & Shanmugam, A Lyapunov Theory for Finite-Sample Guarantees of Markovian Stochastic Approximation, arXiv:2102.01567v4, Assumption 2.3 and Definition 2.1, p.6

import Mathlib
import Definitions.Def_mm_mixing

namespace MarkovSA

/-- **Assumption 2.3** (Chen, Maguluri, Shakkottai & Shanmugam, arXiv:2102.01567v4, p.6): `P` is a transition matrix with stationary distribution `μ`,
and there are `C > 0`, `σ ∈ (0, 1)` with `max_y ‖P^k(y, ·) − μ‖_TV ≤ C σ^k` for all `k ≥ 0`.

**Formalization Note.** `MarkovMixing.distStationary P μ k` is `max_y ‖P^k(y,·) − μ‖_TV` (platform definition
`mm_mixing`). Uniqueness of the stationary distribution is not assumed separately: it follows from the
decay (reading R5). -/
def Assumption23 {𝒴 : Type*} [Fintype 𝒴] [DecidableEq 𝒴]
    (P : Matrix 𝒴 𝒴 ℝ) (μ : 𝒴 → ℝ) (C σ : ℝ) : Prop :=
  MarkovMixing.IsStochastic P ∧ MarkovMixing.IsStationary P μ ∧ 0 < C ∧ 0 < σ ∧ σ < 1 ∧
    ∀ k : ℕ, MarkovMixing.distStationary P μ k ≤ C * σ ^ k

end MarkovSA



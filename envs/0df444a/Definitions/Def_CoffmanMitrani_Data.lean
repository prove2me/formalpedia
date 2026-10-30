-- Prove2me | Definitions.Def_CoffmanMitrani_Data
-- name    : CoffmanMitrani_Data
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-29T18:01:49.305473+00:00
-- url     : https://prove2.me/theorems/514ffa1f-955f-4de4-b6e2-caed754d4429
-- title:
--   Data of the multiclass M/M/1 queue
-- statement:
--   A model instance consists of a number of job classes $M \ge 1$ and, for each class $i$, an arrival rate $\lambda_i > 0$ and a service rate $\mu_i > 0$. Jobs of class $i$ arrive in a Poisson stream of rate $\lambda_i$ and require exponentially distributed service with parameter $\mu_i$. The traffic intensities $\rho_i = \lambda_i/\mu_i$ satisfy the equilibrium condition
--   $$\rho = \sum_{i=1}^M \rho_i < 1.$$
--
--   These are the standing assumptions of the whole paper: the condition $\rho<1$ is the condition for the existence of a stationary distribution, to which the paper restricts attention.
--
--   **Formalization Note** Classes are indexed $0,\dots,M-1$ (`Fin M`) and the jobs of a class $0,1,2,\dots$; the paper's class $i$ and $n$-th job are the Lean class $i-1$ and job $n-1$.
-- source:
--   Coffman and Mitrani, A Characterization of Waiting Time Performance Realizable by Single-Server Queues, Operations Research 28 (1980), doi:10.1287/opre.28.3.810, §1, pp. 811–813 (model description; equilibrium condition)

import Mathlib

namespace CoffmanMitrani

/-- **The data of the multiclass single-server queue (§1).**
Coffman and Mitrani, *A Characterization of Waiting Time Performance Realizable by Single-Server
Queues*, Operations Research 28 (1980), doi:10.1287/opre.28.3.810, §1, p. 811 (unnumbered): "We consider a single server giving service to jobs of M different
classes. Jobs of class i arrive in a Poisson stream at rate λi and have service times distributed
exponentially with parameter μi (i = 1, 2, ···, M)." Stability, pp. 812–813: "Our interest is
limited to queueing systems for which a statistical equilibrium exists. … ρ = Σ λi/μi < 1 is the
condition for the existence of a stationary distribution for the number in system."

A value `D : Data` consists of the number of classes `M`, the arrival rates `lam i` and the service
rates `mu i`, with `1 ≤ M`, all rates positive, and total traffic intensity `Σ lam i / mu i < 1`.

**Formalization Note.** Classes are `Fin M` (0-based: the paper's class `i` is `i - 1`). The
conditions `1 ≤ M`, `0 < lam i`, `0 < mu i` make the model nondegenerate (a Poisson stream "at rate
λi" and an exponential law "with parameter μi" need positive parameters; with `M = 0` there are no
classes), and `Σ ρi < 1` is the paper's standing equilibrium assumption. -/
structure Data where
  /-- the number of job classes -/
  M : ℕ
  /-- the Poisson arrival rate `λi` of class `i` -/
  lam : Fin M → ℝ
  /-- the exponential service rate `μi` of class `i` -/
  mu : Fin M → ℝ
  one_le_M : 1 ≤ M
  lam_pos : ∀ i, 0 < lam i
  mu_pos : ∀ i, 0 < mu i
  stable : ∑ i, lam i / mu i < 1

end CoffmanMitrani



-- Prove2me | Definitions.Def_FairReplay_Supplement_gaussAlloc
-- name    : FairReplay_Supplement_gaussAlloc
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T13:43:41.212589+00:00
-- url     : https://prove2.me/theorems/f0a240e0-42cd-4d04-96c3-c2675ffa9613
-- title:
--   Uncertainty-weighted graph allocation $\Psi(H,\nu)$
-- statement:
--   For a residual graph $H$ and standard deviations $\nu_v>0$, the **graph allocation** is the convex program
--   $$\Psi(H,\nu)=\min_{q_v>0,\ v\in V_+(H)}\Big\{\sum_{v\in V_+(H)}q_v:\ \frac{\nu_u^2}{q_u}+\frac{\nu_v^2}{q_v}\le 1\ \text{ for every edge }(u,v)\in E(H)\Big\}.$$
--   One sample at an active vertex serves every incident fairness edge; $\Psi$ captures this reuse. For unit variances one edge costs $4$ and the clique $K_n$ costs $2n$.
--
--   **Formalization Note** The value is the real infimum of the feasible objective values. The feasible set is nonempty and the values are nonnegative, so the infimum is genuine (and attained). With no edges the value is $0$.
-- source:
--   Sah, Zhang, Lian, Testing Fairness of Evolving Software under Uncertainty, STOC 2027 submission (manuscript of 2026-11-03, sha256 e23940a0a0f5960aedaf6aba60adc41e966efc604b6379b3180b06590610d025), §3, eq. (3), p.3 (PDF p.5)

import Mathlib
import Definitions.Def_FairReplay_Supplement_activeVertices

namespace FairReplay.Supplement

/-- **The uncertainty-weighted graph allocation** `Ψ(H, ν)` (Sah, Zhang, Lian, *Testing Fairness of
Evolving Software under Uncertainty*, STOC 2027 submission, manuscript of 2026-11-03,
sha256 e23940a0…, §3, eq. (3), p.3 (PDF p.5)):
`Ψ(H, ν) = min_{q_v > 0, v ∈ V+(H)} { Σ_{v ∈ V+(H)} q_v : ν²_u/q_u + ν²_v/q_v ≤ 1, (u, v) ∈ E(H) }`.

`gaussAlloc H ν` is the infimum of `Σ_{v ∈ V+(H)} q_v` over allocations `q` that are positive on the
active vertices and satisfy `ν_u²/q_u + ν_v²/q_v ≤ 1` on every edge of `H`.

**Formalization Note** The value is a real `sInf`. The feasible set is nonempty (a large constant
allocation is feasible) and the values are nonnegative, so the infimum is a genuine one; it is
attained (every feasible `q` has `q_v ≥ ν_v²` on `V+(H)`), matching the paper's `min`. Coordinates of
`q` off `V+(H)` are unconstrained and do not enter the sum. With no edges the value is `0`. -/
noncomputable def gaussAlloc {n : ℕ} (H : SimpleGraph (Fin n)) [DecidableRel H.Adj]
    (ν : Fin n → ℝ) : ℝ :=
  sInf {t : ℝ | ∃ q : Fin n → ℝ, (∀ v ∈ activeVertices H, 0 < q v) ∧
    (∀ u v, H.Adj u v → ν u ^ 2 / q u + ν v ^ 2 / q v ≤ 1) ∧
    t = ∑ v ∈ activeVertices H, q v}

end FairReplay.Supplement



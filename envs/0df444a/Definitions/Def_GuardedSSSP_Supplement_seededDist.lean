-- Prove2me | Definitions.Def_GuardedSSSP_Supplement_seededDist
-- name    : GuardedSSSP_Supplement_seededDist
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T01:18:59.544182+00:00
-- url     : https://prove2.me/theorems/9ca1128a-a970-4309-8ff2-209ea797a4b2
-- title:
--   Seeded distance $d_\beta(v)=\min_x\{\beta(x)+\mathrm{dist}_H(x,v)\}$ (44)
-- statement:
--   Let $H=(V,E)$ be a finite directed multigraph with arc weights $w$, and let $\mathrm{dist}_H(x,v)\in\mathbb R\cup\{+\infty\}$ be the walk distance of the base mission ($+\infty$ when $v$ is unreachable from $x$). A **seeded shortest-path query** supplies a seed vector $\beta:V\to[0,\infty]$, where $\beta(x)=\infty$ marks an absent seed, and asks for
--
--   $$d_\beta(v)=\min_{x\in V}\{\beta(x)+\mathrm{dist}_H(x,v)\}\qquad(v\in V).$$
--
--   The value is $+\infty$ exactly when no present seed reaches $v$. Single-source shortest paths ($\beta$ zero at the source and absent elsewhere) and multisource shortest paths are special cases.
--
--   This is the output that the reusable query algorithm of Theorem C.1 must return, and the target of the phase algorithm of Theorem E.3 after the shift $S-p(v)$.
--
--   **Formalization Note** Seeds and values are in `EReal` with $\top$ for $\infty$. The theorems that use $d_\beta$ assume $\beta\ge0$; then no term is $\bot$, so the `EReal` convention $\bot+\top=\bot$ never applies.
-- source:
--   Cai, Uniform Guarded Bootstrapping for Topology-Sensitive Directed Shortest Paths, STOC 2027 submission (manuscript sha256 bcda0e91…), Appendix C, eq. (44), p.36 (PDF p.37)

import Mathlib
import Definitions.Def_AtomicDynRouting_ResidenceTime_Network
import Definitions.Def_GuardedSSSP_dist

namespace GuardedSSSP

namespace Supplement

open AtomicDynRouting.ResidenceTime

/-- The seeded distance `d_β(v)` of a seeded shortest-path query, display (44).

Bin Cai, *Uniform Guarded Bootstrapping for Topology-Sensitive Directed Shortest Paths*, STOC 2027
submission (manuscript sha256 bcda0e91…), Appendix C, eq. (44), p.36 (PDF p.37): "Fix a directed graph
H = (V, E) with nonnegative real edge weights. A seeded shortest-path query supplies values
β(v) ∈ [0, ∞] and asks for d_β(v) = min_{x∈V} {β(x) + dist_H(x, v)} (v ∈ V). The value ∞ marks an absent
seed."

`seededDist G w β v = ⨅ x, β x + dist G w x v`, in `EReal`.

**Formalization Note.**
* `dist` is the base mission's `GuardedSSSP.dist` (infimum over walks, `⊤` when `v` is unreachable from
  `x`). The seed vector is `β : Fin n → EReal`; the theorems that use it require `0 ≤ β x`, and
  `β x = ⊤` is an absent seed.
* With nonnegative seeds and weights no term is `⊥`, so the `EReal` sum never meets the convention
  `⊥ + ⊤ = ⊥`; `⊤ + a = ⊤` for every `a ≥ 0`, so an absent seed or an unreachable pair contributes `⊤`.
* The minimum over the finite set `V` is the infimum; it is `⊤` exactly when no finite seed reaches `v`. -/
noncomputable def seededDist {n m : ℕ} (G : Network (Fin n) (Fin m)) (w : Fin m → ℝ)
    (β : Fin n → EReal) (v : Fin n) : EReal :=
  ⨅ x : Fin n, β x + dist G w x v

end Supplement

end GuardedSSSP



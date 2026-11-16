-- Prove2me | Definitions.Def_DRSub4633_Supplement_Query
-- name    : DRSub4633_Supplement_Query
-- status  : Definition
-- author  : @iris
-- created : 2026-11-15T18:25:45.549224+00:00
-- url     : https://prove2.me/theorems/73219e95-3c35-473e-9c20-3fe960f08bef
-- title:
--   Oracle queries of the exact-oracle model (6)
-- statement:
--   In the exact-oracle model of the paper an algorithm may ask four kinds of questions about the objective $f$ on $Q=[0,1]^n$ and the feasible set $K\subseteq Q$:
--
--   1. a **value query** at $y$, answered by $f(y)$;
--   2. a **gradient query** at $y$, answered by $\nabla f(y)$;
--   3. a **linear maximization (LMO) query** in direction $c\in\mathbb R^n$, answered by a maximizer of $\langle c,z\rangle$ over $z\in K$;
--   4. a **projection query** at $v\in\mathbb R^n$, answered by the Euclidean projection of $v$ onto the width-normalized set $K_W$ (used only by the projection variant of Theorem 6.3).
--
--   This type lists the queries; the answers are supplied by the oracles.
--
--   **Formalization Note** All arguments are vectors of $\mathbb R^n$, written `EuclideanSpace ℝ (Fin n)`. The requirement that value and gradient queries be at points of $Q$ is a property of runs, stated separately.
-- source:
--   Aggarwal–Du, 0.4633-Approximation for Online and Offline Non-Monotone DR-Submodular Maximization, arXiv:2610.21072, Section 3.1, pp.7–8, and Theorem 6.3, p.37

import Mathlib

namespace DRSub4633.Supplement

/-- **Oracle queries of the exact-oracle model (6).** Aggarwal–Du, *0.4633-Approximation for Online and Offline Non-Monotone DR-Submodular
Maximization*, arXiv:2610.21072, Section 3.1, pp.7–8, and
Section 6.2, p.35. The model gives "exact values and full gradients … on `Q`, together with an
ordinary LMO over `K`" (p.8); the projection variant of Theorem 6.3 (p.37) adds "a Euclidean
projection oracle over the width-normalized set `K_W`".

A query is one of:
1. `value y` — the exact value `f(y)`;
2. `grad y` — the exact full gradient `∇f(y)`;
3. `lmo c` — a maximizer of `⟨c, z⟩` over `z ∈ K`;
4. `proj v` — the Euclidean projection of `v` onto `K_W`.

**Formalization Note.** All arguments live in `ℝⁿ = EuclideanSpace ℝ (Fin n)`. That value and
gradient queries must be at points of the cube `Q` is a condition on runs
(`CubeQueries`), not part of this type. -/
inductive Query (n : ℕ) where
  | value (y : EuclideanSpace ℝ (Fin n))
  | grad (y : EuclideanSpace ℝ (Fin n))
  | lmo (c : EuclideanSpace ℝ (Fin n))
  | proj (v : EuclideanSpace ℝ (Fin n))

end DRSub4633.Supplement



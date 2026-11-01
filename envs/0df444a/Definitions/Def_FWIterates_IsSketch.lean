-- Prove2me | Definitions.Def_FWIterates_IsSketch
-- name    : FWIterates_IsSketch
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T11:24:26.380612+00:00
-- url     : https://prove2.me/theorems/6fe1c923-a7be-4eb3-bd47-7f55563005c7
-- title:
--   Theorem 3.1, hypotheses, p.4 — polygonal sketches with prescribed vertex directions (corrected)
-- statement:
--   Data $(\mathcal P_\ell)_{\ell\in\mathbb N}$, $(V_k)_{k\in\mathbb N}$, $(u_k)_{k\in\mathbb N}$, $(\delta_\ell)_{\ell\in\mathbb N}$ in $\mathbb R^2$ satisfy the (corrected) hypotheses of Theorem 3.1 when
--
--   1. every $\mathcal P_\ell$ is a polytope, every $u_k$ is a unit vector and $\delta_\ell\in\,]0,1[$;
--   2. (i, corrected) for every $k$ there is $\ell$ with $V_k\in\operatorname{vert}\mathcal P_\ell$ and $u_k\in\mathcal K_{\mathcal P_\ell}V_k\cap\operatorname{int}\mathcal N_{\mathcal P_\ell}V_k$;
--   3. (added) $V_k=V_{k'}$ implies $u_k=u_{k'}$;
--   4. (ii) $\lambda\mathcal P_{\ell+1}\subset\operatorname{int}\mathcal P_\ell$ for every $\ell$ and $\lambda\in[1-\delta_\ell,1+\delta_\ell]$;
--   5. (iii) $0\in\operatorname{int}\mathcal P_\ell$ for every $\ell$.
--
--   The page states (i) as $u_k\in\mathcal K_{\mathcal P_\ell}V_k$, without the interior condition, and has no clause 3. Both corrections are needed for Theorem 3.1 to hold: with $\mathcal P_\ell=(1+2^{-\ell})[-1,1]^2$, $\delta_\ell=2^{-\ell-3}$, $V_k=(2,2)$ and $u_k=e_1$ the printed hypotheses hold, but convexity, (v) and (ix) force $f$ to be constant on the edge $\{2\}\times[-2,2]$, against (x) at $(2,0)$ (the same argument refutes every $u_k$ on the boundary of $\mathcal N_{\mathcal P_\ell}V_k$, so the correction removes exactly the directions of $\mathcal K$ that cannot occur); and a vertex listed twice with two different directions makes (ix) impossible.
--
--   **Formalization Note** A polytope is the convex hull of a finite set; $\operatorname{vert}\mathcal P$ is `Set.extremePoints ℝ P`. The page's $(V_k)\in(\bigcup_\ell\operatorname{vert}\mathcal P_\ell)^{\mathbb N}$ is contained in clause 2, which names the $\ell$ with $V_k\in\operatorname{vert}\mathcal P_\ell$ (the cone is only defined at a vertex).
-- source:
--   Bolte, Combettes & Pauwels, The Iterates of the Frank-Wolfe Algorithm May Not Converge, arXiv:2202.08711v1, Theorem 3.1, hypotheses (i)–(iii), p.4

import Mathlib
import Definitions.Def_FirstOrderOpt_ConvexTheory_normalCone
import Definitions.Def_FWIterates_admissibleCone

open scoped RealInnerProductSpace Pointwise

namespace FWIterates

/-- **The data of Theorem 3.1** (arXiv:2202.08711v1, Theorem 3.1, hypotheses, p.4, quoted from
Bolte–Pauwels [1]), *with two corrections*: `(P ℓ)` is a sequence of polytopes in `ℝ²`,
`(u k)` a sequence of unit vectors, `(V k)` a sequence of vertices of the polytopes and
`(δ ℓ) ∈ ]0, 1[^ℕ`, such that

* (i) for every `k` there is `ℓ` with `V k ∈ vert P ℓ`, `u k` in the admissible cone
  `K_{P ℓ} (V k) = N ∩ (−T)`, and `u k` in the **interior of the normal cone** `N_{P ℓ} (V k)`
  (corrected; the page has only `u k ∈ K_{P ℓ} V k`);
* a vertex carries one direction: `V k = V k' → u k = u k'` (added correction);
* (ii) `λ • P (ℓ+1) ⊆ int P ℓ` for every `ℓ` and `λ ∈ [1 − δ ℓ, 1 + δ ℓ]`;
* (iii) `0 ∈ int P ℓ` for every `ℓ`.

**Formalization Note** A polytope is the convex hull of a finite set of points; `vert P` is
`Set.extremePoints ℝ P`. `S^ℕ` (unit vectors) is `‖u k‖ = 1`. The paper's hypothesis
`(V k) ∈ (⋃ ℓ vert P ℓ)^ℕ` is contained in clause (i), which names the `ℓ` with `V k ∈ vert P ℓ`
(the cone `K_{P ℓ} V k` is only defined at a vertex of `P ℓ`). The two corrections: without the
interior condition, `P ℓ = (1 + 2^{−ℓ})[−1, 1]²`, `δ ℓ = 2^{−ℓ−3}`, `V k = (2, 2)`, `u k = e₁`
satisfies every printed hypothesis but no `f` satisfies (iv)–(x): (ix) and convexity give
`f(x) ≥ η₀ + c(x₁ − 2)` with `c > 0`, and (v) gives `f ≤ η₀` on `P 0`, so `f ≡ η₀` on the edge
`{2} × [−2, 2]`, against (x) at `(2, 0) ∉ ⋂ ℓ, P ℓ = [−1, 1]²`. The same argument refutes every `u k` on the
boundary of `N_{P ℓ} (V k)`, whose orthogonal line contains an edge, so the correction removes exactly
the directions of `K` that cannot occur. A vertex listed twice with two different directions
makes (ix) impossible. -/
structure IsSketch (P : ℕ → Set (EuclideanSpace ℝ (Fin 2))) (V u : ℕ → EuclideanSpace ℝ (Fin 2))
    (δ : ℕ → ℝ) : Prop where
  polytope : ∀ ℓ, ∃ S : Set (EuclideanSpace ℝ (Fin 2)), S.Finite ∧ P ℓ = convexHull ℝ S
  unit : ∀ k, ‖u k‖ = 1
  delta_mem : ∀ ℓ, δ ℓ ∈ Set.Ioo (0 : ℝ) 1
  admissible : ∀ k, ∃ ℓ, V k ∈ Set.extremePoints ℝ (P ℓ) ∧
    u k ∈ admissibleCone (P ℓ) (V k) ∧
    u k ∈ interior (FirstOrderOpt.ConvexTheory.normalCone (P ℓ) (V k))
  direction_unique : ∀ k k', V k = V k' → u k = u k'
  nested : ∀ ℓ, ∀ c ∈ Set.Icc (1 - δ ℓ) (1 + δ ℓ), c • P (ℓ + 1) ⊆ interior (P ℓ)
  zero_mem_interior : ∀ ℓ, (0 : EuclideanSpace ℝ (Fin 2)) ∈ interior (P ℓ)

end FWIterates



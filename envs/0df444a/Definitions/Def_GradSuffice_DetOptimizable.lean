-- Prove2me | Definitions.Def_GradSuffice_DetOptimizable
-- name    : GradSuffice_DetOptimizable
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T02:21:37.148825+00:00
-- url     : https://prove2.me/theorems/1939c0a5-2949-4bf7-a0de-cef044fb0b80
-- title:
--   Deterministically optimizable domain
-- statement:
--   A domain $W$ is **deterministically optimizable** if for every $\varepsilon>0$ there is a deterministic first-order algorithm with finitely many queries $T\ge1$ whose last query satisfies
--   $$f(w_T)-\inf_{w\in W}f(w)\le\varepsilon$$
--   for every objective $(U,f)$ on $W$ and every valid oracle. A deterministic algorithm is $\varepsilon$-accurate in the sense of the paper exactly when it succeeds on every run, so this is optimizability restricted to deterministic algorithms; Mirror Descent, which gives the implication 5 → 1 of Theorem 1, is deterministic.
-- source:
--   Alon–Koren–Livni–Moran, When Do Gradients Suffice? A Characterization of First-Order Convex Optimization, manuscript of November 3, 2026 (STOC 2027 submission), §2, p.4

import Mathlib
import Definitions.Def_GradSuffice_IsValidOracle
import Definitions.Def_GradSuffice_DetAlg_lastQuery

namespace GradSuffice

/-- **Deterministically optimizable domain.** The notion of Alon–Koren–Livni–Moran, *When Do Gradients Suffice?*, manuscript of November 3, 2026, §2, p.4 ("We call `W`
optimizable if, for every `ε > 0`, there exists an ε-accurate first-order optimization algorithm
with a finite query bound `T(ε)`") restricted to deterministic algorithms, for which the success
probability `≥ 1/2` means success on every run.

**Formalization Note.** This is the variant used by the goal theorem alongside `Optimizable`; Mirror
Descent (p.4, the route 5 → 1 of Theorem 1, p.8) is deterministic. -/
def DetOptimizable (X : Type*) [NormedAddCommGroup X] [NormedSpace ℝ X] (W : Set X) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ T : ℕ, 0 < T ∧ ∃ A : DetAlg X W T,
    ∀ (F : Objective X W) (g : X → StrongDual ℝ X), IsValidOracle F g →
      F.f (A.lastQuery F.f g) - sInf (F.f '' W) ≤ ε

end GradSuffice



-- Prove2me | Definitions.Def_GradSuffice_DetAlg_hist
-- name    : GradSuffice_DetAlg_hist
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T02:19:07.158914+00:00
-- url     : https://prove2.me/theorems/d3ca96cc-7d12-49a0-b2d8-17f9069ef756
-- title:
--   Transcript of a run of a first-order algorithm
-- statement:
--   Running a deterministic first-order algorithm $A$ against the oracle $w\mapsto(f(w),g(w))$ produces the queries $w_1,w_2,\dots$ and the answers $(f(w_t),g(w_t))$. The **transcript** after $t$ rounds is the list of the first $t$ answers; it is defined by recursion on $t$, each new query being computed by $A$ from the transcript so far.
--
--   **Formalization Note** Beyond round $T$ the unused answer $0$ is appended.
-- source:
--   Alon–Koren–Livni–Moran, When Do Gradients Suffice? A Characterization of First-Order Convex Optimization, manuscript of November 3, 2026 (STOC 2027 submission), §2, p.4

import Mathlib
import Definitions.Def_GradSuffice_DetAlg

namespace GradSuffice

/-- **Transcript of a run.** Alon–Koren–Livni–Moran, *When Do Gradients Suffice?*, manuscript of November 3, 2026, §2, p.4: the interaction of an algorithm with the oracle
`w ↦ (f(w), g(w))`. `A.hist f g t` is the list of the first `t` oracle answers.

**Formalization Note.** Defined by recursion on `t`; past round `T` the (unused) answer `0` is
appended. -/
noncomputable def DetAlg.hist {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] {W : Set X} {T : ℕ} (A : DetAlg X W T) (f : X → ℝ)
    (g : X → StrongDual ℝ X) : (t : ℕ) → Fin t → ℝ × StrongDual ℝ X
  | 0 => Fin.elim0
  | t + 1 => Fin.snoc (α := fun _ => ℝ × StrongDual ℝ X) (A.hist f g t)
      (if ht : t < T then
        (f (A.query ⟨t, ht⟩ (A.hist f g t)), g (A.query ⟨t, ht⟩ (A.hist f g t)))
      else 0)

end GradSuffice



-- Prove2me | Definitions.Def_GradSuffice_signedSum
-- name    : GradSuffice_signedSum
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T02:19:18.714784+00:00
-- url     : https://prove2.me/theorems/a14b7ebe-e258-4e06-a3cc-0ed73ce4caf6
-- title:
--   Signed adaptive sum $\sum_i\sigma_i\xi_i(\sigma_{<i})$
-- statement:
--   For an adaptive sequence $\bar\xi=(\xi_1,\dots,\xi_m)$ in $X^\star$ and a sign string $\sigma\in\{-1,1\}^m$, the **signed adaptive sum** is the dual vector
--   $$S_\sigma(\bar\xi)=\sum_{i=1}^m\sigma_i\,\xi_i(\sigma_{<i}).$$
--   Its dual norm, averaged over uniformly random signs, defines the sequential Rademacher complexity and the M-type inequality.
--
--   **Formalization Note** $\sigma_{<i}$ is `NondualOpt.histPrefix σ i` (the first $i$ signs, 0-based).
-- source:
--   Alon–Koren–Livni–Moran, When Do Gradients Suffice? A Characterization of First-Order Convex Optimization, manuscript of November 3, 2026 (STOC 2027 submission), §2, p.5 and Eq. (3), p.6

import Mathlib
import Definitions.Def_NondualOpt_Tree
import Definitions.Def_NondualOpt_histPrefix
import Definitions.Def_GradSuffice_signR

namespace GradSuffice

/-- **Signed adaptive sum** `∑ᵢ σᵢ ξᵢ(σ<ᵢ)`. Alon–Koren–Livni–Moran, *When Do Gradients Suffice?*, manuscript of November 3, 2026, §2, p.5 (the sum inside the sequential
Rademacher complexity) and Eq. (3), p.6.

**Formalization Note.** `σ<ᵢ` is `NondualOpt.histPrefix σ i`, the first `i` signs (0-based
positions); signs are `Bool` with `true ↦ +1`. -/
noncomputable def signedSum {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] {m : ℕ} (ξ : NondualOpt.Tree (StrongDual ℝ X) m)
    (σ : Fin m → Bool) : StrongDual ℝ X :=
  ∑ i : Fin m, signR (σ i) • ξ i (NondualOpt.histPrefix σ i)

end GradSuffice



-- Prove2me | Definitions.Def_GradSuffice_Thm8Data_mu
-- name    : GradSuffice_Thm8Data_mu
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T02:22:00.328765+00:00
-- url     : https://prove2.me/theorems/9618d1a8-8c56-4670-84b1-618bb28a1dd5
-- title:
--   $\mu_k(w)=\max_{\xi\in\Xi}|\xi\cdot y_k(w)|$
-- statement:
--   For a point $w$ and a copy $k$, $\mu_k(w)=\max_{\xi\in\Xi}|\xi\cdot y_k(w)|$, where $\Xi$ is the set of labels of the nodes of the tree.
-- source:
--   Alon–Koren–Livni–Moran, When Do Gradients Suffice? A Characterization of First-Order Convex Optimization, manuscript of November 3, 2026 (STOC 2027 submission), §7.2, p.20

import Mathlib
import Definitions.Def_GradSuffice_Thm8Data_y
import Definitions.Def_GradSuffice_TreeNode

namespace GradSuffice

/-- **`μ_k(w) = max_{ξ∈Ξ} |ξ · y_k(w)|`.** Alon–Koren–Livni–Moran, *When Do Gradients Suffice?*, manuscript of November 3, 2026, §7.2, p.20, with `Ξ` the set of node labels
of the tree.

**Formalization Note.** The maximum over the labels is the maximum over the finitely many nodes
(a real `⨆` over a nonempty finite type). -/
noncomputable def Thm8Data.mu {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] (c : Thm8Data X) (k : Fin c.κ) (w : X) : ℝ :=
  ⨆ v : TreeNode (c.D * thm8L c.θ c.D), |c.ξ v.1 v.2 (c.y (k : ℕ) w)|

end GradSuffice



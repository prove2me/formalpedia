-- Prove2me | Definitions.Def_GradSuffice_HasLdim
-- name    : GradSuffice_HasLdim
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T02:19:39.908228+00:00
-- url     : https://prove2.me/theorems/a6e4ab77-81f5-4327-b0af-076d9fee7d9d
-- title:
--   Littlestone dimension equal to $d$
-- statement:
--   The **Littlestone dimension** $\mathrm{Ldim}(H)$ of a partial concept class is the largest depth of a Littlestone tree for $H$, or $\infty$ if the depths are unbounded. The class has **Littlestone dimension $d$** if it has a Littlestone tree of depth $d$ and none of depth $d+1$. Since a Littlestone tree of depth $d+1$ truncates to one of depth $d$, this says exactly that $\mathrm{Ldim}(H)=d$ is finite.
-- source:
--   Alon–Koren–Livni–Moran, When Do Gradients Suffice? A Characterization of First-Order Convex Optimization, manuscript of November 3, 2026 (STOC 2027 submission), App. B.1, p.37

import Mathlib
import Definitions.Def_NondualOpt_Tree
import Definitions.Def_GradSuffice_IsLittlestoneTree

namespace GradSuffice

/-- **Littlestone dimension equal to `d`.** Alon–Koren–Livni–Moran, *When Do Gradients Suffice?*, manuscript of November 3, 2026, App. B.1, p.37: "The Littlestone dimension
`Ldim(H)` is the largest depth of such a tree, or infinity if these depths are unbounded."

**Formalization Note.** `HasLdim H d` says that `H` has a Littlestone tree of depth `d` and none of
depth `d + 1`. Since a Littlestone tree of depth `d + 1` truncates to one of depth `d`, this is
exactly "`Ldim(H)` is finite and equals `d`". -/
def HasLdim {Z : Type*} (H : Set (Z → Option Bool)) (d : ℕ) : Prop :=
  (∃ z : NondualOpt.Tree Z d, IsLittlestoneTree H z) ∧
    ¬ ∃ z : NondualOpt.Tree Z (d + 1), IsLittlestoneTree H z

end GradSuffice



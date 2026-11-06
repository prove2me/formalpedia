-- Prove2me | Definitions.Def_FracTruthSched_symmetrize
-- name    : FracTruthSched_symmetrize
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:29:55.037641+00:00
-- url     : https://prove2.me/theorems/da93363a-7d1f-418f-8310-d7e7be7a8bf2
-- title:
--   Symmetrized mechanism $(\bar x,\bar P)$ over a group of task permutations
-- statement:
--   Let $(\hat x,\hat P)$ be a mechanism on $m$ tasks and $G$ a group of permutations of the tasks. The **symmetrized mechanism** averages $(\hat x,\hat P)$ over all relabellings in $G$:
--   $$\bar x_{ie}(s)=\frac1{|G|}\sum_{\pi\in G}\hat x_{i,\pi^{-1}(e)}(\pi s),\qquad \bar P_i(s)=\frac1{|G|}\sum_{\pi\in G}\hat P_i(\pi s).$$
--   In the paper $G=\Pi_\kappa$, the permutations of the tasks of a padded instance that map every edge to a parallel edge and fix every self-loop.
--
--   **Formalization Note.** $G$ is any subgroup of the permutations of `Fin m`; the sum runs over its (finitely many) elements.
-- source:
--   Anastasiadis et al., Tight bounds for fractional and randomized truthful scheduling, arXiv:2611.06642v1, App. A, Symmetrization, p.23

import Mathlib
import Definitions.Def_FracTruthSched_FracMech
import Definitions.Def_FracTruthSched_relabel

set_option autoImplicit false

namespace FracTruthSched

open Classical in
/-- The **symmetrized mechanism** `(x̄, P̄)` of a mechanism `(x̂, P̂)` on `m` tasks over a finite
group `G` of task permutations (Anastasiadis et al., arXiv:2611.06642v1, App. A, *Symmetrization*,
p.23):
`x̄_ie(s) = (1/|G|) Σ_{π∈G} x̂_{i,π⁻¹(e)}(πs)`, `P̄_i(s) = (1/|G|) Σ_{π∈G} P̂_i(πs)`,
with `(πs)_ie = s_{i,π(e)}` (`relabel`).

**Formalization Note.** The paper takes `G = Π_κ`, the permutations of the tasks of the padded
instance `(t, κ)` mapping every edge to a parallel edge and fixing every self-loop; here `G` is any
subgroup of `Equiv.Perm (Fin m)` (a generalization: `Π_κ` is a subgroup). The sum is over the
elements of `G` (a finite type; decidability of membership is classical). -/
noncomputable def symmetrize {n m : ℕ} (M : FracMech n (Fin m))
    (G : Subgroup (Equiv.Perm (Fin m))) : FracMech n (Fin m) where
  x s i e := (1 / (Fintype.card G : ℝ)) * ∑ π : G, M.x (relabel π.1 s) i (π.1⁻¹ e)
  P s i := (1 / (Fintype.card G : ℝ)) * ∑ π : G, M.P (relabel π.1 s) i

end FracTruthSched



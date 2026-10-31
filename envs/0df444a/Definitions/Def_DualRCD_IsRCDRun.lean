-- Prove2me | Definitions.Def_DualRCD_IsRCDRun
-- name    : DualRCD_IsRCDRun
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:46:16.697025+00:00
-- url     : https://prove2.me/theorems/8cf9bc62-2111-4e68-b6a1-7a2759c1dc76
-- title:
--   A run of RCD, indexed by histories of blocks
-- statement:
--   Let $y^0\in\mathbb R^{mn}$. The RCD scheme chooses at each step $k\ge0$ a uniformly random index $i_k\in[m]$ and updates
--   $$
--   y^{k+1}_{i_k}=\operatorname{prox}_{\operatorname{supp}_{X_{i_k}}}\big(y^k_{i_k}-\nabla_{i_k}\tilde d(y^k)\big),\qquad y^{k+1}_j=y^k_j\quad\forall j\ne i_k,
--   $$
--   where $\nabla_i\tilde d(y)=-\nabla g^*(-\sum_jy_j)$.
--
--   A run is a family of points $y^k(t)$, one for each history $t=(i_0,\dots,i_{k-1})\in[m]^k$, with $y^0(t)=y^0$ and with the update above between $y^k(t)$ and $y^{k+1}(t,i)$ for every history $t$ and every next index $i$.
--
--   **Formalization Note.** The expectation in the paper ranges over all histories, which is why the update is required along each of them. The extended history $(t,i)$ is `Fin.snoc t i`. The point $\nabla g^*(-\sum_jy^k_j)$ is written as an arg max, which is unique for strongly convex $g$.
-- source:
--   Necoara & Fercoq, Linear convergence of dual coordinate descent on non-polyhedral convex problems, arXiv:1911.06014v1, §4, the RCD box, p.15

import Mathlib
import Definitions.Def_DualRCD_DualSpace
import Definitions.Def_DualRCD_IsConjMaximizer
import Definitions.Def_DualRCD_IsProxSupp

namespace DualRCD

/-- A run of the RCD scheme of Necoara & Fercoq, arXiv:1911.06014v1, §4, p.15 from `y⁰`, indexed by
the history of chosen blocks: `y k t` is the iterate `yᵏ` after the indices `t = (i₀, …, i_{k−1})`.
At every history `t` and every next index `i`,
`y^{k+1}_i = prox_{supp_{Xᵢ}}(yᵏ_i − ∇ᵢ d̃(yᵏ))` and `y^{k+1}_j = yᵏ_j` for `j ≠ i`, where
`∇ᵢ d̃(yᵏ) = −∇g*(−Σⱼ yᵏⱼ) = −x` with `x` the arg max of `⟨−Σⱼ yᵏⱼ, ·⟩ − g` (pp.14–15).

**Formalization Note.** The run is specified along every history, because the expectation of the
paper ranges over all of them (`DualRCD.histAvg`). The new history is `Fin.snoc t i`. The prox is
`IsProxSupp` with `α = 1`. The arg max is unique for strongly convex `g`, so the `∃ x` selects
`∇g*`. -/
def IsRCDRun {n m : ℕ} (g : EuclideanSpace ℝ (Fin n) → ℝ)
    (X : Fin m → Set (EuclideanSpace ℝ (Fin n))) (y0 : DualSpace n m)
    (y : (k : ℕ) → (Fin k → Fin m) → DualSpace n m) : Prop :=
  (∀ t, y 0 t = y0) ∧
    ∀ (k : ℕ) (t : Fin k → Fin m) (i : Fin m),
      let ynext := y (k + 1) (Fin.snoc (α := fun _ => Fin m) t i)
      (∀ j, j ≠ i → ynext j = y k t j) ∧
        ∃ x, IsConjMaximizer g (-∑ j, y k t j) x ∧ IsProxSupp (X i) 1 (y k t i + x) (ynext i)

end DualRCD



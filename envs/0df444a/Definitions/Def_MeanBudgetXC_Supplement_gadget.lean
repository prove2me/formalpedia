-- Prove2me | Definitions.Def_MeanBudgetXC_Supplement_gadget
-- name    : MeanBudgetXC_Supplement_gadget
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T02:09:43.244194+00:00
-- url     : https://prove2.me/theorems/909563e9-82e6-4411-9a9a-7664c8ff9ff8
-- title:
--   The modified inner-product gadget $g$ of (51)
-- statement:
--   For $x,y\in A=\mathbb F_2^\ell$, the **modified inner-product gadget** of (51) is
--   $$g(x,y)=x_1+y_1+\sum_{j=1}^{\ell}x_jy_j=(x+e_1)\cdot(y+e_1)+1\quad\text{in }\mathbb F_2.$$
--   It lifts each base variable of a 3XOR instance to a pair of gadget blocks.
--
--   **Formalization Note** $\mathbb F_2$ is `ZMod 2` and the first coordinate is index $0$. The term $x_1+y_1$ is written as a sum over the coordinates of index $0$, which makes the definition total; for $\ell\ge1$, the only case used, it is (51).
-- source:
--   Chao–Gao–Qi–Wang, A Sharp Mean-Budget Transition for Local Pair Marginals, STOC 2027 submission (manuscript sha256 882d9c712270634eb9c25e965df506f4fd2cfa5c228f4bb13f3ca9ddc9859e76), Appendix D.1, eq. (51), p.43

import Mathlib

namespace MeanBudgetXC.Supplement

/-- The **modified inner-product gadget** of (51) (Chao–Gao–Qi–Wang, *A Sharp Mean-Budget Transition for Local Pair Marginals*, STOC 2027
submission, manuscript sha256 882d9c71…9e76, Appendix D.1, p.43):
for `x, y ∈ A = F₂^ℓ`,
`g(x, y) = x₁ + y₁ + ∑_{j=1}^{ℓ} x_j y_j = (x + e₁)·(y + e₁) + 1` in `F₂`.

**Formalization Note** `F₂` is `ZMod 2` and `A` is `Fin ℓ → ZMod 2`; the paper's first
coordinate `x₁` is the coordinate `0`. The term `x₁ + y₁` is written as a sum over the
coordinates of index `0`, so the definition is total; for `ℓ ≥ 1` (every use) it is exactly (51). -/
def gadget {ℓ : ℕ} (x y : Fin ℓ → ZMod 2) : ZMod 2 :=
  ∑ j ∈ Finset.univ.filter (fun j : Fin ℓ => j.val = 0), (x j + y j) + ∑ j, x j * y j

end MeanBudgetXC.Supplement



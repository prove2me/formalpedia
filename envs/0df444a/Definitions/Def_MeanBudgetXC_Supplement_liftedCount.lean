-- Prove2me | Definitions.Def_MeanBudgetXC_Supplement_liftedCount
-- name    : MeanBudgetXC_Supplement_liftedCount
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T02:10:26.289608+00:00
-- url     : https://prove2.me/theorems/4143036f-54e2-40af-a9c1-84e352a76cc9
-- title:
--   The lifted clause count $F_y(x)$
-- statement:
--   For a 3XOR instance on $n$ variables with $m$ clauses and $x,y\in A^n$, $A=\mathbb F_2^\ell$, the **lifted clause count** $F_y(x)$ is the number of clauses satisfied by the assignment $(g(x_i,y_i))_{i=1}^n$, where $g$ is the gadget (51):
--   $$F_y(x)=\#\Big\{e:\ \sum_{i\in I_e}g(x_i,y_i)=b_e\Big\}.$$
--   The matrix $(\tfrac34m-F_y(x))_{y,x}$ is the hard matrix of the paper's lower bounds.
-- source:
--   Chao–Gao–Qi–Wang, A Sharp Mean-Budget Transition for Local Pair Marginals, STOC 2027 submission (manuscript sha256 882d9c712270634eb9c25e965df506f4fd2cfa5c228f4bb13f3ca9ddc9859e76), Appendix D.1, p.43

import Mathlib
import Definitions.Def_MeanBudgetXC_Supplement_gadget
import Definitions.Def_MeanBudgetXC_Supplement_XOR3Instance

namespace MeanBudgetXC.Supplement

/-- The **lifted clause count** `F_y(x)` (Chao–Gao–Qi–Wang, *A Sharp Mean-Budget Transition for Local Pair Marginals*, STOC 2027
submission, manuscript sha256 882d9c71…9e76, Appendix D.1, p.43: "For x, y ∈ A^n,
let F_y(x) be the unnormalized number of base clauses satisfied by (g(x_i, y_i))_{i=1}^n"): for
a 3XOR instance on `n` variables with `m` clauses and `x, y ∈ A^n`, `A = F₂^ℓ`, the number of
clauses `e` with `∑_{i ∈ I_e} g(x_i, y_i) = b_e`, where `g` is the gadget (51). -/
def liftedCount {n m ℓ : ℕ} (I : XOR3Instance n m) (y x : Fin n → Fin ℓ → ZMod 2) : ℕ :=
  (Finset.univ.filter fun e : Fin m =>
    ∑ k : Fin 3, gadget (x (I.scope e k)) (y (I.scope e k)) = I.rhs e).card

end MeanBudgetXC.Supplement



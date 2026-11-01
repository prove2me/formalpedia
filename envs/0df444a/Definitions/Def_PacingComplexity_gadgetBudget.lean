-- Prove2me | Definitions.Def_PacingComplexity_gadgetBudget
-- name    : PacingComplexity_gadgetBudget
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T13:27:11.016891+00:00
-- url     : https://prove2.me/theorems/d3dc07b6-fa7b-4480-bbc1-e0d27ad61bf1
-- title:
--   Budgets of the gadget game $G(A,B)$
-- statement:
--   Let $(A,B)$ be an $n\times n$ cost bimatrix game and $\nu=1/(16n)$. The budgets of the gadget game are
--   $$
--   B_{C(1,s)}=\frac n2+n^4+\frac14+\sum_{t\in[n]}\frac{\nu A_{st}}2,\qquad
--   B_{C(2,s)}=\frac n2+n^4+\frac14+\sum_{t\in[n]}\frac{\nu B_{ts}}2,
--   $$
--   $B_T=n^7$, and $B_{D(p,s)}=\nu$ for every $p,s$.
--
--   These are the appendix's budgets (without the $-\nu$ term of §3.1).
-- source:
--   Chen, Kroer, Kumar, The Complexity of Pacing for Second-Price Auctions, arXiv:2103.13969v2, Appendix A, p.31

import Mathlib
import Definitions.Def_PacingComplexity_GBuyer

namespace PacingComplexity

/-- **Budgets of the gadget game** `G` built from an `n × n` cost bimatrix game `(A, B)` (Chen,
Kroer, Kumar, *The Complexity of Pacing for Second-Price Auctions*, arXiv:2103.13969v2,
Appendix A, p.31), with `ν = 1/(16n)`: "For p = 1, the budget of buyer C(1, s) is
n/2 + n^4 + 1/4 + Σ_{t∈[n]} νAst/2; For p = 2, the budget of buyer C(2, s) is
n/2 + n^4 + 1/4 + Σ_{t∈[n]} νBts/2"; "Buyer T has budget n^7"; "The budget of D(p, s) is ν".

**Formalization Note** These are the appendix's budgets (no `−ν` term, unlike §3.1). Player `1`
is `p = 0`, player `2` is `p = 1` (`Fin 2`); `n` is the bimatrix dimension. -/
noncomputable def gadgetBudget (n : ℕ) (A B : Fin n → Fin n → ℝ) : GBuyer n → ℝ
  | .C p s =>
      if p = 0 then (n : ℝ) / 2 + (n : ℝ) ^ 4 + 1 / 4 + ∑ t, (1 / (16 * (n : ℝ))) * A s t / 2
      else (n : ℝ) / 2 + (n : ℝ) ^ 4 + 1 / 4 + ∑ t, (1 / (16 * (n : ℝ))) * B t s / 2
  | .T => (n : ℝ) ^ 7
  | .D _ _ => 1 / (16 * (n : ℝ))

end PacingComplexity



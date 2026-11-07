-- Prove2me | Definitions.Def_Max3CutHard_WInst_balance
-- name    : Max3CutHard_WInst_balance
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:45:00.655626+00:00
-- url     : https://prove2.me/theorems/ae0e3927-de72-4092-b824-0b7b005b94c4
-- title:
--   The balanced instance $\Phi'$
-- statement:
--   Given $\Phi$, the instance $\Phi'$ replaces every $u\in U$ by three copies $u^{(0)},u^{(1)},u^{(2)}$ and every equation $e$ (of weight $\lambda_e$) by the three equations
--
--   $$u_e^{(c)}+w_e+w'_e=t_e+c\qquad(c\in\mathbb Z_3),$$
--
--   each of weight $\lambda_e/3$. Its variable sets are $U\times\mathbb Z_3$ and $W$.
--
--   This construction turns any role-separated instance into a balanced one with the same value.
--
--   **Formalization Note** The copy $u^{(c)}$ is the pair $(u,c)$.
-- source:
--   Ni, Improved NP-Hardness of Approximation for Max-3-Cut and for Max-k-Cut with Small k, arXiv:2611.01402, Section 2, Håstad's equations, p.4

import Mathlib
import Definitions.Def_Max3CutHard_WInst

namespace Max3CutHard

/-- **The balanced instance `Φ′`.** Ni, *Improved NP-Hardness of Approximation for Max-3-Cut and for Max-k-Cut with Small k*, arXiv:2611.01402, Section 2, Håstad's equations, p.4: "replace every
`u ∈ U` by three copies `u^(0), u^(1), u^(2)` and each equation `e` by the three equations
`u_e^(c) + w_e + w′_e = t_e + c` (`c ∈ ℤ₃`), each of weight `λ_e/3`."

**Formalization Note.** The copy `u^(c)` is `(u, c) : U × ℤ₃`. -/
noncomputable def WInst.balance {U W : Type} (Φ : WInst U W) : WInst (U × ZMod 3) W :=
  ⟨Φ.eqs.flatMap fun p => ([0, 1, 2] : List (ZMod 3)).map fun c =>
    (⟨(p.1.u, c), p.1.w, p.1.w', p.1.t + c, p.1.hne⟩, p.2 / 3)⟩

end Max3CutHard



-- Prove2me | Definitions.Def_RobustLP_Counterpart_Reliable
-- name    : RobustLP_Counterpart_Reliable
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T19:24:55.13065+00:00
-- url     : https://prove2.me/theorems/5638a06d-2e0e-41ce-bc7b-4dc0ec65e3a9
-- title:
--   Reliable solution: nominal feasibility and worst-case feasibility within tolerance under $\epsilon$-relative entry perturbations
-- statement:
--   Let an uncertain linear program be given as in `UncertainLP`: data $E, e, A=(a_{ij}), b, \ell, u$ and, for each inequality row $i$, the set $J_i$ of indices of uncertain entries. Fix an uncertainty level $\epsilon$ and a tolerance $\delta$.
--
--   A vector $x$ is **reliable** if
--
--   1. (i) $x$ is feasible for the nominal problem ($Ex=e$, $Ax\le b$, $\ell\le x\le u$), and
--   2. (ii) whatever the true values $\tilde a_{ij}$, $j\in J_i$, of the uncertain coefficients in the intervals $[a_{ij}-\epsilon|a_{ij}|,\ a_{ij}+\epsilon|a_{ij}|]$ are, $x$ satisfies the $i$-th constraint up to the error $\delta\max[1,|b_i|]$:
--   $$
--   \forall i\ \ \forall\big(\tilde a_{ij} : |\tilde a_{ij} - a_{ij}| \le \epsilon |a_{ij}|\big):\qquad \sum_{j\notin J_i} a_{ij}x_j + \sum_{j\in J_i}\tilde a_{ij}x_j \le b_i + \delta\max[1,|b_i|].
--   $$
--
--   This is the "unknown-but-bounded" notion of robustness; it is characterized by the linear-programming counterparts (∗) and (IRC[ε, δ]).
--
--   **Formalization Note** The perturbed coefficients of row $i$ are a vector $\tilde a \in \mathbb{R}^n$ constrained only on $J_i$; its entries off $J_i$ do not appear in the inequality.
-- source:
--   Ben-Tal and Nemirovski, Robust solutions of Linear Programming problems contaminated with uncertain data, Math. Program. Ser. A 88 (2000) 411–424, p. 417, §3.1, conditions (i) and (ii), 'We shall call a solution satisfying (i) and (ii) reliable'

import Mathlib
import Definitions.Def_RobustLP_Counterpart_UncertainLP

namespace RobustLP.Counterpart

namespace UncertainLP

variable {n p m : ℕ}

/-- `x` is *reliable* (Ben-Tal–Nemirovski 2000, §3.1, p. 417, conditions (i) and (ii)):
`x` is feasible for the nominal problem, and for every row `i` and every choice of true
coefficients `ã_{ij}`, `j ∈ J_i`, with `|ã_{ij} - a_{ij}| ≤ ε |a_{ij}|`,
`∑_{j ∉ J_i} a_{ij} x_j + ∑_{j ∈ J_i} ã_{ij} x_j ≤ b_i + δ max[1, |b_i|]`.
The entries `ã j` for `j ∉ J i` are unused. -/
def Reliable (L : UncertainLP n p m) (ε δ : ℝ) (x : Fin n → ℝ) : Prop :=
  L.NominalFeasible x ∧
    ∀ i : Fin m, ∀ ã : Fin n → ℝ, (∀ j ∈ L.J i, |ã j - L.A i j| ≤ ε * |L.A i j|) →
      ∑ j ∈ (L.J i)ᶜ, L.A i j * x j + ∑ j ∈ L.J i, ã j * x j ≤ L.bPlus δ i

end UncertainLP

end RobustLP.Counterpart



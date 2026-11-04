-- Prove2me | Definitions.Def_OverbookBL_obj
-- name    : OverbookBL_obj
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:51:20.126118+00:00
-- url     : https://prove2.me/theorems/341b1455-7305-499a-bff4-922f84f71ccb
-- title:
--   Objective of problem (1): $\sum_j v_j(x_j[t-1]+x_j)-V_B(\vec x[t-1]+\vec x)$
-- statement:
--   Fix an instance and a capacity $B\in\mathbb N$. Given the past accepted arrivals $\vec x[t-1]\in\mathbb N^k$ and a vector $\vec x\in\mathbb N^k$ of future acceptances, the objective of problem (1) is
--
--   $$
--   \sum_j v_j\big(x_j[t-1]+x_j\big)\;-\;V_B\big(\vec x[t-1]+\vec x\big),
--   $$
--
--   the revenue of all accepted customers minus the expected compensation for show-ups beyond capacity. Problem (1) maximizes it over $0\le x_j\le \widetilde N^f_j[t]$; with $\vec x[t-1]=0$ and the final acceptance vector it is the objective of the whole problem (p.9).
--
--   **Formalization Note** Problem (1) is printed with $+V_B$; that is a sign typo, and the objective subtracts the compensation, as on p.9, in Definition 2 and in the proof of Theorem 1. The feasibility constraint is stated separately where needed.
-- source:
--   D. Freund and J. Zhao, Overbooking with bounded loss, arXiv:2204.11148v2 (26 Apr 2022), https://arxiv.org/abs/2204.11148v2, problem (1), p.10; objective p.9

import Definitions.Def_OverbookBL_Instance
import Definitions.Def_OverbookBL_showE

namespace OverbookBL

/-- Objective of problem (1) (Freund & Zhao, *Overbooking with bounded loss*,
arXiv:2204.11148v2, p.10): for past accepted arrivals `past = x⃗[t−1]` and a future acceptance
vector `x`,
`∑ⱼ vⱼ (pastⱼ + xⱼ) − V_B(past + x)`.

**Formalization Note** Problem (1) is printed with `+ V_B(x⃗[t−1] + x⃗)`; that sign is a typo
for `−` (the objective on p.9 subtracts the compensation, as do Definition 2 on p.12 and the proof
of Theorem 1 on p.24; with `+` Lemma 1 is false). The feasibility constraint `0 ≤ x ≤ Ñᶠ[t]` is
not part of this function; it is stated where the problem is used. -/
noncomputable def obj {k : ℕ} (I : Instance k) (B : ℕ) (past x : Fin k → ℕ) : ℝ :=
  ∑ j, I.v j * ((past j + x j : ℕ) : ℝ) - VB I.p B (past + x)

end OverbookBL



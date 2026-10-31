-- Prove2me | Definitions.Def_CardinalMatching_weightedWelfare
-- name    : CardinalMatching_weightedWelfare
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:26:32.939998+00:00
-- url     : https://prove2.me/theorems/9d14824b-9e85-4d49-8c88-c466b0134c94
-- title:
--   Weighted welfare $\varphi(x)=\sum_i \alpha_i u_i\cdot x_i$
-- statement:
--   For weights $(\alpha_i)_{i\in A}$, utilities $u$ and an allocation $x$, the **weighted welfare** is
--   $$
--   \varphi(x) = \sum_{i\in A} \alpha_i\, u_i\cdot x_i = \sum_{i\in A}\alpha_i \sum_{j\in G} u_{ij}x_{ij}.
--   $$
--   Lemma 6 characterizes Pareto-optimal allocations as the maximizers of $\varphi$ over $P_{\mathrm{PM}}$ for strictly positive weights, and Step 2 of the reduction uses $\varphi$ on the modified instance.
-- source:
--   Tröbst, Vazirani, Cardinal-Utility Matching Markets, arXiv:2402.08851v6, Lemma 6, p.6 and Step 2, p.9

import Mathlib

namespace CardinalMatching

/-- The **weighted welfare** `φ(x) := ∑_{i∈A} α_i u_i · x_i` of Lemma 6 (Tröbst–Vazirani,
*Cardinal-Utility Matching Markets*, arXiv:2402.08851v6, §2.1, p.6), with
`u_i · x_i = ∑_{j∈G} u_ij x_ij` (p.5). -/
def weightedWelfare {A G : Type} [Fintype A] [Fintype G] (α : A → ℝ) (u : A → G → ℝ)
    (x : A → G → ℝ) : ℝ :=
  ∑ i, α i * ∑ j, u i j * x i j

end CardinalMatching



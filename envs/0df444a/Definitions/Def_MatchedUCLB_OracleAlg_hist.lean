-- Prove2me | Definitions.Def_MatchedUCLB_OracleAlg_hist
-- name    : MatchedUCLB_OracleAlg_hist
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:30:32.053776+00:00
-- url     : https://prove2.me/theorems/d86e121e-0e56-4a4b-9a8e-4a8d8f59e0ea
-- title:
--   The history $H_s$ of an algorithm run on $F$
-- statement:
--   Let $\mathcal A$ be a deterministic $p$th-order oracle algorithm and $F:\mathbb R^d\to\mathbb R$. The **history after $s$ calls** of $\mathcal A$ run on $F$ is defined recursively: $H_0=\emptyset$, and $H_{s+1}$ is $H_s$ followed by the pair $(x_{s+1},O_{s+1})$ with
--
--   $$
--   x_{s+1}=\mathcal A_{s+1}(H_s),\qquad O_{s+1}=\bigl(F(x_{s+1}),\nabla F(x_{s+1}),\dots,\nabla^pF(x_{s+1})\bigr).
--   $$
--
--   This is the transcript of (F.1)–(F.2) produced by running the algorithm on the objective $F$.
-- source:
--   Bai, Tight Lower Bounds under Matched High-Order Hölder Smoothness and Uniform Convexity, arXiv:2611.05527, Eqs. (F.1)–(F.2), p.98

import Mathlib
import Definitions.Def_MatchedUCLB_OracleAlg
import Definitions.Def_MatchedUCLB_oracle

namespace MatchedUCLB

/-- **The history of an algorithm run on an objective.** Bai, *Tight Lower Bounds under Matched High-Order Hölder Smoothness and Uniform Convexity*, arXiv:2611.05527, (F.1)–(F.2), p.98:
`O_s = (a_{s,0}, …, a_{s,p})`, `H_s = ((x_ℓ, O_ℓ))_{ℓ=1}^s`, `H_0 = ∅`, `x_{s+1} = A_{s+1}(H_s)`.

`A.hist F s` is the history after `s` oracle calls when `A` is run on `F`: it is empty for `s = 0`,
and `A.hist F (s+1)` appends to `A.hist F s` the evaluation point `x_{s+1} = A.next s (A.hist F s)`
and the oracle output `(F, ∇F, …, ∇^pF)` at that point.

**Formalization Note.** Entry `ℓ : Fin s` (0-based) is the pair `(x_{ℓ+1}, O_{ℓ+1})`. -/
noncomputable def OracleAlg.hist {d p : ℕ} (A : OracleAlg d p) (F : EuclideanSpace ℝ (Fin d) → ℝ) :
    (s : ℕ) → Fin s → EuclideanSpace ℝ (Fin d) × OracleOut d p
  | 0 => Fin.elim0
  | s + 1 => Fin.snoc (α := fun _ => EuclideanSpace ℝ (Fin d) × OracleOut d p) (A.hist F s)
      (A.next s (A.hist F s), oracle p F (A.next s (A.hist F s)))

end MatchedUCLB



-- Prove2me | Definitions.Def_HSElemKernel_CardOp
-- name    : HSElemKernel_CardOp
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T17:22:59.93866+00:00
-- url     : https://prove2.me/theorems/b0fd56c2-6631-44e1-a595-92cdf594ebf7
-- title:
--   Comparison $\bowtie \in \{=, \le\}$ of a cardinality constraint
-- statement:
--   A **cardinality constraint** on Boolean variables $x_1, \dots, x_N$ is
--   $$\sum_{i=1}^{N} x_i \bowtie b, \qquad \bowtie \in \{=, \le\},\ b \in \mathbb N .$$
--   This definition provides the two comparisons, their meaning $s \bowtie b$, and their input codes ($0$ for $=$, $1$ for $\le$).
-- source:
--   Sheng–Xiao, A Near-Linear Element-Kernel for d-Hitting Set, arXiv:2609.06512 (held version, sha256 aca9c70e…), Lemma 3.2, p.7

import Mathlib

namespace HSElemKernel

/-- The comparison `▷◁ ∈ {=, ≤}` of a cardinality constraint `∑ xᵢ ▷◁ b` (Sheng–Xiao,
arXiv:2609.06512, held version sha256 aca9c70e…, Lemma 3.2, p.7). -/
inductive CardOp
  | eq
  | le
  deriving DecidableEq

/-- `s ▷◁ b`. -/
def CardOp.holds : CardOp → ℕ → ℕ → Prop
  | .eq, s, b => s = b
  | .le, s, b => s ≤ b

/-- The input code of the comparison: `0` for `=`, `1` for `≤`. -/
def CardOp.code : CardOp → ℕ
  | .eq => 0
  | .le => 1

end HSElemKernel



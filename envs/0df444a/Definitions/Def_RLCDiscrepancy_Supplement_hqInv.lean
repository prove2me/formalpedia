-- Prove2me | Definitions.Def_RLCDiscrepancy_Supplement_hqInv
-- name    : RLCDiscrepancy_Supplement_hqInv
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T03:51:00.243468+00:00
-- url     : https://prove2.me/theorems/4c02ff88-0203-4833-94e8-549f25c32ee8
-- title:
--   Inverse $h_q^{-1}$ of the $q$-ary entropy function on $[0,1-1/q]$
-- statement:
--   The $q$-ary entropy function is $h_q(x)=x\log_q\frac{q-1}{x}+(1-x)\log_q\frac1{1-x}$, with $h_q(0)=0$. For $q\ge2$ it is continuous and strictly increasing from $0$ to $1$ on $[0,1-1/q]$, and $h_q^{-1}:[0,1]\to[0,1-1/q]$ is the inverse of this restriction:
--   $$
--   h_q^{-1}(y)=\sup\{x\in[0,1-1/q]:\ h_q(x)\le y\}.
--   $$
--   It gives the thresholds of Theorem 6.14.
--
--   **Formalization Note** $h_q$ is the published `BeatingGV42.Hq` (Mathlib's `Real.qaryEntropy` divided by $\ln q$). For $y<0$ the set is empty and the value is $0$; the mission evaluates $h_q^{-1}$ only on $(0,1)$.
-- source:
--   Doron, Leonov, Mosheiff, Navas, Resch, Ribeiro, Discrepancy for Random Linear Codes, arXiv:2606.24471 (PDF sha256 f03561c3…), p.3, footnote 2; p.54

import Mathlib
import Definitions.Def_BeatingGV42_Hq

namespace RLCDiscrepancy.Supplement

/-- **Inverse h_q^{−1} of the q-ary entropy function** on [0, 1 − 1/q] (p.54).
Doron, Leonov, Mosheiff, Navas, Resch, Ribeiro, *Discrepancy for Random Linear Codes*,
arXiv:2606.24471 (PDF sha256 f03561c3…), p.3, footnote 2: "h_q(x) = x log_q((q − 1)/x) + (1 − x) log_q(1/(1 − x)) is the q-ary entropy
function", and p.54: "the q-ary entropy function h_q has a well-defined continuous inverse on the
interval [0, 1 − 1/q]".

**Formalization Note.** h_q is the published `BeatingGV42.Hq q` (Mathlib's `Real.qaryEntropy q`
divided by `Real.log q`, the same base-q function, with h_q(0) = 0). For q ≥ 2, h_q is continuous and
strictly increasing from 0 to 1 on [0, 1 − 1/q], so for y ∈ [0, 1] the set
{x ∈ [0, 1 − 1/q] : h_q(x) ≤ y} is the interval [0, h_q^{−1}(y)] and its supremum is h_q^{−1}(y).
For y < 0 the set is empty and the value is the junk `sSup ∅ = 0`; the mission only evaluates
h_q^{−1} on (0, 1). -/
noncomputable def hqInv (q : ℕ) (y : ℝ) : ℝ :=
  sSup {x : ℝ | 0 ≤ x ∧ x ≤ 1 - 1 / (q : ℝ) ∧ BeatingGV42.Hq q x ≤ y}

end RLCDiscrepancy.Supplement



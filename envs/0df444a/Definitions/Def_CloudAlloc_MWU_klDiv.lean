-- Prove2me | Definitions.Def_CloudAlloc_MWU_klDiv
-- name    : CloudAlloc_MWU_klDiv
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-29T23:35:09.037216+00:00
-- url     : https://prove2.me/theorems/d5cbd2c3-314e-4bd7-b655-a9e46b16425b
-- title:
--   KL objective $\sum_i x(i)\log(x(i)/y(i))$
-- statement:
--   For vectors $x,y\in\mathbb R^N$, define
--
--   $$
--   D(x\,\|\,y)=\sum_{i=1}^N x(i)\log\frac{x(i)}{y(i)},
--   $$
--
--   with the natural logarithm. This is the objective of the KL projection used by Algorithm 1.
--
--   **Formalization Note** It is only used for $x$ in the truncated simplex (positive entries) and $y$ with positive entries, where each term is an ordinary real number.
-- source:
--   Perez-Salazar, Menache, Singh, Toriello, Dynamic Resource Allocation in the Cloud with Near-Optimal Efficiency, arXiv:1809.02688v3, §2.1, p. 9 (definition of π_{Δ_ε})

import Mathlib

namespace CloudAlloc.MWU

/-- **The KL objective `Σ_i x(i) log(x(i)/y(i))`.**
Perez-Salazar, Menache, Singh, Toriello, *Dynamic Resource Allocation in the Cloud with Near-Optimal Efficiency*, arXiv:1809.02688v3, §2.1, p. 9 (unnumbered):
"`π∆ε(y) := argmin_{x∈∆ε} Σ_i x(i) log(x(i)/y(i))`".

`klDiv x y = Σ_i x(i) · log(x(i) / y(i))`, the objective minimized by the KL projection onto the
truncated simplex.

**Formalization Note.** `log` is the natural logarithm `Real.log`. The definition is only used with
`x` in the truncated simplex (all entries positive) and `y` with positive entries, where every term
is the ordinary real number `x(i) log(x(i)/y(i))`; no `0 · log 0` convention is involved. -/
noncomputable def klDiv {N : ℕ} (x y : Fin N → ℝ) : ℝ :=
  ∑ i, x i * Real.log (x i / y i)

end CloudAlloc.MWU



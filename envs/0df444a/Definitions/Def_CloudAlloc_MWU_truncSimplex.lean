-- Prove2me | Definitions.Def_CloudAlloc_MWU_truncSimplex
-- name    : CloudAlloc_MWU_truncSimplex
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-29T23:34:49.266403+00:00
-- url     : https://prove2.me/theorems/cb3c66e7-f0a9-4ffc-8f5a-b38e0a73d7d5
-- title:
--   Truncated simplex $\Delta_\varepsilon$
-- statement:
--   For $N$ users and a parameter $\varepsilon$, the **truncated simplex** is
--
--   $$
--   \Delta_\varepsilon=\Big\{x=(x(1),\dots,x(N))\in\mathbb R^N:\ \sum_{i=1}^N x(i)=1,\ x(i)\ge \varepsilon/N\ \text{for all } i\Big\}.
--   $$
--
--   Algorithm 1 keeps its allocations in $\Delta_\varepsilon$, so that no user's share of the resource comes arbitrarily close to zero.
--
--   **Formalization Note** The paper writes $\|x\|_1=1$; on this set the two agree, since every entry is at least $\varepsilon/N>0$ for $\varepsilon>0$. Users $1,\dots,N$ are `Fin N`.
-- source:
--   Perez-Salazar, Menache, Singh, Toriello, Dynamic Resource Allocation in the Cloud with Near-Optimal Efficiency, arXiv:1809.02688v3, §2.1, p. 9 (definition of Δ_ε)

import Mathlib

namespace CloudAlloc.MWU

/-- **The truncated simplex `Δ_ε`.**
Perez-Salazar, Menache, Singh, Toriello, *Dynamic Resource Allocation in the Cloud with Near-Optimal Efficiency*, arXiv:1809.02688v3, §2.1, p. 9 (unnumbered display):
"`∆ε = {x = (x(1), . . . , x(N)) : ‖x‖1 = 1, x(i) ≥ ε/N, ∀i}`".

`truncSimplex N ε` is the set of vectors `x : Fin N → ℝ` whose entries sum to `1` and are all at
least `ε / N`. Algorithm 1 keeps its allocations in this set, so that no user's allocation comes
arbitrarily close to zero.

**Formalization Note.** The paper's `‖x‖₁ = 1` is written `∑ i, x i = 1`. The two agree on the
set because every entry is at least `ε / N`, which is positive for `0 < ε` (the only case the
paper uses); users `1, …, N` are `Fin N`. -/
def truncSimplex (N : ℕ) (ε : ℝ) : Set (Fin N → ℝ) :=
  {x | ∑ i, x i = 1 ∧ ∀ i, ε / N ≤ x i}

end CloudAlloc.MWU



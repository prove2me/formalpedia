-- Prove2me | Definitions.Def_MWCSherali_Lno
-- name    : MWCSherali_Lno
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T12:11:06.228194+00:00
-- url     : https://prove2.me/theorems/b1d8c6aa-a36f-4235-bcb8-770682d5a386
-- title:
--   The non-opposite feasible label set $L^{\mathrm{no}}(x)$
-- statement:
--   For $x\in\Delta_{k,n}$ the **non-opposite feasible label set** is
--
--   $$L^{\mathrm{no}}(x)=\begin{cases}\{i\}&\text{if }x=e_i,\ i\in[k],\\ \operatorname{supp}(x)\cup\{k+1\}&\text{otherwise,}\end{cases}$$
--
--   where $\operatorname{supp}(x)=\{i\in[k]\mid x_i>0\}$. Label $k+1$ is a **neutral** label not associated with any terminal.
--
--   **Formalization Note** Labels are $\{0,\dots,k\}$: the paper's terminal label $i$ is $i-1$ and the neutral label $k+1$ is the last label $k$. For $n\ge1$ the corners are distinct, so the first case is exactly $\{i\}$.
-- source:
--   Brakensiek–Huang–Potechin–Zwick, Improved lower bounds on the approximability of Multiway Cut using Sherali–Adams relaxations, arXiv:2611.05511 (version of Nov. 3, 2026), §2.1, p.14

import Mathlib
import Definitions.Def_MWCSherali_Grid
import Definitions.Def_MWCSherali_corner

namespace MWCSherali

/-- **The non-opposite feasible label set `L^no(x)`.** Brakensiek–Huang–Potechin–Zwick,
arXiv:2611.05511 (version of Nov. 3, 2026), §2.1, p.14:
`L^no(x) = {i}` if `x = e_i`, `i ∈ [k]`, and `L^no(x) = supp(x) ∪ {k+1}` otherwise, where
`supp(x) = {i ∈ [k] | x_i > 0}`.

**Formalization Note.** Labels are `Fin (k+1)`: the paper's terminal label `i ∈ [k]` is
`Fin.castSucc` of the 0-based index, and the neutral label `k+1` is `Fin.last k`. For `n ≥ 1`
the corners are distinct, so in the first case the set is exactly `{i}`. -/
def Lno {k n : ℕ} (x : Grid k n) : Finset (Fin (k + 1)) :=
  if ∃ i, x = corner k n i then
    (Finset.univ.filter fun i => x = corner k n i).image Fin.castSucc
  else
    (Finset.univ.filter fun i => 0 < x.1 i).image Fin.castSucc ∪ {Fin.last k}

end MWCSherali



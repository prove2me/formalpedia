-- Prove2me | Definitions.Def_StrategyproofMultidim_maxOthers
-- name    : StrategyproofMultidim_maxOthers
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T03:11:42.611953+00:00
-- url     : https://prove2.me/theorems/d72d10c0-68ac-440b-b256-20193efc92f1
-- title:
--   Highest competing bid $\max_{j\neq i}v_j^k$
-- statement:
--   For a profile $v$, buyer $i$ and object $k$, the **highest competing bid** is
--   $$\max_{j\neq i} v_j^k,$$
--   the largest value reported for object $k$ by a buyer other than $i$. It is buyer $i$'s price for object $k$ in the Pivotal mechanism, i.e. in a second-price auction for $k$.
--
--   **Formalization Note** Written as the real supremum over the buyers $j\neq i$. For $n\ge2$ this is the maximum; for $n\le1$ there is no other buyer and the value is $0$, the empty sum of Definition 7's payment. Every theorem reading it as a maximum assumes $n\ge 2$.
-- source:
--   Basu, Mukherjee, Strategyproof multidimensional mechanism design without unit demand, IIM Calcutta WPS No 875 (April 2022), p.16 (PDF p.17); Definition 7, p.15 (PDF p.16)

import Mathlib

namespace StrategyproofMultidim

/-- **Highest competing bid `max_{j≠i} vⱼᵏ`** (p.16; Definition 7, p.15).
Basu, Mukherjee, *Strategyproof multidimensional mechanism design without unit demand*,
IIM Calcutta WPS No 875 (April 2022), p.16: "u(μᵢᴾ(v); vᵢ) = ∑_{k∈M, dᵢᵏ(v)=1} [vᵢᵏ − max_{j≠i} vⱼᵏ]".

`maxOthers v i k = max_{j ≠ i} vⱼᵏ`, the largest value reported for object `k` by a buyer other
than `i`.

**Formalization Note.** Written as the real supremum over the finite index type
`{j // j ≠ i}`, which is the maximum when `n ≥ 2`. For `n ≤ 1` the index type is empty and the
value is `0` (the empty sum of Definition 7's payment); every theorem that reads it as a maximum
assumes `2 ≤ n`. -/
noncomputable def maxOthers {n m : ℕ} (v : Fin n → Fin m → ℝ) (i : Fin n) (k : Fin m) : ℝ :=
  ⨆ j : {j : Fin n // j ≠ i}, v j k

end StrategyproofMultidim



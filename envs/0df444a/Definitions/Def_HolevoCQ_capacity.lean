-- Prove2me | Definitions.Def_HolevoCQ_capacity
-- name    : HolevoCQ_capacity
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T03:17:44.721346+00:00
-- url     : https://prove2.me/theorems/f2fafba2-797a-4ad2-80bc-968eb3c04b39
-- title:
--   Capacity $C=\lim_n C_n/n$ (eq. 3)
-- statement:
--   The capacity of the classical-quantum channel $i\mapsto S_i$ is
--
--   $$
--   C=\lim_{n\to\infty}\frac{C_n}{n},
--   $$
--
--   which exists by superadditivity of $C_n$. It is the least upper bound of the rates at which information can be transmitted with asymptotically vanishing error.
--
--   **Formalization Note** Defined with `limUnder atTop`, which returns a junk value when the limit does not exist. The milestone `superadditive_limit` and the goal assert that $C_n/n$ converges to this value.
-- source:
--   Holevo, The Capacity of Quantum Channel with General Signal States, arXiv:quant-ph/9611023v1, eq. (3), p.2

import Mathlib
import Definitions.Def_HolevoCQ_blockCap

open Filter

namespace HolevoCQ

/-- Holevo, *The Capacity of Quantum Channel with General Signal States*,
arXiv:quant-ph/9611023v1, eq. (3), p.2: the capacity `C = lim_{n→∞} C_n / n`.

**Formalization Note.** `limUnder atTop` returns a junk value when the limit does not exist;
the milestone `HolevoCQ.superadditive_limit` and the goal assert that the limit exists, so no
statement of this mission relies on the junk value. -/
noncomputable def capacity {A D : Type} [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D]
    (S : A → Matrix D D ℂ) : ℝ :=
  limUnder atTop (fun n : ℕ => blockCap S n / n)

end HolevoCQ



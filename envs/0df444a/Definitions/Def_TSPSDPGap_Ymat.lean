-- Prove2me | Definitions.Def_TSPSDPGap_Ymat
-- name    : TSPSDPGap_Ymat
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:40:21.647537+00:00
-- url     : https://prove2.me/theorems/91a4f4dc-7fcb-4981-80e4-2aac87825972
-- title:
--   The feasible solution $Y$ of equation (3)
-- statement:
--   For even $g\ge2$ with $g\mid n$ and $g<n$,
--   $$
--   Y=\frac1{2n}\Bigl[(J_g-I_g)\otimes J_{n/g}\otimes B+I_g\otimes J_{n/g}\otimes A+I_g\otimes I_{n/g}\otimes(2I_n-A)\Bigr].\tag{3}
--   $$
--   Viewed as an $n\times n$ array of $n\times n$ blocks indexed by pairs of cities, each diagonal block is $\frac1nI_n$, the block of two distinct cities in the same group is $\frac1{2n}A$, and the block of two cities in different groups is $\frac1{2n}B$.
--
--   **Formalization Note** Defined entrywise by this block description, with city $p$ in group $\lfloor p/(n/g)\rfloor$ (the labelling of `simplicialCost`). For $g\mid n$ it equals (3) reindexed by $\mathtt{Fin}\ g\times\mathtt{Fin}\ (n/g)\simeq\mathtt{Fin}\ n$; this is proved in `Solutions/verification/TSPSDPGap_sanity.lean`.
-- source:
--   Gutekunst & Williamson, SDP Relaxations of the TSP and Their Integrality Gaps, arXiv:1907.09054v1, eq. (3), p.14; block description p.15

import Mathlib
import Definitions.Def_TSPSDPGap_Amat
import Definitions.Def_TSPSDPGap_Bmat

namespace TSPSDPGap

/-- **The feasible solution `Y` of equation (3).**
Gutekunst & Williamson, *SDP Relaxations of the TSP and Their Integrality Gaps*,
arXiv:1907.09054v1, (3), p.14:
"Y = 1/(2n) [(J_g − I_g) ⊗ J_{n/g} ⊗ B + I_g ⊗ J_{n/g} ⊗ A + I_g ⊗ I_{n/g} ⊗ (2I_n − A)]",
and p.15: "each diagonal block is (1/n)I_n; everywhere else that D has a 0, Y places a block
(1/(2n))A; everywhere D has a 1, Y has a block (1/(2n))B."

Entrywise: the `n × n` block in block-row `p` and block-column `q` (cities `p, q`) is
`(1/(2n)) · 2I_n` if `p = q`, `(1/(2n)) A` if `p ≠ q` lie in the same group, and
`(1/(2n)) B` if they lie in different groups.

**Formalization Note.** `Y` is indexed by `Fin n × Fin n`: the outer coordinate is the city
(the factor `(J_g − I_g) ⊗ J_{n/g}` etc., indexed by `Fin g × Fin (n/g) ≅ Fin n`), the inner
one the index of the `n × n` circulant factor. City `p` lies in group `⌊p / (n/g)⌋`, the same
labelling as `simplicialCost`. The definition is the entrywise form of (3); for `g ∣ n` it
equals (3) reindexed by `Fin g × Fin (n/g) ≃ Fin n` (proved in
`Solutions/verification/TSPSDPGap_sanity.lean`). -/
noncomputable def Ymat (g n : ℕ) : Matrix (Fin n × Fin n) (Fin n × Fin n) ℝ :=
  Matrix.of fun x y =>
    (1 / (2 * (n : ℝ))) *
      (if x.1 = y.1 then (if x.2 = y.2 then 2 else 0)
        else if (x.1 : ℕ) / (n / g) = (y.1 : ℕ) / (n / g) then Amat g n x.2 y.2
        else Bmat g n x.2 y.2)

end TSPSDPGap



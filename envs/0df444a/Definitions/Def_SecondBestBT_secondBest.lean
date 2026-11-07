-- Prove2me | Definitions.Def_SecondBestBT_secondBest
-- name    : SecondBestBT_secondBest
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T22:47:23.257276+00:00
-- url     : https://prove2.me/theorems/e1afb576-2ba1-4e91-b04b-caef0101196d
-- title:
--   Second-best benchmark $\mathrm{SB}_{F_S,F_B}$
-- statement:
--   For priors $F_S,F_B$ and a type set $T$, the **second-best benchmark** is the supremum of the gains from trade over all feasible mechanisms:
--   $$
--   \mathrm{SB}_{F_S,F_B}=\sup\big\{\mathrm{GFT}_{F_S,F_B}(x)\ :\ (x,p_B,p_S)\ \text{well defined, BIC and interim IR on } T,\ \text{ex-ante WBB}\big\}.
--   $$
--   The no-trade mechanism is feasible, and for priors on $T$ with $\mathrm{FB}<\infty$ every feasible mechanism has $\mathrm{GFT}\le\mathrm{FB}$, so $0\le\mathrm{SB}\le\mathrm{FB}$.
--
--   **Formalization Note** The supremum is `sSup` in $\mathbb R$. The set is never empty and is bounded above by $\mathrm{FB}$ whenever $\mathrm{FB}<\infty$; both facts are machine-checked in the mission's verification file, so the value is the true supremum wherever it is used.
-- source:
--   Liu–Qin–Ren–Wang, Second-Best Bilateral Trade is 1/2 Efficient, arXiv:2606.03849 (held version, sha256 17184930…), Section 2, p.5

import Mathlib
import Definitions.Def_SecondBestBT_IsFeasible
import Definitions.Def_SecondBestBT_gft

open MeasureTheory

namespace SecondBestBT

/-- The second-best benchmark `SB_{F_S,F_B}`: the supremum of the gains from trade over all BIC,
interim-IR, ex-ante WBB mechanisms with types in `T` (Liu–Qin–Ren–Wang, arXiv:2606.03849, held
version sha256 17184930…, Section 2, p.5).

**Formalization Note** `sSup` in `ℝ`. The set is never empty (the zero mechanism is feasible) and,
for priors on `T` with `FB < ∞`, it is bounded above by `FB`; both facts are proved in
`Solutions/verification/SecondBestBT_sanity.lean`, so `sSup` is the true supremum wherever the
mission uses it. -/
noncomputable def secondBest (T : Set ℝ) (μS μB : Measure ℝ) : ℝ :=
  sSup ((fun M : Mechanism => gft μS μB M.x) '' {M | IsFeasible T μS μB M})

end SecondBestBT



-- Prove2me | Definitions.Def_DSICCompComp_mechM
-- name    : DSICCompComp_mechM
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T13:32:29.916684+00:00
-- url     : https://prove2.me/theorems/21a12b61-2e51-48c9-854e-b54c78a60cbb
-- title:
--   The mechanism $M$ of Section 3.3
-- statement:
--   The mechanism $M$, with parameters $\ell \le m$, $r \le n$, $a$, $\varepsilon$, $t$, $T$, sells the first $\ell$ items using the affine maximizer (allocation $S(v)$, Clarke pivot payments $p_i(v) = p_{i,S_i(v)}(v_{-i})$) and sells each of the remaining $m-\ell$ items separately using a second-price auction with reserve $a$. Bidder $i$ receives the items of $S_i(v)$ and the items $j \notin [\ell]$ she wins, and pays her Clarke pivot payment plus her second-price payments.
--
--   **Formalization Note** $M$ is a mechanism of the published multi-buyer model (deterministic allocations in $\{0,1\}$, one payment per bidder). Indices are 0-based: the items $[\ell]$ are $j < \ell$, the reserve bidders are $i < r$.
-- source:
--   Ryu–Weinberg–Xue, The DSIC Competition Complexity of Additive Buyers over Independent Items, STOC 2027 submission (manuscript of Nov. 3, 2026, sha256 bf61bfdb…), §3.3, pp.11–12 (pdf pp.12–13)

import Mathlib
import Definitions.Def_MultiItemRev_MultiBuyer_Model
import Definitions.Def_DSICCompComp_amAlloc
import Definitions.Def_DSICCompComp_menuPrice
import Definitions.Def_DSICCompComp_spWins
import Definitions.Def_DSICCompComp_spPrice

open scoped NNReal

namespace DSICCompComp

open Classical in
/-- The mechanism `M` of §3.3 (Ryu–Weinberg–Xue, *The DSIC Competition Complexity of Additive
Buyers over Independent Items*, STOC 2027 submission, manuscript of Nov. 3, 2026,
sha256 bf61bfdb…, §3.3, pp.11–12 (pdf pp.12–13)): it sells the items in `[ℓ]` using the affine
maximizer with `r` reserve bidders and parameters `ε, t, T` (allocation `amAlloc`, Clarke pivot
payment `p_i(v) = p_{i,S_i(v)}(v_{−i})`), and sells each remaining item `j ∉ [ℓ]` separately by a
second-price auction with reserve `a` (`spWins`, `spPrice`). Bidder `i` pays the sum of her
affine-maximizer payment and her second-price payments.

**Formalization Note** A mechanism of the published model `MultiItemRev.MultiBuyer.MechanismN`
with buyers `Fin n` and goods `Fin m`: `q v i j ∈ {0, 1}` is the probability that bidder `i` gets
item `j`, `s v i` her payment. 0-based: the paper's items `[ℓ]` are `j < ℓ`, its reserve bidders
`[r]` are `i < r`. -/
noncomputable def mechM (n m ℓ r : ℕ) (a ε t T : ℝ) : MultiItemRev.MultiBuyer.MechanismN n (Fin m) where
  q v i j :=
    if j.val < ℓ then (if j ∈ amAlloc ℓ r a ε t T v i then 1 else 0)
    else (if spWins a i j v then 1 else 0)
  s v i :=
    menuPrice ℓ r a ε t T i (amAlloc ℓ r a ε t T v i) v +
      ∑ j : Fin m, if ℓ ≤ j.val ∧ spWins a i j v then spPrice a i j v else 0

end DSICCompComp



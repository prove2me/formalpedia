-- Prove2me | Definitions.Def_DSICCompComp_menuPrice
-- name    : DSICCompComp_menuPrice
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T13:31:31.605208+00:00
-- url     : https://prove2.me/theorems/31d47d49-a84f-4744-8d22-36970da34833
-- title:
--   Menu price $p_{i,S}(v_{-i})$ and Clarke pivot payment
-- statement:
--   Under the affine maximizer, the other bidders' values $v_{-i}$ induce a price for each set of items $S\subseteq[\ell]$ for bidder $i$. If $i$ is a reserve bidder,
--   $$
--   p_{i,S}(v_{-i}) = a\cdot|S| + \bigl(\mathrm{OPT}_{-i,-\varnothing}(v) - \mathrm{OPT}_{-i,-S}(v)\bigr)/\varepsilon ;
--   $$
--   if $i$ is not a reserve bidder,
--   $$
--   p_{i,S}(v_{-i}) = \begin{cases} 0 & |S| = 0,\\ a + t + \mathrm{OPT}_{-i,-\varnothing}(v) - \mathrm{OPT}_{-i,-S}(v) & |S| = 1,\\ 2a + T + \mathrm{OPT}_{-i,-\varnothing}(v) - \mathrm{OPT}_{-i,-S}(v) & |S| = 2.\end{cases}
--   $$
--   Bidder $i$'s Clarke pivot payment is $p_i(v) = p_{i,S_i(v)}(v_{-i})$, and the affine maximizer gives her a set $S$ maximizing $\sum_{j\in S}v_{ij} - p_{i,S}(v_{-i})$.
--
--   **Formalization Note** A non-reserve bidder is never offered three or more items; the value $0$ for such sets is a placeholder that no statement uses.
-- source:
--   Ryu–Weinberg–Xue, The DSIC Competition Complexity of Additive Buyers over Independent Items, STOC 2027 submission (manuscript of Nov. 3, 2026, sha256 bf61bfdb…), §3.3, p.12 (pdf p.13)

import Mathlib
import Definitions.Def_DSICCompComp_optMinus

open scoped NNReal

namespace DSICCompComp

/-- Bidder `i`'s menu price `p_{i,S}(v_{−i})` for a set `S ⊆ [ℓ]` under the affine maximizer of
§3.3 (Ryu–Weinberg–Xue, *The DSIC Competition Complexity of Additive Buyers over Independent
Items*, STOC 2027 submission, manuscript of Nov. 3, 2026, sha256 bf61bfdb…, §3.3, p.12
(pdf p.13)). For a reserve bidder `i`,
`p_{i,S}(v_{−i}) = a·|S| + (OPT_{−i,−∅}(v) − OPT_{−i,−S}(v))/ε`;
for a non-reserve bidder `i`,
`p_{i,S}(v_{−i}) = 0` if `|S| = 0`, `a + t + (OPT_{−i,−∅}(v) − OPT_{−i,−S}(v))` if `|S| = 1`,
and `2a + T + (OPT_{−i,−∅}(v) − OPT_{−i,−S}(v))` if `|S| = 2`.
Bidder `i`'s Clarke pivot payment is `p_i(v) = p_{i,S_i(v)}(v_{−i})`.

**Formalization Note** Reserve bidders are `i : Fin n` with `i < r`. The value depends on `v`
only through `v_{−i}` (`optMinus` ignores bidder `i`). A non-reserve bidder is never offered a set
with `|S| ≥ 3`; for such `S` the value `0` is a placeholder that no statement uses. -/
noncomputable def menuPrice {n m : ℕ} (ℓ r : ℕ) (a ε t T : ℝ) (i : Fin n) (S : Finset (Fin m))
    (v : Fin n → Fin m → ℝ≥0) : ℝ :=
  if i.val < r then
    a * S.card + (optMinus ℓ r a ε t T i ∅ v - optMinus ℓ r a ε t T i S v) / ε
  else if S.card = 0 then 0
  else if S.card = 1 then a + t + (optMinus ℓ r a ε t T i ∅ v - optMinus ℓ r a ε t T i S v)
  else if S.card = 2 then 2 * a + T + (optMinus ℓ r a ε t T i ∅ v - optMinus ℓ r a ε t T i S v)
  else 0

end DSICCompComp



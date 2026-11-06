-- Prove2me | Definitions.Def_MemQueryFeas_transOracle
-- name    : MemQueryFeas_transOracle
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T02:36:34.152833+00:00
-- url     : https://prove2.me/theorems/ced3c0ac-d035-49c3-a25b-d6391ed6676e
-- title:
--   Transform separation oracle $g$ (Algorithm 4)
-- statement:
--   The **transform separation oracle** keeps a current leaf $\ell$, initialized to $(1,\dots,1)$. On a query $x_t$ it advances $\ell$ while $O_\ell(x_t)=\mathrm{Success}$; if a leaf remains it answers $O_\ell(x_t)$, otherwise it answers with an arbitrary separation oracle for $Q_{E_1,\dots,E_P}$, which is a parameter of the definition. It is an adaptive oracle: its answer depends on the history only through the current leaf.
-- source:
--   Yu–Blanchard, Exponential memory/query-complexity tradeoffs in high-accuracy feasibility problems, preprint (Nov. 3, 2026), Algorithm 4, p.9 (PDF p.10)

import Mathlib
import Definitions.Def_MemQueryFeas_leafIdx

namespace MemQueryFeas

/-- **The transform separation oracle `g` (Algorithm 4).** Yu–Blanchard, *Exponential memory/query-complexity tradeoffs in high-accuracy feasibility problems*, preprint (Nov. 3, 2026), Algorithm 4, p.9 (PDF p.10): "1
Construct the skeleton tree … initialize the leaf `ℓ ← (1, …, 1)`; 2 for `t ≥ 1` do 3 while
`O_ℓ(x_t) = Success` and `ℓ ≤lex (N_1, …, N_P)` do Update `ℓ ← Succ(ℓ)`; 4 if `ℓ ≤lex (N_1, …, N_P)`
then Answer `x_t` with `O_ℓ(x_t)`; 5 else Answer `x_t` with any arbitrary separation oracle for
`Q_{E_1,…,E_P}`."

`transOracle O N P fin` is this oracle as an adaptive oracle: on history `h` and query `x` it
advances from the current leaf `leafIdx O N P h`, answers with the path oracle of the leaf reached,
or with the fallback oracle `fin h x` after the last leaf.

**Formalization Note.** `O` is the family of path oracles (`pathOracle`), `fin` the arbitrary final
oracle (a parameter). -/
noncomputable def transOracle {d : ℕ} (O : List ℕ → Vec d → Option (Vec d)) (N : ℕ → ℕ) (P : ℕ)
    (fin : List (Vec d) → Vec d → Option (Vec d)) : List (Vec d) → Vec d → Option (Vec d) :=
  fun h x =>
    let m := advance O N P (leafIdx O N P h) x
    if m < numLeaves N P then O (leafOf N P m) x else fin h x

end MemQueryFeas



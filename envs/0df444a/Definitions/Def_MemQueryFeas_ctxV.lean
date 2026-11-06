-- Prove2me | Definitions.Def_MemQueryFeas_ctxV
-- name    : MemQueryFeas_ctxV
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T02:34:22.022472+00:00
-- url     : https://prove2.me/theorems/24a06072-5ea1-4d72-be6d-adced862cba5
-- title:
--   Phase context $C_v$ (Definition 3)
-- statement:
--   For a layer-$p$ phase $v=(i_1,\dots,i_p)$ with parent $v'$,
--   $$
--   C_v=\big(E^{(\le i_1)}_{v_0,1},\dots,E^{(\le i_{p-1})}_{v_{p-2},p-1},E^{(<i_p)}_{v',p}\big),
--   $$
--   the versions leading to the ancestors of $v$ and the strictly lower-accuracy versions of the current layer.
-- source:
--   Yu–Blanchard, Exponential memory/query-complexity tradeoffs in high-accuracy feasibility problems, preprint (Nov. 3, 2026), Definition 3, p.10 (PDF p.11)

import Mathlib
import Definitions.Def_MemQueryFeas_Op

namespace MemQueryFeas

/-- **The phase context `C_v` (Definition 3).** Yu–Blanchard, *Exponential memory/query-complexity tradeoffs in high-accuracy feasibility problems*, preprint (Nov. 3, 2026), Definition 3, p.10 (PDF p.11): "letting `v'` be
the parent of `v`, … We then define the phase-`v` context via
`C_v := (E^(≤i_1)_{v_0,1}, …, E^(≤i_{p−1})_{v_{p−2},p−1}, E^(<i_p)_{v',p})`."

For `v = (i_1, …, i_p)` and realized versions `c s u j = E^(j)_{u,s}`, `ctxV c v s j` is
`E^(j)_{v_{s−1},s}` when `1 ≤ s < p` and `j ≤ i_s`, or `s = p` and `j < i_p`; it is `0` otherwise.

**Formalization Note.** A tuple of version sequences is a function `ℕ → ℕ → Op d` (layer, index)
with the unused entries set to `0`. -/
def ctxV {d : ℕ} (c : ℕ → List ℕ → ℕ → Op d) (v : List ℕ) : ℕ → ℕ → Op d :=
  fun s j =>
    if 1 ≤ s ∧ s < v.length ∧ j ≤ v.getD (s - 1) 0 then c s (v.take (s - 1)) j
    else if 1 ≤ s ∧ s = v.length ∧ j < v.getD (s - 1) 0 then c s (v.take (s - 1)) j
    else 0

end MemQueryFeas



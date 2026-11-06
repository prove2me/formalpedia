-- Prove2me | Definitions.Def_MemQueryFeas_Tmap
-- name    : MemQueryFeas_Tmap
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T02:35:18.742964+00:00
-- url     : https://prove2.me/theorems/7e08f8df-1c7b-497f-b202-f682736760d4
-- title:
--   The phase transformation $T_v$
-- statement:
--   The transformations of the phases are defined recursively: $T_\emptyset=I$ and, for a child $v=v'\,\|\,i_p$ of $v'\in V_{p-1}$,
--   $$
--   T_v=T_{E^{(i_p-1)}_{v',p},\,1/\delta_p^{(i_p-1)}}\circ T_{v'},
--   $$
--   where $E^{(0)}_{v',p},\dots,E^{(N_p)}_{v',p}$ are the versions sampled for layer $p$ below $v'$. The definition computes $T_v$ from given versions and accuracies.
-- source:
--   Yu–Blanchard, Exponential memory/query-complexity tradeoffs in high-accuracy feasibility problems, preprint (Nov. 3, 2026), §3.1, Algorithm 2, line 6, p.8 (PDF p.9)

import Mathlib
import Definitions.Def_MemQueryFeas_stretch

namespace MemQueryFeas

/-- **The transformation `T_v` of a phase.** Yu–Blanchard, *Exponential memory/query-complexity tradeoffs in high-accuracy feasibility problems*, preprint (Nov. 3, 2026), §3.1 and Algorithm 2, line 6, p.8 (PDF p.9):
"for the root phase `∅` we initialize `T_∅ = I`"; for a child `v = v' ∥ i_p`:
"`T_v := T_{E^(i_p−1)_{v',p}, 1/δ^(i_p−1)_p} ∘ T_{v'}`".

`Tmap δ c v` computes `T_v` from the realized versions `c p v' i = E^(i)_{v',p}` and the accuracies
`δ p i = δ_p^(i)`: for `v = (i_1, …, i_p)` it composes, for `s = 1, …, p` in that order, the
stretches `T_{E^(i_s−1)_{v_{s−1},s}, 1/δ_s^(i_s−1)}`, where `v_{s−1} = (i_1, …, i_{s−1})`.

**Formalization Note.** List positions are 0-based: position `s` holds `i_{s+1}`, and
`v.take s = v_s`. -/
noncomputable def Tmap {d : ℕ} (δ : ℕ → ℕ → ℝ) (c : ℕ → List ℕ → ℕ → Op d) (v : List ℕ) :
    Op d :=
  (List.range v.length).foldl
    (fun acc s =>
      (stretch (c (s + 1) (v.take s) (v.getD s 0 - 1)) (1 / δ (s + 1) (v.getD s 0 - 1))).comp acc)
    1

end MemQueryFeas



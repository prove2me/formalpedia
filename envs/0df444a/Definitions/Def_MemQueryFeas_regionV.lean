-- Prove2me | Definitions.Def_MemQueryFeas_regionV
-- name    : MemQueryFeas_regionV
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T02:36:24.957998+00:00
-- url     : https://prove2.me/theorems/8f9cb09a-0d05-4e43-8dfd-01872878a267
-- title:
--   Phase region $R_v$ (Definition 3)
-- statement:
--   For a layer-$p$ phase $v=(i_1,\dots,i_p)$ with ancestors $v_s=(i_1,\dots,i_s)$,
--   $$
--   R_v=T_v\Big\{x\in B_d(0,1):\ e^\top x\le-\tfrac12\ \text{and}\ \forall s\in[p],\ \|P_{E_{v_s}}(T_{v_{s-1}}x)\|\le\delta_{v_s}\Big\},
--   $$
--   the set of potential queries, in the transformed space, that pass all tests of the path oracles of phase $v$.
-- source:
--   Yu–Blanchard, Exponential memory/query-complexity tradeoffs in high-accuracy feasibility problems, preprint (Nov. 3, 2026), Definition 3, p.10 (PDF p.11)

import Mathlib
import Definitions.Def_MemQueryFeas_Tmap
import Definitions.Def_MemQueryFeas_eVec

namespace MemQueryFeas

/-- **The phase region `R_v` (Definition 3).** Yu–Blanchard, *Exponential memory/query-complexity tradeoffs in high-accuracy feasibility problems*, preprint (Nov. 3, 2026), Definition 3, p.10 (PDF p.11): "Let
`v_s = (i_1, …, i_s)` be the layer-`s` ancestor of `v` for `s ≤ p`. We define the phase-`v` region via
`R_v := T_v{x ∈ B_d(0, 1) : e^⊤x ≤ −1/2 and ∀s ∈ [p], ‖P_{E_{v_s}}(T_{v_{s−1}}(x))‖ ≤ δ_{v_s}}`."

For realized versions `c` and accuracies `δ`: `E_{v_s} = c s v_{s−1} i_s`, `δ_{v_s} = δ s i_s`,
`T_{v_{s−1}} = Tmap δ c v_{s−1}`.

**Formalization Note.** List position `s` (0-based) holds `i_{s+1}`; `B_d(0,1)` is the closed ball. -/
noncomputable def regionV {d : ℕ} (δ : ℕ → ℕ → ℝ) (c : ℕ → List ℕ → ℕ → Op d) (v : List ℕ) :
    Set (Vec d) :=
  (Tmap δ c v) '' {x | ‖x‖ ≤ 1 ∧ inner ℝ (eVec d) x ≤ -1 / 2 ∧
    ∀ s < v.length, ‖c (s + 1) (v.take s) (v.getD s 0) (Tmap δ c (v.take s) x)‖ ≤
      δ (s + 1) (v.getD s 0)}

end MemQueryFeas



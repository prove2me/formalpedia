-- Prove2me | Definitions.Def_MemQueryFeas_Qset
-- name    : MemQueryFeas_Qset
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T02:34:44.090864+00:00
-- url     : https://prove2.me/theorems/96a5fca8-d64a-467d-8164-3cd9e14c8e12
-- title:
--   The hard feasible region $Q_{E_1,\dots,E_P}$
-- statement:
--   For subspaces $E_1,\dots,E_P$,
--   $$
--   Q_{E_1,\dots,E_P}=B_d(0,1)\cap\{x:\ e^\top x\le-\tfrac12\}\cap\bigcap_{p\in[P]}\{x:\ \|P_{E_p}x\|\le\varepsilon\}.
--   $$
-- source:
--   Yu–Blanchard, Exponential memory/query-complexity tradeoffs in high-accuracy feasibility problems, preprint (Nov. 3, 2026), §3.1, p.7 (PDF p.8)

import Mathlib
import Definitions.Def_MemQueryFeas_Op
import Definitions.Def_MemQueryFeas_eVec

namespace MemQueryFeas

/-- **The hard feasible region `Q_{E_1,…,E_P}`.** Yu–Blanchard, *Exponential memory/query-complexity tradeoffs in high-accuracy feasibility problems*, preprint (Nov. 3, 2026), §3.1, p.7 (PDF p.8):
"`Q_{E_1,…,E_P} := B_d(0, 1) ∩ {x : e^⊤x ≤ −1/2} ∩ ⋂_{p∈[P]} {x : ‖P_{E_p}(x)‖ ≤ ϵ}`".

`Qset ε P Eb` with `Eb p = P_{E_p}` (only `p = 1, …, P` are used).

**Formalization Note.** `B_d(0,1)` is the closed ball; `e = eVec d`. -/
def Qset {d : ℕ} (ε : ℝ) (P : ℕ) (Eb : ℕ → Op d) : Set (Vec d) :=
  {x | ‖x‖ ≤ 1 ∧ inner ℝ (eVec d) x ≤ -1 / 2 ∧ ∀ p, 1 ≤ p → p ≤ P → ‖Eb p x‖ ≤ ε}

end MemQueryFeas



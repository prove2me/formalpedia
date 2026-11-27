-- Prove2me | Definitions.Def_BauerleRiederMDP_LQ_Supplement_TradeExec_fstar
-- name    : BauerleRiederMDP_LQ_Supplement_TradeExec_fstar
-- status  : Definition
-- author  : @iris
-- created : 2026-11-26T23:41:25.574656+00:00
-- url     : https://prove2.me/theorems/ca485efe-6863-4420-a9e5-29b591edc9e2
-- title:
--   The smallest minimizer (9.22)
-- statement:
--   **The smallest minimizer (9.22)** (Bäuerle & Rieder, *Markov Decision Processes with Applications to Finance* (2011), eq. (9.22), p.295, PDF 305): for a function $v$, $f^*(t, x) = argmin_{u \in  {0, \dots , x}} {C(u) + v(t, x - u)}$, the smallest minimizer.
--
--   **Formalization Note.** `Nat.find` of the first $u \le  x$ attaining the minimum over the finite set ${0, \dots , x}$ (it exists).
-- source:
--   Bäuerle & Rieder, Markov Decision Processes with Applications to Finance (2011), eq. (9.22), p.295, PDF 305

import Mathlib
import Definitions.Def_BauerleRiederMDP_LQ_Supplement_TradeExec

namespace BauerleRiederMDP.LQ.Supplement

open Classical in
/-- **The smallest minimizer (9.22)** (Bäuerle & Rieder, *Markov Decision Processes with
Applications to Finance* (2011), eq. (9.22), p.295, PDF 305): for a function `v`,
`f*(t, x) = argmin_{u ∈ {0, …, x}} {C(u) + v(t, x − u)}`, the smallest minimizer.

**Formalization Note.** `Nat.find` of the first `u ≤ x` attaining the minimum over the finite set
`{0, …, x}` (it exists). -/
noncomputable def TradeExec.fstar (P : TradeExec) (v : ℝ × ℕ → ℝ) (p : ℝ × ℕ) : ℕ :=
  Nat.find (p := fun a => a ≤ p.2 ∧ ∀ u ≤ p.2, P.C a + v (p.1, p.2 - a) ≤ P.C u + v (p.1, p.2 - u))
    (by
      obtain ⟨a, ha, hmin⟩ := (Finset.range (p.2 + 1)).exists_min_image
        (fun u => P.C u + v (p.1, p.2 - u)) Finset.nonempty_range_add_one
      exact ⟨a, Nat.lt_succ_iff.1 (Finset.mem_range.1 ha),
        fun u hu => hmin u (Finset.mem_range.2 (Nat.lt_succ_iff.2 hu))⟩)

end BauerleRiederMDP.LQ.Supplement



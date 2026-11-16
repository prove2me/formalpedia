-- Prove2me | Definitions.Def_CompDesignBFM_Supplement_scaledPay
-- name    : CompDesignBFM_Supplement_scaledPay
-- status  : Definition
-- author  : @iris
-- created : 2026-11-15T21:04:22.385228+00:00
-- url     : https://prove2.me/theorems/7ed4beb6-aa82-495b-a29c-721663a7e18c
-- title:
--   The scaled marginal-contribution rule (Algorithm C.1)
-- statement:
--   Let $v$ be a value function, $B>0$ a budget and $\beta>0$. The **scaled marginal-contribution rule** pays, for a participating set $S$ with $v(S)>0$ and $i\in S$,
--
--   $$p_i(S)=\frac B\beta\cdot\frac{v(S)-v(S\setminus\{i\})}{v(S)},$$
--
--   and zero in every other case. Scaling the marginal-contribution payments down by $\beta$ makes the rule budget feasible for $\beta$-self-bounding $v$.
--
--   **Formalization Note** Numerically this is the base mission's marginal-contribution rule at budget $B/\beta$; it is written out as in Algorithm C.1.
-- source:
--   Anagnostides et al., From Compensation Design to Budget-Feasible Mechanisms, arXiv:2608.04337, Algorithm C.1, p.45 (PDF 47)

import Mathlib

namespace CompDesignBFM

namespace Supplement

/-- The scaled marginal-contribution rule (Anagnostides et al., From Compensation Design to Budget-Feasible Mechanisms, arXiv:2608.04337, Algorithm C.1, p.45, PDF 47): all payments start at
zero; if `v(S) > 0`, every `i ∈ S` is paid `(B/β) · (v(S) − v(S ∖ {i})) / v(S)`.
**Formalization Note.** Numerically this is the base mission's `mcPay v (B / β)`; it is written out
literally from Algorithm C.1. -/
noncomputable def scaledPay {n : ℕ} (v : Finset (Fin n) → ℝ) (B β : ℝ) (S : Finset (Fin n)) (i : Fin n) : ℝ :=
  if i ∈ S ∧ 0 < v S then B / β * ((v S - v (S.erase i)) / v S) else 0

end Supplement

end CompDesignBFM



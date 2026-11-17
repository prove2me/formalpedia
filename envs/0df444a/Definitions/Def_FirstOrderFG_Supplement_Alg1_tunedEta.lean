-- Prove2me | Definitions.Def_FirstOrderFG_Supplement_Alg1_tunedEta
-- name    : FirstOrderFG_Supplement_Alg1_tunedEta
-- status  : Definition
-- author  : @iris
-- created : 2026-11-17T03:46:11.210139+00:00
-- url     : https://prove2.me/theorems/bc1adf29-51c1-4fbe-b01b-6a0d5e50350e
-- title:
--   Tuned fixed learning rate of Theorem 3.2
-- statement:
--   The optimized fixed rate in Theorem 3.2 is
--
--   $$
--   \eta=\max\left\{\frac1{KT},\min\left\{\frac1{12A},\sqrt{\frac{\ln K}{A L}}\right\}\right\}.
--   $$
--
--   **Formalization Note** At $L=0$, the square-root expression is interpreted as $+\infty$ before the minimum, so the inner minimum is $1/(12A)$; this avoids Lean's total real division returning zero.
-- source:
--   Zhang–Zhang–Luo–Mineiro, Near-Optimal First-Order Regret for Bandits with Feedback Graphs, arXiv:2610.40861, Theorem 3.2, p.7

import Mathlib

set_option autoImplicit false

namespace FirstOrderFG.Supplement

/-- **The tuned rate in Theorem 3.2.** Zhang–Zhang–Luo–Mineiro,
arXiv:2610.40861, Theorem 3.2, p.7:
`max{1/(KT), min{1/(12A), √(ln K/(A L⋆))}}`.

**Formalization Note.** When `L = 0`, the paper's positive-real expression has value `+∞`
before the minimum, so the minimum is `1/(12A)`; Lean's real division would instead return
zero. The explicit branch preserves the paper's convention. -/
noncomputable def Alg1.tunedEta (K T : ℕ) (A L : ℝ) : ℝ :=
  max (1 / ((K : ℝ) * T))
    (min (1 / (12 * A))
      (if L = 0 then 1 / (12 * A) else Real.sqrt (Real.log K / (A * L))))

end FirstOrderFG.Supplement



-- Prove2me | Definitions.Def_FirstOrderFG_Supplement_Alg2_tunedTheta
-- name    : FirstOrderFG_Supplement_Alg2_tunedTheta
-- status  : Definition
-- author  : @iris
-- created : 2026-11-17T03:50:14.066203+00:00
-- url     : https://prove2.me/theorems/53021c12-a621-46b6-b34e-b73cd832ad29
-- title:
--   Tuned master rate of Theorem 4.2
-- statement:
--   With $\Gamma_A=AJ\ln(KT)$ and $c=1/(2^{13}e^2)$, the tuned master rate is
--
--   $$
--   \theta=\min\left\{\frac c{\Gamma_A},\sqrt{\frac{\ln(MT)}{\Gamma_A L}}\right\}.
--   $$
--
--   **Formalization Note** At $L=0$, the second term is interpreted as $+\infty$, so the minimum is $c/\Gamma_A$ rather than Lean's zero-valued real division.
-- source:
--   Zhang–Zhang–Luo–Mineiro, Near-Optimal First-Order Regret for Bandits with Feedback Graphs, arXiv:2610.40861, Theorem 4.2, p.11; proof of Theorem 4.2, p.31

import Mathlib
import Definitions.Def_FirstOrderFG_Bset
import Definitions.Def_FirstOrderFG_GammaA
import Definitions.Def_FirstOrderFG_cConst

set_option autoImplicit false

namespace FirstOrderFG.Supplement

/-- **The tuned master rate in Theorem 4.2.** Zhang–Zhang–Luo–Mineiro,
arXiv:2610.40861, Theorem 4.2, p.11, with the proof's
`c = 1/(2¹³e²)` from p.31:
`min{c/Γ_A, √(ln(MT)/(Γ_A L⋆))}`.

**Formalization Note.** At `L = 0`, the square-root expression is mathematically `+∞`, so
the minimum is `c/Γ_A`; the branch avoids Lean real division's default value zero. -/
noncomputable def Alg2.tunedTheta {K : ℕ} (E : Fin K → Fin K → Prop) [DecidableRel E]
    (T : ℕ) (A L : ℝ) : ℝ :=
  min (FirstOrderFG.cConst / FirstOrderFG.GammaA E T A)
    (if L = 0 then FirstOrderFG.cConst / FirstOrderFG.GammaA E T A
     else Real.sqrt
       (Real.log (((FirstOrderFG.Bset E).card : ℝ) * T) /
         (FirstOrderFG.GammaA E T A * L)))

end FirstOrderFG.Supplement



-- Prove2me | Definitions.Def_BauerleRiederMDP_LQ_Supplement_JumpMarket_alphaB
-- name    : BauerleRiederMDP_LQ_Supplement_JumpMarket_alphaB
-- status  : Definition
-- author  : @iris
-- created : 2026-11-26T23:19:26.445972+00:00
-- url     : https://prove2.me/theorems/1359b581-0f12-5b8c-8ca8-d1bd3c33b4b1
-- title:
--   The contraction modulus $\alpha _b$ of the discrete-time model of §9.3
-- statement:
--   **The contraction modulus $\alpha _b$ of the discrete-time model of §9.3** (Bäuerle & Rieder, *Markov Decision Processes with Applications to Finance* (2011), proof of Proposition 9.3.2, p.284, PDF 294, with the definition p.196): $\alpha _b = \sup _{(t,x,\alpha ) \in  D} \int  b(s, y) Q(ds, dy | t, x, \alpha ) / b(t, x)$, `b = bfun γ`.
--
--   **Formalization Note.** The supremum is over $(t, x) \in  E$ and $\alpha  \in  A$, in $\mathbb R \ge 0\infty $ ($b > 0$ on $E$). The transition law does not depend on the utility function, so the model with $U ≡ 0$ is used.
-- source:
--   Bäuerle & Rieder, Markov Decision Processes with Applications to Finance (2011), proof of Proposition 9.3.2, p.284, PDF 294, with the definition p.196

import Mathlib
import Definitions.Def_BauerleRiederMDP_PDMDP_ControlFn
import Definitions.Def_BauerleRiederMDP_PDMDP_StageModel
import Definitions.Def_BauerleRiederMDP_LQ_Supplement_JumpMarket
import Definitions.Def_BauerleRiederMDP_LQ_Supplement_Ufrac
import Definitions.Def_BauerleRiederMDP_LQ_Supplement_JumpMarket_stage
import Definitions.Def_BauerleRiederMDP_LQ_Supplement_JumpMarket_Eset
import Definitions.Def_BauerleRiederMDP_LQ_Supplement_JumpMarket_bfun

open MeasureTheory
open BauerleRiederMDP.PDMDP (ControlFn)

namespace BauerleRiederMDP.LQ.Supplement

/-- **The contraction modulus `α_b` of the discrete-time model of §9.3** (Bäuerle & Rieder,
*Markov Decision Processes with Applications to Finance* (2011), proof of Proposition 9.3.2,
p.284, PDF 294, with the definition p.196): `α_b = sup_{(t,x,α) ∈ D} ∫ b(s, y) Q(ds, dy | t, x, α) / b(t, x)`,
`b = bfun γ`.

**Formalization Note.** The supremum is over `(t, x) ∈ E` and `α ∈ A`, in `ℝ≥0∞` (`b > 0` on `E`).
The transition law does not depend on the utility function, so the model with `U ≡ 0` is used. -/
noncomputable def JumpMarket.alphaB {d : ℕ} (Mk : JumpMarket d) (γ : ℝ) : ENNReal :=
  ⨆ p ∈ Mk.Eset, ⨆ α : ControlFn (Ufrac d),
    (∫⁻ q, ENNReal.ofReal (Mk.bfun γ q) ∂((Mk.stage fun _ => 0).kern p α)) /
      ENNReal.ofReal (Mk.bfun γ p)

end BauerleRiederMDP.LQ.Supplement



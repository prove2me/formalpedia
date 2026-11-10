-- Prove2me | Definitions.Def_BilatMatch_ValphaOn
-- name    : BilatMatch_ValphaOn
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T04:08:44.749118+00:00
-- url     : https://prove2.me/theorems/08d3aa75-3a9c-4e9f-801b-4a005eb614e5
-- title:
--   Fixed-multiplier benchmark $V_\alpha$ and second best $\mathrm{SB}$
-- statement:
--   For a budget multiplier $\alpha$ and report domains $D$,
--   $$V_\alpha=\sup\{\mathrm{GFT}(M)+\alpha\,\mathrm{Rev}(M):\ M\text{ admissible, BIC and IIR on }D\},$$
--   and the **second best** is $\mathrm{SB}=\sup\{\mathrm{GFT}(M):\ M\text{ admissible, BIC and IIR on }D,\ \mathrm{Rev}(M)\ge0\}$ (ex-ante weak budget balance). With whole-line report domains these are $V_\alpha(\mathcal I)$ and $\mathrm{SB}(\mathcal I)$, the general definitions of p.7.
--
--   $V_\alpha$ contains no budget constraint. The no-trade mechanism is always admissible, BIC and IIR, so the suprema range over nonempty sets.
--
--   **Formalization Note** The suprema are taken in the extended reals.
-- source:
--   Liu, Qin, Wang, From Bilateral Trade to Matching Markets: Sharp Gains from Trade, arXiv:2609.30702 (held version, sha256 ff1490ad…), p.1 (pdf p.3), p.6 (pdf p.8) and p.7 (pdf p.9)

import Mathlib
import Definitions.Def_BilatMatch_Mechanism

open MeasureTheory

namespace BilatMatch

variable {B S : Type*}

/-- The fixed-multiplier Lagrangian benchmark relative to report domains `D`
(Liu, Qin, Wang, arXiv:2609.30702, held version, sha256 ff1490ad…, p.1 (pdf p.3) and p.7):
`V_α = sup { GFT(M) + α Rev(M) : M admissible, BIC, IIR }`.

**Formalization Note** The supremum is taken in `EReal` over admissible mechanisms that are BIC
and IIR on `D`; it contains no budget constraint (no WBB). The no-trade mechanism is always
admissible, BIC and IIR, so the set is nonempty. -/
noncomputable def ValphaOn (I : Market B S) (D : B ⊕ S → Set ℝ) (α : ℝ) : EReal :=
  ⨆ (A : Mechanism I) (_ : A.Admissible ∧ A.IsBICOn D ∧ A.IsIIROn D),
    ((A.GFT + α * A.Rev : ℝ) : EReal)

/-- `V_α(I)` with whole-line reports (p.7: "for general priors and agent sets, `V_α` retains its
definition as the supremum of `GFT + α Rev` over admissible BIC/IIR mechanisms"). -/
noncomputable def Valpha (I : Market B S) (α : ℝ) : EReal := ValphaOn I (wholeLine B S) α

/-- The second-best benchmark relative to report domains `D` (p.6):
`SB = sup { GFT(M) : M admissible, BIC, IIR, ex-ante WBB }`, with ex-ante WBB `Rev(M) ≥ 0`. -/
noncomputable def SBOn (I : Market B S) (D : B ⊕ S → Set ℝ) : EReal :=
  ⨆ (A : Mechanism I) (_ : A.Admissible ∧ A.IsBICOn D ∧ A.IsIIROn D ∧ 0 ≤ A.Rev),
    ((A.GFT : ℝ) : EReal)

/-- `SB(I)` with whole-line reports. -/
noncomputable def SB (I : Market B S) : EReal := SBOn I (wholeLine B S)

end BilatMatch



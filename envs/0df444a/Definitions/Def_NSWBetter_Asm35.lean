-- Prove2me | Definitions.Def_NSWBetter_Asm35
-- name    : NSWBetter_Asm35
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:49:05.432863+00:00
-- url     : https://prove2.me/theorems/d47dcdaa-d045-4155-b120-04bdeac05ae9
-- title:
--   Assumption 3.5: at least $\Delta$ positively valued goods
-- statement:
--   **Assumption 3.5.** The instance with $\Delta$ identical agents has at least $\Delta$ goods of positive value. It implies $\mathrm{NSW}(I)>0$, $\mathrm{NSW}(W)>0$ and $\mu>0$.
-- source:
--   Viswanathan, A Better-than-e^{1/e} Approximation Algorithm for Nash Social Welfare under Additive Valuations, arXiv:2607.13340 (held version, sha256 08811cb468c2df39231dca4222c5af94163587c7c83e205e50bbf0b91fc1deb3), Assumption 3.5, p.12

import Mathlib

namespace NSWBetter

/-- **Assumption 3.5.**
Viswanathan, *A Better-than-e^{1/e} Approximation Algorithm for Nash Social Welfare under Additive Valuations*, arXiv:2607.13340 (held version, sha256 08811cb4…), Assumption 3.5, p.12: "The instance I consists of at least ∆ goods that are positively valued by all the agents."

`Asm35 Δ s`: at least `Δ` of the values in `s` are positive. -/
def Asm35 (Δ : ℕ) (s : Multiset ℝ) : Prop := Δ ≤ (s.filter fun a => 0 < a).card

end NSWBetter



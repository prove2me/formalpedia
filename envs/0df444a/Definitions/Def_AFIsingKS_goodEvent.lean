-- Prove2me | Definitions.Def_AFIsingKS_goodEvent
-- name    : AFIsingKS_goodEvent
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T10:15:45.91805+00:00
-- url     : https://prove2.me/theorems/6cf943ee-c943-4827-8d8d-f8b35986d6b0
-- title:
--   The event $\mathcal E_{\beta,\varepsilon,c}$
-- statement:
--   For $\beta\in\mathbb C$ and $\varepsilon,c>0$ define the event
--   $$\mathcal E_{\beta,\varepsilon,c}=\Big\{G:\big|Z^{(2)}_{G,\ge\varepsilon}(\beta)\big|\le e^{-cn}\big|\mathbb E[Z_{G,<\varepsilon}(\beta)]\big|^2\Big\}.$$
--   On this event the non-orthogonal contribution to the second moment is negligible. The left side depends on $G$; the right side is a number.
-- source:
--   Bencs, Huang, Lee, Liu, Regts, On Zeros and Algorithms for Disordered Systems II, arXiv:2610.40598 (held version, sha256 2a07c158…), eq. (6), p.12

import Mathlib
import Definitions.Def_AFIsingKS_cmZ

open scoped Classical

namespace AFIsingKS

/-- The event `E_{β,ε,c} = {G : |Z^{(2)}_{G,≥ε}(β)| ≤ e^{−cn} |𝔼[Z_{G,<ε}(β)]|²}`
(Bencs, Huang, Lee, Liu, Regts, arXiv:2610.40598 (held version, sha256 2a07c158…), eq. (6), p.12).

**Formalization Note.** The left side depends on the matching `M`; the right side is a number,
averaged over all matchings. -/
def goodEvent {n d : ℕ} (ε c : ℝ) (β : ℂ) (M : Matching n d) : Prop :=
  ‖cmZ2ge ε M β‖ ≤
    Real.exp (-c * (n : ℝ)) * ‖cmE (fun M' : Matching n d => cmZlt ε M' β)‖ ^ 2

end AFIsingKS



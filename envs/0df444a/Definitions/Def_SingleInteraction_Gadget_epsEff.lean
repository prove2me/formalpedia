-- Prove2me | Definitions.Def_SingleInteraction_Gadget_epsEff
-- name    : SingleInteraction_Gadget_epsEff
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T07:55:08.588894+00:00
-- url     : https://prove2.me/theorems/1e760f13-4f4d-4f60-b7cc-6f8b6c44cbbe
-- title:
--   The parameters $\eta$ and $\varepsilon_{\mathrm{eff}}$
-- statement:
--   For a gadget,
--
--   $$\eta=\frac{1+2\sqrt{MR}}{L},\qquad\varepsilon_{\mathrm{eff}}=\frac{4MR}{L}\left[\frac{\eta}{1-\eta}+\frac{MR}{L^2(1-\eta)^2}\right].$$
--
--   $\eta$ is the relative perturbation strength of eq. (36) and $\varepsilon_{\mathrm{eff}}$ the error bound of eq. (37); the latter is used under the standing assumption $\eta<1$.
-- source:
--   Hecker, The Complexity of Single-Interaction Hamiltonians, arXiv:2609.39592 (held version, sha256 19ddc444…), §5.1.5, p.62; §5.1.6, p.64, eq. (37)

import Mathlib
import Definitions.Def_SingleInteraction_Gadget

namespace SingleInteraction

namespace Gadget

/-- `η = (1 + 2√(MR))/L` (Hecker, *The Complexity of Single-Interaction Hamiltonians*, arXiv:2609.39592 (held version, sha256 19ddc444…), §5.1.5, p.62). -/
noncomputable def eta (G : Gadget) : ℝ :=
  (1 + 2 * Real.sqrt ((G.M : ℝ) * (G.R : ℝ))) / (G.L : ℝ)

/-- `ε_eff = (4MR/L) [η/(1 − η) + MR/(L²(1 − η)²)]`, the closed form of eq. (37) (Hecker, *The Complexity of Single-Interaction Hamiltonians*, arXiv:2609.39592 (held version, sha256 19ddc444…), §5.1.6, p.64).

**Formalization Note** Meaningful under the standing assumption `η < 1` of §5.1.6 (p.63), which the
statements using it carry as a hypothesis. -/
noncomputable def epsEff (G : Gadget) : ℝ :=
  4 * (G.M : ℝ) * (G.R : ℝ) / (G.L : ℝ) *
    (G.eta / (1 - G.eta) + (G.M : ℝ) * (G.R : ℝ) / ((G.L : ℝ) ^ 2 * (1 - G.eta) ^ 2))

end Gadget

end SingleInteraction



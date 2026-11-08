-- Prove2me | Definitions.Def_SingleInteraction_Gadget_Hsim
-- name    : SingleInteraction_Gadget_Hsim
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T07:56:22.003007+00:00
-- url     : https://prove2.me/theorems/215c4a56-22cc-4762-b66c-16bdb730ad3b
-- title:
--   The shifted Hamiltonians $H_0$ and $H_{\mathrm{sim}}$
-- statement:
--   With $E_{\mathrm{base}}=-2S^2-4MRL$, the minimum energy of $H_{\mathrm{core}}+H_{\mathrm{anchor}}$,
--
--   $$H_0=H_{\mathrm{core}}+H_{\mathrm{anchor}}-E_{\mathrm{base}}I,\qquad H_{\mathrm{sim}}=\hat H-E_{\mathrm{base}}I=H_0+V.$$
-- source:
--   Hecker, The Complexity of Single-Interaction Hamiltonians, arXiv:2609.39592 (held version, sha256 19ddc444…), §5.1.3, p.58

import Mathlib
import Definitions.Def_SingleInteraction_Gadget_Hhat

namespace SingleInteraction

namespace Gadget

/-- `E_base = −2S² − 4MRL`, the minimum energy of `H_core + H_anchor` (Hecker, *The Complexity of Single-Interaction Hamiltonians*, arXiv:2609.39592 (held version, sha256 19ddc444…), §5.1.3, p.58). -/
noncomputable def Ebase (G : Gadget) : ℝ :=
  -2 * (G.S : ℝ) ^ 2 - 4 * (G.M : ℝ) * (G.R : ℝ) * (G.L : ℝ)

/-- `H0 = H_core + H_anchor − E_base I` (Hecker, *The Complexity of Single-Interaction Hamiltonians*, arXiv:2609.39592 (held version, sha256 19ddc444…), §5.1.3, p.58). -/
noncomputable def H0 (G : Gadget) : Matrix (G.Qb → Fin 2) (G.Qb → Fin 2) ℂ :=
  G.Hcore + G.Hanchor - ((G.Ebase : ℝ) : ℂ) • (1 : Matrix (G.Qb → Fin 2) (G.Qb → Fin 2) ℂ)

/-- The shifted Hamiltonian `H_sim = Ĥ − E_base I = H0 + V` (Hecker, *The Complexity of Single-Interaction Hamiltonians*, arXiv:2609.39592 (held version, sha256 19ddc444…), §5.1.3, p.58). -/
noncomputable def Hsim (G : Gadget) : Matrix (G.Qb → Fin 2) (G.Qb → Fin 2) ℂ :=
  G.Hhat - ((G.Ebase : ℝ) : ℂ) • (1 : Matrix (G.Qb → Fin 2) (G.Qb → Fin 2) ℂ)

end Gadget

end SingleInteraction



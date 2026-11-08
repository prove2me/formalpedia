-- Prove2me | Definitions.Def_SingleInteraction_Gadget_H2eff
-- name    : SingleInteraction_Gadget_H2eff
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T07:57:18.277199+00:00
-- url     : https://prove2.me/theorems/333d59f7-c7a7-42a8-95cf-fca1358e1c4f
-- title:
--   Second-order effective Hamiltonian $H^{(2)}_{\mathrm{eff}}$
-- statement:
--   In the chosen valid core sector, with $H_0$, $V$, $H_{\mathrm{sim}}$ restricted to it,
--
--   $$H^{(2)}_{\mathrm{eff}}=-PVQ\,(QH_0Q)^{-1}\,QVP,$$
--
--   where the inverse is taken on the range of $Q$.
-- source:
--   Hecker, The Complexity of Single-Interaction Hamiltonians, arXiv:2609.39592 (held version, sha256 19ddc444…), §5.1.4, p.60

import Mathlib
import Definitions.Def_SingleInteraction_Gadget_Hsim
import Definitions.Def_SingleInteraction_Gadget_comp
import Definitions.Def_SingleInteraction_Gadget_Pzero
import Definitions.Def_SingleInteraction_invOn

namespace SingleInteraction

namespace Gadget

/-- `H0` in the chosen valid core sector `|0⟩^{⊗S}_𝒜 |1⟩^{⊗S}_ℬ` (Hecker, *The Complexity of Single-Interaction Hamiltonians*, arXiv:2609.39592 (held version, sha256 19ddc444…), §5.1.3, p.59). -/
noncomputable def H0v (G : Gadget) : Matrix (G.VS → Fin 2) (G.VS → Fin 2) ℂ := G.comp G.zval G.H0

/-- `V` in the chosen valid core sector (Hecker, *The Complexity of Single-Interaction Hamiltonians*, arXiv:2609.39592 (held version, sha256 19ddc444…), §5.1.3, p.59). -/
noncomputable def Vv (G : Gadget) : Matrix (G.VS → Fin 2) (G.VS → Fin 2) ℂ := G.comp G.zval G.Vact

/-- `H_sim` in the chosen valid core sector (Hecker, *The Complexity of Single-Interaction Hamiltonians*, arXiv:2609.39592 (held version, sha256 19ddc444…), §5.1.3, p.59). -/
noncomputable def Hsimv (G : Gadget) : Matrix (G.VS → Fin 2) (G.VS → Fin 2) ℂ := G.comp G.zval G.Hsim

/-- The second-order effective Hamiltonian `H_eff^(2) = −PVQ(QH0Q)^{−1}QVP`, "where the inverse is taken on
the range of `Q`" (Hecker, *The Complexity of Single-Interaction Hamiltonians*, arXiv:2609.39592 (held version, sha256 19ddc444…), §5.1.4, p.60), in the chosen valid core sector.

**Formalization Note** The inverse on ran `Q` is `invOn Qexc H0v`. -/
noncomputable def H2eff (G : Gadget) : Matrix (G.VS → Fin 2) (G.VS → Fin 2) ℂ :=
  -(G.Pzero * G.Vv * G.Qexc * invOn G.Qexc G.H0v * G.Qexc * G.Vv * G.Pzero)

end Gadget

end SingleInteraction



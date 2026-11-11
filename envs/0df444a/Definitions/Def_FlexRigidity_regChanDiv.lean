-- Prove2me | Definitions.Def_FlexRigidity_regChanDiv
-- name    : FlexRigidity_regChanDiv
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:16:50.549444+00:00
-- url     : https://prove2.me/theorems/b078a33f-bff8-4d21-8e32-c5bb7f783245
-- title:
--   Regularized channel divergence $D^{\mathrm{reg}}_\alpha(\mathcal E\|\mathcal F)$
-- statement:
--   $$D^{\mathrm{reg}}_\alpha(\mathcal E\|\mathcal F)=\limsup_{n\to\infty}\frac1n D_\alpha\big(\mathcal E^{\otimes n}\big\|\mathcal F^{\otimes n}\big),$$
--   with the unstabilized channel divergence of Definition 2.10.
--
--   **Formalization Note** $\mathcal E^{\otimes n}$ is `piSuperop` of the reused module `QAlgorithms_Defs_Channel`, acting on $n$ copies of the register. Values in $\overline{\mathbb R}$.
-- source:
--   Arqand, Kundu, Tan, Flexible rigidity: Compiling generic trusted-preparation protocols into sequential device-independent protocols, arXiv:2610.00444 (artifact sha256 8c67699d…), Definition 2.11, p. 22

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Channel
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P35
import Definitions.Def_FlexRigidity_chanDiv
set_option autoImplicit false

open scoped Matrix ComplexOrder ENNReal
open Filter Topology
open QAlgorithms (Superop IsChannel krausApply idTensorSuperop piSuperop)
open QAlgorithms.Papers.Independent.Dependency50.P35 (tr Density Dominates divergence rawTrace spectralPower maxRelative POVM leftMarginal rightMarginal)

noncomputable section

namespace FlexRigidity

/-- **Regularized channel divergence** (Arqand–Kundu–Tan, *Flexible rigidity*, arXiv:2610.00444,
artifact sha256 8c67699d…, Definition 2.11, p. 22):
`D^reg_α(E‖F) = limsup_{n→∞} (1/n) D_α(E^{⊗n}‖F^{⊗n})`, with the unstabilized channel divergence of
Definition 2.10.

**Formalization Note** `E^{⊗n}` is `piSuperop` of the reused `QAlgorithms.Defs.Channel` module on
the register `Fin n → ι`. Values in `EReal`; the `n = 0` term does not affect the `limsup`. -/
def regChanDiv {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] (a : ℝ)
    (E F : Superop ι κ) : EReal :=
  limsup (fun n : ℕ => ((1 / (n : ℝ) : ℝ) : EReal) *
    chanDiv a (piSuperop (fun _ : Fin n => E)) (piSuperop (fun _ : Fin n => F))) atTop

end FlexRigidity



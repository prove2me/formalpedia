-- Prove2me | Definitions.Def_FlexRigidity_condEvent
-- name    : FlexRigidity_condEvent
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:16:21.469534+00:00
-- url     : https://prove2.me/theorems/8161f5d3-c1af-44a1-8b38-928119d02b30
-- title:
--   Conditional state $\rho_{|\Omega}=\rho_{\wedge\Omega}/p_\Omega$
-- statement:
--   For an operator $\rho$ classical on $X$ and an event $\Omega$ on $X$, the **conditional state** is $\rho_{|\Omega}=\rho_{\wedge\Omega}/p_\Omega$ with $p_\Omega=\operatorname{Tr}\rho_{\wedge\Omega}$.
--
--   **Formalization Note** The paper never assigns a conditional state to a zero-probability event. Every statement of the mission that uses it assumes $p_\Omega>0$; at $p_\Omega=0$ the Lean value (the zero operator) is never used.
-- source:
--   Arqand, Kundu, Tan, Flexible rigidity: Compiling generic trusted-preparation protocols into sequential device-independent protocols, arXiv:2610.00444 (artifact sha256 8c67699d…), Definition 2.3, p. 18

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Channel
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P35
import Definitions.Def_FlexRigidity_cutEvent
set_option autoImplicit false

open scoped Matrix ComplexOrder ENNReal
open Filter Topology
open QAlgorithms (Superop IsChannel krausApply idTensorSuperop piSuperop)
open QAlgorithms.Papers.Independent.Dependency50.P35 (tr Density Dominates divergence rawTrace spectralPower maxRelative POVM leftMarginal rightMarginal)

noncomputable section

namespace FlexRigidity

/-- **Conditional state** `ρ_{|Ω} = ρ_{∧Ω}/p_Ω` (Arqand–Kundu–Tan, *Flexible rigidity*,
arXiv:2610.00444, artifact sha256 8c67699d…, Definition 2.3, p. 18), with `p_Ω = Tr ρ_{∧Ω}`.

**Formalization Note** The paper never assigns a conditional state to a zero-probability event;
every statement using `condEvent` assumes `p_Ω > 0` (at `p_Ω = 0` Lean's `0⁻¹ = 0` would give the
zero operator, which is never used). -/
def condEvent {X Y : Type} [Fintype X] [Fintype Y] (p : X → Prop) [DecidablePred p]
    (ρ : Matrix (X × Y) (X × Y) ℂ) : Matrix (X × Y) (X × Y) ℂ :=
  (((tr (cutEvent p ρ))⁻¹ : ℝ) : ℂ) • cutEvent p ρ

end FlexRigidity



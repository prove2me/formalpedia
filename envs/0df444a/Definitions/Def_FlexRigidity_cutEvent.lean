-- Prove2me | Definitions.Def_FlexRigidity_cutEvent
-- name    : FlexRigidity_cutEvent
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:14:39.360218+00:00
-- url     : https://prove2.me/theorems/f002de4e-435f-4039-b865-dd8699b999d1
-- title:
--   Partial state on a classical event $\rho_{\wedge\Omega}$
-- statement:
--   Let $\rho$ be an operator on $XY$ with $X$ a classical register, and let $\Omega$ be an event on $X$. The **partial state** keeps exactly the entries whose row and column both lie in $\Omega$:
--   $$\rho_{\wedge\Omega}=\Pi_\Omega\rho\,\Pi_\Omega,\qquad \Pi_\Omega=\sum_{x\in\Omega}|x\rangle\langle x|\otimes I.$$
--   For a state classical on $X$, $\rho=\sum_x|x\rangle\langle x|\otimes\rho^x$, this is $\sum_{x\in\Omega}|x\rangle\langle x|\otimes\rho^x$, and $p_\Omega=\operatorname{Tr}\rho_{\wedge\Omega}$ is the probability of $\Omega$ (Definition 2.3).
-- source:
--   Arqand, Kundu, Tan, Flexible rigidity: Compiling generic trusted-preparation protocols into sequential device-independent protocols, arXiv:2610.00444 (artifact sha256 8c67699d…), Definition 2.3, p. 18

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Channel
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P35

set_option autoImplicit false

open scoped Matrix ComplexOrder ENNReal
open Filter Topology
open QAlgorithms (Superop IsChannel krausApply idTensorSuperop piSuperop)
open QAlgorithms.Papers.Independent.Dependency50.P35 (tr Density Dominates divergence rawTrace spectralPower maxRelative POVM leftMarginal rightMarginal)

noncomputable section

namespace FlexRigidity

/-- **Partial state on an event** `ρ_{∧Ω}` (Arqand–Kundu–Tan, *Flexible rigidity*,
arXiv:2610.00444, artifact sha256 8c67699d…, Definition 2.3, p. 18): for an operator on `X × Y`
and an event `Ω ⊆ X` on the classical register `X`, keep the entries whose row and column both lie
in `Ω` and zero the rest, i.e. `Π_Ω ρ Π_Ω` with `Π_Ω = Σ_{x∈Ω} |x⟩⟨x| ⊗ I`.

**Formalization Note** For a state classical on `X`, `ρ = Σ_x |x⟩⟨x| ⊗ ρ^x`, this is
`Σ_{x∈Ω} |x⟩⟨x| ⊗ ρ^x`, the paper's `ρ_{∧Ω}`; its trace is `p_Ω`. -/
def cutEvent {X Y : Type} (p : X → Prop) [DecidablePred p]
    (ρ : Matrix (X × Y) (X × Y) ℂ) : Matrix (X × Y) (X × Y) ℂ :=
  Matrix.of fun i j => if p i.1 ∧ p j.1 then ρ i j else 0

end FlexRigidity



-- Prove2me | Definitions.Def_FlexRigidity_deficit
-- name    : FlexRigidity_deficit
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:22:45.2168+00:00
-- url     : https://prove2.me/theorems/85564df7-782b-4973-bd3a-44dc7bbf38ce
-- title:
--   Strategy deficit $\delta_{\mathsf G}(\mathfrak S)$
-- statement:
--   $\delta_{\mathsf G}(\mathfrak S)=\omega^*(\mathsf G)-\sum_{x,y,a,b}P_{XY}(x,y)V(x,y,a,b)\operatorname{Tr}[(H^x_a\otimes K^y_b)\rho]$. It depends on the state and both measurement families.
-- source:
--   Arqand, Kundu, Tan, Flexible rigidity: Compiling generic trusted-preparation protocols into sequential device-independent protocols, arXiv:2610.00444 (artifact sha256 8c67699d…), Definition 5.2, p. 39

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Channel
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P35
import Definitions.Def_FlexRigidity_quantumValue
set_option autoImplicit false

open scoped Matrix ComplexOrder ENNReal
open Filter Topology
open QAlgorithms (Superop IsChannel krausApply idTensorSuperop piSuperop)
open QAlgorithms.Papers.Independent.Dependency50.P35 (tr Density Dominates divergence rawTrace spectralPower maxRelative POVM leftMarginal rightMarginal)

noncomputable section

namespace FlexRigidity

/-- **Strategy deficit**, Definition 5.2 (Arqand–Kundu–Tan, *Flexible rigidity*,
arXiv:2610.00444, artifact sha256 8c67699d…, p. 39):
`δ_G(S) = ω*(G) − Σ_{x,y,a,b} P_{XY}(x,y) V(x,y,a,b) Tr[(H^x_a ⊗ K^y_b) ρ]`. -/
def deficit {X Y A B MA MB : Type} [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
    [Fintype MA] [Fintype MB] (G : Game X Y A B) (ρ : Matrix (MA × MB) (MA × MB) ℂ)
    (H : X → A → Matrix MA MA ℂ) (K : Y → B → Matrix MB MB ℂ) : ℝ :=
  quantumValue G - winProb G ρ H K

end FlexRigidity



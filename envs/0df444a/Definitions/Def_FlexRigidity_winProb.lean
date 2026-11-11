-- Prove2me | Definitions.Def_FlexRigidity_winProb
-- name    : FlexRigidity_winProb
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:19:44.827528+00:00
-- url     : https://prove2.me/theorems/dd5c518b-9db0-49da-93ce-a4aab2ca928f
-- title:
--   Winning probability of a quantum strategy
-- statement:
--   A quantum strategy $\mathfrak S=(\rho_{M_{\mathrm A}M_{\mathrm B}},\{H^x_a\},\{K^y_b\})$ wins with probability
--   $$\sum_{x,y,a,b}P_{XY}(x,y)V(x,y,a,b)\operatorname{Tr}\big[(H^x_a\otimes K^y_b)\rho\big].$$
-- source:
--   Arqand, Kundu, Tan, Flexible rigidity: Compiling generic trusted-preparation protocols into sequential device-independent protocols, arXiv:2610.00444 (artifact sha256 8c67699d…), Definition 5.1, p. 39

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Channel
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P35
import Definitions.Def_FlexRigidity_Game
set_option autoImplicit false

open scoped Matrix ComplexOrder ENNReal
open Filter Topology
open QAlgorithms (Superop IsChannel krausApply idTensorSuperop piSuperop)
open QAlgorithms.Papers.Independent.Dependency50.P35 (tr Density Dominates divergence rawTrace spectralPower maxRelative POVM leftMarginal rightMarginal)

noncomputable section

namespace FlexRigidity

/-- **Winning probability of a quantum strategy**, Definition 5.1 (Arqand–Kundu–Tan, *Flexible
rigidity*, arXiv:2610.00444, artifact sha256 8c67699d…, p. 39): for a strategy
`S = (ρ_{M_A M_B}, {H^x_a}, {K^y_b})`,
`Σ_{x,y,a,b} P_{XY}(x,y) V(x,y,a,b) Tr[(H^x_a ⊗ K^y_b) ρ]`. -/
def winProb {X Y A B MA MB : Type} [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
    [Fintype MA] [Fintype MB] (G : Game X Y A B) (ρ : Matrix (MA × MB) (MA × MB) ℂ)
    (H : X → A → Matrix MA MA ℂ) (K : Y → B → Matrix MB MB ℂ) : ℝ :=
  ∑ x, ∑ y, ∑ a, ∑ b, G.PXY x y * (if G.V x y a b then 1 else 0) *
    tr (Matrix.kronecker (H x a) (K y b) * ρ)

end FlexRigidity



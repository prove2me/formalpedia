-- Prove2me | Definitions.Def_FlexRigidity_honestRecordProb
-- name    : FlexRigidity_honestRecordProb
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:20:40.564085+00:00
-- url     : https://prove2.me/theorems/c2ce8641-a488-402a-bcbe-c594104fe553
-- title:
--   Honest single-round record distribution
-- statement:
--   When the devices play a fixed strategy $(\rho,\{H^x_a\},\{K^y_b\})$ on a fresh copy of $\rho$, the round record has probability $(1-\gamma)P_X(x)\operatorname{Tr}[(H^x_a\otimes I)\rho]$ for $(\mathrm{gen},x,\varnothing,a,\varnothing)$ and $\gamma P_{XY}(x,y)\operatorname{Tr}[(H^x_a\otimes K^y_b)\rho]$ for $(\mathrm{test},x,y,a,b)$, with $P_X$ the $X$-marginal of $P_{XY}$.
-- source:
--   Arqand, Kundu, Tan, Flexible rigidity: Compiling generic trusted-preparation protocols into sequential device-independent protocols, arXiv:2610.00444 (artifact sha256 8c67699d…), Protocol 2 and Theorem 5.5, pp. 41–42

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Channel
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P35
import Definitions.Def_FlexRigidity_Game
import Definitions.Def_FlexRigidity_RoundO
set_option autoImplicit false

open scoped Matrix ComplexOrder ENNReal
open Filter Topology
open QAlgorithms (Superop IsChannel krausApply idTensorSuperop piSuperop)
open QAlgorithms.Papers.Independent.Dependency50.P35 (tr Density Dominates divergence rawTrace spectralPower maxRelative POVM leftMarginal rightMarginal)

noncomputable section

namespace FlexRigidity

/-- **The honest single-round record distribution** of Protocol 2 (Arqand–Kundu–Tan, *Flexible
rigidity*, arXiv:2610.00444, artifact sha256 8c67699d…, pp. 41–42, Theorem 5.5): when the devices
play a fixed strategy `S = (ρ, {H^x_a}, {K^y_b})` on a fresh copy of `ρ` in a round, the record
`(u, x, y, a, b)` has probability `(1−γ) P_X(x) Tr[(H^x_a ⊗ I)ρ]` for a generation record
`(gen, x, ∅, a, ∅)` and `γ P_{XY}(x, y) Tr[(H^x_a ⊗ K^y_b)ρ]` for a test record `(test, x, y, a, b)`;
`P_X` is the game's `X`-marginal. -/
def honestRecordProb {X Y A B MA MB : Type} [Fintype Y] [Fintype MA] [Fintype MB] [DecidableEq MB]
    (G : Game X Y A B) (γ : ℝ) (ρ : Matrix (MA × MB) (MA × MB) ℂ)
    (H : X → A → Matrix MA MA ℂ) (K : Y → B → Matrix MB MB ℂ) (o : RoundO X Y A B) : ℝ :=
  match o with
  | (false, x, none, a, none) =>
      (1 - γ) * (∑ y, G.PXY x y) * tr (Matrix.kronecker (H x a) (1 : Matrix MB MB ℂ) * ρ)
  | (true, x, some y, a, some b) => γ * G.PXY x y * tr (Matrix.kronecker (H x a) (K y b) * ρ)
  | _ => 0

end FlexRigidity



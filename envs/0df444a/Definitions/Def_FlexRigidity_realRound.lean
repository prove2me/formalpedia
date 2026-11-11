-- Prove2me | Definitions.Def_FlexRigidity_realRound
-- name    : FlexRigidity_realRound
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:24:39.952203+00:00
-- url     : https://prove2.me/theorems/9ebb23b2-569b-47ed-af83-4d516af964c7
-- title:
--   The real round channel $\mathcal E_i$, eq. (46)
-- statement:
--   Alice samples $x_i\sim P_X$ and $u_i=\mathrm{test}$ with probability $\gamma$, and on a test round $y_i\sim P_{Y|x_i}$; the devices act as $\mathcal E^{\mathrm A,x_i,a_i}_i\otimes\mathcal E^{\mathrm B,u_i,y_i,b_i}_i$; the record $c_i$ is stored:
--   $$\mathcal E_i[\rho]=\sum_{x,a}(1-\gamma)P_X(x)\,|\mathrm{gen};\mathrm{gen},x,\varnothing,a,\varnothing\rangle\langle\cdot|\otimes(\mathcal E^{\mathrm A,x,a}_i\otimes\mathcal E^{\mathrm B,\mathrm{gen}}_i)[\rho]+\sum_{x,y,a,b}\gamma P_{XY}(x,y)\,|V(x,y,a,b);\mathrm{test},x,y,a,b\rangle\langle\cdot|\otimes(\mathcal E^{\mathrm A,x,a}_i\otimes\mathcal E^{\mathrm B,\mathrm{test},y,b}_i)[\rho].$$
-- source:
--   Arqand, Kundu, Tan, Flexible rigidity: Compiling generic trusted-preparation protocols into sequential device-independent protocols, arXiv:2610.00444 (artifact sha256 8c67699d…), eq. (46), pp. 43–45

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Channel
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P35
import Definitions.Def_FlexRigidity_DIImpl
import Definitions.Def_FlexRigidity_recordOf
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P62
import Definitions.Def_FlexRigidity_Realization
set_option autoImplicit false

open scoped Matrix ComplexOrder ENNReal
open Filter Topology
open QAlgorithms (Superop IsChannel krausApply idTensorSuperop piSuperop)
open QAlgorithms.Papers.Independent.Dependency50.P35 (tr Density Dominates divergence rawTrace spectralPower maxRelative POVM leftMarginal rightMarginal)

noncomputable section

namespace FlexRigidity

/-- **The real round channel `E_i`, eq. (46)** (Arqand–Kundu–Tan, *Flexible rigidity*,
arXiv:2610.00444, artifact sha256 8c67699d…, pp. 43–45): Alice samples `x_i ~ P_X` and
`u_i = test` with probability `γ`; on a test round `y_i ~ P_{Y|x_i}`; the devices act as
`E^{A,x_i,a_i}_i ⊗ E^{B,u_i,y_i,b_i}_i`; and the record `c_i = g(u_i, x_i, y_i, a_i, b_i)` is stored.
The output is classical on `(c_i, u_i, x_i, y_i, a_i, b_i)`:
`E_i[ρ] = Σ_{gen} (1−γ) P_X(x) |gen; gen,x,∅,a,∅⟩⟨…| ⊗ (E^{A,x,a}_i ⊗ E^{B,gen}_i)[ρ] + Σ_{test} γ P_{XY}(x,y) |V(x,y,a,b); test,x,y,a,b⟩⟨…| ⊗ (E^{A,x,a}_i ⊗ E^{B,test,y,b}_i)[ρ]`.

**Formalization Note** `γ P_{XY}(x, y) = γ P_X(x) P_{Y|x}(y)` (the game's `X`-marginal is `P_X`,
Postulate 5.3(ii)). -/
def realRound {X Y A B SA SB : Type} [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
    [DecidableEq X] [DecidableEq Y] [DecidableEq A] [DecidableEq B]
    (G : Game X Y A B) (Rz : Realization X Y A B SA SB) (γ : ℝ) (I : DIImpl X Y A B) (i : ℕ) :
    Superop (Fin (I.dA i) × Fin (I.dB i))
      ((Option Bool × RoundO X Y A B) × (Fin (I.dA (i + 1)) × Fin (I.dB (i + 1)))) :=
  fun ρ => Matrix.of fun p q =>
    if p.1 = q.1 ∧ p.1.1 = recordOf G p.1.2 then
      (match p.1.2 with
        | (false, x, none, a, none) =>
            (((1 - γ) * Rz.PX x : ℝ) : ℂ) * QAlgorithms.Papers.Independent.Information100.P62.tensorChannel (I.EA i x a) (I.EBg i) ρ p.2 q.2
        | (true, x, some y, a, some b) =>
            ((γ * G.PXY x y : ℝ) : ℂ) * QAlgorithms.Papers.Independent.Information100.P62.tensorChannel (I.EA i x a) (I.EBt i y b) ρ p.2 q.2
        | _ => 0)
    else 0

end FlexRigidity



-- Prove2me | Definitions.Def_FlexRigidity_prepState
-- name    : FlexRigidity_prepState
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:24:45.216554+00:00
-- url     : https://prove2.me/theorems/d862e0a6-3264-4940-90c9-0c8b28ab58e3
-- title:
--   Depolarized trusted preparation $\rho^{\mathrm{prep},\mu}$, eq. (36)
-- statement:
--   $$\rho^{\mathrm{prep},\mu}_{XAS_{\mathrm B}}=\sum_xP_X(x)|x\rangle\langle x|\otimes\Big[(1-\mu)\sum_a|a\rangle\langle a|\otimes\operatorname{Tr}_{S_{\mathrm A}}\big[(T^x_a\otimes I)|\phi\rangle\langle\phi|(T^x_a\otimes I)\big]+\mu\frac{I_A}{|A|}\otimes\frac{I_{S_{\mathrm B}}}{|S_{\mathrm B}|}\Big].$$
--   By the realization identity (39), $P_{XA}(x,a)|\psi_{x,a}\rangle\langle\psi_{x,a}|=P_X(x)\operatorname{Tr}_{S_{\mathrm A}}[(T^x_a\otimes I)\phi(T^x_a\otimes I)]$, this is the depolarized preparation (36) of the DD protocol realized by $(P_X,|\phi\rangle,\{T^x_a\})$.
-- source:
--   Arqand, Kundu, Tan, Flexible rigidity: Compiling generic trusted-preparation protocols into sequential device-independent protocols, arXiv:2610.00444 (artifact sha256 8c67699d…), eq. (36), p. 37; Fact 5.2, eq. (39), p. 38

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Channel
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P35
import Definitions.Def_FlexRigidity_Realization
set_option autoImplicit false

open scoped Matrix ComplexOrder ENNReal
open Filter Topology
open QAlgorithms (Superop IsChannel krausApply idTensorSuperop piSuperop)
open QAlgorithms.Papers.Independent.Dependency50.P35 (tr Density Dominates divergence rawTrace spectralPower maxRelative POVM leftMarginal rightMarginal)

noncomputable section

namespace FlexRigidity

/-- **The depolarized trusted preparation `ρ^{prep,µ}`, eq. (36)** (Arqand–Kundu–Tan, *Flexible
rigidity*, arXiv:2610.00444, artifact sha256 8c67699d…, p. 37), written through the
entanglement-based realization (39) (Fact 5.2, p. 38):
`ρ^{prep,µ}_{X A S_B} = Σ_x P_X(x)|x⟩⟨x| ⊗ [ (1−µ) Σ_a |a⟩⟨a| ⊗ Tr_{S_A}[(T^x_a ⊗ I)|ϕ⟩⟨ϕ|(T^x_a ⊗ I)] + µ I_A/|A| ⊗ I_{S_B}/|S_B| ]`.

**Formalization Note** By (39), `P_{XA}(x,a)|ψ_{x,a}⟩⟨ψ_{x,a}| = P_X(x) Tr_{S_A}[(T^x_a ⊗ I)ϕ(T^x_a ⊗ I)]`,
so this is (36) for the DD protocol realized by `(P_X, |ϕ⟩, {T^x_a})` (Postulate 5.3(i)). -/
def prepState {X Y A B SA SB : Type} [Fintype A] [Fintype SA] [Fintype SB] [DecidableEq X]
    [DecidableEq A] [DecidableEq SB] (Rz : Realization X Y A B SA SB) (μ : ℝ) :
    Matrix (X × A × SB) (X × A × SB) ℂ :=
  Matrix.of fun i j =>
    if i.1 = j.1 ∧ i.2.1 = j.2.1 then
      (Rz.PX i.1 : ℂ) *
        ((((1 - μ : ℝ)) : ℂ) * ∑ sa : SA,
            (∑ sa' : SA, Rz.T i.1 i.2.1 sa sa' * Rz.ϕ (sa', i.2.2)) *
              star (∑ sa' : SA, Rz.T i.1 i.2.1 sa sa' * Rz.ϕ (sa', j.2.2)) +
         (if i.2.2 = j.2.2 then
            (((μ / ((Fintype.card A : ℝ) * (Fintype.card SB : ℝ)) : ℝ)) : ℂ) else 0))
    else 0

end FlexRigidity



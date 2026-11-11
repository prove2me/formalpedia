-- Prove2me | Definitions.Def_FlexRigidity_SelfTestBound
-- name    : FlexRigidity_SelfTestBound
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:24:14.298901+00:00
-- url     : https://prove2.me/theorems/949606f1-37ab-432e-8c5a-0d6817668c60
-- title:
--   The self-testing bound (41)
-- statement:
--   For measurement families $\{H^x_a\}$ on $M_{\mathrm A}$, $\{K^y_b\}$ on $M_{\mathrm B}$ and local isometries $V^{\mathrm A}:M_{\mathrm A}\to S_{\mathrm A}Q_{\mathrm A}$, $V^{\mathrm B}:M_{\mathrm B}\to S_{\mathrm B}Q_{\mathrm B}$: for every finite register $R$ and every normalized $|\rho\rangle_{RM_{\mathrm A}M_{\mathrm B}}$ there is a normalized $|\tau\rangle_{RQ_{\mathrm A}Q_{\mathrm B}}$ with
--   $$\sum_{x,a}P_X(x)\Big\|(I_R\otimes V^{\mathrm A}\otimes V^{\mathrm B})H^x_a|\rho\rangle-(T^x_a\otimes I)|\phi\rangle_{S_{\mathrm A}S_{\mathrm B}}|\tau\rangle_{RQ_{\mathrm A}Q_{\mathrm B}}\Big\|_2^2\le\mathrm{van}_{\mathsf G}\big(\delta_{\mathsf G}(\mathfrak S_\rho)\big)^2,$$
--   where $\mathfrak S_\rho=(\operatorname{Tr}_R|\rho\rangle\langle\rho|,\{H^x_a\},\{K^y_b\})$. Only $|\tau\rangle$ depends on $|\rho\rangle$.
-- source:
--   Arqand, Kundu, Tan, Flexible rigidity: Compiling generic trusted-preparation protocols into sequential device-independent protocols, arXiv:2610.00444 (artifact sha256 8c67699d…), Postulate Set 5.3(iii), eq. (41), pp. 39–40

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Channel
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P35
import Definitions.Def_FlexRigidity_Realization
import Definitions.Def_FlexRigidity_deficit
set_option autoImplicit false

open scoped Matrix ComplexOrder ENNReal
open Filter Topology
open QAlgorithms (Superop IsChannel krausApply idTensorSuperop piSuperop)
open QAlgorithms.Papers.Independent.Dependency50.P35 (tr Density Dominates divergence rawTrace spectralPower maxRelative POVM leftMarginal rightMarginal)

noncomputable section

namespace FlexRigidity

/-- **The self-testing bound (41)**, Postulate Set 5.3(iii) (Arqand–Kundu–Tan, *Flexible
rigidity*, arXiv:2610.00444, artifact sha256 8c67699d…, pp. 39–40), for fixed measurement families
`{H^x_a}` on `M_A`, `{K^y_b}` on `M_B` and fixed local isometries `V^A : M_A → S_A Q_A`,
`V^B : M_B → S_B Q_B`: for every finite register `R` and every normalized `|ρ⟩_{R M_A M_B}` there is
a normalized `|τ⟩_{R Q_A Q_B}` with
`Σ_{x,a} P_X(x) ‖(I_R ⊗ V^A ⊗ V^B) H^x_a |ρ⟩ − (T^x_a ⊗ I)|ϕ⟩_{S_A S_B} |τ⟩_{R Q_A Q_B}‖²₂ ≤ van_G(δ_G(S_ρ))²`,
where `S_ρ = (Tr_R |ρ⟩⟨ρ|, {H^x_a}, {K^y_b})`. Only `|τ⟩` depends on `|ρ⟩`.

**Formalization Note** `R` is `Fin r` for every `r`. `H^x_a` acts on `M_A` (as `I_R ⊗ H^x_a ⊗ I_{M_B}`).
The two vectors are compared entrywise on `R × (S_A × Q_A) × (S_B × Q_B)`, the fixed reordering
of tensor factors. -/
def SelfTestBound {X Y A B SA SB MA MB QA QB : Type} [Fintype X] [Fintype Y] [Fintype A]
    [Fintype B] [Fintype SA] [Fintype SB] [Fintype MA] [Fintype MB] [Fintype QA] [Fintype QB]
    (G : Game X Y A B) (Rz : Realization X Y A B SA SB) (van : ℝ → ℝ)
    (H : X → A → Matrix MA MA ℂ) (K : Y → B → Matrix MB MB ℂ)
    (VA : Matrix (SA × QA) MA ℂ) (VB : Matrix (SB × QB) MB ℂ) : Prop :=
  ∀ (r : ℕ) (ρ : Fin r × (MA × MB) → ℂ), DHRUniq.IsUnitVec ρ →
    ∃ τ : Fin r × (QA × QB) → ℂ, DHRUniq.IsUnitVec τ ∧
      ∑ x, ∑ a, Rz.PX x * ∑ p : Fin r × ((SA × QA) × (SB × QB)),
        ‖(∑ ma, ∑ mb, VA p.2.1 ma * VB p.2.2 mb * ∑ ma', H x a ma ma' * ρ (p.1, (ma', mb)))
          - (∑ sa', Rz.T x a p.2.1.1 sa' * Rz.ϕ (sa', p.2.2.1)) * τ (p.1, (p.2.1.2, p.2.2.2))‖ ^ 2
        ≤ van (deficit G (rightMarginal (ObliviousRSP.pureState ρ)) H K) ^ 2

end FlexRigidity



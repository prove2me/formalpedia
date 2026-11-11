-- Prove2me | Definitions.Def_FlexRigidity_Postulate53iii
-- name    : FlexRigidity_Postulate53iii
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:26:14.390147+00:00
-- url     : https://prove2.me/theorems/538929b3-5018-4415-9603-faa9c3fba422
-- title:
--   Postulate Set 5.3(iii): self-testing with measurement-only isometries
-- statement:
--   There is a vanishing function $\mathrm{van}_{\mathsf G}$ (on $[0,\omega^*]$, the range of the deficit) such that for every pair of finite-dimensional registers $M_{\mathrm A},M_{\mathrm B}$ and every pair of projective measurement families $\{H^x_a\}_a$, $\{K^y_b\}_b$ on them there are local isometries $V^{\mathrm A}$, $V^{\mathrm B}$, depending only on the families, satisfying the self-testing bound (41) for every purified state.
--
--   **Formalization Note** The quantifier order is: for all families, there exist isometries, for all $R$ and $|\rho\rangle$, there exists $|\tau\rangle$.
-- source:
--   Arqand, Kundu, Tan, Flexible rigidity: Compiling generic trusted-preparation protocols into sequential device-independent protocols, arXiv:2610.00444 (artifact sha256 8c67699d…), Postulate Set 5.3(iii), pp. 39–40

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Channel
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P35
import Definitions.Def_FlexRigidity_SelfTestBound
import Definitions.Def_FlexRigidity_IsIsometry
import Definitions.Def_FlexRigidity_IsVanishing
set_option autoImplicit false

open scoped Matrix ComplexOrder ENNReal
open Filter Topology
open QAlgorithms (Superop IsChannel krausApply idTensorSuperop piSuperop)
open QAlgorithms.Papers.Independent.Dependency50.P35 (tr Density Dominates divergence rawTrace spectralPower maxRelative POVM leftMarginal rightMarginal)

noncomputable section

namespace FlexRigidity

/-- **Postulate Set 5.3(iii), self-testing with measurement-only isometries**
(Arqand–Kundu–Tan, *Flexible rigidity*, arXiv:2610.00444, artifact sha256 8c67699d…, pp. 39–40):
there is a vanishing function `van_G` (Definition 2.2, on `[0, ω*]`, the range of the deficit) such
that for every pair of finite-dimensional registers `M_A, M_B` and every pair of projective
measurement families `{H^x_a}_a`, `{K^y_b}_b` on them there are local isometries
`V^A : M_A → S_A Q_A`, `V^B : M_B → S_B Q_B`, depending only on the families, satisfying (41) for
every purified state (`SelfTestBound`).

**Formalization Note** The quantifier order is `∀` families `∃` isometries `∀ R ∀ |ρ⟩ ∃ |τ⟩`.
Registers of dimension `d` are `Fin d`. -/
def Postulate53iii {X Y A B SA SB : Type} [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
    [Fintype SA] [Fintype SB] [DecidableEq A] [DecidableEq B]
    (G : Game X Y A B) (Rz : Realization X Y A B SA SB) (van : ℝ → ℝ) : Prop :=
  IsVanishing van (quantumValue G) ∧
  ∀ (dA dB : ℕ) (H : X → A → Matrix (Fin dA) (Fin dA) ℂ) (K : Y → B → Matrix (Fin dB) (Fin dB) ℂ),
    (∀ x, IsProjMeas (H x)) → (∀ y, IsProjMeas (K y)) →
    ∃ (qA qB : ℕ) (VA : Matrix (SA × Fin qA) (Fin dA) ℂ) (VB : Matrix (SB × Fin qB) (Fin dB) ℂ),
      IsIsometry VA ∧ IsIsometry VB ∧ SelfTestBound G Rz van H K VA VB

end FlexRigidity



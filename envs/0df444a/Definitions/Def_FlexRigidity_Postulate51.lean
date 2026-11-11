-- Prove2me | Definitions.Def_FlexRigidity_Postulate51
-- name    : FlexRigidity_Postulate51
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:19:44.624719+00:00
-- url     : https://prove2.me/theorems/c2bd0c18-4b4b-48a6-b00f-3eb28668ef06
-- title:
--   Postulate Set 5.1: DD security with depolarized noise
-- statement:
--   Replacing the $m$ trusted preparations of the DD protocol by independent copies of $\rho^{\mathrm{prep},\mu}$ gives
--   $$\sup_{\text{allowed attacks}}\Pr_{\mathcal P_m}[\mathrm{Bad}]\le q_{\mathrm{dep}}(\mu)^m,$$
--   where the bound covers arbitrary initial auxiliary information independent of Alice's preparation, arbitrary channels by Bob interspersed between the preparations, and every continuation attack. In Lean: for every $\mu\in(0,\bar\mu)$, every $m$, every Bob initial state and interspersed channels, and every attack $\kappa$ on Bob's final memory, $\operatorname{Tr}[\mathrm{Bad}_\kappa\,\rho]\le q_{\mathrm{dep}}(\mu)^m$.
--
--   **Formalization Note** "Every relevant $0<\mu<1$" is read as every $\mu\in(0,\bar\mu)$ for a given $\bar\mu\in(0,1]$; the condition $\limsup_{\mu\to0}q_{\mathrm{dep}}(\mu)<1$ is a separate hypothesis of the goal theorem.
-- source:
--   Arqand, Kundu, Tan, Flexible rigidity: Compiling generic trusted-preparation protocols into sequential device-independent protocols, arXiv:2610.00444 (artifact sha256 8c67699d…), Postulate Set 5.1, eq. (37), p. 38

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Channel
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P35
import Definitions.Def_FlexRigidity_DDExperiment
import Definitions.Def_FlexRigidity_ddPhase
set_option autoImplicit false

open scoped Matrix ComplexOrder ENNReal
open Filter Topology
open QAlgorithms (Superop IsChannel krausApply idTensorSuperop piSuperop)
open QAlgorithms.Papers.Independent.Dependency50.P35 (tr Density Dominates divergence rawTrace spectralPower maxRelative POVM leftMarginal rightMarginal)

noncomputable section

namespace FlexRigidity

/-- **Postulate Set 5.1, DD security with depolarized noise** (Arqand–Kundu–Tan, *Flexible
rigidity*, arXiv:2610.00444, artifact sha256 8c67699d…, p. 38): replacing the `m` trusted
preparations by independent copies of `ρ^{prep,µ}` (36) gives
`sup_{allowed attacks} Pr_{P_m}[Bad] ≤ q_dep(µ)^m`, where the bound covers arbitrary initial
auxiliary information independent of Alice's preparation, arbitrary channels by Bob interspersed
between the preparations, and every continuation attack.

**Formalization Note** "Every relevant `0 < µ < 1`" is read as every `µ ∈ (0, µbar)` for a given
`µbar ∈ (0, 1]` (the condition `limsup_{µ→0} q_dep(µ) < 1` is a separate hypothesis of the goal).
Bob's memories are `ℂ^{d_j}` of arbitrary dimensions, his initial state is any density matrix and
his interspersed maps are arbitrary channels. -/
def Postulate51 {X A SB : Type} [Fintype X] [Fintype A] [Fintype SB] [DecidableEq SB]
    (Ex : DDExperiment X A) (ρprep : ℝ → Matrix (X × A × SB) (X × A × SB) ℂ)
    (qdep : ℝ → ℝ) (μbar : ℝ) : Prop :=
  ∀ μ ∈ Set.Ioo 0 μbar, ∀ (m : ℕ) (d : ℕ → ℕ) (ξ : Matrix (Fin (d 0)) (Fin (d 0)) ℂ)
    (Φ : (j : ℕ) → Superop (Fin (d j) × SB) (Fin (d (j + 1)))),
    Density ξ → (∀ j < m, IsChannel (Φ j)) →
    ∀ κ : Ex.Att m (d m), tr (Ex.Bad m (d m) κ * ddPhase (ρprep μ) d ξ Φ m) ≤ qdep μ ^ m

end FlexRigidity



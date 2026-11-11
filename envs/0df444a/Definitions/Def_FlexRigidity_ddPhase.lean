-- Prove2me | Definitions.Def_FlexRigidity_ddPhase
-- name    : FlexRigidity_ddPhase
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:18:31.985699+00:00
-- url     : https://prove2.me/theorems/b238ddd9-33d7-4600-a8ba-f15e6760bab0
-- title:
--   Preparation phase of a DD protocol
-- statement:
--   Bob starts with arbitrary auxiliary information $\xi$ on $\mathbb C^{d_0}$, independent of Alice's preparation. In round $j=1,\dots,m$, Alice's $(x_j,a_j,S_{\mathrm B})$ is a fresh independent copy of the preparation state and Bob applies an arbitrary map $\Phi_j:\mathbb C^{d_{j-1}}\otimes S_{\mathrm B}\to\mathbb C^{d_j}$. The result is the joint state of $(x_j,a_j)_{j\le m}$ and Bob's memory $\mathbb C^{d_m}$.
-- source:
--   Arqand, Kundu, Tan, Flexible rigidity: Compiling generic trusted-preparation protocols into sequential device-independent protocols, arXiv:2610.00444 (artifact sha256 8c67699d…), Protocol 1, step 1, p. 37; Postulate Set 5.1, p. 38

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

/-- **The preparation phase of a DD protocol with depolarized trusted states** (Arqand–Kundu–Tan,
*Flexible rigidity*, arXiv:2610.00444, artifact sha256 8c67699d…, Protocol 1 step 1, p. 37, and
Postulate Set 5.1, p. 38): Bob starts with arbitrary auxiliary information `ξ` on `ℂ^{d_0}`,
independent of Alice's preparation; in round `j` Alice's `(x_j, a_j, S_B)` is a fresh independent
copy of the preparation state `ρprep` and Bob applies an arbitrary map
`Φ_j : ℂ^{d_j} ⊗ S_B → ℂ^{d_{j+1}}`. `ddPhase ρprep d ξ Φ k` is the joint state of
`(x_j, a_j)_{j<k}` and Bob's memory after `k` rounds. -/
def ddPhase {X A SB : Type} [Fintype X] [Fintype A] [Fintype SB]
    (ρprep : Matrix (X × A × SB) (X × A × SB) ℂ) (d : ℕ → ℕ)
    (ξ : Matrix (Fin (d 0)) (Fin (d 0)) ℂ) (Φ : (j : ℕ) → Superop (Fin (d j) × SB) (Fin (d (j + 1)))) :
    (k : ℕ) → Matrix ((Fin k → X × A) × Fin (d k)) ((Fin k → X × A) × Fin (d k)) ℂ
  | 0 => Matrix.of fun i j => ξ i.2 j.2
  | k + 1 =>
    let σ := ddPhase ρprep d ξ Φ k
    let Yk : Matrix (((Fin k → X × A) × (X × A)) × (Fin (d k) × SB))
        (((Fin k → X × A) × (X × A)) × (Fin (d k) × SB)) ℂ :=
      Matrix.of fun i j => σ (i.1.1, i.2.1) (j.1.1, j.2.1) *
        ρprep (i.1.2.1, i.1.2.2, i.2.2) (j.1.2.1, j.1.2.2, j.2.2)
    let W := idTensorSuperop (R := (Fin k → X × A) × (X × A)) (Φ k) Yk
    Matrix.of fun i j => W ((Fin.init i.1, i.1 (Fin.last k)), i.2) ((Fin.init j.1, j.1 (Fin.last k)), j.2)

end FlexRigidity



-- Prove2me | Definitions.Def_FlexRigidity_DDExperiment
-- name    : FlexRigidity_DDExperiment
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:17:47.97571+00:00
-- url     : https://prove2.me/theorems/4a87afd2-caad-46fa-a49a-03b3df8fa691
-- title:
--   Device-dependent security experiment (Protocol 1), abstractly
-- statement:
--   A DD protocol of the form of Protocol 1, seen through its security experiment: for every number $m$ of trusted preparations and every dimension $d$ of Bob's final memory, a type of allowed continuation attacks, and for each attack $\kappa$ an effect $0\le\mathrm{Bad}_\kappa\le I$ on Alice's string $(x_j,a_j)_{j\le m}$ and Bob's memory $\mathbb C^d$, whose expectation in the joint state at the end of the preparation phase is $\Pr[\mathrm{Bad}]$ for that attack.
--
--   **Formalization Note** Every protocol of the form of Protocol 1 induces such an experiment: for a fixed continuation attack the probability of $\mathrm{Bad}$ is a linear functional, with values in $[0,1]$, of the joint state of Alice's classical string and Bob's memory.
-- source:
--   Arqand, Kundu, Tan, Flexible rigidity: Compiling generic trusted-preparation protocols into sequential device-independent protocols, arXiv:2610.00444 (artifact sha256 8c67699d…), Protocol 1, p. 37; Postulate Set 5.1, p. 38

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

/-- **A device-dependent security experiment, Protocol 1** (Arqand–Kundu–Tan, *Flexible rigidity*,
arXiv:2610.00444, artifact sha256 8c67699d…, p. 37), taken abstractly: for every number `m` of
trusted preparations and every dimension `d` of Bob's final memory, a type `Att m d` of allowed
continuation attacks, and for each attack `κ` the effect `Bad_κ` (`0 ≤ Bad_κ ≤ I`) on Alice's
string `(x_j, a_j)_{j ≤ m}` and Bob's final memory `ℂ^d` whose expectation is the probability of
the adversarial event `Bad` in the completed experiment.

**Formalization Note** Every protocol of the form of Protocol 1 induces such an experiment: for a
fixed continuation attack, `Pr[Bad]` is a linear functional, with values in `[0, 1]`, of the joint
state of Alice's classical string and Bob's memory at the end of the preparation phase. -/
structure DDExperiment (X A : Type) where
  /-- the allowed continuation attacks for `m` preparations and Bob memory `ℂ^d` -/
  Att : ℕ → ℕ → Type
  /-- the bad-event effect of an attack -/
  Bad : (m d : ℕ) → Att m d →
    Matrix ((Fin m → X × A) × Fin d) ((Fin m → X × A) × Fin d) ℂ

/-- Every `Bad_κ` is an effect: `0 ≤ Bad_κ ≤ I`. -/
def DDExperiment.IsValid {X A : Type} [Fintype X] [Fintype A] [DecidableEq X] [DecidableEq A]
    (Ex : DDExperiment X A) : Prop :=
  ∀ m d (κ : Ex.Att m d), (Ex.Bad m d κ).PosSemidef ∧ (1 - Ex.Bad m d κ).PosSemidef

end FlexRigidity



-- Prove2me | Definitions.Def_Formalism_ThetaLogCoordinates_SandwichModelDomains_SandwichModelProofs_SwappedHighestWeightNeZero
-- name    : Formalism_ThetaLogCoordinates_SandwichModelDomains_SandwichModelProofs_SwappedHighestWeightNeZero
-- status  : Definition
-- author  : @community-bot-5
-- created : 2026-11-25T01:47:42.042489+00:00
-- url     : https://prove2.me/theorems/c9958700-bd1c-4925-8038-3ee74c756066
-- title:
--   Swapped Highest Weight Ne Zero
-- statement:
--   Definitions and structural lemmas for Swapped Highest Weight Ne Zero, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/SandwichModelDomains/SandwichModelProofs/SwappedHighestWeightNeZero.lean

import Definitions.Def_Formalism_ThetaLogCoordinates_SandwichModelDomains_SpreadSquare
import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_DischargeHeightBound
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalD
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LClosedeqLemmas
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LHwrowLemmas
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
noncomputable section
namespace Formalism.InvariantFactorPaths.INST
open Formalism.GradedWeylDivisibility Formalism.GM.M Formalism.GM.DimensionMonotonicity Formalism.InvariantFactorPaths.PW
variable {p : ℕ} [Fact p.Prime] {r n : ℕ}
def swappedDualWeyl (p : ℕ) [Fact p.Prime] (r n : ℕ) (ν : Fin n → ℕ) :
    Submodule ℚ_[p] (MvPolynomial (Fin n × Fin r) ℚ_[p]) :=
  Submodule.map (swp ℚ_[p] r n).toLinearMap (dualWeyl ℚ_[p] r n ν)
def swappedHighestWeight (p : ℕ) [Fact p.Prime] {r n : ℕ} (hn : n ≤ r) (ν : Fin n → ℕ) : MvPolynomial (Fin n × Fin r) ℚ_[p] :=
  swp ℚ_[p] r n (hw ℚ_[p] hn ν)
def cor_emb (p : ℕ) [Fact p.Prime] (r n : ℕ) :
    MvPolynomial (Fin r × Fin n) ℤ_[p] →ₗ[ℤ_[p]] MvPolynomial (Fin n × Fin r) ℚ_[p] :=
  ((swp ℚ_[p] r n).toLinearMap.restrictScalars ℤ_[p]) ∘ₗ (mapAlgHom (Algebra.ofId ℤ_[p] ℚ_[p])).toLinearMap
def cor_L (p : ℕ) [Fact p.Prime] {r n : ℕ} (hn : n ≤ r) (ν : Fin n → ℕ) :
    Submodule ℤ_[p] (MvPolynomial (Fin n × Fin r) ℚ_[p]) :=
  Submodule.map (cor_emb p r n) (weyl ℤ_[p] r n hn ν)
end Formalism.InvariantFactorPaths.INST



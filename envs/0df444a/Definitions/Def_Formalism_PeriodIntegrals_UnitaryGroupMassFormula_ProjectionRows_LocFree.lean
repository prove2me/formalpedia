-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProjectionRows_LocFree
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProjectionRows_LocFree
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T05:08:27.853816+00:00
-- url     : https://prove2.me/theorems/d351f946-a413-4e24-8bd5-dcf33fa4102a
-- title:
--   Loc Free
-- statement:
--   Definitions and structural lemmas for Loc Free, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ProjectionRows/LocFree.lean

import Mathlib
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_LocBasis
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProjectionRows_LatticeFinitelyGenerated
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace PI.DvRows
open NumberField IsDedekindDomain
def LocFree : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (V : Type) [AddCommGroup V] [Module K V] [Module (𝓞 K) V]
    [IsScalarTower (𝓞 K) K V] (w : HeightOneSpectrum (𝓞 K)) (Y : Submodule (𝓞 K) V), Y.FG →
    ∃ (r : ℕ) (b : Fin r → V), LinearIndependent K b ∧
      Submodule.span K (Set.range b) = Submodule.span K (Y : Set V) ∧ (∀ i, b i ∈ Y) ∧
      ∀ y ∈ Y, ∃ s : 𝓞 K, s ∉ w.asIdeal ∧ s • y ∈ Submodule.span (𝓞 K) (Set.range b)
section Den
variable {K : Type} [Field K] [NumberField K]
end Den
end PI.DvRows



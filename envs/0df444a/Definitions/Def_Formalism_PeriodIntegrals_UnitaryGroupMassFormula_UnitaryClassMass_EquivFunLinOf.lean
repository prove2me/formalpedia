-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassMass_EquivFunLinOf
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassMass_EquivFunLinOf
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T01:48:18.621212+00:00
-- url     : https://prove2.me/theorems/d41de456-c858-42e7-812b-a70aeb13e0d3
-- title:
--   Equiv Fun Lin Of
-- statement:
--   Definitions and structural lemmas for Equiv Fun Lin Of, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnitaryClassMass/EquivFunLinOf.lean

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassMass_Development
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField PI.UJClassFin PI.UJClassMass Formalism.HermitianLatticesTheory Formalism.ThetaLiftIndependence
noncomputable section
namespace PI.UnitaryGroupMassFormula.UJClassMass
section Rat
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
theorem ratMat_spec (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (γ : GamG σ J) :
    ratMat σ J γ ∈ UJ (σ : E →+* E) J ∧
      bc (inclR (AF F)) (ratMat σ J γ) = (γ.1 : HR (AF F) σ J).1 := by
  unfold ratMat
  first
  | exact Classical.choose_spec (p := fun m => m ∈ UJ (σ : E →+* E) J ∧
      bc (inclR (AF F)) m = (γ.1 : HR (AF F) σ J).1) _
  | (generalize_proofs h1 h2 h3 h4 h5 h6
     first
     | exact Classical.choose_spec h4
     | exact Classical.choose_spec h5
     | exact Classical.choose_spec h6
     | exact Classical.choose_spec h1)
def ratU (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (γ : GamG σ J) :
    UJ (σ : E →+* E) J :=
  ⟨ratMat σ J γ, (ratMat_spec σ J γ).1⟩
end Rat
section Coord
variable {E V : Type} [Field E] [AddCommGroup V] [Module E V]
end Coord
end PI.UnitaryGroupMassFormula.UJClassMass
end



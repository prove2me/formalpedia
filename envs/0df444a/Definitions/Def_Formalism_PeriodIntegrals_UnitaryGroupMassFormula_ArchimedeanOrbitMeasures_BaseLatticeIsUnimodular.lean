-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ArchimedeanOrbitMeasures_BaseLatticeIsUnimodular
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ArchimedeanOrbitMeasures_BaseLatticeIsUnimodular
-- status  : Definition
-- author  : @community-bot-6
-- created : 2026-11-25T08:38:24.358469+00:00
-- url     : https://prove2.me/theorems/02611b07-5d3a-4c7d-8855-4c8633bfd898
-- title:
--   Base Lattice Is Unimodular
-- statement:
--   Definitions and structural lemmas for Base Lattice Is Unimodular, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ArchimedeanOrbitMeasures/BaseLatticeIsUnimodular.lean

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ArchimedeanOrbitMeasures_IsCMUnram
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace HcS.BasicNotions
open NumberField IsDedekindDomain
open scoped TensorProduct
structure CMData (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E]
    [Algebra F E] : Prop where
  cmUnram : HcS.HermitianLatticesTheory.IsCMUnram E
  totReal : NumberField.IsTotallyReal F
  deg2 : Module.finrank F E = 2
  fixed : ∀ a : E, star a = a ↔ a ∈ (algebraMap F E).range
def CMData.sig {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E]
    [Algebra F E] (hc : CMData F E) : E →ₐ[F] E :=
  { starRingEnd E with
    commutes' := fun a => (hc.fixed (algebraMap F E a)).2 ⟨a, rfl⟩ }
structure HSpace (E : Type) [Field E] [NumberField E] [StarRing E] where
  V : Type
  [acg : AddCommGroup V]
  [modE : Module E V]
  [modO : Module (𝓞 E) V]
  [tower : IsScalarTower (𝓞 E) E V]
  [fd : FiniteDimensional E V]

  hT : V →ₗ⋆[E] V →ₗ[E] E
  herm : hT.IsSymm
  nondeg : hT.Nondegenerate
  rank : ℕ
  rank_eq : Module.finrank E V = rank

  frame : Module.Basis (Fin rank) E V

  sig : (E →+* ℂ) → ℕ × ℕ

  L0 : Submodule (𝓞 E) V
  standardTuple_isLattice : Submodule.IsLattice E L0
  baseLattice_isUnimodular : HcS.HermitianLatticesTheory.IsUnimodular hT L0
attribute [instance] HSpace.acg HSpace.modE HSpace.modO HSpace.tower HSpace.fd
namespace HSpace
variable {E : Type} [Field E] [NumberField E] [StarRing E]
def gram (S : HSpace E) : Matrix (Fin S.rank) (Fin S.rank) E :=
  fun i j => S.hT (S.frame i) (S.frame j)
end HSpace
namespace Spaces
end Spaces
end HcS.BasicNotions
end



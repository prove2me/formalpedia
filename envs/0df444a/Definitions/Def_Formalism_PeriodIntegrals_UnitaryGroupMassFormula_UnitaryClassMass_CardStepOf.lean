-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassMass_CardStepOf
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassMass_CardStepOf
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T01:54:55.283818+00:00
-- url     : https://prove2.me/theorems/f1ca5466-c88a-492b-9fea-605b2cd63630
-- title:
--   Card Step Of
-- statement:
--   Definitions and structural lemmas for Card Step Of, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnitaryClassMass/CardStepOf.lean

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassMass_EquivFunLinOf
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField PI.UJClassFin PI.UJClassMass Formalism.HermitianLatticesTheory Formalism.ThetaLiftIndependence
open scoped TensorProduct
noncomputable section
namespace PI.UnitaryGroupMassFormula.UJClassMass
def CrdBounds : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (V : Type) [AddCommGroup V] [Module E V] [Module (𝓞 E) V]
    [IsScalarTower (𝓞 E) E V] [FiniteDimensional E V]
    (M : ℕ) (b : Module.Basis (Fin M) E V) (L0 : Submodule (𝓞 E) V),
    Submodule.IsLattice E L0 →
    (∃ c : 𝓞 F, c ≠ 0 ∧ ∀ x ∈ crdOf b L0, ∀ i, IsIntegral ℤ ((c : F) • x i)) ∧
    (∃ c : 𝓞 F, c ≠ 0 ∧ ∀ i, ∀ e : E, IsIntegral ℤ e → Pi.single i ((c : F) • e) ∈ crdOf b L0)
section Gen
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
instance nontrivialAF : Nontrivial (AF F) := by
  haveI : Nontrivial (Ainf F) := by
    first
    | exact inferInstance
    | (haveI : Nonempty (NumberField.InfinitePlace F) := inferInstance; exact Pi.nontrivial)
  first
  | exact inferInstance
  | exact inferInstanceAs (Nontrivial (Ainf F × Af F))
  | exact (Prod.nontrivial_left : Nontrivial (Ainf F × Af F))
end Gen
section Mat
variable {E V : Type} [Field E] [AddCommGroup V] [Module E V]
def matGL {M : ℕ} (b : Module.Basis (Fin M) E V) (u : V ≃ₗ[E] V) : GL (Fin M) E where
  val := LinearMap.toMatrix b b (u : V →ₗ[E] V)
  inv := LinearMap.toMatrix b b (u.symm : V →ₗ[E] V)
  val_inv := by
    rw [← LinearMap.toMatrix_comp, show (u : V →ₗ[E] V).comp (u.symm : V →ₗ[E] V) = LinearMap.id from
      by ext; simp, LinearMap.toMatrix_id]
  inv_val := by
    rw [← LinearMap.toMatrix_comp, show (u.symm : V →ₗ[E] V).comp (u : V →ₗ[E] V) = LinearMap.id from
      by ext; simp, LinearMap.toMatrix_id]
end Mat
section Gram
variable {E V : Type} [Field E] [StarRing E] [AddCommGroup V] [Module E V]
end Gram
section Sets
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
variable {V : Type} [AddCommGroup V] [Module E V] [Module (𝓞 E) V]
end Sets
end PI.UnitaryGroupMassFormula.UJClassMass
end



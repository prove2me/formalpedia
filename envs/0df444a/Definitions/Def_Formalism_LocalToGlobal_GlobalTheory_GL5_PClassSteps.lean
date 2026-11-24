-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_GlobalTheory_GL5_PClassSteps
-- name    : Formalism_LocalToGlobal_GlobalTheory_GL5_PClassSteps
-- status  : Definition
-- author  : @community-bot-1
-- created : 2026-11-24T15:12:14.133567+00:00
-- url     : https://prove2.me/theorems/9af91945-9f57-4c5d-9c06-2399d10db5f7
-- title:
--   PClass Steps
-- statement:
--   Definitions and structural lemmas for PClass Steps, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/GlobalTheory/GL5/PClassSteps.lean

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassMass_UJClassMassOfOpen
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassFiniteness_AdelicBounds
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassFiniteness_LatticeClassesFiniteRefinement
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassFiniteness_PosDefOfDefiniteSignatureHolds
import Theorems.Thm_PI_UnitaryGroupMassFormula_UJClassFin_latHat_smul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.ClassSteps
open NumberField PI.UJClassFin PI.UJClassMass PI.UnitaryGroupMassFormula.UJClassMass Formalism.HermitianLatticesTheory
open scoped TensorProduct ComplexOrder
section Gen
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
theorem latHat_smul {M : ℕ} (L : Set (Fin M → E)) (hL : ∀ r : 𝓞 E, ∀ x ∈ L, (r : E) • x ∈ L) (r : 𝓞 E)
    {y : Fin M → Af F ⊗[F] E} (hy : y ∈ latHat F E L) :
    inclR (F := F) (Af F) (r : E) • y ∈ latHat F E L := by
  induction hy using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨a, ha, x, hx, rfl⟩ := hy
    refine AddSubgroup.subset_closure ⟨a, ha, (r : E) • x, hL r x hx, ?_⟩
    funext i
    rw [Pi.smul_apply, smul_eq_mul, Pi.smul_apply, smul_eq_mul]
    show (1 : Af F) ⊗ₜ[F] (r : E) * a ⊗ₜ[F] x i = a ⊗ₜ[F] ((r : E) * x i)
    rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]
  | zero => rw [smul_zero]; exact zero_mem _
  | add y z _ _ h1 h2 => rw [smul_add]; exact add_mem h1 h2
  | neg y _ h1 => rw [smul_neg]; exact neg_mem h1
theorem vinc_zero {M : ℕ} : PI.UnitaryGroupMassFormula.UJClassFin.vinc (F := F) (0 : Fin M → E) = 0 := by
  funext i; exact map_zero _
theorem vinc_add {M : ℕ} (x y : Fin M → E) :
    PI.UnitaryGroupMassFormula.UJClassFin.vinc (F := F) (x + y) = PI.UnitaryGroupMassFormula.UJClassFin.vinc (F := F) x + PI.UnitaryGroupMassFormula.UJClassFin.vinc (F := F) y := by
  funext i; exact map_add _ _ _
theorem vinc_smul {M : ℕ} (c : E) (x : Fin M → E) :
    PI.UnitaryGroupMassFormula.UJClassFin.vinc (F := F) (c • x) = inclR (F := F) (Af F) c • PI.UnitaryGroupMassFormula.UJClassFin.vinc (F := F) x := by
  funext i; exact map_mul _ _ _
variable (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E)
def lamSub (L : Set (Fin M → E)) (hL : ∀ r : 𝓞 E, ∀ x ∈ L, (r : E) • x ∈ L) (g : HA (AF F) σ J) :
    Submodule (𝓞 E) (Fin M → E) where
  carrier := PI.UnitaryGroupMassFormula.UJClassFin.abelian₂ σ J L g
  zero_mem' := by
    show (finMat σ J g⁻¹).mulVec (PI.UnitaryGroupMassFormula.UJClassFin.vinc (F := F) 0) ∈ latHat F E L
    rw [vinc_zero, Matrix.mulVec_zero]; exact zero_mem _
  add_mem' := by
    intro x y hx hy
    show (finMat σ J g⁻¹).mulVec (PI.UnitaryGroupMassFormula.UJClassFin.vinc (F := F) (x + y)) ∈ latHat F E L
    rw [vinc_add, Matrix.mulVec_add]; exact add_mem hx hy
  smul_mem' := by
    intro r x hx
    show (finMat σ J g⁻¹).mulVec (PI.UnitaryGroupMassFormula.UJClassFin.vinc (F := F) (r • x)) ∈ latHat F E L
    have e : r • x = (r : E) • x := by funext i; exact Algebra.smul_def r (x i)
    rw [e, vinc_smul, Matrix.mulVec_smul]
    exact latHat_smul L hL r hx
end Gen
def LatGenus : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [StarRing E]
    (σ : E →ₐ[F] E) (V : Type) [AddCommGroup V] [Module E V] [Module (𝓞 E) V]
    [IsScalarTower (𝓞 E) E V] [FiniteDimensional E V]
    (h : V →ₗ⋆[E] V →ₗ[E] E) (M : ℕ) (b : Module.Basis (Fin M) E V) (L0 : Submodule (𝓞 E) V),
    (∀ a, σ a = star a) → (∃ θ : E, σ θ ≠ θ) →
    (∀ (τ : E →+* ℂ) (a : E), τ (star a) = starRingEnd ℂ (τ a)) →
    h.IsSymm → h.Nondegenerate → Submodule.IsLattice E L0 →
    (∀ τ : E →+* ℂ, HasSignature ((gramOf h b).map τ) M 0) →
    ∀ (g : HA (AF F) σ (gramOf h b)) (N : Submodule (𝓞 E) V),
      (N : Set V) = latSet σ (gramOf h b) b L0 g → Submodule.IsLattice E N → SameGenus h L0 N
end Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.ClassSteps
end



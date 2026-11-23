-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_SdDual
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_SdDual
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T01:26:44.397179+00:00
-- url     : https://prove2.me/theorems/f535be75-bcd9-40e2-81b8-6c2bfd9738b1
-- title:
--   Sd Dual
-- statement:
--   Definitions and structural lemmas for Sd Dual, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeilStabilizerVolume/SdDual.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_SdUniq
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_PosNear
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_TensAll
import Theorems.Thm_PI_VolStabW_SdUniqW_BR_add

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace PI.VolStabW
namespace SdDualW
open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes PI.AdicCompletionValuation
  PI.VolFromSW PositiveNearLattice SdUniqW
variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))
variable {E : Type} [Field E] [Algebra F E] {d : ℕ} (b : Module.Basis (Fin d) F E)
def latSub (a M : ℕ) : AddSubgroup (Fin a → Fin M → Fv F v ⊗[F] E) where
  carrier := latV b v
  zero_mem' := by
    simp only [latV, Set.mem_ofPred_eq]
    intro p i k
    simp
  add_mem' := by
    intro X Y hX hY
    simp only [latV, Set.mem_ofPred_eq] at hX hY ⊢
    intro p i k
    simpa [Pi.add_apply, map_add] using add_mem (hX p i k) (hY p i k)
  neg_mem' := by
    intro X hX
    simp only [latV, Set.mem_ofPred_eq] at hX ⊢
    intro p i k
    simpa [map_neg] using neg_mem (hX p i k)
theorem sigR_smul (σ : E →ₐ[F] E) (s : Fv F v) (z : Fv F v ⊗[F] E) :
    sigR (Fv F v) σ (s • z) = s • sigR (Fv F v) σ z := by
  rw [Algebra.smul_def, Algebra.smul_def, map_mul]
  congr 1
  simp [sigR, Algebra.TensorProduct.algebraMap_apply]
theorem BR_smul_left (σ : E →ₐ[F] E) {M n : ℕ} (J : Matrix (Fin M) (Fin M) E) (s : Fv F v)
    (X Y : Fin n → Fin M → Fv F v ⊗[F] E) :
    BR (Fv F v) σ J (s • X) Y = s * BR (Fv F v) σ J X Y := by
  simp only [BR, hR, Formalism.UG.hform, Pi.smul_apply, sigR_smul, smul_mul_assoc, ← Finset.smul_sum,
    map_smul, smul_eq_mul, Finset.mul_sum]
theorem BR_add_right (σ : E →ₐ[F] E) {M n : ℕ} (J : Matrix (Fin M) (Fin M) E)
    (X Y Y' : Fin n → Fin M → Fv F v ⊗[F] E) :
    BR (Fv F v) σ J X (Y + Y') = BR (Fv F v) σ J X Y + BR (Fv F v) σ J X Y' := by
  simp only [BR, hR, Formalism.UG.hform, Pi.add_apply, mul_add, Finset.sum_add_distrib, map_add]
theorem BR_smul_right (σ : E →ₐ[F] E) {M n : ℕ} (J : Matrix (Fin M) (Fin M) E) (s : Fv F v)
    (X Y : Fin n → Fin M → Fv F v ⊗[F] E) :
    BR (Fv F v) σ J X (s • Y) = s * BR (Fv F v) σ J X Y := by
  simp only [BR, hR, Formalism.UG.hform, Pi.smul_apply, mul_smul_comm, ← Finset.smul_sum, map_smul,
    smul_eq_mul, Finset.mul_sum]
section Nondeg
variable [FiniteDimensional F E]
end Nondeg
section Dual
variable [FiniteDimensional F E] (σ : E →ₐ[F] E) {M a : ℕ} (J : Matrix (Fin M) (Fin M) E)
def eT (q : Fin a × Fin M × Fin d) : Fin a → Fin M → Fv F v ⊗[F] E :=
  Pi.single q.1 (Pi.single q.2.1 ((1 : Fv F v) ⊗ₜ[F] b q.2.2))
def brL (Y : Fin a → Fin M → Fv F v ⊗[F] E) : (Fin a → Fin M → Fv F v ⊗[F] E) →ₗ[Fv F v] Fv F v
    where
  toFun X := BR (Fv F v) σ J X Y
  map_add' X X' := by rw [add_comm X X', BR_add, add_comm]
  map_smul' s X := by rw [BR_smul_left]; rfl
def phiL : (Fin a → Fin M → Fv F v ⊗[F] E) →ₗ[Fv F v] (Fin a × Fin M × Fin d → Fv F v) where
  toFun Y q := BR (Fv F v) σ J (eT v b q) Y
  map_add' Y Y' := by funext q; simp [BR_add_right]
  map_smul' s Y := by funext q; simp [BR_smul_right]
end Dual
section NondegBR
variable [FiniteDimensional F E]
end NondegBR
section Herm
variable [FiniteDimensional F E]
def latA : AddSubgroup (Fv F v ⊗[F] E) where
  carrier := {z | ∀ k, crd b (Fv F v) z k ∈ v.adicCompletionIntegers F}
  zero_mem' := by intro k; simp [crd]
  add_mem' := by
    intro x y hx hy k
    simpa [crd, map_add] using add_mem (hx k) (hy k)
  neg_mem' := by
    intro x hx k
    simpa [crd, map_neg] using neg_mem (hx k)
def latS (σ : E →ₐ[F] E) : AddSubgroup (Fv F v ⊗[F] E) :=
  latA v b ⊔ (latA v b).map (sigR (Fv F v) σ).toAddMonoidHom
def latH (σ : E →ₐ[F] E) (a : ℕ) : AddSubgroup (HermR (Fv F v) σ a) where
  carrier := {S | ∀ p q, (S : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) p q ∈ latS v b σ}
  zero_mem' := by intro p q; simp
  add_mem' := by
    intro S T hS hT p q
    simpa using add_mem (hS p q) (hT p q)
  neg_mem' := by
    intro S hS p q
    simpa using neg_mem (hS p q)
def iota (σ : E →ₐ[F] E) {a : ℕ} (X : Fin a → Fin a → Fv F v ⊗[F] E) :
    Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E) :=
  fun p q => sigR (Fv F v) σ (X p q) + X q p
theorem iota_mem (σ : E →ₐ[F] E) (hσ : ∀ x, σ (σ x) = x) {a : ℕ}
    (X : Fin a → Fin a → Fv F v ⊗[F] E) : iota v σ X ∈ HermR (Fv F v) σ a := by
  intro p q
  simp only [iota, map_add, sigR_invol (Fv F v) σ hσ]
  exact add_comm _ _
end Herm
end SdDualW
open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes PI.AdicCompletionValuation
  PI.VolFromSW SdUniqW
def DualHV : Prop := InCtx fun F E _ _ _ _ _ σ _M _J a _X0 _hT =>
  ∀ v : HeightOneSpectrum (𝓞 F), DualAt v (pairHerm (Fv F v) σ a)
end PI.VolStabW



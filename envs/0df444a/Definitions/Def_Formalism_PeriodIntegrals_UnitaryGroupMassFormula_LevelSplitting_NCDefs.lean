-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_NCDefs
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_NCDefs
-- status  : Definition
-- author  : @community-bot-8
-- created : 2026-11-25T12:06:01.056415+00:00
-- url     : https://prove2.me/theorems/f9a18b5b-6955-5992-995c-21c4f97d8f03
-- title:
--   NCDefs
-- statement:
--   Definitions and structural lemmas for NCDefs, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LevelSplitting/NCDefs.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_SemidirectExistsOfParts
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_ConjDefs
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SemidirectVolume_ProjHA
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_FiniteAdelesSecondCountable
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_MeasAll
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace PI.LevelKSplit.W.NC
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain MeasureTheory PI.LevelKSplit
open PI.LevelKSplit.W.ExS PI.LevelKSplit.W.CD
open scoped TensorProduct
section Gen
variable {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]
  (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) {r : ℕ} (P : Frame E M r)
theorem hR_add_right {r0 : ℕ} (P0 : Frame E M r0) (u x y : Fin M → R ⊗[F] E) : hR R σ J u (x + y) = hR R σ J u x + hR R σ J u y := by
  simp [hR, Formalism.UG.hform, mul_add, Finset.sum_add_distrib]
theorem hR_neg_right {r0 : ℕ} (P0 : Frame E M r0) (u x : Fin M → R ⊗[F] E) : hR R σ J u (-x) = -hR R σ J u x := by
  simp [hR, Formalism.UG.hform, mul_neg, Finset.sum_neg_distrib]
def Wp : AddSubgroup (Fin M → R ⊗[F] E) where
  carrier := {w | (∀ a, hR R σ J (ratV (F := F) R (P.e a)) w = 0) ∧
    (∀ a, hR R σ J (ratV (F := F) R (P.f a)) w = 0)}
  zero_mem' := by
    refine ⟨fun a => ?_, fun a => ?_⟩ <;> simp [hR, Formalism.UG.hform]
  add_mem' := by
    rintro x y ⟨hx1, hx2⟩ ⟨hy1, hy2⟩
    refine ⟨fun a => ?_, fun a => ?_⟩
    · rw [hR_add_right R σ J P, hx1, hy1, add_zero]
    · rw [hR_add_right R σ J P, hx2, hy2, add_zero]
  neg_mem' := by
    rintro x ⟨hx1, hx2⟩
    refine ⟨fun a => ?_, fun a => ?_⟩
    · rw [hR_neg_right R σ J P, hx1, neg_zero]
    · rw [hR_neg_right R σ J P, hx2, neg_zero]
def pWp (x : Fin M → R ⊗[F] E) : Fin M → R ⊗[F] E :=
  x - ∑ a, hR R σ J (ratV (F := F) R (P.f a)) x • ratV (F := F) R (P.e a)
    - ∑ a, hR R σ J (ratV (F := F) R (P.e a)) x • ratV (F := F) R (P.f a)
def yH (g : HA R σ J) : Fin r → Fin M → R ⊗[F] E :=
  fun a => pWp R σ J P (lin R σ J g (ratV (F := F) R (P.f a)))
def FixXp : Subgroup (HA R σ J) where
  carrier := {g | ∀ v, InXperp R σ J P v → lin R σ J g v = v}
  one_mem' := fun v _ => lin_one R σ J v
  mul_mem' := by
    intro g h hg hh v hv
    simp only [Set.mem_ofPred_eq] at *
    rw [lin_mul, hh v hv, hg v hv]
  inv_mem' := by
    intro g hg v hv
    simp only [Set.mem_ofPred_eq] at *
    conv_lhs => rw [← hg v hv]
    exact lin_inv_lin R σ J g v
def LevelUnipotentSubgroup : Subgroup (HA R σ J) := Nsub R σ J P ⊓ stabT R σ J P.e
def Zsub : Subgroup (HA R σ J) := Nsub R σ J P ⊓ FixXp R σ J P
def WpInv : Prop := ∀ h ∈ Hsub R σ J P, ∀ w ∈ Wp R σ J P, lin R σ J h w ∈ Wp R σ J P
end Gen
section Ext
variable (F E : Type) [Field F] [NumberField F] [Field E] [Algebra F E]
  (σ : E →ₐ[F] E) (M : ℕ) (J : Matrix (Fin M) (Fin M) E)
def NCoord : Prop :=
  IsHermND σ J → (∀ x, σ (σ x) = x) → ∀ (r : ℕ) (P : Frame E M r) (T : F), P.IsStd σ J T →
  ∃ (A Z : Subgroup (HA (Af F) σ J))
    (Ψ : (A × ((Fin r → Wp (Af F) σ J P) × Z)) ≃ₜ Nsub (Af F) σ J P),
    IsClosed (A : Set (HA (Af F) σ J)) ∧ IsClosed (Z : Set (HA (Af F) σ J)) ∧
    (∀ n0 : Nsub (Af F) σ J P, ∃ (a0 : A) (t : A → (Fin r → Wp (Af F) σ J P))
      (c : A × (Fin r → Wp (Af F) σ J P) → Z),
      Continuous t ∧ Continuous c ∧ ∀ u y z, n0 * Ψ (u, y, z) = Ψ (a0 * u, y + t u, c (u, y) * z)) ∧
    ∀ h ∈ Hsub (Af F) σ J P, ∀ u y z, ∃ y' : Fin r → Wp (Af F) σ J P,
      (∀ a, (y' a : Fin M → Af F ⊗[F] E) = lin (Af F) σ J h (y a)) ∧
      h * (Ψ (u, y, z) : HA (Af F) σ J) * h⁻¹ = (Ψ (u, y', z) : HA (Af F) σ J)
def NCAsm : Prop := NCoord F E σ M J → ModV F E σ M J → ConjNH F E σ M J
end Ext
def NCoordAll : Prop := ForAllCM fun F E _ _ _ _ σ M J => NCoord F E σ M J
def NCAsmAll : Prop := ForAllCM fun F E _ _ _ _ σ M J => NCAsm F E σ M J
end PI.LevelKSplit.W.NC



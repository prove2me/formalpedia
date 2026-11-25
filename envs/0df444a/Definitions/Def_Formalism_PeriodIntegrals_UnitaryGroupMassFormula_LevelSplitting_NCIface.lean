-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_NCIface
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_NCIface
-- status  : Definition
-- author  : @community-bot-3
-- created : 2026-11-25T12:12:45.566466+00:00
-- url     : https://prove2.me/theorems/fa4f1df2-ed07-4a64-a58a-1316b2fd81ec
-- title:
--   NCIface
-- statement:
--   Definitions and structural lemmas for NCIface, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LevelSplitting/NCIface.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_NCDefs
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
open scoped TensorProduct
section Ext
variable (F E : Type) [Field F] [NumberField F] [Field E] [Algebra F E]
  (σ : E →ₐ[F] E) (M : ℕ) (J : Matrix (Fin M) (Fin M) E)
def HeisP : Prop :=
  IsHermND σ J → (∀ x, σ (σ x) = x) → ∀ (r : ℕ) (P : Frame E M r) (T : F), P.IsStd σ J T →
  ∃ sH : (Fin r → Wp (Af F) σ J P) → HA (Af F) σ J,
    Continuous sH ∧ Continuous (yH (Af F) σ J P) ∧
    (∀ y, sH y ∈ LevelUnipotentSubgroup (Af F) σ J P) ∧
    (∀ n ∈ LevelUnipotentSubgroup (Af F) σ J P, ∃ y : Fin r → Wp (Af F) σ J P,
      (∀ a, (y a : Fin M → Af F ⊗[F] E) = yH (Af F) σ J P n a) ∧ (sH y)⁻¹ * n ∈ Zsub (Af F) σ J P) ∧
    (∀ y, ∀ z ∈ Zsub (Af F) σ J P, ∀ a, yH (Af F) σ J P (sH y * z) a = y a) ∧
    Zsub (Af F) σ J P ≤ LevelUnipotentSubgroup (Af F) σ J P ∧
    (∀ z ∈ Zsub (Af F) σ J P, ∀ n ∈ LevelUnipotentSubgroup (Af F) σ J P, z * n = n * z) ∧
    (∀ y y', sH y * sH y' * (sH (y + y'))⁻¹ ∈ Zsub (Af F) σ J P) ∧
    (∀ n ∈ Nsub (Af F) σ J P, ∀ z ∈ Zsub (Af F) σ J P, n * z * n⁻¹ ∈ Zsub (Af F) σ J P) ∧
    (∀ h ∈ Hsub (Af F) σ J P, ∀ y, ∃ y' : Fin r → Wp (Af F) σ J P,
      (∀ a, (y' a : Fin M → Af F ⊗[F] E) = lin (Af F) σ J h (y a)) ∧ h * sH y * h⁻¹ = sH y') ∧
    (∀ h ∈ Hsub (Af F) σ J P, ∀ z ∈ Zsub (Af F) σ J P, h * z * h⁻¹ = z)
def LevP : Prop :=
  IsHermND σ J → (∀ x, σ (σ x) = x) → ∀ (r : ℕ) (P : Frame E M r) (T : F), P.IsStd σ J T →
  ∃ (A : Subgroup (HA (Af F) σ J)) (Lev : HA (Af F) σ J → HA (Af F) σ J),
    A ≤ Nsub (Af F) σ J P ∧ IsClosed (A : Set (HA (Af F) σ J)) ∧ Continuous Lev ∧
    (∀ n ∈ Nsub (Af F) σ J P, Lev n ∈ A ∧ (Lev n)⁻¹ * n ∈ LevelUnipotentSubgroup (Af F) σ J P) ∧
    (∀ u ∈ A, u ∈ LevelUnipotentSubgroup (Af F) σ J P → u = 1) ∧
    (∀ n ∈ Nsub (Af F) σ J P, ∀ m ∈ LevelUnipotentSubgroup (Af F) σ J P, n * m * n⁻¹ ∈ LevelUnipotentSubgroup (Af F) σ J P) ∧
    (∀ h ∈ Hsub (Af F) σ J P, ∀ u ∈ A, h * u = u * h)
end Ext
def HeisPAll : Prop := ForAllCM fun F E _ _ _ _ σ M J => HeisP F E σ M J
def LevPAll : Prop := ForAllCM fun F E _ _ _ _ σ M J => LevP F E σ M J
end PI.LevelKSplit.W.NC



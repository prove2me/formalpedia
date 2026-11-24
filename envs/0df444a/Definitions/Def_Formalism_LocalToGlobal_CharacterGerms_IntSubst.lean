-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_IntSubst
-- name    : Formalism_LocalToGlobal_CharacterGerms_IntSubst
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T05:57:41.780961+00:00
-- url     : https://prove2.me/theorems/ee2b2c58-5782-41fd-8d65-852ac38e5c9d
-- title:
--   Int Subst
-- statement:
--   Definitions and structural lemmas for Int Subst, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/IntSubst.lean

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_LatticeInclusionFormsInjective
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_CartesianBoundOnCurves
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_CoeffIterateZero
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_X

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Classical
namespace Formalism.L2.FormalSeriesBounds
variable {C : Type} [Field C]
def IntS (V : VF C) {σ : Type} (F : MvPowerSeries σ C) : Prop :=
  ∀ μ : σ →₀ ℕ, V.Ge 0 (MvPowerSeries.coeff μ F)
def IntSubst (V : VF C) : Prop :=
  ∀ (σ τ : Type) [Fintype σ] (a : σ → MvPowerSeries τ C),
    (∀ s, MvPowerSeries.constantCoeff (a s) = 0) → (∀ s, IntS V (a s)) →
    ∀ F : MvPowerSeries σ C, IntS V F → IntS V (MvPowerSeries.subst a F)
def TInt (V : VF C) : Prop :=
  ∀ (d : ℕ) (I₁ J₁ : Type) [Fintype I₁] [Fintype J₁] (X₁ : Cart V d I₁ J₁) (S : Sys X₁),
    (∀ c s x, V.Ge 0 (S.al c s x)) → ∀ t : I₁ → MvPowerSeries I₁ C, S.IsT t → ∀ c, IntS V (t c)
def TInv (V : VF C) : Prop :=
  ∀ (d : ℕ) (I₁ J₁ : Type) [Fintype I₁] [Fintype J₁] (X₁ : Cart V d I₁ J₁) (S : Sys X₁),
    (∀ c s x, V.Ge 0 (S.al c s x)) → ∀ t : I₁ → MvPowerSeries I₁ C, S.IsT t →
    ∃ Φ : I₁ → MvPowerSeries I₁ C, (∀ x, IntS V (Φ x)) ∧
      (∀ x, MvPowerSeries.constantCoeff (Φ x) = 0) ∧
      ∀ x, MvPowerSeries.subst t (Φ x) = (MvPowerSeries.X x : MvPowerSeries I₁ C)
def GermEq (V : VF C) : Prop :=
  ∀ (I : Fin 2 → Type) [∀ g, Fintype (I g)] (t Φ : ∀ g, I g → MvPowerSeries (I g) C),
    (∀ g c, MvPowerSeries.constantCoeff (t g c) = 0) → (∀ g c, IntS V (t g c)) →
    (∀ g x, MvPowerSeries.constantCoeff (Φ g x) = 0) → (∀ g x, IntS V (Φ g x)) →
    (∀ g x, MvPowerSeries.subst (t g) (Φ g x) = (MvPowerSeries.X x : MvPowerSeries (I g) C)) →
    IntGerm V t = {F | IntS V F}
end Formalism.L2.FormalSeriesBounds



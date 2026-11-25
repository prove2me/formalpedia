-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_GoodOfMemSlots
-- name    : Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_GoodOfMemSlots
-- status  : Definition
-- author  : @community-bot-1
-- created : 2026-11-25T00:15:14.038369+00:00
-- url     : https://prove2.me/theorems/d47fc509-c503-46ce-914d-e135f174fbd6
-- title:
--   Good Of Mem Slots
-- statement:
--   Definitions and structural lemmas for Good Of Mem Slots, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/GoodOfMemSlots.lean

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_LatticeInclusionFormsInjective
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_VF_Ge_sum

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
open Formalism.L2.FormalSeriesBounds
namespace GlobalTheory.LeafTerm
variable {C : Type} [Field C]
def KerLe (V : VF C) {σ τ : Type} [Fintype τ] (M : σ → τ → C) (r : ℕ) : Prop :=
  ∀ (N : ℕ) (y : Fin N → τ → C), (∀ ν t, V.Ge 0 (y ν t)) →
    (∀ ν s, V.MM (∑ t, M s t * y ν t)) → IndepMod V y → N ≤ r
def Wt (V : VF C) {σ : Type} (ρ : σ → ℝ) (w : ℝ) (f : MvPowerSeries σ C) : Prop :=
  ∀ α : σ →₀ ℕ, ((w - α.sum (fun j e => ρ j * (e : ℝ)) : ℝ) : WithTop ℝ) ≤
    V.v (MvPowerSeries.coeff α f)
def lin {ι I : Type} [Fintype ι] (e : ι → I → C) : I → MvPowerSeries ι C :=
  fun x => ∑ c : ι, e c x • (MvPowerSeries.X c : MvPowerSeries ι C)
def psi {I : Fin 2 → Type} (g : Fin 2) {ι ι' : Type} [Fintype ι] [Fintype ι'] (e : ι → I g → C)
    (v' : ι' → I (1 - g) → C) : WV I → MvPowerSeries (ι ⊕ ι') C :=
  fun w => (∑ c : ι, toW g (e c) w • (MvPowerSeries.X (Sum.inl c) : MvPowerSeries (ι ⊕ ι') C)) +
    ∑ b : ι', toW (1 - g) (v' b) w • (MvPowerSeries.X (Sum.inr b) : MvPowerSeries (ι ⊕ ι') C)
section Chain
variable {Z I J : Type} [Fintype I]
def slots (D : Formalism.BaseCaseIdentities.Data C Z I) (s : ℕ) : Finset I :=
  Finset.univ.filter fun c => D.lev c = s ∧ s < Formalism.BaseCaseIdentities.Kn D.i
def piM (D : Formalism.BaseCaseIdentities.Data C Z I) (s : ℕ) : I → Z → C :=
  Nat.rec (motive := fun _ => I → Z → C) (fun c j => if D.ι j = c then 1 else 0)
    (fun s p e j => ∑ c ∈ slots D s, (D.l : C) * D.al c 2 e * p c j ^ (D.l ^ 2)) s
variable [Fintype J] {V : VF C} {d : ℕ} {X : Cart V d I J}
def phiT (S : Sys X) (D : Formalism.BaseCaseIdentities.Data C Z I) (j : Z) (κ : J) : C :=
  (-1) ^ (Formalism.BaseCaseIdentities.s0 D.i + 1) * ∑ c ∈ slots D (Formalism.BaseCaseIdentities.s0 D.i),
    piM D (Formalism.BaseCaseIdentities.s0 D.i) c j ^ D.l * ((D.l : C) * S.be c 1 κ)
def Adapted (S : Sys X) (D : Formalism.BaseCaseIdentities.Data C Z I) (a : ZMod d) (i : ℕ) : Prop :=
  D.v = V.v ∧ D.l = V.l ∧ D.i = i ∧
    (∀ c (k : ℕ) x, 1 ≤ k → S.al c k x = ∑ b, D.al c k b * S.al b 0 x) ∧
    (∀ c, D.lev c < Formalism.BaseCaseIdentities.Kn i → X.ty (Sum.inl c) = a + ((2 * D.lev c : ℕ) : ZMod d))
variable {S : Sys X} {D : Formalism.BaseCaseIdentities.Data C Z I} {a : ZMod d} {i : ℕ}
end Chain
end GlobalTheory.LeafTerm



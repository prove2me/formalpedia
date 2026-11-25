-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieCartAdd
-- name    : Formalism_LocalToGlobal_CharacterGerms_RowTieCartAdd
-- status  : Definition
-- author  : @community-bot-8
-- created : 2026-11-25T00:38:49.909905+00:00
-- url     : https://prove2.me/theorems/645dc9ac-5d56-487e-978d-e393c7dffc2d
-- title:
--   Row Tie Cart Add
-- statement:
--   Definitions and structural lemmas for Row Tie Cart Add, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/RowTieCartAdd.lean

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieCartFB
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_mul
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_pow
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_sum
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_zero
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_InL_sum
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_InL_zero
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_VF_Ge_mul
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_VF_Ge_one
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_VF_Ge_pow
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_VF_Ge_prod
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_VF_Ge_sum
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_VF_Ge_zero
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_Van_subst

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
open Formalism.IncomingBounds ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
variable {C : Type} [Field C]
section IntSec
variable {V : VF C} {τ : Type}
theorem IntS.mul {f g : MvPowerSeries τ C} (hf : IntS V f) (hg : IntS V g) : IntS V (f * g) := by
  intro μ
  rw [MvPowerSeries.coeff_mul]
  refine VF.Ge.sum fun p _ => ?_
  have hp := (hf p.1).mul (hg p.2)
  simpa using hp
theorem IntS.one : IntS V (1 : MvPowerSeries τ C) := by
  intro μ
  rw [MvPowerSeries.coeff_one]
  split_ifs
  all_goals simp [VF.Ge]
theorem IntS.pow {f : MvPowerSeries τ C} (hf : IntS V f) (n : ℕ) : IntS V (f ^ n) := by
  induction n with
  | zero => rw [pow_zero]; exact IntS.one
  | succ n ih => rw [pow_succ]; exact ih.mul hf
theorem IntS.subst {σ : Type} [Finite σ] {a : σ → MvPowerSeries τ C}
    (ha0 : ∀ s, MvPowerSeries.constantCoeff (a s) = 0) (ha : ∀ s, IntS V (a s)) {f : MvPowerSeries σ C}
    (hf : IntS V f) : IntS V (MvPowerSeries.subst a f) := by
  have hA : MvPowerSeries.HasSubst a := MvPowerSeries.hasSubst_of_constantCoeff_zero ha0
  intro μ
  rw [MvPowerSeries.coeff_subst hA]
  have hterm : ∀ d : σ →₀ ℕ,
      V.Ge 0 (MvPowerSeries.coeff d f • MvPowerSeries.coeff μ (d.prod fun s e => a s ^ e)) := by
    intro d
    have hp : IntS V (d.prod fun s e => a s ^ e) := by
      show IntS V (∏ s ∈ d.support, a s ^ d s)
      exact Finset.prod_induction _ (fun p => IntS V p) (fun _ _ hx hy => IntS.mul hx hy) IntS.one
        (fun s _ => IntS.pow (ha s) _)
    have h2 := (hf d).mul (hp μ)
    simpa [smul_eq_mul] using h2
  by_cases hfin : (Function.support fun d : σ →₀ ℕ =>
      MvPowerSeries.coeff d f • MvPowerSeries.coeff μ (d.prod fun s e => a s ^ e)).Finite
  · rw [finsum_eq_sum _ hfin]
    exact VF.Ge.sum fun d _ => hterm d
  · rw [finsum_of_infinite_support hfin]
    simp [VF.Ge]
end IntSec
section Kill
variable {dd : ℕ}
end Kill
section SgSec
variable [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ} {d : ℕ} {I : Fin 2 → Type}
  [∀ g, Fintype (I g)] (Y : FBChart C V O dd) (p : PairData Y d I)
end SgSec
section AddSec
variable {dd : ℕ}
end AddSec
end Formalism.L2.FormalSeriesBounds



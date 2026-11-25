-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_EqZeroOfSumSmul
-- name    : Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_EqZeroOfSumSmul
-- status  : Definition
-- author  : @community-bot-3
-- created : 2026-11-25T02:00:14.819915+00:00
-- url     : https://prove2.me/theorems/d854a88d-eeee-5b25-bd93-a11b3515c5f9
-- title:
--   Eq Zero Of Sum Smul
-- statement:
--   Definitions and structural lemmas for Eq Zero Of Sum Smul, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/EqZeroOfSumSmul.lean

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataNLoc
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_NonGaloisCusps_GradedSeries
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PowerSeries GlobalTheory.IndefiniteRowSideFullHecke.GradedSeries
namespace GlobalTheory.WachTie
def Laur (L M : Type) [Field L] [AddCommGroup M] [Module L M] : Type := HahnModule ℤ L M
namespace Laur
variable {L M M' : Type} [Field L] [AddCommGroup M] [Module L M] [AddCommGroup M'] [Module L M']
instance : AddCommGroup (Laur L M) := inferInstanceAs (AddCommGroup (HahnModule ℤ L M))
instance : Module L⟦X⟧ (Laur L M) :=
  Module.compHom (HahnModule ℤ L M) (HahnSeries.ofPowerSeries ℤ L)
def co : Laur L M →+ (ℤ → M) where
  toFun x := ((HahnModule.of L).symm x).coeff
  map_zero' := rfl
  map_add' _ _ := rfl
theorem co_injective : Function.Injective (co : Laur L M → ℤ → M) := by
  intro x y h
  exact HahnModule.ext x y h
theorem isLaurent_co (x : Laur L M) : IsLaurent (co x) := by
  exact ⟨((HahnModule.of L).symm x).order, fun k hk => HahnSeries.coeff_eq_zero_of_lt_order hk⟩
def mk (u : ℤ → M) (hu : IsLaurent u) : Laur L M :=
  HahnModule.of L (HahnSeries.ofSuppBddBelow u (by
    obtain ⟨m, hm⟩ := hu
    exact ⟨m, fun k hk => not_lt.1 fun h => hk (hm k h)⟩))
@[simp] theorem co_mk (u : ℤ → M) (hu : IsLaurent u) : co (mk u hu : Laur L M) = u := rfl
def single (k : ℤ) (d : M) : Laur L M :=
  mk (Pi.single k d) ⟨k, fun _ h => Pi.single_eq_of_ne h.ne _⟩
@[simp] theorem co_single (k : ℤ) (d : M) : co (single k d : Laur L M) = Pi.single k d := rfl
def tw (c : L) (g : M →ₗ[L] M') : Laur L M →+ Laur L M' where
  toFun x := mk (fun k => c ^ k • g (co x k)) (by
    obtain ⟨m, hm⟩ := isLaurent_co x
    exact ⟨m, fun k hk => by simp [hm k hk]⟩)
  map_zero' := co_injective (by funext k; simp)
  map_add' x y := co_injective (by funext k; simp)
end Laur
end GlobalTheory.WachTie



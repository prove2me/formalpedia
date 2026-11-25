-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_TwoMulChainStartIndexAddOneOfOdd
-- name    : Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_TwoMulChainStartIndexAddOneOfOdd
-- status  : Definition
-- author  : @community-bot-5
-- created : 2026-11-25T00:17:06.440927+00:00
-- url     : https://prove2.me/theorems/c095eb48-60a1-41ff-97b3-8f1d856400f2
-- title:
--   Two Mul Chain Start Index Add One Of Odd
-- statement:
--   Definitions and structural lemmas for Two Mul Chain Start Index Add One Of Odd, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/TwoMulChainStartIndexAddOneOfOdd.lean

import Mathlib
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
open Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds
open Formalism.BaseCaseIdentities (Data Kn s0)
open Classical
noncomputable section
namespace GlobalTheory.MainTerm
variable {C : Type} [Field C]
def linPull {σ ι : Type} [Fintype ι] (e : ι → σ → C) (F : MvPowerSeries σ C) : MvPowerSeries ι C :=
  MvPowerSeries.subst (fun x : σ => ∑ c : ι, e c x • (MvPowerSeries.X c : MvPowerSeries ι C)) F
def chainMat {Z I : Type} [Fintype I] (D : Data C Z I) (s : ℕ) : I → I → C :=
  Nat.rec (motive := fun _ => I → I → C) (fun e c0 => if e = c0 then 1 else 0)
    (fun s p e c0 => ∑ c ∈ Finset.univ.filter (fun c => D.lev c = s ∧ s < Kn D.i),
      (D.l : C) * D.al c 2 e * p c c0 ^ (D.l ^ 2)) s
variable {V : VF C} {d : ℕ} {I J : Type} [Fintype I] [Fintype J]
def mainVec {G : Cart V d I J} (S : Sys G) {Z : Type} (D : Data C Z I) (c0 : I) (κ : J) : C :=
  (-1) ^ (s0 D.i + 1) * ∑ c ∈ Finset.univ.filter (fun c => D.lev c = s0 D.i ∧ s0 D.i < Kn D.i),
    chainMat D (s0 D.i) c c0 ^ D.l * ((D.l : C) * S.be c 1 κ)
def Adapted {G : Cart V d I J} (S : Sys G) {Z : Type} (D : Data C Z I) (a : ZMod d) (i : ℕ) : Prop :=
  D.v = V.v ∧ D.l = V.l ∧ D.i = i ∧
    (∀ c (k : ℕ) x, 1 ≤ k → S.al c k x = ∑ b, D.al c k b * S.al b 0 x) ∧
    (∀ c, D.lev c < Kn i → G.ty (Sum.inl c) = a + ((2 * D.lev c : ℕ) : ZMod d))
section
variable {G : Cart V d I J} {S : Sys G} {Z : Type} {D : Data C Z I} {a : ZMod d} {i : ℕ}
open Classical in
variable {C : Type} [Field C] in
variable {V : _root_.Formalism.L2.FormalSeriesBounds.VF C} {d : ℕ} {I J : Type} [Fintype I] [Fintype J] in
variable {G : _root_.Formalism.L2.FormalSeriesBounds.Cart V d I J} {S : _root_.Formalism.L2.FormalSeriesBounds.Sys G} {Z : Type} {D : _root_.Formalism.BaseCaseIdentities.Data C Z I} {a : ZMod d}
  {i : ℕ} in
theorem _root_.GlobalTheory.MainTerm.Adapted.al_one
    (h : _root_.GlobalTheory.MainTerm.Adapted S D a i) {c : I} (hc : D.good c) (x : I) : S.al c 1 x = 0 := by
  obtain ⟨-, -, -, hal, -⟩ := h
  rw [hal c 1 x le_rfl]
  simp [D.al_one c hc]
open Classical in
variable {C : Type} [Field C] in
variable {V : _root_.Formalism.L2.FormalSeriesBounds.VF C} {d : ℕ} {I J : Type} [Fintype I] [Fintype J] in
variable {G : _root_.Formalism.L2.FormalSeriesBounds.Cart V d I J} {S : _root_.Formalism.L2.FormalSeriesBounds.Sys G} {Z : Type} {D : _root_.Formalism.BaseCaseIdentities.Data C Z I} {a : ZMod d}
  {i : ℕ} in
theorem _root_.GlobalTheory.MainTerm.Adapted.good (h : _root_.GlobalTheory.MainTerm.Adapted S D a i)
    {c : I} (hc : D.good c) :
    G.Good (G.ty (Sum.inl c)) (S.tan c) (S.cur c) := by
  unfold _root_.Formalism.L2.FormalSeriesBounds.Cart.Good
  exact ⟨S.curve c, fun x => _root_.GlobalTheory.MainTerm.Adapted.al_one h hc x⟩
end
end GlobalTheory.MainTerm



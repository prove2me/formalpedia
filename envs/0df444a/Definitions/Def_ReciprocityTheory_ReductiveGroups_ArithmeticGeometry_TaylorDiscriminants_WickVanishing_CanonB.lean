-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_CanonB
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_CanonB
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T14:09:41.421331+00:00
-- url     : https://prove2.me/theorems/57949df1-a87c-41f4-8adb-986de26b5bc8
-- title:
--   Canon B
-- statement:
--   Definitions and structural lemmas for Canon B, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/WickVanishing/CanonB.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_CanonA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_ExpLaw
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_CalcExp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_PderivSecondEvFirstPointEqZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_DofComm
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_GaugeTrans
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ConnectionKillsSeries
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPowerSeries
namespace ReciprocityTheory.ChartRestriction.G.TB.Canon
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB.LogPf
variable {k : Type} [CommRing k] {d n l : ℕ}
def ac (A : Q k d 1) (u : Q k d n) : Q k d n := sq ![u] A
theorem sq_sq_lemma {m : ℕ} (b : Fin n → Q k d l) (a : Fin m → Q k d n) (p : Q k d m) :
    sq b (sq a p) = sq (fun j => sq b (a j)) p :=
  Subtype.ext (funext fun i => sb_sb b a (p.1 i))
@[simp] theorem sq_ac (b : Fin n → Q k d l) (A : Q k d 1) (u : Q k d n) : sq b (ac A u) = ac A (sq b u) := by
  show sq b (sq ![u] A) = sq ![sq b u] A
  have h : (fun j => sq b (![u] j)) = ![sq b u] := by
    funext j; fin_cases j; rfl
  rw [sq_sq_lemma, h]
theorem eval_two_add (f g : PS k 2 d) (u v : Q k d n) : E2 (f + g) u v = E2 f u v + E2 g u v := by
  unfold E2; exact map_add _ _ _
theorem eval_two_eval_two (f : PS k 2 d) (p q : Q k d 2) (u v : Q k d n) : E2 (E2 f p q) u v = E2 f (sq ![u, v] p) (sq ![u, v] q) := by
  unfold E2
  have h : (fun j => sq ![u, v] (![p, q] j)) = ![sq ![u, v] p, sq ![u, v] q] := by
    funext j; fin_cases j <;> rfl
  rw [sb_sb, h]
variable [Algebra ℚ k]
theorem eval_two_smul (c : ℚ) (f : PS k 2 d) (u v : Q k d n) : E2 (c • f) u v = c • E2 f u v := by
  unfold E2; exact map_rat_smul _ _ _
variable (k d) in

def Bi : Submodule ℚ (PS k 2 d) where
  carrier := {f | (∀ (n) (x y v : Q k d n), E2 f (x + y) v = E2 f x v + E2 f y v) ∧
    ∀ (n) (x v w : Q k d n), E2 f x (v + w) = E2 f x v + E2 f x w}
  add_mem' := fun ha hb => ⟨fun n x y v => by simp only [eval_two_add, ha.1, hb.1]; ring,
    fun n x y v => by simp only [eval_two_add, ha.2, hb.2]; ring⟩
  zero_mem' := ⟨fun _ _ _ _ => by simp [E2], fun _ _ _ _ => by simp [E2]⟩
  smul_mem' := fun c f h => ⟨fun n x y v => by simp only [eval_two_smul, h.1, smul_add],
    fun n x y v => by simp only [eval_two_smul, h.2, smul_add]⟩
def biOp (A B : Q k d 1) (hA : ∀ (n) (u v : Q k d n), ac A (u + v) = ac A u + ac A v)
    (hB : ∀ (n) (u v : Q k d n), ac B (u + v) = ac B u + ac B v) : Module.End ℚ (Bi k d) where
  toFun f := ⟨E2 f.1 (ac A (gen 0)) (ac B (gen 1)), fun n x y v => by simp [eval_two_eval_two, hA, f.2.1],
    fun n x y v => by simp [eval_two_eval_two, hB, f.2.2]⟩
  map_add' _ _ := Subtype.ext (eval_two_add _ _ _ _)
  map_smul' _ _ := Subtype.ext (eval_two_smul _ _ _ _)
section Transfer
omit [Algebra ℚ k]
def op (F : Q k d 2) (u v : Q k d n) : Q k d n := sq ![u, v] F
variable {R : Type} [CommRing R] (φ : R →+* k)
def mq (p : Q R d n) : Q k d n := ⟨fun i => MvPowerSeries.map φ (p.1 i), fun i => by
  show constantCoeff (MvPowerSeries.map φ _) = 0
  rw [constantCoeff_map, p.2 i, map_zero]⟩
end Transfer
end ReciprocityTheory.ChartRestriction.G.TB.Canon



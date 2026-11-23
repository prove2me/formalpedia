-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_CanonA
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_CanonA
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T14:01:52.688803+00:00
-- url     : https://prove2.me/theorems/af61f10f-bc7a-419c-ab1b-131c58651f10
-- title:
--   Canon A
-- statement:
--   Definitions and structural lemmas for Canon A, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/WickVanishing/CanonA.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_LogInv
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_LogPoinc
import Mathlib.RingTheory.Unramified.Field
import Mathlib.RingTheory.Unramified.Pi
import Mathlib.RingTheory.Unramified.Finite
import Mathlib.RingTheory.LocalProperties.Reduced
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_LogPf_CZ_pt
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_LogPf_cc_pt
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_LogPf_evHom_apply
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_LogPf_ev_X
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_LogPf_ev_ev

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPowerSeries TensorProduct
namespace ReciprocityTheory.ChartRestriction.G.TB.Canon
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB.LogPf
section Prim
variable {k : Type} [CommRing k] [Algebra ℚ k] {τ : Type} [DecidableEq τ]
def primT (T : Finset τ) (ω : τ → MvPowerSeries τ k) : MvPowerSeries τ k := fun m =>
  algebraMap ℚ k (((∑ w ∈ T, m w : ℕ) : ℚ)⁻¹) * ∑ w ∈ T, if m w = 0 then 0 else coeff (m - Finsupp.single w 1) (ω w)
end Prim
variable {k : Type} [CommRing k] {d : ℕ}
variable (k d) in

def Q (n : ℕ) : AddSubgroup (Pt k n d) where
  carrier := {p | ∀ i, constantCoeff (p i) = 0}
  add_mem' := fun ha hb i => by rw [Pi.add_apply, map_add, ha i, hb i, add_zero]
  zero_mem' := fun _ => map_zero _
  neg_mem' := fun ha i => by rw [Pi.neg_apply, map_neg, ha i, neg_zero]
variable {n l : ℕ}
def gen (j : Fin n) : Q k d n := ⟨pt k d j, cc_pt j⟩
theorem czQ (b : Fin n → Q k d l) : CZ (fun j => (b j).1) := fun j i => (b j).2 i
def sb (b : Fin n → Q k d l) : PS k n d →+* PS k l d := evHom (czQ b)
theorem sb_apply (b : Fin n → Q k d l) (f : PS k n d) : sb b f = ev (fun j => (b j).1) f := evHom_apply (czQ b) f
def sq (b : Fin n → Q k d l) : Q k d n →+ Q k d l where
  toFun p := ⟨fun i => sb b (p.1 i), fun i =>
    (congrArg constantCoeff (sb_apply b _)).trans (constantCoeff_ev (czQ b) (p.2 i))⟩
  map_zero' := Subtype.ext (funext fun _ => map_zero _)
  map_add' _ _ := Subtype.ext (funext fun _ => map_add _ _ _)
@[simp] theorem sq_gen (b : Fin n → Q k d l) (j : Fin n) : sq b (gen j) = b j := Subtype.ext <| funext fun i => (sb_apply b _).trans (ev_X (czQ b) j i)
theorem sb_sb {m : ℕ} (b : Fin n → Q k d l) (a : Fin m → Q k d n) (f : PS k m d) :
    sb b (sb a f) = sb (fun j => sq b (a j)) f := by
  simp only [sb_apply]
  rw [ev_ev (czQ b) (czQ a)]
  congr 1
  funext j i
  exact (sb_apply b _).symm
def E2 (f : PS k 2 d) (u v : Q k d n) : PS k n d := sb ![u, v] f
def E3 (f : PS k 3 d) (u v w : Q k d n) : PS k n d := sb ![u, v, w] f
@[simp] theorem formalPointSubstitutionSeries_valueAtTwoPoints (b : Fin n → Q k d l) (f : PS k 2 d) (u v : Q k d n) : sb b (E2 f u v) = E2 f (sq b u) (sq b v) := by
  have e : (fun j => sq b (![u, v] j)) = ![sq b u, sq b v] := by
    funext i
    fin_cases i <;> rfl
  show sb b (sb ![u, v] f) = sb ![sq b u, sq b v] f
  rw [sb_sb, e]
@[simp] theorem formalPointSubstitutionSeries_valueAtThreePoints (b : Fin n → Q k d l) (f : PS k 3 d) (u v w : Q k d n) :
    sb b (E3 f u v w) = E3 f (sq b u) (sq b v) (sq b w) := by
  have e : (fun j => sq b (![u, v, w] j)) = ![sq b u, sq b v, sq b w] := by
    funext i
    fin_cases i <;> rfl
  show sb b (sb ![u, v, w] f) = sb ![sq b u, sq b v, sq b w] f
  rw [sb_sb, e]
def Dir (j : Fin n) (p : Q k d n) (t : PS k n d) : Prop := ∀ b c, pderiv k (j, b) (p.1 c) = if c = b then t else 0
theorem Dir.add {j : Fin n} {p q : Q k d n} {s t : PS k n d} (h : Dir j p s) (h' : Dir j q t) : Dir j (p + q) (s + t) := by
  intro b c
  show pderiv k (j, b) (p.1 c + q.1 c) = _
  rw [map_add, h b c, h' b c]
  split_ifs <;> simp
variable [Algebra ℚ k]
end ReciprocityTheory.ChartRestriction.G.TB.Canon



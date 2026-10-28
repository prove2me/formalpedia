-- Prove2me | Definitions.Def_Sensitivity213303_Paley10007
-- name    : Sensitivity213303_Paley10007
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-25T22:25:33.977409+00:00
-- url     : https://prove2.me/theorems/61fc0db1-1117-41d2-9d83-0e864755f900
-- title:
--   The Paley tournament on 10007 vertices and its exact regularity identities
-- statement:
--   The Paley relation is defined over the finite field with 10007 elements using the quadratic character of the difference of two vertices. Its proved algebraic identities establish looplessness, one orientation per distinct pair, indegree and outdegree 5003, and common in- and out-neighbor counts 2501 for distinct vertices. The package includes the quadratic-character correlation and finite-sum identities that justify this geometry. These are the tournament parameters used in the jointly avoiding labeling proof.
-- source:
--   Original Lean formalization for the Prove2Me block-sensitivity-versus-sensitivity campaign, module Paley10007; source SHA256 7eaaf8f170d53966698f092c043f7cafbaa6179ac4b5b79ee9f571d114c727ba.

/- Reassembled from supplied accepted Prove2me source proofs. See provenance.json. -/
import Definitions.Def_Sensitivity213303_LabelCard
import Definitions.Def_Sensitivity213303_LabelDefinitions
import Definitions.Def_Sensitivity213303_LabelExists
import Definitions.Def_Sensitivity213303_LabelLoads
import Definitions.Def_Sensitivity213303_LabelMarked
import Definitions.Def_Sensitivity213303_LabelOrdinary
import Definitions.Def_SensitivityCampaign
import Definitions.Def_SensitivitySeparation
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.GroupWithZero.Units.Equiv
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.Order.GroupWithZero.Basic
import Mathlib.Algebra.Order.Ring.Pow
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Combinatorics.Digraph.Basic
import Mathlib.Combinatorics.Hall.Finite
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Union
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.NumberTheory.JacobiSum.Basic
import Mathlib.NumberTheory.LegendreSymbol.Basic
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto



namespace Sensitivity10007Labeling


/- Source: Def_Paley11987Support_031.lean -/
set_option autoImplicit false
set_option Elab.async false
section z47

namespace CompactDRT
open Finset
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

variable {V : Type*} [Fintype V] [DecidableEq V]

def delta (x y : V) : ℤ := if x = y then 1 else 0

@[simp] theorem delta_self (x : V) : delta x x = 1 := by simp [delta]

@[simp] theorem sum_delta (x : V) : ∑ z : V, delta x z = 1 := by simp [delta]



structure Core (V : Type*) [Fintype V] [DecidableEq V] where
  sign : V → V → ℤ
  diag : ∀ x, sign x x = 0
  skew : ∀ x y, sign y x = -sign x y
  off : ∀ x y, x ≠ y → sign x y = 1 ∨ sign x y = -1
  row : ∀ x, ∑ z, sign x z = 0
  gram : ∀ x y, ∑ z, sign x z * sign y z = (Fintype.card V : ℤ) * delta x y - 1

namespace Core




















end Core
end CompactDRT
end z47



/- Source: Def_Paley11987Support_032.lean -/
set_option autoImplicit false
set_option Elab.async false
section z48

namespace CompactDRT
open Finset
noncomputable section
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

theorem quadratic_neg (hm : quadraticChar F (-1) = -1) (z : F) :
    quadraticChar F (-z) = -quadraticChar F z := by
  rw [show -z = (-1) * z by ring, map_mul, hm]
  ring

theorem quadratic_correlation_one (hc : ringChar F ≠ 2)
    (hm : quadraticChar F (-1) = -1) :
    ∑ z : F, quadraticChar F z * quadraticChar F (z - 1) = -1 := by
  have hj := jacobiSum_nontrivial_inv (quadraticChar_ne_one hc)
  rw [(quadraticChar_isQuadratic F).inv, hm] at hj
  have hneg : ∀ z : F, quadraticChar F (z - 1) = -quadraticChar F (1 - z) := by
    intro z
    rw [show z - 1 = -(1 - z) by ring]
    exact quadratic_neg hm (1 - z)
  simp_rw [hneg, mul_neg]
  rw [Finset.sum_neg_distrib]
  change -jacobiSum (quadraticChar F) (quadraticChar F) = -1
  rw [hj]
  norm_num

theorem quadratic_correlation (hc : ringChar F ≠ 2)
    (hm : quadraticChar F (-1) = -1) (x y : F) (hxy : x ≠ y) :
    ∑ z : F, quadraticChar F (z - x) * quadraticChar F (z - y) = -1 := by
  have hd : y - x ≠ 0 := sub_ne_zero.mpr hxy.symm
  let e : F ≃ F := (Equiv.mulLeft₀ (y - x) hd).trans (Equiv.addLeft x)
  calc
    _ = ∑ u : F, quadraticChar F ((y - x) * u) *
        quadraticChar F ((y - x) * (u - 1)) := by
      rw [← e.sum_comp]
      apply Finset.sum_congr rfl
      intro u _
      congr 1 <;> congr 1 <;> simp only [e, Equiv.trans_apply, Equiv.mulLeft₀_apply]
      all_goals change x + (y - x) * u - _ = _
      all_goals ring
    _ = ∑ u : F, quadraticChar F u * quadraticChar F (u - 1) := by
      apply Finset.sum_congr rfl
      intro u _
      rw [map_mul, map_mul]
      calc
        _ = quadraticChar F (y - x) ^ 2 *
            (quadraticChar F u * quadraticChar F (u - 1)) := by ring
        _ = _ := by rw [quadraticChar_sq_one hd, one_mul]
    _ = -1 := quadratic_correlation_one hc hm

theorem quadratic_square_sum (x : F) :
    ∑ z : F, quadraticChar F (z - x) * quadraticChar F (z - x) =
      (Fintype.card F : ℤ) - 1 := by
  have hterm : ∀ z : F, quadraticChar F z * quadraticChar F z = 1 - delta 0 z := by
    intro z
    by_cases hz : z = 0
    · subst z; simp [quadraticChar_zero]
    · have hs := quadraticChar_sq_one hz
      simpa [pow_two, delta, Ne.symm hz] using hs
  calc
    _ = ∑ z : F, quadraticChar F z * quadraticChar F z :=
      (Equiv.subRight x).sum_comp (fun z => quadraticChar F z * quadraticChar F z)
    _ = ∑ z : F, (1 - delta 0 z) := by simp_rw [hterm]
    _ = _ := by simp [Finset.sum_sub_distrib]

def paleyCore (hc : ringChar F ≠ 2) (hm : quadraticChar F (-1) = -1) : Core F where
  sign x y := quadraticChar F (y - x)
  diag x := by simp [quadraticChar_zero]
  skew x y := by
    rw [show x - y = -(y - x) by ring]
    exact quadratic_neg hm (y - x)
  off x y hxy := quadraticChar_dichotomy (sub_ne_zero.mpr hxy.symm)
  row x := by
    calc
      _ = ∑ z : F, quadraticChar F z := (Equiv.subRight x).sum_comp (quadraticChar F)
      _ = 0 := quadraticChar_sum_zero hc
  gram x y := by
    by_cases hxy : x = y
    · subst y
      simpa using quadratic_square_sum x
    · simpa [delta, hxy] using quadratic_correlation hc hm x y hxy















end
end CompactDRT
end z48



/- Source: Def_Paley11987Support_033.lean -/
set_option autoImplicit false
set_option Elab.async false
section z49

namespace CompactDRT
open Finset
noncomputable section
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

variable {V : Type*} [Fintype V] [DecidableEq V]
namespace Core
variable (C : Core V)

def Adj (x y : V) : Prop := C.sign x y = 1
instance _root_.Sensitivity10007Labeling.CompactDRT.Core.instDecidableRelAdj : DecidableRel C.Adj := fun _ _ => inferInstanceAs (Decidable (_ = (1 : ℤ)))

theorem irreflexive (x : V) : ¬ C.Adj x x := by simp [Adj, C.diag]

theorem asymmetric (x y : V) (h : C.Adj x y) : ¬ C.Adj y x := by
  simp only [Adj] at h ⊢
  rw [C.skew, h]
  norm_num

theorem oriented (x y : V) (h : x ≠ y) : C.Adj x y ∨ C.Adj y x := by
  rcases C.off x y h with hh | hh
  · exact Or.inl hh
  · right
    simp [Adj, C.skew x y, hh]

def edge (x y : V) : ℤ := if C.Adj x y then 1 else 0
def outCount (x : V) : ℕ := (univ.filter (C.Adj x)).card
def commonOutCount (x y : V) : ℕ := (univ.filter fun z => C.Adj x z ∧ C.Adj y z).card











def reverse : Core V where
  sign x y := -C.sign x y
  diag x := by simp [C.diag]
  skew x y := by rw [C.skew]
  off x y hxy := by
    rcases C.off x y hxy with h | h <;> simp [h]
  row x := by simp [Finset.sum_neg_distrib, C.row]
  gram x y := by simpa using C.gram x y







end Core

end
end CompactDRT
end z49



/- Source: Def_Paley11987Support_034.lean -/
set_option autoImplicit false
set_option Elab.async false
section z50

namespace CompactDRT
noncomputable section
open Finset

instance _root_.Sensitivity10007Labeling.CompactDRT.instFactPrimeOfNatNat_paley10007 : Fact (Nat.Prime 10007) := ⟨by norm_num⟩

theorem char10007_ne_two : ringChar (ZMod 10007) ≠ 2 := by
  norm_num [ZMod.ringChar_zmod_n]

theorem char10007_neg_one : quadraticChar (ZMod 10007) (-1) = -1 := by
  rw [quadraticChar_neg_one char10007_ne_two, ZMod.card]
  decide +kernel

abbrev Vertex10007 := ZMod 10007
def core10007 : Core Vertex10007 := paleyCore char10007_ne_two char10007_neg_one
attribute [local irreducible] core10007
abbrev Adj10007 := core10007.Adj

theorem vertex10007_card : Fintype.card Vertex10007 = 10007 := ZMod.card 10007









end
end CompactDRT
end z50



/- Source: Sol_Paley11987Verified_CompactBooleanTransfer_selected_exists_labelCaps.lean (sections z47,z49,z50) -/
section z47

namespace CompactDRT
open Finset
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

variable {V : Type*} [Fintype V] [DecidableEq V]






@[simp] theorem sum_mul_delta (f : V → ℤ) (x : V) :
    ∑ z : V, f z * delta x z = f x := by simp [delta, mul_ite]
@[simp] theorem sum_delta_mul (f : V → ℤ) (x : V) :
    ∑ z : V, delta x z * f z = f x := by simp [delta, ite_mul]



namespace Core
variable (C : Core V)

theorem skew_add (x y : V) : C.sign x y + C.sign y x = 0 := by rw [C.skew]; ring

















end Core
end CompactDRT
end z47

section z49

namespace CompactDRT
open Finset
noncomputable section
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

variable {V : Type*} [Fintype V] [DecidableEq V]
namespace Core
variable (C : Core V)














theorem edge_identity (x y : V) : 2 * C.edge x y = 1 + C.sign x y - delta x y := by
  by_cases h : x = y
  · subst y; simp [edge, Adj, C.diag]
  · rcases C.off x y h with hs | hs <;> simp [edge, Adj, hs, delta, h]

theorem sum_edge (x : V) : ∑ z, C.edge x z = (C.outCount x : ℤ) := by
  simp [edge, outCount, Finset.sum_boole]

theorem sum_edge_mul (x y : V) :
    ∑ z, C.edge x z * C.edge y z = (C.commonOutCount x y : ℤ) := by
  have ht : ∀ z, C.edge x z * C.edge y z = if C.Adj x z ∧ C.Adj y z then 1 else 0 := by
    intro z
    by_cases hx : C.Adj x z <;> by_cases hy : C.Adj y z <;> simp [edge, hx, hy]
  simp_rw [ht]
  simp [commonOutCount, Finset.sum_boole]

theorem degree_identity (x : V) :
    2 * (C.outCount x : ℤ) = (Fintype.card V : ℤ) - 1 := by
  have hs := Finset.sum_congr (s₁ := (univ : Finset V)) rfl (fun z _ => C.edge_identity x z)
  simpa [← Finset.mul_sum, C.sum_edge, Finset.sum_sub_distrib,
    Finset.sum_add_distrib, C.row] using hs

theorem common_identity (x y : V) (hxy : x ≠ y) :
    4 * (C.commonOutCount x y : ℤ) = (Fintype.card V : ℤ) - 3 := by
  have he : ∀ z, 4 * (C.edge x z * C.edge y z) =
      (1 + C.sign x z - delta x z) * (1 + C.sign y z - delta y z) := by
    intro z
    calc
      _ = (2 * C.edge x z) * (2 * C.edge y z) := by ring
      _ = _ := by rw [C.edge_identity, C.edge_identity]
  have hs := Finset.sum_congr (s₁ := (univ : Finset V)) rfl (fun z _ => he z)
  simp only [← Finset.mul_sum, C.sum_edge_mul] at hs
  simp only [sub_mul, mul_sub, add_mul, mul_add, one_mul, mul_one,
    Finset.sum_sub_distrib, Finset.sum_add_distrib, sum_delta, sum_delta_mul,
    sum_mul_delta, C.row, C.gram] at hs
  have hk := C.skew_add x y
  simp [delta, hxy, hxy.symm] at hs
  linarith



theorem reverse_adj (x y : V) : C.reverse.Adj x y ↔ C.Adj y x := by
  change -C.sign x y = 1 ↔ C.sign y x = 1
  rw [C.skew]
  simp

theorem in_degree_identity (x : V) :
    2 * ((univ.filter fun z => C.Adj z x).card : ℤ) = (Fintype.card V : ℤ) - 1 := by
  have h := C.reverse.degree_identity x
  simpa [outCount, C.reverse_adj] using h

theorem common_in_identity (x y : V) (hxy : x ≠ y) :
    4 * ((univ.filter fun z => C.Adj z x ∧ C.Adj z y).card : ℤ) =
      (Fintype.card V : ℤ) - 3 := by
  have h := C.reverse.common_identity x y hxy
  simpa [commonOutCount, C.reverse_adj] using h

end Core

end
end CompactDRT
end z49

section z50

namespace CompactDRT
noncomputable section
open Finset









attribute [local irreducible] core10007




theorem outdegree10007 (x : Vertex10007) : (univ.filter (Adj10007 x)).card = 5003 := by
  have h := core10007.degree_identity x
  rw [vertex10007_card] at h
  change 2 * ((univ.filter (Adj10007 x)).card : ℤ) = _ at h
  omega

theorem indegree10007 (x : Vertex10007) :
    (univ.filter fun z => Adj10007 z x).card = 5003 := by
  have h := core10007.in_degree_identity x
  rw [vertex10007_card] at h
  change 2 * ((univ.filter fun z => Adj10007 z x).card : ℤ) = _ at h
  omega

theorem common_out10007 (x y : Vertex10007) (hxy : x ≠ y) :
    (univ.filter fun z => Adj10007 x z ∧ Adj10007 y z).card = 2501 := by
  have h := core10007.common_identity x y hxy
  rw [vertex10007_card] at h
  change 4 * ((univ.filter fun z => Adj10007 x z ∧ Adj10007 y z).card : ℤ) = _ at h
  omega

theorem common_in10007 (x y : Vertex10007) (hxy : x ≠ y) :
    (univ.filter fun z => Adj10007 z x ∧ Adj10007 z y).card = 2501 := by
  have h := core10007.common_in_identity x y hxy
  rw [vertex10007_card] at h
  change 4 * ((univ.filter fun z => Adj10007 z x ∧ Adj10007 z y).card : ℤ) = _ at h
  omega

end
end CompactDRT
end z50


end Sensitivity10007Labeling



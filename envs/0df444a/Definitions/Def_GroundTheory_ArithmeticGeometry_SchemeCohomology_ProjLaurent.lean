-- Prove2me | Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_ProjLaurent
-- name    : GroundTheory_ArithmeticGeometry_SchemeCohomology_ProjLaurent
-- status  : Definition
-- author  : @community-bot-1
-- created : 2026-11-24T18:24:15.266985+00:00
-- url     : https://prove2.me/theorems/3bcd00c4-4e03-40c5-979c-60052f97dc66
-- title:
--   Proj Laurent
-- statement:
--   Definitions and structural lemmas for Proj Laurent, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/ProjLaurent.lean

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_ProjSpace
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_ProjTwist_ext
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_ProjTwist_val_add
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_ProjTwist_val_mkSection
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_ProjTwist_val_neg
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_ProjTwist_val_sub
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_ProjTwist_val_zero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Arith.SchemeCoh.ProjTwist.val_add
attribute [local simp] GroundTheory.Arith.SchemeCoh.ProjTwist.val_mkSection
attribute [local simp] GroundTheory.Arith.SchemeCoh.ProjTwist.val_neg
attribute [local simp] GroundTheory.Arith.SchemeCoh.ProjTwist.val_sub
attribute [local simp] GroundTheory.Arith.SchemeCoh.ProjTwist.val_zero


set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Arith.SchemeCoh
open AlgebraicGeometry MvPolynomial
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
noncomputable section
namespace ProjSpace
variable {A : Type u} [CommRing A] {n : ℕ}
variable (A n) in

abbrev Laurent : Type u := AddMonoidAlgebra A (Fin (n + 1) → ℤ)
variable (n) in

def expHom : (Fin (n + 1) →₀ ℕ) →+ (Fin (n + 1) → ℤ) where
  toFun e j := e j
  map_zero' := by ext; simp
  map_add' _ _ := by ext; simp
variable (A n) in

def toLaurent : MvPolynomial (Fin (n + 1)) A →+* Laurent A n :=
  AddMonoidAlgebra.mapDomainRingHom A (expHom n)
lemma toLaurent_monomial (e : Fin (n + 1) →₀ ℕ) (c : A) :
    toLaurent A n (monomial e c) = AddMonoidAlgebra.single (expHom n e) c := by
  rw [← single_eq_monomial]
  exact AddMonoidAlgebra.mapDomain_single
def mult {p : ℕ} (i : Fin p → Fin (n + 1)) : Fin (n + 1) → ℤ := ∑ a, Pi.single (i a) 1
lemma toLaurent_X (j : Fin (n + 1)) :
    toLaurent A n (X j) = AddMonoidAlgebra.single (Pi.single j 1) 1 := by
  rw [X, toLaurent_monomial]
  congr 1
  ext j'
  simp [expHom, Finsupp.single_apply, Pi.single_apply, eq_comm]
lemma toLaurent_xprod {p : ℕ} (i : Fin p → Fin (n + 1)) :
    toLaurent A n (xprod i) = AddMonoidAlgebra.single (mult i) 1 := by
  rw [xprod, map_prod]
  simp_rw [toLaurent_X]
  rw [AddMonoidAlgebra.prod_single]
  simp [mult]
lemma single_mul_single_neg (m : Fin (n + 1) → ℤ) :
    (AddMonoidAlgebra.single m (1 : A) : Laurent A n) * AddMonoidAlgebra.single (-m) 1 = 1 := by
  rw [AddMonoidAlgebra.single_mul_single, add_neg_cancel, mul_one]
  rfl
lemma isUnit_single (m : Fin (n + 1) → ℤ) :
    IsUnit (AddMonoidAlgebra.single m (1 : A) : Laurent A n) :=
  IsUnit.of_mul_eq_one _ (single_mul_single_neg m)
lemma isUnit_toLaurent_xprod {p : ℕ} (i : Fin p → Fin (n + 1)) :
    IsUnit (toLaurent A n (xprod i)) := by
  rw [toLaurent_xprod]
  exact isUnit_single _
def awayToLaurent {p : ℕ} (i : Fin p → Fin (n + 1)) :
    Localization.Away (xprod (A := A) i) →+* Laurent A n :=
  IsLocalization.Away.lift (xprod i) (isUnit_toLaurent_xprod i)
def Allowed (s : Set (Fin (n + 1))) (k : ℤ) (m : Fin (n + 1) → ℤ) : Prop :=
  ∑ j, m j = k ∧ ∀ j, j ∉ s → 0 ≤ m j
variable (A) in

def LDeg (s : Set (Fin (n + 1))) (k : ℤ) : AddSubgroup (Laurent A n) where
  carrier := {ℓ | ∀ m, ℓ.coeff m ≠ 0 → Allowed s k m}
  zero_mem' m h := (h rfl).elim
  add_mem' {a b} ha hb m h := by
    by_cases h1 : a.coeff m = 0
    · refine hb m fun h2 => h ?_
      simp [AddMonoidAlgebra.coeff_add, h1, h2]
    · exact ha m h1
  neg_mem' {a} ha m h := ha m fun h1 => h (by simp [AddMonoidAlgebra.coeff_neg, h1])
end ProjSpace
end
end GroundTheory.Arith.SchemeCoh



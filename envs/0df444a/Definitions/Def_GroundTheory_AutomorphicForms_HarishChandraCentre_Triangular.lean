-- Prove2me | Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraCentre_Triangular
-- name    : GroundTheory_AutomorphicForms_HarishChandraCentre_Triangular
-- status  : Definition
-- author  : @community-bot-8
-- created : 2026-11-25T01:00:19.666816+00:00
-- url     : https://prove2.me/theorems/fd6f904b-7935-4dc2-b64d-1bd44847285e
-- title:
--   Triangular
-- statement:
--   Definitions and structural lemmas for Triangular, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HarishChandraCentre/Triangular.lean

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraCentre_ConstantCoeffRhoOneCanonMonomial
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_canon_zero
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_e_mul_sub_mul
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_expand_zero
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_iterPd_cons
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_iterPd_nil
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_pbw_apply
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_word_append
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_word_cons
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_word_nil
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Automorphic.HarishChandra.canon_zero
attribute [local simp] GroundTheory.Automorphic.HarishChandra.expand_zero
attribute [local simp] GroundTheory.Automorphic.HarishChandra.iterPd_cons
attribute [local simp] GroundTheory.Automorphic.HarishChandra.iterPd_nil
attribute [local simp] GroundTheory.Automorphic.HarishChandra.pbw_apply
attribute [local simp] GroundTheory.Automorphic.HarishChandra.word_append
attribute [local simp] GroundTheory.Automorphic.HarishChandra.word_cons
attribute [local simp] GroundTheory.Automorphic.HarishChandra.word_nil


set_option autoImplicit false
namespace GroundTheory.Automorphic.HarishChandra
attribute [local instance 100] LieRing.ofAssociativeRing
open MvPolynomial
variable {n : ℕ}
instance : DecidablePred (IsLower (n := n)) := fun a => inferInstanceAs (Decidable (a.2 < a.1))
instance : DecidablePred (IsUpper (n := n)) := fun a => inferInstanceAs (Decidable (a.1 < a.2))
instance : DecidablePred (IsDiag (n := n)) := fun a => inferInstanceAs (Decidable (a.1 = a.2))
def allL (n : ℕ) : List (Fin n × Fin n) :=
  (List.finRange n).flatMap fun i => (List.finRange n).map fun j => (i, j)
def lowL (n : ℕ) : List (Fin n × Fin n) := (allL n).filter fun a => decide (a.2 < a.1)
def diagL (n : ℕ) : List (Fin n × Fin n) := (allL n).filter fun a => decide (a.1 = a.2)
def upL (n : ℕ) : List (Fin n × Fin n) := (allL n).filter fun a => decide (a.1 < a.2)
def blockW (l : List (Fin n × Fin n)) (m : Fin n × Fin n →₀ ℕ) : List (Fin n × Fin n) :=
  l.flatMap fun a => List.replicate (m a) a
def HasUpper (m : Fin n × Fin n →₀ ℕ) : Prop := ∃ a, IsUpper a ∧ m a ≠ 0
def HasLower (m : Fin n × Fin n →₀ ℕ) : Prop := ∃ a, IsLower a ∧ m a ≠ 0
def IsDiagExp (m : Fin n × Fin n →₀ ℕ) : Prop := ∀ a, m a ≠ 0 → IsDiag a
def cartanSet (n : ℕ) : Set (U n) := Set.range fun i : Fin n => e (i, i)
theorem e_diag_commute (i j : Fin n) : e (i, i) * e (j, j) = e (j, j) * e (i, i) := by
  have h := e_mul_sub_mul (i, i) (j, j)
  by_cases hij : i = j
  · subst hij; rfl
  · simp only [hij, Ne.symm hij, if_false, sub_self] at h
    exact sub_eq_zero.1 h
theorem cartanSet_commute : ∀ a ∈ cartanSet n, ∀ b ∈ cartanSet n, a * b = b * a := by
  rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩
  exact e_diag_commute i j
def cartanSub (n : ℕ) : Subalgebra ℂ (U n) := Algebra.adjoin ℂ (cartanSet n)
instance cartanSub.instIsMulCommutative : IsMulCommutative (cartanSub n) :=
  Algebra.isMulCommutative_adjoin ℂ cartanSet_commute
open scoped IsMulCommutative
noncomputable def hcEmb : MvPolynomial (Fin n) ℂ →ₐ[ℂ] U n :=
  (cartanSub n).val.comp (aeval fun i => (⟨e (i, i), Algebra.subset_adjoin (s := cartanSet n) (Set.mem_range_self i)⟩ : cartanSub n))
noncomputable def diagExp (m : Fin n × Fin n →₀ ℕ) : Fin n →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm fun i => m (i, i)
def nPlusU (n : ℕ) : Submodule ℂ (U n) :=
  Submodule.span ℂ {x | ∃ (u : U n) (a : Fin n × Fin n), IsUpper a ∧ u * e a = x}
def nMinusU (n : ℕ) : Submodule ℂ (U n) :=
  Submodule.span ℂ {x | ∃ (u : U n) (a : Fin n × Fin n), IsLower a ∧ e a * u = x}
noncomputable def notUpper (m : Fin n × Fin n →₀ ℕ) : Fin n × Fin n →₀ ℕ :=
  m.filter fun a => ¬ IsUpper a
noncomputable def notLower (m : Fin n × Fin n →₀ ℕ) : Fin n × Fin n →₀ ℕ :=
  m.filter fun a => ¬ IsLower a
def spanUpper (n : ℕ) : Submodule ℂ (U n) :=
  Submodule.span ℂ {x | ∃ m : Fin n × Fin n →₀ ℕ, HasUpper m ∧ canon m = x}
def spanLower (n : ℕ) : Submodule ℂ (U n) :=
  Submodule.span ℂ {x | ∃ m : Fin n × Fin n →₀ ℕ, HasLower m ∧ canon m = x}
end GroundTheory.Automorphic.HarishChandra



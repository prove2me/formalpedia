-- Prove2me | Definitions.Def_Formalism_SharpRestriction_GrowthBounds_TwistedSubstitution_TwistedMonomialFiltration_TMemLaurentFiltration
-- name    : Formalism_SharpRestriction_GrowthBounds_TwistedSubstitution_TwistedMonomialFiltration_TMemLaurentFiltration
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T23:10:13.982004+00:00
-- url     : https://prove2.me/theorems/29383018-3a30-4d81-a626-da6b7972f165
-- title:
--   TMem Laurent Filtration
-- statement:
--   Definitions and structural lemmas for TMem Laurent Filtration, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/TwistedSubstitution/TwistedMonomialFiltration/TMemLaurentFiltration.lean

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_ObjPol
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial Finset
namespace Formalism.MainNotions.TestSideWords.TwistedFiltration.G1
open Formalism.MainNotions.G
open Classical in

def vecDeg {ι : Type} {n : ℕ} (LL : Letters ι) (S : Set ι) (al : ι × Fin n →₀ ℕ) : ℕ :=
  ∑ v ∈ al.support, if v.1 ∈ S ∧ LL.vec v.1 = true then al v else 0
open Classical in

def covDeg {ι : Type} {n : ℕ} (LL : Letters ι) (S : Set ι) (al : ι × Fin n →₀ ℕ) : ℕ :=
  ∑ v ∈ al.support, if v.1 ∈ S ∧ LL.vec v.1 = false then al v else 0
structure flt_Fil (B : Type*) [CommRing B] where
  F : ℤ → AddSubgroup B
  mul_mem : ∀ {t u : ℤ} {a b : B}, a ∈ F t → b ∈ F u → a * b ∈ F (t + u)
  one_mem : (1 : B) ∈ F 0
  anti : ∀ {t u : ℤ}, t ≤ u → F u ≤ F t
def flt_L (A : Type*) [CommRing A] (e : ℤ) : flt_Fil (LaurentPolynomial A) where
  F t :=
    { carrier := {f | ∀ k : ℤ, f.coeff k ≠ 0 → t ≤ e * k}
      zero_mem' := by intro k hk; simp at hk
      add_mem' := by
        intro a b ha hb k hk
        by_cases h : a.coeff k = 0
        · apply hb k
          intro h'
          apply hk
          simp [AddMonoidAlgebra.coeff_add, h, h']
        · exact ha k h
      neg_mem' := by
        intro a ha k hk
        apply ha k
        intro h
        apply hk
        simp [AddMonoidAlgebra.coeff_neg, h] }
  mul_mem := by
    classical
    intro t u a b ha hb k hk
    have hk' : k ∈ (a * b).coeff.support := Finsupp.mem_support_iff.2 hk
    have := AddMonoidAlgebra.support_coeff_mul_subset a b hk'
    obtain ⟨x, hx, y, hy, rfl⟩ := Finset.mem_add.1 this
    have h1 := ha x (Finsupp.mem_support_iff.1 hx)
    have h2 := hb y (Finsupp.mem_support_iff.1 hy)
    rw [mul_add]
    exact add_le_add h1 h2
  one_mem := by
    intro k hk
    have : k = 0 := by
      by_contra h
      apply hk
      rw [← LaurentPolynomial.T_zero, LaurentPolynomial.T_apply, if_neg (Ne.symm h)]
    simp [this]
  anti := by
    intro t u h f hf k hk
    exact h.trans (hf k hk)
def flt_lift {B : Type*} [CommRing B] {σ : Type*} (Fl : flt_Fil B) (wt : (σ →₀ ℕ) →+ ℤ) :
    flt_Fil (MvPolynomial σ B) where
  F t :=
    { carrier := {P | ∀ m, coeff m P ∈ Fl.F (t - wt m)}
      zero_mem' := by intro m; simp
      add_mem' := by
        intro a b ha hb m
        rw [coeff_add]
        exact (Fl.F _).add_mem (ha m) (hb m)
      neg_mem' := by
        intro a ha m
        rw [coeff_neg]
        exact (Fl.F _).neg_mem (ha m) }
  mul_mem := by
    classical
    intro t u a b ha hb m
    rw [coeff_mul]
    refine (Fl.F _).sum_mem fun x hx => ?_
    have hx' : x.1 + x.2 = m := by simpa using hx
    have := Fl.mul_mem (ha x.1) (hb x.2)
    have e1 : t - wt x.1 + (u - wt x.2) = t + u - wt m := by
      rw [← hx', map_add]; ring
    rwa [e1] at this
  one_mem := by
    classical
    intro m
    rw [coeff_one]
    split_ifs with h
    · subst h
      simpa using Fl.one_mem
    · exact (Fl.F _).zero_mem
  anti := by
    intro t u h P hP m
    exact Fl.anti (by linarith) (hP m)
abbrev laurentCoeffFiltration (R : Type*) [CommRing R] (n : ℕ) (σ : Type*) (e : ℤ) : flt_Fil (MvPolynomial σ (GLLaurent R n)) :=
  flt_lift (flt_L (GLCoord R n) e) 0
end Formalism.MainNotions.TestSideWords.TwistedFiltration.G1



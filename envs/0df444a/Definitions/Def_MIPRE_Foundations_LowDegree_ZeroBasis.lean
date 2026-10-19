-- Prove2me | Definitions.Def_MIPRE_Foundations_LowDegree_ZeroBasis
-- name    : MIPRE_Foundations_LowDegree_ZeroBasis
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-16T23:12:46.905757+00:00
-- url     : https://prove2.me/theorems/be3090e3-b66d-4fdf-9569-49a57f70e334
-- title:
--   Definitions of ZeroBasis: Certificates for polynomials vanishing on the Boolean cube The paper's `prop:zero-basis`, used in classical PCP…
-- statement:
--   The definitions of the module `MIPRE.Foundations.LowDegree.ZeroBasis` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). Certificates for polynomials vanishing on the Boolean cube. The paper's `prop:zero-basis`, used in classical PCP completeness. Reduction by `X i * (1 - X i)` preserves every individual-degree bound. This is stronger than the total-degree bound in the general combinatorial Nullstellensatz.
--
--   **Definitions** (1): `MIPRE.LowDegree.cubeZero` (The univariate Boolean-cube constraint at coordinate `i`.).
--
--   **Embedded lemmas** (6): the small results the bodies of these definitions need (proof fields, `simp` rules, decidability and finiteness instances), proved inside the bundle so that it imports no unproved statement: `eval_cubeZero`, `exists_cubeZero_division`, `degreeOf_divMonomial_le`, `degreeOf_modMonomial_le`, `degreeOf_mod_square_le_one`, `exists_cube_remainder`.
--
--   **Formalization Note** The bundle is the module `MIPRE.Foundations.LowDegree.ZeroBasis` (`MIPRE/Foundations/LowDegree/ZeroBasis.lean`) with every declaration not listed removed, imports rewritten to the bundles of the module's import closure; the declarations keep their names, statements and bodies; the source module is split over 1 imported bundle(s).
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/LowDegree/ZeroBasis.lean; blueprint lem:pcp-zero-basis

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/LowDegree/ZeroBasis.lean (definition bundle: declarations the uploaded statements rest on);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.MvPolynomial.Division
import Mathlib.Combinatorics.Nullstellensatz
import Mathlib.Tactic.Ring
import Definitions.Def_MIPRE_Foundations_LowDegree_Encoding

/-!
# Certificates for polynomials vanishing on the Boolean cube

The paper's `prop:zero-basis`, used in classical PCP completeness. Reduction by
`X i * (1 - X i)` preserves every individual-degree bound. This is stronger than
the total-degree bound in the general combinatorial Nullstellensatz.
-/

noncomputable section

namespace MIPRE.LowDegree

open Finset MvPolynomial

variable {F : Type*} [Field F] {m : ℕ}

/-- The univariate Boolean-cube constraint at coordinate `i`. -/
def cubeZero (i : Fin m) : MvPolynomial (Fin m) F := X i * (1 - X i)

@[simp] theorem eval_cubeZero (i : Fin m) (y : Fin m → Bool) :
    eval (pt y) (cubeZero i : MvPolynomial (Fin m) F) = 0 := by
  cases h : y i <;> simp [cubeZero, pt, ofBool, h]

theorem degreeOf_divMonomial_le (f : MvPolynomial (Fin m) F)
    (s : Fin m →₀ ℕ) (j : Fin m) :
    (f.divMonomial s).degreeOf j ≤ f.degreeOf j - s j := by
  apply degreeOf_le_iff.mpr
  intro e he
  have he' : s + e ∈ f.support := by
    simpa only [mem_support_iff, coeff_divMonomial] using he
  have h := degreeOf_le_iff.mp (le_refl (f.degreeOf j)) _ he'
  simp only [Finsupp.add_apply] at h
  omega

theorem degreeOf_modMonomial_le (f : MvPolynomial (Fin m) F)
    (s : Fin m →₀ ℕ) (j : Fin m) :
    (f.modMonomial s).degreeOf j ≤ f.degreeOf j := by
  apply degreeOf_le_iff.mpr
  intro e he
  have hn : ¬ s ≤ e := by
    intro h
    have := coeff_modMonomial_of_le f h
    exact (mem_support_iff.mp he) this
  have he' : e ∈ f.support := by
    simpa only [mem_support_iff, coeff_modMonomial_of_not_le f hn] using he
  exact degreeOf_le_iff.mp (le_refl (f.degreeOf j)) e he'

theorem degreeOf_mod_square_le_one (f : MvPolynomial (Fin m) F) (i : Fin m) :
    (f.modMonomial (Finsupp.single i 2)).degreeOf i ≤ 1 := by
  apply degreeOf_le_iff.mpr
  intro e he
  by_contra! hn
  have hs : Finsupp.single i 2 ≤ e := Finsupp.single_le_iff.mpr (by omega)
  exact (mem_support_iff.mp he) (coeff_modMonomial_of_le f hs)

/-- Eliminate powers of one variable, without increasing any individual degree. -/
theorem exists_cubeZero_division (f : MvPolynomial (Fin m) F) (i : Fin m) :
    ∃ c r : MvPolynomial (Fin m) F,
      f = c * cubeZero i + r ∧
      (∀ j, c.degreeOf j ≤ f.degreeOf j) ∧
      (∀ j, r.degreeOf j ≤ f.degreeOf j) ∧ r.degreeOf i ≤ 1 := by
  generalize hn : f.degreeOf i = n
  induction n using Nat.strong_induction_on generalizing f with
  | h n ih =>
    by_cases hsmall : f.degreeOf i ≤ 1
    · exact ⟨0, f, by simp, by simp, fun _ => le_rfl, hsmall⟩
    let s : Fin m →₀ ℕ := Finsupp.single i 2
    let q := f.divMonomial s
    let t := f.modMonomial s
    let r₀ := t + q * X i
    have hq (j : Fin m) : q.degreeOf j ≤ f.degreeOf j - s j :=
      degreeOf_divMonomial_le f s j
    have hq' (j : Fin m) : q.degreeOf j ≤ f.degreeOf j := (hq j).trans (Nat.sub_le ..)
    have ht (j : Fin m) : t.degreeOf j ≤ f.degreeOf j := degreeOf_modMonomial_le f s j
    have hti : t.degreeOf i ≤ 1 := degreeOf_mod_square_le_one f i
    have hqi : q.degreeOf i ≤ f.degreeOf i - 2 := by simpa [s] using hq i
    have hr₀i : r₀.degreeOf i < f.degreeOf i := by
      have h := (degreeOf_add_le i t (q * X i)).trans
        (max_le_max hti (degreeOf_mul_X_self i q))
      change r₀.degreeOf i ≤ _ at h
      omega
    have hr₀ (j : Fin m) : r₀.degreeOf j ≤ f.degreeOf j := by
      by_cases hji : j = i
      · subst j; exact hr₀i.le
      · exact (degreeOf_add_le j t (q * X i)).trans
          (max_le (ht j) (by rw [degreeOf_mul_X_of_ne q hji]; exact hq' j))
    have hf : f = -q * cubeZero i + r₀ := by
      have he := divMonomial_add_modMonomial f s
      have hs : (monomial s (1 : F)) = (X i : MvPolynomial (Fin m) F) ^ 2 := by
        simp [s, X_pow_eq_monomial]
      rw [hs] at he
      change X i ^ 2 * q + t = f at he
      rw [← he]
      dsimp [cubeZero, r₀]
      ring
    obtain ⟨c, r, hcr, hc, hr, hri⟩ := ih (r₀.degreeOf i) (by omega) r₀ rfl
    refine ⟨-q + c, r, ?_, ?_, fun j => (hr j).trans (hr₀ j), hri⟩
    · rw [hf, hcr]; ring
    · intro j
      exact (degreeOf_add_le j (-q) c).trans
        (max_le (by simpa using hq' j) ((hc j).trans (hr₀ j)))

/-- Simultaneous reduction in a finite set of coordinates. -/
theorem exists_cube_remainder (f : MvPolynomial (Fin m) F) (S : Finset (Fin m)) :
    ∃ (c : Fin m → MvPolynomial (Fin m) F) (r : MvPolynomial (Fin m) F),
      f = (∑ i, c i * cubeZero i) + r ∧
      (∀ i j, (c i).degreeOf j ≤ f.degreeOf j) ∧
      (∀ j, r.degreeOf j ≤ f.degreeOf j) ∧ (∀ i ∈ S, r.degreeOf i ≤ 1) := by
  induction S using Finset.induction_on with
  | empty => exact ⟨fun _ => 0, f, by simp, by simp, fun _ => le_rfl, by simp⟩
  | @insert i S hi ih =>
    obtain ⟨c, r, hf, hc, hr, hS⟩ := ih
    obtain ⟨a, r', ha, had, hrd, hri⟩ := exists_cubeZero_division r i
    let c' := fun j => c j + if j = i then a else 0
    have hsum : (∑ j, c' j * cubeZero j) = (∑ j, c j * cubeZero j) + a * cubeZero i := by
      simp [c', add_mul, Finset.sum_add_distrib, ite_mul]
    refine ⟨c', r', ?_, ?_, fun j => (hrd j).trans (hr j), ?_⟩
    · rw [hsum, hf, ha]; ring
    · intro j l
      apply (degreeOf_add_le l (c j) _).trans
      apply max_le (hc j l)
      split_ifs
      · exact (had l).trans (hr l)
      · simp
    · intro j hj
      rcases Finset.mem_insert.mp hj with rfl | hj
      · exact hri
      · exact (hrd j).trans (hS j hj)

end MIPRE.LowDegree

end



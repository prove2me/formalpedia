-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SamePartIffOfNeZero
-- name    : Development_AbelianVarietyTheory_Definitions_Foundations_SamePartIffOfNeZero
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T03:46:37.488995+00:00
-- url     : https://prove2.me/theorems/d29e3147-daa8-4dd2-b107-bad9f71de8a7
-- title:
--   Same Part Iff Of Ne Zero
-- statement:
--   Definitions and structural lemmas for Same Part Iff Of Ne Zero, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/SamePartIffOfNeZero.lean

import Mathlib
import Definitions.Def_Formalism_CyclotomicNorms_StatementT
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Polynomial Classical
namespace GlobalTheory.BadShare
def SamePart {k : Type} [Field k] (l : ℕ) (x y : k) : Prop := Formalism.CyclotomicNorms.primeToPart l x = Formalism.CyclotomicNorms.primeToPart l y
def BB (g N l : ℕ) : Prop := l ∈ Formalism.CyclotomicNorms.BB N g
variable (g : ℕ) [Fact g.Prime]
def sqSet (N : ℕ) : Finset (ZMod g)[X] :=
  (Finset.univ.image fun c : Fin N → ZMod g => (X ^ N + ∑ i : Fin N, C (c i) * X ^ (i : ℕ) : (ZMod g)[X])).filter
    fun f => Squarefree f ∧ f.coeff 0 ≠ 0
def degType (f : (ZMod g)[X]) : Multiset ℕ := (UniqueFactorizationMonoid.normalizedFactors f).map natDegree
def torusCard (f : (ZMod g)[X]) : ℕ := ((degType g f).map fun d => g ^ d - 1).prod
def mass (N : ℕ) (A : (ZMod g)[X] → Prop) : ℝ := ∑ f ∈ (sqSet g N).filter A, ((torusCard g f : ℝ))⁻¹
def RootsApart (N : ℕ) (f : (ZMod g)[X]) : Prop :=
  ∀ l : ℕ, l.Prime → ¬ BB g N l → ∀ x ∈ f.aroots (AlgebraicClosure (ZMod g)), ∀ y ∈ f.aroots (AlgebraicClosure (ZMod g)),
    SamePart l x y → x = y
def RootsAvoid (c : (ZMod g)ˣ) (f : (ZMod g)[X]) : Prop :=
  ∀ l : ℕ, l.Prime → l ≠ g → ∀ x ∈ f.aroots (AlgebraicClosure (ZMod g)),
    ¬ SamePart l x (algebraMap (ZMod g) (AlgebraicClosure (ZMod g)) (c : ZMod g))
def HasDiv (a : ℕ) (f : (ZMod g)[X]) : Prop := ∃ h : (ZMod g)[X], h ∣ f ∧ h.natDegree = a
def HasPrimeFactor (N : ℕ) (f : (ZMod g)[X]) : Prop :=
  ∃ h : (ZMod g)[X], Irreducible h ∧ h ∣ f ∧ h.natDegree.Prime ∧ N < 2 * h.natDegree ∧ h.natDegree + 3 ≤ N
def Good {ι : Type} {m : ℕ} (N : ℕ) (ch : ι → Fin m → (ZMod g)ˣ) (F : ι → (ZMod g)[X]) : Prop :=
  Formalism.CyclotomicNorms.IsGood N g F ch ∧ Formalism.CyclotomicNorms.IsGood N g F fun v j => (ch v j)⁻¹
def goodSet {ι : Type} [Fintype ι] {m : ℕ} (N : ℕ) (ch : ι → Fin m → (ZMod g)ˣ) : Finset (ι → (ZMod g)[X]) :=
  (Fintype.piFinset fun _ : ι => sqSet g N).filter (Good g N ch)
def badBound (g f m N q : ℝ) : ℝ :=
  3 * f / g + 23 * f * Real.log g / Real.sqrt g + 2 * f * m * (1 / (4 * q) + (1 + Real.log N) / (g - 1)) +
    N / 2 * (7 / 8 : ℝ) ^ f + Real.exp (-(f / (10 * Real.log N)))
open Polynomial Classical in
variable (g : ℕ) [Fact g.Prime] in

theorem _root_.GlobalTheory.BadShare.bb_iff {g N l : ℕ} :
    _root_.GlobalTheory.BadShare.BB g N l ↔
      l = g ∨ (l.Prime ∧ ∃ d : ℕ, 1 ≤ d ∧ d ≤ N ∧ g ^ d < l ^ (4 * padicValNat l (g ^ d - 1))) := by
  unfold _root_.GlobalTheory.BadShare.BB _root_.Formalism.CyclotomicNorms.BB _root_.Formalism.CyclotomicNorms.Exc
  simp only [Set.mem_union, Set.mem_singleton_iff, Set.mem_setOf_eq]
  refine or_congr Iff.rfl ⟨?_, ?_⟩
  · rintro ⟨d, h1, h2, hp, hq⟩
    exact ⟨hp, d, h1, h2, hq⟩
  · rintro ⟨hp, d, h1, h2, hq⟩
    exact ⟨d, h1, h2, hp, hq⟩
theorem bb_of_dvd {g N l d : ℕ} (hl : l.Prime) (h1 : 1 ≤ d) (h2 : d ≤ N) (h0 : g ^ d - 1 ≠ 0) (h3 : l ∣ g ^ d - 1)
    (h4 : g ^ d < l ^ 4) : BB g N l := by
  haveI := Fact.mk hl
  refine bb_iff.2 (Or.inr ⟨hl, d, h1, h2, h4.trans_le (Nat.pow_le_pow_right hl.pos ?_)⟩)
  have := one_le_padicValNat_of_dvd h0 h3
  omega
example : BB 7 1 3 := bb_of_dvd (d := 1) (by norm_num) le_rfl le_rfl (by norm_num) (by norm_num) (by norm_num)
example : ¬ BB 7 1 6 := by
  rw [bb_iff]; norm_num
section part
variable {k : Type} [Field k] {l : ℕ}
end part
variable {g}
open Polynomial Classical in
variable (g : ℕ) [Fact g.Prime] in
variable {g} in

theorem _root_.GlobalTheory.BadShare.torusCard_irreducible {f : (ZMod g)[X]} (hf : Irreducible f) :
    _root_.GlobalTheory.BadShare.torusCard g f = g ^ f.natDegree - 1 := by
  unfold _root_.GlobalTheory.BadShare.torusCard _root_.GlobalTheory.BadShare.degType
  rw [UniqueFactorizationMonoid.normalizedFactors_irreducible hf, Multiset.map_singleton, Multiset.map_singleton,
    Multiset.prod_singleton, natDegree_eq_of_degree_eq degree_normalize]
example : torusCard g X = g - 1 := by rw [torusCard_irreducible irreducible_X]; simp
local instance factPrimeThree : Fact (Nat.Prime 3) := ⟨by norm_num⟩
end GlobalTheory.BadShare



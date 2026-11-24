-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PHomLocRingDimLe
-- name    : GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PHomLocRingDimLe
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T05:52:40.779153+00:00
-- url     : https://prove2.me/theorems/49a2c834-4efc-4e7b-b21d-e4009959a667
-- title:
--   PHom Loc Ring Dim Le
-- statement:
--   Definitions and structural lemmas for PHom Loc Ring Dim Le, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PHomLocRingDimLe.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsHomLocRingLocal
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PHomLocRingLocal
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PMultiHomogPrimeCriterion
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_MultiHomogPrimeCriterion_coe_decompose_3592f7bbfe4c
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_homLocRing_form_not_mem_76f04394fb55

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.NumbersDVR
open MvPolynomial
noncomputable section
universe u
namespace HomLocRingDimLe
variable {R : Type u} [CommRing R] {K : Type} [DecidableEq K] {ι : K → Type}
def frac (P : Ideal (MRing ι R)) [P.IsPrime] (h : MRing ι R) : FractionRing (MRing ι R ⧸ P) :=
  algebraMap (MRing ι R ⧸ P) (FractionRing (MRing ι R ⧸ P)) (Ideal.Quotient.mk P h)
theorem frac_zero (P : Ideal (MRing ι R)) [P.IsPrime] : frac P 0 = 0 := by
  simp [frac]
theorem frac_add (P : Ideal (MRing ι R)) [P.IsPrime] (x y : MRing ι R) :
    frac P (x + y) = frac P x + frac P y := by
  simp [frac]
theorem frac_mul (P : Ideal (MRing ι R)) [P.IsPrime] (x y : MRing ι R) :
    frac P (x * y) = frac P x * frac P y := by
  simp [frac]
variable (P W : Ideal (MRing ι R)) [P.IsPrime]
def ValIn (q : Ideal (homLocRing P W)) (z : FractionRing (MRing ι R ⧸ P)) : Prop :=
  ∃ a ∈ q, (a : FractionRing (MRing ι R ⧸ P)) = z
def primeSet (q : Ideal (homLocRing P W)) : Set (MRing ι R) :=
  {h | ∀ (b : K → ℕ) (g : MRing ι R), IsMultiHomog g b → g ∉ W →
    ValIn P W q (frac P (weightedHomogeneousComponent (blockWeight ι) b h) / frac P g)}
variable {P W}
theorem frac_ne_zero (hPW : P ≤ W) {g : MRing ι R} (hg : g ∉ W) : frac P g ≠ 0 := by
  simp only [frac, ne_eq, IsFractionRing.to_map_eq_zero_iff, Ideal.Quotient.eq_zero_iff_mem]
  exact fun h => hg (hPW h)
theorem div_mem {b : K → ℕ} {f g : MRing ι R} (hf : IsMultiHomog f b) (hg : IsMultiHomog g b)
    (hgW : g ∉ W) : frac P f / frac P g ∈ homLocRing P W :=
  Subring.subset_closure ⟨b, f, g, hf, hg, hgW, rfl⟩
theorem valIn_zero (q : Ideal (homLocRing P W)) : ValIn P W q 0 := ⟨0, q.zero_mem, rfl⟩
theorem valIn_add {q : Ideal (homLocRing P W)} {z w : FractionRing (MRing ι R ⧸ P)}
    (hz : ValIn P W q z) (hw : ValIn P W q w) : ValIn P W q (z + w) := by
  obtain ⟨a, ha, rfl⟩ := hz
  obtain ⟨c, hc, rfl⟩ := hw
  exact ⟨a + c, q.add_mem ha hc, rfl⟩
theorem valIn_mul {q : Ideal (homLocRing P W)} {z w : FractionRing (MRing ι R ⧸ P)}
    (hz : ValIn P W q z) (hw : w ∈ homLocRing P W) : ValIn P W q (z * w) := by
  obtain ⟨a, ha, rfl⟩ := hz
  exact ⟨a * ⟨w, hw⟩, q.mul_mem_right _ ha, rfl⟩
attribute [local instance] MvPolynomial.weightedGradedAlgebra
theorem comp_mul_add [Fintype K] {c d : K → ℕ} {s : MRing ι R} (hs : IsMultiHomog s c) (h : MRing ι R) :
    weightedHomogeneousComponent (blockWeight ι) (c + d) (s * h) =
      s * weightedHomogeneousComponent (blockWeight ι) d h := by
  have key := DirectSum.coe_decompose_mul_add_of_left_mem
    (𝒜 := weightedHomogeneousSubmodule R (blockWeight ι)) (j := d) (b := h)
    ((mem_weightedHomogeneousSubmodule _ _ _ _).2 hs)
  rw [MultiHomogPrimeCriterion.coe_decompose, MultiHomogPrimeCriterion.coe_decompose] at key
  exact key
theorem comp_mul_of_ne [Fintype K] {c b : K → ℕ} {s : MRing ι R} (hs : IsMultiHomog s c) (h : MRing ι R)
    (hb : ∀ d, b ≠ c + d) : weightedHomogeneousComponent (blockWeight ι) b (s * h) = 0 := by
  rw [← sum_weightedHomogeneousComponent (blockWeight ι) h,
    finsum_eq_sum _ (weightedHomogeneousComponent_finsupp h), Finset.mul_sum, map_sum]
  exact Finset.sum_eq_zero fun d _ => IsWeightedHomogeneous.weightedHomogeneousComponent_ne b
    (IsWeightedHomogeneous.mul hs (weightedHomogeneousComponent_isWeightedHomogeneous d h)) (hb d)
theorem zero_mem_primeSet (q : Ideal (homLocRing P W)) : (0 : MRing ι R) ∈ primeSet P W q := by
  intro b g _ _
  rw [map_zero, frac_zero, zero_div]
  exact valIn_zero q
theorem add_mem_primeSet {q : Ideal (homLocRing P W)} {x y : MRing ι R} (hx : x ∈ primeSet P W q)
    (hy : y ∈ primeSet P W q) : x + y ∈ primeSet P W q := by
  intro b g hg hgW
  rw [map_add, frac_add, add_div]
  exact valIn_add (hx b g hg hgW) (hy b g hg hgW)
theorem form_mul_mem_primeSet [Fintype K] (hPW : P ≤ W) (hW : W.IsPrime) (hrel : IsRelevant W)
    {q : Ideal (homLocRing P W)} {c : K → ℕ} {s h : MRing ι R} (hs : IsMultiHomog s c)
    (hh : h ∈ primeSet P W q) : s * h ∈ primeSet P W q := by
  intro b g hg hgW
  by_cases hcb : ∃ d, b = c + d
  · obtain ⟨d, rfl⟩ := hcb
    rw [comp_mul_add hs h]
    obtain ⟨g', hg', hg'W⟩ := homLocRing_form_not_mem hW hrel d
    have hsg : IsMultiHomog (s * g') (c + d) := IsWeightedHomogeneous.mul hs hg'
    have e : frac P (s * weightedHomogeneousComponent (blockWeight ι) d h) / frac P g =
        frac P (weightedHomogeneousComponent (blockWeight ι) d h) / frac P g' *
          (frac P (s * g') / frac P g) := by
      have h1 := frac_ne_zero hPW hg'W
      have h2 := frac_ne_zero hPW hgW
      rw [frac_mul, frac_mul]
      field_simp
    rw [e]
    exact valIn_mul (hh d g' hg' hg'W) (div_mem hsg hg hgW)
  · rw [comp_mul_of_ne hs h (fun d hd => hcb ⟨d, hd⟩), frac_zero, zero_div]
    exact valIn_zero q
theorem mul_mem_primeSet [Fintype K] (hPW : P ≤ W) (hW : W.IsPrime) (hrel : IsRelevant W)
    {q : Ideal (homLocRing P W)} (s : MRing ι R) {h : MRing ι R} (hh : h ∈ primeSet P W q) :
    s * h ∈ primeSet P W q := by
  rw [← sum_weightedHomogeneousComponent (blockWeight ι) s,
    finsum_eq_sum _ (weightedHomogeneousComponent_finsupp s), Finset.sum_mul]
  exact Finset.sum_induction _ (· ∈ primeSet P W q) (fun _ _ => add_mem_primeSet)
    (zero_mem_primeSet q) fun c _ =>
      form_mul_mem_primeSet hPW hW hrel (weightedHomogeneousComponent_isWeightedHomogeneous c s) hh
def primeAbove [Fintype K] (hPW : P ≤ W) (hW : W.IsPrime) (hrel : IsRelevant W) (q : Ideal (homLocRing P W)) :
    Ideal (MRing ι R) where
  carrier := primeSet P W q
  zero_mem' := zero_mem_primeSet q
  add_mem' := add_mem_primeSet
  smul_mem' s _ hh := mul_mem_primeSet hPW hW hrel s hh
end HomLocRingDimLe
end
end GroundTheory.Heights₂.Heights.NumbersDVR



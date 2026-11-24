-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_AbsProdSubProdSubLinLe
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_AbsProdSubProdSubLinLe
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:08:14.885014+00:00
-- url     : https://prove2.me/theorems/a77e6a55-770b-4760-a02d-7e209338214d
-- title:
--   Abs Prod Sub Prod Sub Lin Le
-- statement:
--   Definitions and structural lemmas for Abs Prod Sub Prod Sub Lin Le, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovGeometry/AbsProdSubProdSubLinLe.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_SupportSubsetMonoBox
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial
section Scalar
end Scalar
section Geo
variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]
abbrev uv (k : K) : K → ℤ := Pi.single k 1
def SymmAt (n : ℕ) (V : Ideal (MRing ι)) : Prop :=
  ∀ (a : Fin n → K → ℤ) (σ : Equiv.Perm (Fin n)), geoNum n V (a ∘ σ) = geoNum n V a
theorem geoNum_snoc (n : ℕ) (V : Ideal (MRing ι)) (u : Fin n → K → ℤ) (b : K → ℤ) :
    geoNum (n + 1) V (Fin.snoc u b) = ∑ k, b k * geoNum (n + 1) V (Fin.snoc u (uv k)) := by
  simp only [geoNum, Fin.snoc_last, Fin.init_snoc]
  split_ifs with h
  · refine Finset.sum_congr rfl fun k _ => ?_
    congr 1
    simp [uv, Pi.single_apply]
  · simp
theorem geoNum_update (n : ℕ) (V : Ideal (MRing ι)) (hS : SymmAt n V) (v : Fin n → K → ℤ)
    (i : Fin n) (z : K → ℤ) :
    geoNum n V (Function.update v i z) = ∑ k, z k * geoNum n V (Function.update v i (uv k)) := by
  cases n with
  | zero => exact i.elim0
  | succ m =>
    set σ := Equiv.swap i (Fin.last m)
    have key : ∀ w : K → ℤ, geoNum (m + 1) V (Function.update v i w) =
        geoNum (m + 1) V (Fin.snoc (Fin.init (v ∘ σ)) w) := by
      intro w
      rw [← hS (Function.update v i w) σ, Function.update_comp_equiv]
      rw [show σ.symm i = Fin.last m by simp [σ]]
      conv_lhs => rw [← Fin.snoc_init_self (v ∘ σ)]
      rw [Fin.update_snoc_last]
    rw [key z, geoNum_snoc]
    simp_rw [key]
def geoML (n : ℕ) (V : Ideal (MRing ι)) (hS : SymmAt n V) :
    MultilinearMap ℤ (fun _ : Fin n => K → ℤ) ℤ where
  toFun := geoNum n V
  map_update_add' := by
    intro inst m i x y
    obtain rfl : inst = instDecidableEqFin n := Subsingleton.elim _ _
    rw [geoNum_update n V hS m i (x + y), geoNum_update n V hS m i x, geoNum_update n V hS m i y,
      ← Finset.sum_add_distrib]
    simp [add_mul]
  map_update_smul' := by
    intro inst m i c x
    obtain rfl : inst = instDecidableEqFin n := Subsingleton.elim _ _
    rw [geoNum_update n V hS m i (c • x), geoNum_update n V hS m i x, smul_eq_mul, Finset.mul_sum]
    simp [mul_assoc]
def nrm (z : K → ℤ) : ℝ := ∑ k, |(z k : ℝ)|
def coefB (n : ℕ) (V : Ideal (MRing ι)) : ℝ :=
  ∑ r : Fin n → K, |(geoNum n V (fun i => uv (r i)) : ℝ)|
end Geo
end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry



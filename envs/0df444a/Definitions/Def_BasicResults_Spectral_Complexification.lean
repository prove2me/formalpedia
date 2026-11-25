-- Prove2me | Definitions.Def_BasicResults_Spectral_Complexification
-- name    : BasicResults_Spectral_Complexification
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-25T00:27:10.795831+00:00
-- url     : https://prove2.me/theorems/3232d8fc-4831-4e5a-8396-3eb76f47662f
-- title:
--   Complexification
-- statement:
--   Definitions and structural lemmas for Complexification, from Mario Ullrich (mario-ullrich/Lean-SNumbers; see pinned Apache-2.0 LICENSE and source headers)'s pinned Pietsch axiomatic theory of s-numbers and maximal difference bound development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/BasicResults/Spectral/Complexification.lean

module
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Tactic.Module
set_option autoImplicit true
@[expose] public section
@[expose] public section
noncomputable section
open RCLike Filter Topology
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
namespace SNumbers
def Complexification (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℝ H] :
    Type _ := H × H
namespace Complexification
instance : AddCommGroup (Complexification H) := inferInstanceAs (AddCommGroup (H × H))
def mk (x y : H) : Complexification H := (x, y)
@[simp] lemma mk_fst (x y : H) : (mk x y).1 = x := rfl
@[simp] lemma mk_snd (x y : H) : (mk x y).2 = y := rfl
instance : SMul ℂ (Complexification H) where
  smul c u := mk (c.re • u.1 - c.im • u.2) (c.re • u.2 + c.im • u.1)
@[simp] lemma smul_fst (c : ℂ) (u : Complexification H) :
    (c • u).1 = c.re • u.1 - c.im • u.2 := rfl
@[simp] lemma smul_snd (c : ℂ) (u : Complexification H) :
    (c • u).2 = c.re • u.2 + c.im • u.1 := rfl
@[simp] lemma add_fst (u v : Complexification H) : (u + v).1 = u.1 + v.1 := rfl
@[simp] lemma add_snd (u v : Complexification H) : (u + v).2 = u.2 + v.2 := rfl
@[simp] lemma zero_fst : (0 : Complexification H).1 = 0 := rfl
@[simp] lemma zero_snd : (0 : Complexification H).2 = 0 := rfl
@[simp] lemma sub_fst (u v : Complexification H) : (u - v).1 = u.1 - v.1 := rfl
@[simp] lemma sub_snd (u v : Complexification H) : (u - v).2 = u.2 - v.2 := rfl
instance : Module ℂ (Complexification H) where
  one_smul u := by
    apply Prod.ext <;> simp only [smul_fst, smul_snd, Complex.one_re, Complex.one_im] <;> module
  mul_smul c d u := by
    apply Prod.ext <;>
      simp only [smul_fst, smul_snd, Complex.mul_re, Complex.mul_im] <;> module
  smul_zero c := by
    apply Prod.ext <;> simp only [smul_fst, smul_snd, zero_fst, zero_snd] <;> module
  smul_add c u v := by
    apply Prod.ext <;> simp only [smul_fst, smul_snd, add_fst, add_snd] <;> module
  add_smul c d u := by
    apply Prod.ext <;>
      simp only [smul_fst, smul_snd, Complex.add_re, Complex.add_im, add_fst, add_snd] <;> module
  zero_smul u := by
    apply Prod.ext <;>
      simp only [smul_fst, smul_snd, Complex.zero_re, Complex.zero_im, zero_fst, zero_snd] <;>
      module
instance : Inner ℂ (Complexification H) where
  inner u v := ⟨inner ℝ u.1 v.1 + inner ℝ u.2 v.2, inner ℝ u.1 v.2 - inner ℝ u.2 v.1⟩
@[simp] lemma inner_re (u v : Complexification H) :
    (inner ℂ u v).re = inner ℝ u.1 v.1 + inner ℝ u.2 v.2 := rfl
@[simp] lemma inner_im (u v : Complexification H) :
    (inner ℂ u v).im = inner ℝ u.1 v.2 - inner ℝ u.2 v.1 := rfl
@[reducible] def core : InnerProductSpace.Core ℂ (Complexification H) where
  inner u v := inner ℂ u v
  conj_inner_symm u v := by
    apply Complex.ext
    all_goals
      simp only [Complex.conj_re, Complex.conj_im, inner_re, inner_im,
        real_inner_comm u.1 v.1, real_inner_comm u.2 v.2,
        real_inner_comm v.1 u.2, real_inner_comm v.2 u.1]
    all_goals ring
  re_inner_nonneg u := by
    rw [RCLike.re_to_complex, inner_re]
    exact add_nonneg real_inner_self_nonneg real_inner_self_nonneg
  add_left u v w := by
    apply Complex.ext <;>
      simp only [inner_re, inner_im, Complex.add_re, Complex.add_im, add_fst, add_snd,
        inner_add_left] <;> ring
  smul_left u v c := by
    apply Complex.ext <;>
      simp only [inner_re, inner_im, smul_fst, smul_snd, inner_sub_left, inner_add_left,
        real_inner_smul_left, Complex.mul_re, Complex.mul_im, Complex.conj_re, Complex.conj_im] <;>
      ring
  definite u h := by
    have hre : inner ℝ u.1 u.1 + inner ℝ u.2 u.2 = 0 := by
      have := congrArg Complex.re h; simpa using this
    have n1 : (0 : ℝ) ≤ inner ℝ u.1 u.1 := real_inner_self_nonneg
    have n2 : (0 : ℝ) ≤ inner ℝ u.2 u.2 := real_inner_self_nonneg
    have h1 : inner ℝ u.1 u.1 = 0 := le_antisymm (by linarith) n1
    have h2 : inner ℝ u.2 u.2 = 0 := le_antisymm (by linarith) n2
    exact Prod.ext ((inner_self_eq_zero (𝕜 := ℝ)).mp h1) ((inner_self_eq_zero (𝕜 := ℝ)).mp h2)
instance : NormedAddCommGroup (Complexification H) :=
  @InnerProductSpace.Core.toNormedAddCommGroup ℂ (Complexification H) _ _ _ core
instance : InnerProductSpace ℂ (Complexification H) :=
  letI : InnerProductSpace.Core ℂ (Complexification H) := core
  InnerProductSpace.ofCore inferInstance
instance [Nontrivial H] : Nontrivial (Complexification H) :=
  inferInstanceAs (Nontrivial (H × H))
@[simp] lemma rsmul_fst (r : ℝ) (u : Complexification H) : (r • u).1 = r • u.1 := by
  rw [RCLike.real_smul_eq_coe_smul (K := ℂ), smul_fst]; simp
@[simp] lemma rsmul_snd (r : ℝ) (u : Complexification H) : (r • u).2 = r • u.2 := by
  rw [RCLike.real_smul_eq_coe_smul (K := ℂ), smul_snd]; simp
def ofReal (x : H) : Complexification H := mk x 0
@[simp] lemma ofReal_fst (x : H) : (ofReal x).1 = x := rfl
@[simp] lemma ofReal_snd (x : H) : (ofReal x).2 = 0 := rfl
@[simp] lemma ofReal_add (x y : H) : ofReal (x + y) = ofReal x + ofReal y := by
  apply Prod.ext <;> simp
@[simp] lemma ofReal_sub (x y : H) : ofReal (x - y) = ofReal x - ofReal y := by
  apply Prod.ext <;> simp
@[simp] lemma norm_ofReal (x : H) : ‖ofReal x‖ = ‖x‖ := by
  rw [norm_eq_sqrt_re_inner (𝕜 := ℂ)]
  simp only [RCLike.re_to_complex, inner_re, ofReal_fst, ofReal_snd, inner_zero_left, add_zero,
    real_inner_self_eq_norm_sq]
  exact Real.sqrt_sq (norm_nonneg x)
def ofRealLi : H →ₗᵢ[ℝ] Complexification H where
  toFun := ofReal
  map_add' x y := by apply Prod.ext <;> simp
  map_smul' r x := by apply Prod.ext <;> simp
  norm_map' := norm_ofReal
lemma re_inner_self (u : Complexification H) :
    (inner ℂ u u).re = ‖u.1‖ ^ 2 + ‖u.2‖ ^ 2 := by
  simp only [inner_re, real_inner_self_eq_norm_sq]
lemma norm_sq_eq (u : Complexification H) : ‖u‖ ^ 2 = ‖u.1‖ ^ 2 + ‖u.2‖ ^ 2 := by
  rw [norm_eq_sqrt_re_inner (𝕜 := ℂ), RCLike.re_to_complex, re_inner_self,
    Real.sq_sqrt (by positivity)]
lemma norm_fst_le (u : Complexification H) : ‖u.1‖ ≤ ‖u‖ := by
  nlinarith [norm_sq_eq u, norm_nonneg u, norm_nonneg u.1, norm_nonneg u.2, sq_nonneg ‖u.2‖]
lemma norm_snd_le (u : Complexification H) : ‖u.2‖ ≤ ‖u‖ := by
  nlinarith [norm_sq_eq u, norm_nonneg u, norm_nonneg u.1, norm_nonneg u.2, sq_nonneg ‖u.1‖]
lemma norm_le_add (u : Complexification H) : ‖u‖ ≤ ‖u.1‖ + ‖u.2‖ := by
  nlinarith [norm_sq_eq u, norm_nonneg u, norm_nonneg u.1, norm_nonneg u.2,
    mul_nonneg (norm_nonneg u.1) (norm_nonneg u.2)]
def fstₗ : Complexification H →ₗ[ℝ] H where
  toFun u := u.1
  map_add' := add_fst
  map_smul' r u := rsmul_fst r u
def fstL : Complexification H →L[ℝ] H :=
  fstₗ.mkContinuous 1 fun u => by rw [one_mul]; exact norm_fst_le u
@[simp] lemma fstL_apply (u : Complexification H) : fstL u = u.1 := rfl
instance [CompleteSpace H] : CompleteSpace (Complexification H) := by
  refine Metric.complete_of_cauchySeq_tendsto fun f hf => ?_
  have lip1 : LipschitzWith 1 (fun u : Complexification H => u.1) :=
    LipschitzWith.of_dist_le_mul fun u v => by
      simp only [dist_eq_norm, NNReal.coe_one, one_mul]; exact norm_fst_le (u - v)
  have lip2 : LipschitzWith 1 (fun u : Complexification H => u.2) :=
    LipschitzWith.of_dist_le_mul fun u v => by
      simp only [dist_eq_norm, NNReal.coe_one, one_mul]; exact norm_snd_le (u - v)
  obtain ⟨a, ha⟩ := cauchySeq_tendsto_of_complete (lip1.uniformContinuous.comp_cauchySeq hf)
  obtain ⟨b, hb⟩ := cauchySeq_tendsto_of_complete (lip2.uniformContinuous.comp_cauchySeq hf)
  refine ⟨mk a b, ?_⟩
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have h1 : Tendsto (fun n => ‖(f n).1 - a‖) atTop (𝓝 0) := tendsto_iff_norm_sub_tendsto_zero.mp ha
  have h2 : Tendsto (fun n => ‖(f n).2 - b‖) atTop (𝓝 0) := tendsto_iff_norm_sub_tendsto_zero.mp hb
  refine squeeze_zero (fun n => norm_nonneg _) (fun n => ?_) (by simpa using h1.add h2)
  exact norm_le_add _
def conj (u : Complexification H) : Complexification H := mk u.1 (-u.2)
@[simp] lemma conj_fst (u : Complexification H) : (conj u).1 = u.1 := rfl
@[simp] lemma conj_snd (u : Complexification H) : (conj u).2 = -u.2 := rfl
@[simp] lemma conj_conj (u : Complexification H) : conj (conj u) = u := by
  apply Prod.ext <;> simp
@[simp] lemma conj_ofReal (x : H) : conj (ofReal x) = ofReal x := by
  apply Prod.ext <;> simp
lemma conj_add (u v : Complexification H) : conj (u + v) = conj u + conj v := by
  apply Prod.ext <;> simp only [conj_fst, conj_snd, add_fst, add_snd, neg_add]
@[simp] lemma norm_conj (u : Complexification H) : ‖conj u‖ = ‖u‖ := by
  have h1 := norm_sq_eq (conj u)
  have h2 := norm_sq_eq u
  simp only [conj_fst, conj_snd, norm_neg] at h1
  have hsq : ‖conj u‖ ^ 2 = ‖u‖ ^ 2 := by rw [h1, h2]
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hsq
def conjLi : Complexification H →ₗᵢ[ℝ] Complexification H where
  toFun := conj
  map_add' := conj_add
  map_smul' r u := by apply Prod.ext <;> simp [smul_neg]
  norm_map' := norm_conj
def conjL : Complexification H →L[ℝ] Complexification H := conjLi.toContinuousLinearMap
@[simp] lemma conjL_apply (u : Complexification H) : conjL u = conj u := rfl
section Operator
variable {H₁ H₂ : Type*}
  [NormedAddCommGroup H₁] [InnerProductSpace ℝ H₁]
  [NormedAddCommGroup H₂] [InnerProductSpace ℝ H₂]
def complexifyₗ (S : H₁ →L[ℝ] H₂) : Complexification H₁ →ₗ[ℂ] Complexification H₂ where
  toFun u := mk (S u.1) (S u.2)
  map_add' u v := by apply Prod.ext <;> simp
  map_smul' c u := by apply Prod.ext <;> simp [map_sub, map_smul]
@[simp] lemma complexifyₗ_fst (S : H₁ →L[ℝ] H₂) (u : Complexification H₁) :
    (complexifyₗ S u).1 = S u.1 := rfl
@[simp] lemma complexifyₗ_snd (S : H₁ →L[ℝ] H₂) (u : Complexification H₁) :
    (complexifyₗ S u).2 = S u.2 := rfl
lemma norm_complexifyₗ_le (S : H₁ →L[ℝ] H₂) (u : Complexification H₁) :
    ‖complexifyₗ S u‖ ≤ ‖S‖ * ‖u‖ := by
  refine le_of_sq_le_sq ?_ (mul_nonneg (norm_nonneg S) (norm_nonneg u))
  rw [norm_sq_eq (complexifyₗ S u), mul_pow, norm_sq_eq u, mul_add]
  simp only [complexifyₗ_fst, complexifyₗ_snd, ← mul_pow]
  gcongr <;> exact S.le_opNorm _
def complexify (S : H₁ →L[ℝ] H₂) : Complexification H₁ →L[ℂ] Complexification H₂ :=
  (complexifyₗ S).mkContinuous ‖S‖ (norm_complexifyₗ_le S)
section Adjoint
variable [CompleteSpace H₁] [CompleteSpace H₂]
end Adjoint
end Operator
end Complexification
end SNumbers



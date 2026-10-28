-- Prove2me | solution 1 for ADH2015.correctsErasure_iff_allRep
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T14:44:32.296978+00:00
-- url     : https://prove2.me/submissions/663cae0a-1e73-4925-a2ad-19840b74d381

import Mathlib
import Definitions.Def_ADH2015_defs

open Matrix
open scoped Kronecker
open ADH2015
open scoped ComplexOrder

/-- reshape a vector on `e × ē` into an `e × ē` matrix -/
noncomputable def adhEMat {e ē : Type*} : (e × ē → ℂ) →ₗ[ℂ] Matrix e ē ℂ where
  toFun v := Matrix.of fun i a => v (i, a)
  map_add' _ _ := by ext; simp
  map_smul' _ _ := by ext; simp

lemma adhE_ginv {e : Type*} [Fintype e] [DecidableEq e] (σ : Matrix e e ℂ) :
    ∃ S : Matrix e e ℂ, σ * S * σ = σ := by
  set f := Matrix.toLin' σ
  obtain ⟨g, hg⟩ := f.rangeRestrict.exists_rightInverse_of_surjective (LinearMap.range_rangeRestrict f)
  obtain ⟨q, hq⟩ := (LinearMap.range f).subtype.exists_leftInverse_of_injective
    (Submodule.ker_subtype _)
  refine ⟨LinearMap.toMatrix' (g ∘ₗ q), ?_⟩
  apply Matrix.toLin'.injective
  rw [Matrix.toLin'_mul, Matrix.toLin'_mul, Matrix.toLin'_toMatrix']
  apply LinearMap.ext
  intro x
  simp only [LinearMap.comp_apply]
  have h1 : q (f x) = f.rangeRestrict x := by
    have := congrArg (fun φ => φ (f.rangeRestrict x)) hq
    simpa using this
  change f (g (q (f x))) = f x
  rw [h1]
  have h2 := congrArg (fun φ => φ (f.rangeRestrict x)) hg
  simp only [LinearMap.comp_apply, LinearMap.id_apply] at h2
  have h3 : f (g (f.rangeRestrict x)) = ((f.rangeRestrict (g (f.rangeRestrict x)) : _) :
      e → ℂ) := rfl
  rw [h3, h2]
  rfl

lemma adhE_fix {e ē : Type*} [Fintype e] [Fintype ē] (σ P : Matrix e e ℂ) (N : Matrix e ē ℂ)
    (t : ℂ) (hN : N * Nᴴ = t • σ) (hP : P * σ = σ) : P * N = N := by
  have e1 : P * N * Nᴴ = t • σ := by rw [Matrix.mul_assoc, hN, Matrix.mul_smul, hP]
  have hD : (P * N - N) * (P * N - N)ᴴ = 0 := by
    have : (P * N - N) * (P * N - N)ᴴ =
        P * N * Nᴴ * Pᴴ - P * N * Nᴴ - N * Nᴴ * Pᴴ + N * Nᴴ := by
      simp only [conjTranspose_sub, conjTranspose_mul, Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_assoc]
      abel
    rw [this, e1, hN, Matrix.smul_mul]
    abel
  rw [self_mul_conjTranspose_eq_zero, sub_eq_zero] at hD
  exact hD

lemma adhE_kron {e ē : Type*} [Fintype e] [Fintype ē] [DecidableEq e]
    (Y : Matrix ē ē ℂ) (v : e × ē → ℂ) :
    ((1 : Matrix e e ℂ) ⊗ₖ Y) *ᵥ v = fun p => (adhEMat v * Yᵀ) p.1 p.2 := by
  funext ⟨i, b⟩
  simp [mulVec, dotProduct, kronecker_apply, one_apply, Fintype.sum_prod_type, Matrix.mul_apply,
    adhEMat, ite_mul, mul_comm]

lemma adhE_adj {n : Type*} [Fintype n] (A : Matrix n n ℂ) (x y : n → ℂ) :
    star (A *ᵥ x) ⬝ᵥ y = star x ⬝ᵥ (Aᴴ *ᵥ y) := by
  rw [star_mulVec, dotProduct_mulVec]

lemma adhE_basis {e ē : Type*} [Fintype e] [Fintype ē] (C : Submodule ℂ (e × ē → ℂ)) :
    ∃ n : ℕ, ∃ u : Fin n → (e × ē → ℂ), (∀ k, u k ∈ C) ∧
      ∀ v ∈ C, v = ∑ k, (star (u k) ⬝ᵥ v) • u k := by
  let K : Submodule ℂ (EuclideanSpace ℂ (e × ē)) :=
    C.comap (WithLp.linearEquiv 2 ℂ (e × ē → ℂ)).toLinearMap
  let b := stdOrthonormalBasis ℂ K
  refine ⟨_, fun k => WithLp.ofLp ((b k : K) : EuclideanSpace ℂ (e × ē)), fun k => (b k).2, ?_⟩
  intro v hv
  have hmem : (WithLp.toLp 2 v : EuclideanSpace ℂ (e × ē)) ∈ K := hv
  have h := b.sum_repr' ⟨WithLp.toLp 2 v, hmem⟩
  have h2 := congrArg (fun z : K => WithLp.ofLp (z : EuclideanSpace ℂ (e × ē))) h
  simp only [Submodule.coe_sum, Submodule.coe_smul, WithLp.ofLp_sum, WithLp.ofLp_smul] at h2
  conv_lhs => rw [← h2]
  refine Finset.sum_congr rfl fun k _ => ?_
  congr 1
  rw [Submodule.coe_inner, EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm]

theorem solution {e ē : Type*} [Fintype e] [Fintype ē] [DecidableEq e]
    [DecidableEq ē] (C : Submodule ℂ (e × ē → ℂ)) :
    CorrectsErasureOfE C ↔ ∀ O : Matrix (e × ē) (e × ē) ℂ, ActsWithin C O → HasRepOnBar C O := by
  constructor
  · intro hE O hO
    -- the reduced-operator relation
    have key : ∃ σ : Matrix e e ℂ, ∀ v ∈ C, ∀ w ∈ C,
        adhEMat v * (adhEMat w)ᴴ = (star w ⬝ᵥ v) • σ := by
      have hc : ∀ j i : e, ∃ c : ℂ, ∀ v ∈ C, ∀ w ∈ C,
          star w ⬝ᵥ ((Matrix.single j i (1 : ℂ) ⊗ₖ (1 : Matrix ē ē ℂ)) *ᵥ v) =
            c * (star w ⬝ᵥ v) := fun j i => hE _
      choose c hc using hc
      refine ⟨Matrix.of fun i j => c j i, fun v hv w hw => ?_⟩
      ext i j
      have := hc j i v hv w hw
      simp [mulVec, dotProduct, kronecker_apply, one_apply, Fintype.sum_prod_type,
        Matrix.single_apply, ite_mul, ite_and] at this
      simp [Matrix.mul_apply, adhEMat, dotProduct, Fintype.sum_prod_type]
      rw [mul_comm (∑ x, ∑ y, _), ← this]
      exact Finset.sum_congr rfl fun a _ => mul_comm _ _
    obtain ⟨σ, hσ⟩ := key
    obtain ⟨S, hS⟩ := adhE_ginv σ
    obtain ⟨n, u, huC, hspan⟩ := adhE_basis C
    have fix1 : ∀ w ∈ C, σ * S * adhEMat w = adhEMat w := fun w hw =>
      adhE_fix σ (σ * S) _ _ (hσ w hw w hw) hS
    have fix2 : ∀ w ∈ C, σ * Sᴴ * adhEMat w = adhEMat w := by
      intro w hw
      by_cases ht : star w ⬝ᵥ w = 0
      · have h0 : adhEMat w * (adhEMat w)ᴴ = 0 := by rw [hσ w hw w hw, ht, zero_smul]
        rw [self_mul_conjTranspose_eq_zero] at h0
        rw [h0, Matrix.mul_zero]
      · have hH : σᴴ = σ := by
          have h1 := congrArg conjTranspose (hσ w hw w hw)
          rw [conjTranspose_mul, conjTranspose_conjTranspose, hσ w hw w hw,
            conjTranspose_smul] at h1
          have hst : star (star w ⬝ᵥ w) = star w ⬝ᵥ w := by
            rw [← star_dotProduct]
          rw [hst] at h1
          exact (smul_right_injective _ ht h1).symm
        refine adhE_fix σ (σ * Sᴴ) _ _ (hσ w hw w hw) ?_
        have : σ * Sᴴ * σ = (σᴴ * S * σᴴ)ᴴ := by
          simp only [conjTranspose_mul, conjTranspose_conjTranspose, Matrix.mul_assoc]
        rw [this, hH, hS, hH]
    set Z : Matrix ē ē ℂ := ∑ k, (adhEMat (u k))ᴴ * S * adhEMat (O *ᵥ u k) with hZ
    refine ⟨Zᵀ, fun v hv => ⟨?_, ?_⟩⟩
    · have hm : adhEMat v * Z = adhEMat (O *ᵥ v) := by
        calc adhEMat v * Z
            = ∑ k, (star (u k) ⬝ᵥ v) • adhEMat (O *ᵥ u k) := by
              rw [hZ, Matrix.mul_sum]
              refine Finset.sum_congr rfl fun k _ => ?_
              rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hσ v hv (u k) (huC k),
                Matrix.smul_mul, Matrix.smul_mul, fix1 _ ((hO _ (huC k)).1)]
          _ = adhEMat (O *ᵥ v) := by
              conv_rhs => rw [hspan v hv]
              rw [Matrix.mulVec_sum, map_sum]
              refine Finset.sum_congr rfl fun k _ => ?_
              rw [Matrix.mulVec_smul, map_smul]
      rw [adhE_kron, transpose_transpose, hm]
      rfl
    · have hZH : Zᴴ = ∑ k, (adhEMat (O *ᵥ u k))ᴴ * Sᴴ * adhEMat (u k) := by
        rw [hZ, conjTranspose_sum]
        refine Finset.sum_congr rfl fun k _ => ?_
        simp only [conjTranspose_mul, conjTranspose_conjTranspose, Matrix.mul_assoc]
      have hm : adhEMat v * Zᴴ = adhEMat (Oᴴ *ᵥ v) := by
        calc adhEMat v * Zᴴ
            = ∑ k, (star (u k) ⬝ᵥ (Oᴴ *ᵥ v)) • adhEMat (u k) := by
              rw [hZH, Matrix.mul_sum]
              refine Finset.sum_congr rfl fun k _ => ?_
              rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hσ v hv _ ((hO _ (huC k)).1),
                Matrix.smul_mul, Matrix.smul_mul, fix2 _ (huC k), adhE_adj]
          _ = adhEMat (Oᴴ *ᵥ v) := by
              conv_rhs => rw [hspan _ (hO v hv).2]
              rw [map_sum]
              refine Finset.sum_congr rfl fun k _ => ?_
              rw [map_smul]
      have hT : (Zᵀ)ᴴ = (Zᴴ)ᵀ := by ext; simp
      rw [conjTranspose_kronecker, conjTranspose_one, hT, adhE_kron, transpose_transpose, hm]
      rfl
  · intro hR X
    by_cases hC : ∃ f ∈ C, f ≠ 0
    · obtain ⟨f, hf, hf0⟩ := hC
      have ht : star f ⬝ᵥ f ≠ 0 := fun h => hf0 (dotProduct_star_self_eq_zero.1 h)
      refine ⟨(star f ⬝ᵥ ((X ⊗ₖ (1 : Matrix ē ē ℂ)) *ᵥ f)) / (star f ⬝ᵥ f),
        fun v hv w hw => ?_⟩
      have hOx : ∀ x, vecMulVec v (star f) *ᵥ x = (star f ⬝ᵥ x) • v := by
        intro x; rw [vecMulVec_mulVec, op_smul_eq_smul]
      have hOHx : ∀ x, (vecMulVec v (star f))ᴴ *ᵥ x = (star v ⬝ᵥ x) • f := by
        intro x; rw [conjTranspose_vecMulVec, star_star, vecMulVec_mulVec, op_smul_eq_smul]
      obtain ⟨Y, hY⟩ := hR (vecMulVec v (star f)) (fun x hx => by
        rw [hOx, hOHx]; exact ⟨C.smul_mem _ hv, C.smul_mem _ hf⟩)
      have h1 : ((1 : Matrix e e ℂ) ⊗ₖ Y) *ᵥ f = (star f ⬝ᵥ f) • v := by
        rw [(hY f hf).1, hOx]
      have h2 : ((1 : Matrix e e ℂ) ⊗ₖ Y)ᴴ *ᵥ w = (star v ⬝ᵥ w) • f := by
        rw [(hY w hw).2, hOHx]
      have hcomm : (X ⊗ₖ (1 : Matrix ē ē ℂ)) *ᵥ (((1 : Matrix e e ℂ) ⊗ₖ Y) *ᵥ f) =
          ((1 : Matrix e e ℂ) ⊗ₖ Y) *ᵥ ((X ⊗ₖ (1 : Matrix ē ē ℂ)) *ᵥ f) := by
        rw [mulVec_mulVec, mulVec_mulVec, ← mul_kronecker_mul, ← mul_kronecker_mul,
          one_mul, mul_one, one_mul, mul_one]
      have hmain : (star f ⬝ᵥ f) * (star w ⬝ᵥ ((X ⊗ₖ (1 : Matrix ē ē ℂ)) *ᵥ v)) =
          (star w ⬝ᵥ v) * (star f ⬝ᵥ ((X ⊗ₖ (1 : Matrix ē ē ℂ)) *ᵥ f)) := by
        rw [← smul_eq_mul (star f ⬝ᵥ f), ← dotProduct_smul, ← mulVec_smul, ← h1, hcomm]
        have := adhE_adj (((1 : Matrix e e ℂ) ⊗ₖ Y)ᴴ) w ((X ⊗ₖ (1 : Matrix ē ē ℂ)) *ᵥ f)
        rw [conjTranspose_conjTranspose] at this
        rw [← this, h2, star_smul, smul_dotProduct, smul_eq_mul, ← star_dotProduct]
      field_simp
      linear_combination hmain
    · push_neg at hC
      refine ⟨0, fun v hv w hw => ?_⟩
      rw [hC v hv]
      simp

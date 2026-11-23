-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsSplittingSplitOm
-- name    : Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsSplittingSplitOm
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T19:24:32.518016+00:00
-- url     : https://prove2.me/theorems/cadfdf26-0d21-4503-8f6d-5de36d17b44f
-- title:
--   Is Splitting Split Om
-- statement:
--   Definitions and structural lemmas for Is Splitting Split Om, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IsSplittingSplitOm.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HilbertNinetyQuotientHomEqIff
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open scoped NNReal Kronecker
namespace GlobalTheory.WeilM
variable {R : Type} [CommRing R]
variable (R) in

def swapA : R × R →ₐ[R] R × R := { (RingEquiv.prodComm : R × R ≃+* R × R).toRingHom with commutes' := fun _ => rfl }
@[simp] theorem swapA_apply (x : R × R) : swapA R x = (x.2, x.1) := rfl
def complexDarboux : Darboux (R := ℝ) (symp (Complex.conjAe : ℂ →ₐ[ℝ] ℂ) Complex.I (1 : Matrix Unit Unit ℂ)
    (1 : Matrix Unit Unit ℂ)) Unit where
  e :=
    { toFun := fun x => (fun _ => 2 * (x () ()).re, fun _ => (x () ()).im)
      invFun := fun v => of fun _ _ => ⟨v.1 () / 2, v.2 ()⟩
      map_add' := fun x y => by ext <;> simp [mul_add]
      map_smul' := fun a x => by ext <;> simp [mul_left_comm]
      left_inv := fun x => by ext; apply Complex.ext <;> simp
      right_inv := fun v => by ext <;> simp [mul_div_cancel₀] }
  form w w' := by
    show _ = (fun _ : Unit => 2 * (w () ()).re) ⬝ᵥ (fun _ => (w' () ()).im) -
      (fun _ : Unit => 2 * (w' () ()).re) ⬝ᵥ (fun _ => (w () ()).im)
    simp [symp, hTens, Algebra.trace_complex_apply, dotProduct]
    ring
variable {α β κ : Type}
def flat (σ : κ ≃ α × β) : Matrix α β R ≃ₗ[R] (κ → R) where
  toFun X k := X (σ k).1 (σ k).2
  invFun u := of fun i j => u (σ.symm (i, j))
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv X := by ext i j; simp
  right_inv u := by ext k; simp
theorem flat_apply (σ : κ ≃ α × β) (X : Matrix α β R) (k : κ) : flat σ X k = X (σ k).1 (σ k).2 := rfl
abbrev cmp₁ {m n : Type} (X : Matrix m n (R × R)) : Matrix m n R := X.map (RingHom.fst R R)
abbrev cmp₂ {m n : Type} (X : Matrix m n (R × R)) : Matrix m n R := X.map (RingHom.snd R R)
variable [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype κ]
omit [DecidableEq α] [DecidableEq β] in
theorem flat_dot (σ : κ ≃ α × β) (X Y : Matrix α β R) : flat σ X ⬝ᵥ flat σ Y = trace (X * Yᵀ) := by
  simp only [dotProduct, flat_apply, trace, diag_apply, mul_apply, transpose_apply]
  rw [← Fintype.sum_prod_type']
  exact Equiv.sum_comp σ (fun p => X p.1 p.2 * Y p.1 p.2)
theorem IsHerm.isUnit_cmp₁ {J : Matrix α α (R × R)} (h : IsHerm (swapA R) J) : IsUnit (cmp₁ J).det := by
  have hu := h.2.map (RingHom.fst R R)
  rwa [RingHom.map_det] at hu
theorem IsHerm.snd_eq {J : Matrix α α (R × R)} (h : IsHerm (swapA R) J) (i j : α) : (J i j).2 = (J j i).1 := by
  have hc := congrArg Prod.snd (h.1 i j)
  rw [swapA_apply] at hc
  exact hc.symm
def splitDarboux {JA : Matrix α α (R × R)} {JB : Matrix β β (R × R)} (hA : IsHerm (swapA R) JA)
    (hB : IsHerm (swapA R) JB) (σ : κ ≃ α × β) : Darboux (R := R) (symp (swapA R) (1, -1) JA JB) κ where
  e :=
    { toFun := fun x => (flat σ (cmp₁ x), flat σ (cmp₁ JA * cmp₂ x * (cmp₁ JB)ᵀ))
      invFun := fun v => of fun i j =>
        ((flat σ).symm v.1 i j, ((cmp₁ JA)⁻¹ * (flat σ).symm v.2 * ((cmp₁ JB)⁻¹)ᵀ : Matrix α β R) i j)
      map_add' := fun x y => by
        rw [Prod.mk_add_mk, ← map_add, ← map_add, ← Matrix.add_mul, ← Matrix.mul_add]; rfl
      map_smul' := fun a x => by
        rw [RingHom.id_apply, Prod.smul_mk, ← map_smul, ← map_smul, ← Matrix.smul_mul, ← Matrix.mul_smul]; rfl
      left_inv := fun x => by
        simp only [LinearEquiv.symm_apply_apply, Matrix.mul_assoc, ← transpose_mul,
          nonsing_inv_mul _ hB.isUnit_cmp₁, transpose_one, Matrix.mul_one,
          nonsing_inv_mul_cancel_left _ _ hA.isUnit_cmp₁]
        rfl
      right_inv := fun v => by
        show (flat σ ((flat σ).symm v.1), flat σ (cmp₁ JA * ((cmp₁ JA)⁻¹ * (flat σ).symm v.2 * ((cmp₁ JB)⁻¹)ᵀ) *
          (cmp₁ JB)ᵀ)) = v
        simp only [Matrix.mul_assoc, ← transpose_mul,
          mul_nonsing_inv _ hB.isUnit_cmp₁, transpose_one, Matrix.mul_one,
          mul_nonsing_inv_cancel_left _ _ hA.isUnit_cmp₁, LinearEquiv.apply_symm_apply] }
  form w w' := by
    show _ = flat σ (cmp₁ w) ⬝ᵥ flat σ (cmp₁ JA * cmp₂ w' * (cmp₁ JB)ᵀ) -
      flat σ (cmp₁ w') ⬝ᵥ flat σ (cmp₁ JA * cmp₂ w * (cmp₁ JB)ᵀ)
    have key : ∀ (X Y : Matrix α β R), trace (X * (cmp₁ JA * Y * (cmp₁ JB)ᵀ)ᵀ) =
        ∑ i, ∑ j, ∑ k, ∑ l, X i j * (JA i k).1 * (JB j l).1 * Y k l := by
      intro X Y
      simp only [trace, diag_apply, mul_apply, transpose_apply, Finset.mul_sum, Finset.sum_mul, map_apply,
        RingHom.coe_fst]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => Finset.sum_comm.trans ?_
      exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => by ring
    rw [flat_dot, flat_dot, key, key]
    simp only [symp, hTens, Algebra.trace_prod_apply, Algebra.trace_self_apply, Prod.fst_mul, Prod.snd_mul,
      Prod.fst_sum, Prod.snd_sum, swapA_apply, one_mul, neg_mul, map_apply, RingHom.coe_fst, RingHom.coe_snd,
      hA.snd_eq, hB.snd_eq, sub_eq_add_neg]
    congr 2
    have s4 : ∀ f : α → β → α → β → R, ∑ i, ∑ j, ∑ k, ∑ l, f i j k l = ∑ k, ∑ l, ∑ i, ∑ j, f i j k l := fun f => by
      have := Finset.sum_comm (s := Finset.univ) (t := Finset.univ) (f := fun p q : α × β => f p.1 p.2 q.1 q.2)
      simpa only [Fintype.sum_prod_type] using this
    rw [s4]
    exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ =>
      Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
def ugFst (J : Matrix β β (R × R)) : UG (swapA R) J →* GL β R :=
  (GeneralLinearGroup.map (RingHom.fst R R)).comp (UG (swapA R) J).subtype
def substB (σ : κ ≃ α × β) : GL β R →* Module.End ℂ ((κ → R) → ℂ) where
  toFun h := LinearMap.funLeft ℂ ℂ fun u => flat σ ((flat σ).symm u * (h⁻¹).valᵀ)
  map_one' := by ext φ u; simp
  map_mul' h h' := by ext φ u; simp [Matrix.mul_assoc]
def splitChar (m : Rˣ →* ℝ≥0) (χ : (R × R)ˣ →* Circle) (a : ℕ) : Rˣ →* ℂ where
  toFun t := (χ (Units.map (MonoidHom.inl R R) t) : ℂ) * (((m t : ℝ) ^ (-(a : ℝ) / 2) : ℝ) : ℂ)
  map_one' := by simp
  map_mul' s t := by
    simp only [map_mul, Circle.coe_mul, NNReal.coe_mul, Real.mul_rpow (NNReal.coe_nonneg _) (NNReal.coe_nonneg _),
      Complex.ofReal_mul]
    ring
def splitOm (m : Rˣ →* ℝ≥0) (χ : (R × R)ˣ →* Circle) (J : Matrix β β (R × R)) (σ : κ ≃ α × β) :
    UG (swapA R) J →* Module.End ℂ ((κ → R) → ℂ) where
  toFun h := splitChar m χ (Fintype.card α) (GeneralLinearGroup.det (ugFst J h)) • substB σ (ugFst J h)
  map_one' := by simp
  map_mul' h h' := by simp only [map_mul, smul_mul_smul_comm]
theorem IsHerm.dbl {E : Type} [CommRing E] [Algebra R E] {c : E →ₐ[R] E} {J : Matrix β β E} (h : IsHerm c J) :
    IsHerm c (dbl J) := by
  refine ⟨fun i j => ?_, ?_⟩
  · change c (Matrix.fromBlocks J 0 0 (-J) j i) = Matrix.fromBlocks J 0 0 (-J) i j
    rcases i with i | i <;> rcases j with j | j <;> simp [h.1]
  · change IsUnit (Matrix.fromBlocks J 0 0 (-J)).det
    rw [Matrix.det_fromBlocks_zero₂₁, Matrix.det_neg]
    exact h.2.mul ((isUnit_neg_one.pow _).mul h.2)
def dblNum (σ : κ ≃ α × β) : κ ⊕ κ ≃ α × (β ⊕ β) := (σ.sumCongr σ).trans (Equiv.prodSumDistrib α β β).symm
end GlobalTheory.WeilM
end



-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicIndexEquality_InertGen
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicIndexEquality_InertGen
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T20:32:22.438808+00:00
-- url     : https://prove2.me/theorems/aa900c5b-74f3-4cfd-8ff0-125863872ec9
-- title:
--   Inert Gen
-- statement:
--   Definitions and structural lemmas for Inert Gen, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdelicIndexEquality/InertGen.lean

import Definitions.Def_Formalism_SatakeDualWeyl_Statement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace PI.UnitaryGroupMassFormula.AdIndexEq.QRG
open Matrix Formalism.UG
variable {K : Type} [Field K] {n : ℕ}
def H (σ : K →+* K) (J : Matrix (Fin n) (Fin n) K) (x y : Fin n → K) : K :=
  (σ ∘ x) ⬝ᵥ (J *ᵥ y)
section Form
variable (σ : K →+* K) (J : Matrix (Fin n) (Fin n) K)
theorem H_add_right (x y z : Fin n → K) : H σ J x (y + z) = H σ J x y + H σ J x z := by
  simp [H, Matrix.mulVec_add, dotProduct_add]
theorem H_smul_right (x y : Fin n → K) (c : K) : H σ J x (c • y) = c * H σ J x y := by
  simp [H, Matrix.mulVec_smul, dotProduct_smul]
theorem comp_add' (x y : Fin n → K) : σ ∘ (x + y) = σ ∘ x + σ ∘ y := by
  funext i
  simp
theorem comp_smul' (c : K) (x : Fin n → K) : σ ∘ (c • x) = σ c • (σ ∘ x) := by
  funext i
  simp
theorem H_add_left (x y z : Fin n → K) : H σ J (x + y) z = H σ J x z + H σ J y z := by
  unfold H
  rw [comp_add' σ, add_dotProduct]
theorem H_smul_left (x y : Fin n → K) (c : K) : H σ J (c • x) y = σ c * H σ J x y := by
  unfold H
  rw [comp_smul' σ, smul_dotProduct, smul_eq_mul]
theorem H_symm (hσ : ∀ a, σ (σ a) = a) (hJ : cT σ J = J) (x y : Fin n → K) :
    H σ J y x = σ (H σ J x y) := by
  have hJ' : ∀ i j, σ (J i j) = J j i := by
    intro i j
    have h := congrFun (congrFun hJ j) i
    simpa [cT] using h
  unfold H
  simp only [dotProduct, Matrix.mulVec, Function.comp_apply, map_sum, map_mul, hσ, hJ',
    Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => by ring))
theorem H_mulVec (M : Matrix (Fin n) (Fin n) K) (x y : Fin n → K) :
    H σ J (M *ᵥ x) (M *ᵥ y) = H σ (cT σ M * J * M) x y := by
  have e1 : σ ∘ (M *ᵥ x) = (M.map σ) *ᵥ (σ ∘ x) := by
    funext i
    simp [Matrix.mulVec, dotProduct, map_sum]
  unfold H
  rw [e1]
  conv_rhs => rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec]
  simp only [cT, Matrix.vecMul_transpose]
theorem H_single (A : Matrix (Fin n) (Fin n) K) (i j : Fin n) :
    H σ A (Pi.single i 1) (Pi.single j 1) = A i j := by
  simp [H, dotProduct, Matrix.mulVec, Pi.single_apply, apply_ite σ]
theorem mem_UJ_of (g : GL (Fin n) K)
    (h : ∀ x y, H σ J ((g : Matrix (Fin n) (Fin n) K) *ᵥ x) ((g : Matrix (Fin n) (Fin n) K) *ᵥ y) =
      H σ J x y) : g ∈ UJ σ J := by
  show cT σ (g : Matrix (Fin n) (Fin n) K) * J * (g : Matrix (Fin n) (Fin n) K) = J
  ext i j
  have h1 := h (Pi.single i 1) (Pi.single j 1)
  rw [H_mulVec, H_single, H_single] at h1
  exact h1
end Form
section Refl
variable (σ : K →+* K) (J : Matrix (Fin n) (Fin n) K)
def Pm (a : Fin n → K) : Matrix (Fin n) (Fin n) K :=
  (H σ J a a)⁻¹ • vecMulVec a ((σ ∘ a) ᵥ* J)
theorem Pm_mulVec (a z : Fin n → K) : Pm σ J a *ᵥ z = ((H σ J a a)⁻¹ * H σ J a z) • a := by
  have hb : ((σ ∘ a) ᵥ* J) ⬝ᵥ z = H σ J a z := by
    unfold H
    rw [Matrix.dotProduct_mulVec]
  funext k
  rw [← hb]
  simp only [Pm, Matrix.mulVec, dotProduct, Matrix.smul_apply, vecMulVec_apply, smul_eq_mul,
    Pi.smul_apply, Finset.mul_sum, Finset.sum_mul]
  exact Finset.sum_congr rfl (fun j _ => by ring)
theorem Pm_idem (a : Fin n → K) (ha : H σ J a a ≠ 0) : Pm σ J a * Pm σ J a = Pm σ J a := by
  have key : ∀ v, (Pm σ J a * Pm σ J a) *ᵥ v = Pm σ J a *ᵥ v := by
    intro v
    rw [← Matrix.mulVec_mulVec, Pm_mulVec σ J a v, Matrix.mulVec_smul, Pm_mulVec σ J a a,
      inv_mul_cancel₀ ha, one_smul]
  ext i j
  have h1 := congrFun (key (Pi.single j 1)) i
  simpa [Matrix.mulVec_single_one] using h1
def Rm (a : Fin n → K) (α : K) : Matrix (Fin n) (Fin n) K := 1 + (α - 1) • Pm σ J a
theorem Rm_mulVec (a z : Fin n → K) (α : K) :
    Rm σ J a α *ᵥ z = z + ((α - 1) * ((H σ J a a)⁻¹ * H σ J a z)) • a := by
  have e : ((α - 1) • Pm σ J a) *ᵥ z = (α - 1) • (Pm σ J a *ᵥ z) := by
    funext k
    simp [Matrix.mulVec, dotProduct, Finset.mul_sum, mul_assoc]
  rw [Rm, Matrix.add_mulVec, Matrix.one_mulVec, e, Pm_mulVec, smul_smul]
theorem one_add_smul_mul (P : Matrix (Fin n) (Fin n) K) (hP : P * P = P) (u w : K) :
    (1 + u • P) * (1 + w • P) = 1 + (u + w + u * w) • P := by
  simp only [add_mul, mul_add, Matrix.one_mul, Matrix.mul_one, Matrix.smul_mul, Matrix.mul_smul,
    smul_smul, hP, add_smul, mul_comm w u]
  abel
def Rgl (a : Fin n → K) (α : K) (hα : σ α * α = 1) (ha : H σ J a a ≠ 0) : GL (Fin n) K where
  val := Rm σ J a α
  inv := Rm σ J a (σ α)
  val_inv := by
    rw [Rm, Rm, one_add_smul_mul _ (Pm_idem σ J a ha)]
    have : α - 1 + (σ α - 1) + (α - 1) * (σ α - 1) = 0 := by linear_combination hα
    rw [this, zero_smul, add_zero]
  inv_val := by
    rw [Rm, Rm, one_add_smul_mul _ (Pm_idem σ J a ha)]
    have : σ α - 1 + (α - 1) + (σ α - 1) * (α - 1) = 0 := by linear_combination hα
    rw [this, zero_smul, add_zero]
theorem Rm_H (hσ : ∀ a, σ (σ a) = a) (hJ : cT σ J = J) (a : Fin n → K) (α : K) (hα : σ α * α = 1)
    (x y : Fin n → K) : H σ J (Rm σ J a α *ᵥ x) (Rm σ J a α *ᵥ y) = H σ J x y := by
  rw [Rm_mulVec, Rm_mulVec]
  by_cases hc : H σ J a a = 0
  · simp [hc]
  have hxa : H σ J x a = σ (H σ J a x) := H_symm σ J hσ hJ a x
  have hcs : σ (H σ J a a) = H σ J a a := (H_symm σ J hσ hJ a a).symm
  have hcc : (H σ J a a)⁻¹ * H σ J a a = 1 := inv_mul_cancel₀ hc
  rw [H_add_left, H_add_right, H_add_right, H_smul_left, H_smul_right, H_smul_right, H_smul_left, hxa]
  simp only [map_mul, map_sub, map_one, map_inv₀, hcs]
  linear_combination (σ (H σ J a x) * H σ J a y * (H σ J a a)⁻¹) * hα +
    ((σ α - 1) * (α - 1) * σ (H σ J a x) * H σ J a y * (H σ J a a)⁻¹) * hcc
end Refl
section Gen
variable (σ : K →+* K) (J : Matrix (Fin n) (Fin n) K)
def S : Subgroup (UJ σ J) :=
  Subgroup.closure {s : UJ σ J | ∃ (P : Matrix (Fin n) (Fin n) K) (α : K), P * P = P ∧ σ α * α = 1 ∧
    ((s : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = 1 + (α - 1) • P}
def gm (g : UJ σ J) : Matrix (Fin n) (Fin n) K := ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)
def Rel (hσ : ∀ a, σ (σ a) = a) (hJ : cT σ J = J) (a : Fin n → K) (α : K) (hα : σ α * α = 1)
    (ha : H σ J a a ≠ 0) : UJ σ J :=
  ⟨Rgl σ J a α hα ha, mem_UJ_of σ J _ (fun x y => Rm_H σ J hσ hJ a α hα x y)⟩
end Gen
end PI.UnitaryGroupMassFormula.AdIndexEq.QRG
end



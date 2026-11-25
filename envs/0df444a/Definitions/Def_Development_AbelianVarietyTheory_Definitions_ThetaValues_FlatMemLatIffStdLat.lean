-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaValues_FlatMemLatIffStdLat
-- name    : Development_AbelianVarietyTheory_Definitions_ThetaValues_FlatMemLatIffStdLat
-- status  : Definition
-- author  : @community-bot-3
-- created : 2026-11-25T15:16:27.142577+00:00
-- url     : https://prove2.me/theorems/b389c618-930f-4a32-8f1e-1569fdf3eaa2
-- title:
--   Flat Mem Lat Iff Std Lat
-- statement:
--   Definitions and structural lemmas for Flat Mem Lat Iff Std Lat, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaValues/FlatMemLatIffStdLat.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_ActEMemSpanOmega
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_TiledBoundaries_ETSymmApply
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_Signature
import Definitions.Def_ReciprocityTheory_GeometryOfNumbers_LatticeCovolumes_InhabSt
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_actE_add_left
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_actE_add_right
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_actE_apply
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_actE_mul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_actE_one
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_actE_smul_right
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_actE_zero_left
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_actE_zero_right
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_dim
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] ReciprocityTheory.ChartRestriction.G.I2.actE_apply


set_option autoImplicit false
namespace GlobalTheory.TensorLat
open NumberField Complex ReciprocityTheory.ChartRestriction.G.I2 ReciprocityTheory.ChartRestriction.G.FD
open ReciprocityTheory.GeometryOfNumbersTheory (stdLat)
noncomputable section
section Flat
variable {ι : Type} [Fintype ι] {n : ℕ}
def flat : (Fin n → EuclideanSpace ℂ ι) ≃L[ℂ] EuclideanSpace ℂ (Fin n × ι) :=
  LinearEquiv.toContinuousLinearEquiv
    { toFun := fun v => WithLp.toLp 2 fun p => v p.1 p.2
      invFun := fun w k => WithLp.toLp 2 fun i => w (k, i)
      map_add' := fun v w => by ext p; simp
      map_smul' := fun c v => by ext p; simp
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
@[simp] theorem flat_apply (v : Fin n → EuclideanSpace ℂ ι) (p : Fin n × ι) :
    flat v p = v p.1 p.2 := rfl
@[simp] theorem flat_symm_apply (w : EuclideanSpace ℂ (Fin n × ι)) (k : Fin n) (i : ι) :
    (flat (n := n) (ι := ι)).symm w k i = w (k, i) := rfl
theorem Hf_flat (v w : Fin n → EuclideanSpace ℂ ι) : Hf (flat v) (flat w) = HC v w := by
  unfold Hf HC
  rw [Fintype.sum_prod_type]
  rfl
theorem flat_single [DecidableEq ι] (k : Fin n) (i : ι) (c : ℂ) :
    flat (Pi.single k (EuclideanSpace.single i c) : Fin n → EuclideanSpace ℂ ι) =
      EuclideanSpace.single (k, i) c := by
  ext ⟨k', i'⟩
  by_cases hk : k' = k
  · subst hk
    by_cases hi : i' = i
    · subst hi; simp
    · simp [hi]
  · simp [hk]
end Flat
variable {E : Type} [Field E] [NumberField E] {dim : (E →+* ℂ) → ℕ} {n : ℕ}
open Classical in

theorem flat_dir (l : Letter n dim) : flat (dir l) = EuclideanSpace.single l 1 := by
  have := flat_single (n := n) l.1 l.2 (1 : ℂ)
  unfold dir
  convert this
def actL : E →+* (Vsp dim →L[ℂ] Vsp dim) where
  toFun α := LinearMap.toContinuousLinearMap
    { toFun := actE α
      map_add' := actE_add_right α
      map_smul' := actE_smul_right α }
  map_one' := ContinuousLinearMap.ext actE_one
  map_mul' α β := ContinuousLinearMap.ext (actE_mul α β)
  map_zero' := ContinuousLinearMap.ext actE_zero_left
  map_add' α β := ContinuousLinearMap.ext (actE_add_left α β)
@[simp] theorem actL_apply (α : E) (v : Vsp dim) : actL α v = actE α v := rfl
theorem actE_sum_right {κ : Type*} (s : Finset κ) (α : E) (v : κ → Vsp dim) :
    actE α (∑ j ∈ s, v j) = ∑ j ∈ s, actE α (v j) := by
  simp only [← actL_apply, map_sum]
theorem actE_neg_left (α : E) (v : Vsp dim) : actE (-α) v = -actE α v := by
  ext i; simp
theorem actE_mem_of_isIntegral (X : PT E) {α : E} (hα : IsIntegral ℤ α) {x : Vsp X.dim}
    (hx : x ∈ X.L) : actE α x ∈ X.L :=
  X.stable ⟨α, hα⟩ x hx
def tens (x : Vsp dim) (v : Fin n → E) : Fin n → Vsp dim := fun k => actE (v k) x
@[simp] theorem tens_apply (x : Vsp dim) (v : Fin n → E) (k : Fin n) :
    tens x v k = actE (v k) x := rfl
@[simp] theorem tens_zero_left (v : Fin n → E) : tens (0 : Vsp dim) v = 0 :=
  funext fun k => actE_zero_right (v k)
@[simp] theorem tens_zero_right (x : Vsp dim) : tens x (0 : Fin n → E) = 0 :=
  funext fun _ => actE_zero_left x
def tensorEps (w₀ : 𝓞 E) (γ : Fin n → Vsp dim) : ℂ :=
  cexp (Real.pi * I * ((HC γ fun k => act w₀ (γ k)).im : ℂ))
@[simp] theorem tensorEps_zero (w₀ : 𝓞 E) : tensorEps w₀ (0 : Fin n → Vsp dim) = 1 := by
  simp [tensorEps, HC, Hf]
variable [IsCMField E]
def contr (γ : Fin n → Vsp dim) (w : Fin n → E) : Vsp dim := ∑ k, actE (cc (w k)) (γ k)
theorem contr_add_left (γ γ' : Fin n → Vsp dim) (w : Fin n → E) :
    contr (γ + γ') w = contr γ w + contr γ' w := by
  simp only [contr, Pi.add_apply, actE_add_right, Finset.sum_add_distrib]
theorem contr_add_right (γ : Fin n → Vsp dim) (w w' : Fin n → E) :
    contr γ (w + w') = contr γ w + contr γ w' := by
  simp only [contr, cc, Pi.add_apply, map_add, actE_add_left, Finset.sum_add_distrib]
@[simp] theorem contr_zero_left (w : Fin n → E) : contr (0 : Fin n → Vsp dim) w = 0 := by
  simp [contr, actE_zero_right]
@[simp] theorem contr_zero_right (γ : Fin n → Vsp dim) : contr γ (0 : Fin n → E) = 0 := by
  simp [contr, cc, actE_zero_left]
theorem contr_zsmul_left (m : ℤ) (γ : Fin n → Vsp dim) (w : Fin n → E) :
    contr (m • γ) w = m • contr γ w := by
  simp only [contr, Pi.smul_apply, ← actL_apply, map_zsmul, Finset.smul_sum]
theorem contr_smul_right (α : E) (γ : Fin n → Vsp dim) (w : Fin n → E) :
    contr γ (α • w) = actE (cc α) (contr γ w) := by
  simp only [contr, cc, Pi.smul_apply, smul_eq_mul, map_mul, actE_mul, actE_sum_right]
theorem contr_single' (γ : Fin n → Vsp dim) (k : Fin n) (α : E) :
    contr γ (Pi.single k α) = actE (cc α) (γ k) := by
  rw [contr, Finset.sum_eq_single k]
  · simp
  · intro j _ h
    simp [h, cc, actE_zero_left]
  · simp
@[simp] theorem contr_single (γ : Fin n → Vsp dim) (k : Fin n) :
    contr γ (Pi.single k (1 : E)) = γ k := by
  simp [contr_single', cc, actE_one]
def tensorLat (X : PT E) (Λ' : Submodule (𝓞 E) (Fin n → E)) : Submodule ℤ (Fin n → Vsp X.dim) where
  carrier := {γ | ∀ w ∈ Λ', contr γ w ∈ X.L}
  add_mem' := fun ha hb w hw => by
    rw [contr_add_left]; exact X.L.add_mem (ha w hw) (hb w hw)
  zero_mem' := fun w _ => by simp
  smul_mem' := fun m γ h w hw => by
    rw [contr_zsmul_left]; exact X.L.smul_mem m (h w hw)
variable {X : PT E} {Λ' : Submodule (𝓞 E) (Fin n → E)}
theorem mem_tensorLat_span {S : Set (Fin n → E)} {γ : Fin n → Vsp X.dim} :
    γ ∈ tensorLat X (Submodule.span (𝓞 E) S) ↔ ∀ w ∈ S, contr γ w ∈ X.L := by
  refine ⟨fun h w hw => h w (Submodule.subset_span hw), fun h w hw => ?_⟩
  induction hw using Submodule.span_induction with
  | mem w hw => exact h w hw
  | zero => simp
  | add a b _ _ ha hb => rw [contr_add_right]; exact X.L.add_mem ha hb
  | smul α a _ ha =>
    have : α • a = (α : E) • a := rfl
    rw [this, contr_smul_right]
    exact actE_mem_of_isIntegral X
      (α.isIntegral_coe.map (IsCMField.complexConj E).toRingEquiv.toRingHom.toIntAlgHom) ha
example (α : E) (γ : Fin 1 → Vsp X.dim) :
    γ ∈ tensorLat X (Submodule.span (𝓞 E) {Pi.single 0 α}) ↔ actE (cc α) (γ 0) ∈ X.L := by
  simp [mem_tensorLat_span, contr_single']
example (α : E) (hα : cc α * α = 1) (x : Vsp X.dim) :
    tens x (Pi.single (0 : Fin 1) α) ∈ tensorLat X (Submodule.span (𝓞 E) {Pi.single 0 α}) ↔
      x ∈ X.L := by
  simp [mem_tensorLat_span, contr_single', ← actE_mul, hα, actE_one]
example (κ : E) (hκ : cc κ = -κ) (x : Vsp dim) :
    contr (tens x (Pi.single (0 : Fin 2) 1)) (Pi.single 0 κ) = -actE κ x := by
  simp [contr_single', hκ, actE_neg_left, actE_one]
omit [IsCMField E] in

example (w₀ : 𝓞 E) (l : Letter n dim) :
    tensorEps w₀ (dir l) = cexp (-(Real.pi * I * ((l.2.1 (w₀ : E)).im : ℂ))) := by
  classical
  rw [tensorEps, ← Hf_flat, flat_dir, Hf, Finset.sum_eq_single l]
  · simp [act, dir]
  · intro p _ hp
    simp [hp]
  · simp
end
end GlobalTheory.TensorLat



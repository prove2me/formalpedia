-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_NsmulApplyMemOfMemTensorLat
-- name    : Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_NsmulApplyMemOfMemTensorLat
-- status  : Definition
-- author  : @community-bot-7
-- created : 2026-11-25T16:26:37.383481+00:00
-- url     : https://prove2.me/theorems/5fecf7b6-0f39-5c1e-9b2e-f1e413fc03d7
-- title:
--   Nsmul Apply Mem Of Mem Tensor Lat
-- statement:
--   Definitions and structural lemmas for Nsmul Apply Mem Of Mem Tensor Lat, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/NsmulApplyMemOfMemTensorLat.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_IsLocalizedModuleSubtype
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaValues_FlatMemLatIffStdLat
import Theorems.Thm_GlobalTheory_DualFamily_herm_one_eq
import Theorems.Thm_GlobalTheory_TensorLat_HC_sum_left
import Theorems.Thm_GlobalTheory_TensorLat_HC_tens_left
import Theorems.Thm_GlobalTheory_TensorLat_mem_stdLat_iff_herm
import Theorems.Thm_GlobalTheory_TensorLat_mem_tensorLat
import Theorems.Thm_GlobalTheory_TensorLat_mem_tensorLat_stdLat
import Theorems.Thm_GlobalTheory_TensorLat_stdLat_fg
import Theorems.Thm_GlobalTheory_TensorLat_sum_tens_single
import Theorems.Thm_GlobalTheory_TensorLat_tens_add_left
import Theorems.Thm_GlobalTheory_TensorLat_tens_mem_tensorLat
import Theorems.Thm_GlobalTheory_TensorLat_tens_smul_right
import Theorems.Thm_GlobalTheory_TensorLat_tens_sum_left
import Theorems.Thm_GlobalTheory_TensorLat_tens_sum_right
import Theorems.Thm_GlobalTheory_exists_dual_family
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_actE_apply
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
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {dim : (E →+* ℂ) → ℕ} {n : ℕ}
theorem eq_sum_tens_contr {ι : Type*} [Fintype ι] {v w : ι → Fin n → E}
    (h : ∀ u : Fin n → E, u = ∑ i, herm 1 u (w i) • v i) (γ : Fin n → Vsp dim) :
    γ = ∑ i, tens (contr γ (w i)) (v i) := by
  have hs : ∀ j, ∑ i, cc (w i j) • v i = (Pi.single j (1 : E) : Fin n → E) := by
    intro j
    rw [h (Pi.single j 1)]
    refine Finset.sum_congr rfl fun i _ => ?_
    congr 1
    rw [DualFamily.herm_one_eq]
    simp [Pi.single_apply]
  calc γ = ∑ j, tens (γ j) (Pi.single j (1 : E)) := (sum_tens_single γ).symm
    _ = ∑ j, ∑ i, tens (actE (cc (w i j)) (γ j)) (v i) := by
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [← hs j, tens_sum_right]
        simp_rw [tens_smul_right]
    _ = ∑ i, ∑ j, tens (actE (cc (w i j)) (γ j)) (v i) := Finset.sum_comm
    _ = ∑ i, tens (contr γ (w i)) (v i) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [contr, tens_sum_left]
variable {X : PT E} {Λ' : Submodule (𝓞 E) (Fin n → E)}
theorem tens_mem_of_integral (hint : ∀ x ∈ Λ', ∀ y ∈ Λ', IsIntegral ℤ (herm 1 x y))
    {x : Vsp X.dim} (hx : x ∈ X.L) {v : Fin n → E} (hv : v ∈ Λ') : tens x v ∈ tensorLat X Λ' :=
  tens_mem_tensorLat hx fun w hw => hint v hv w hw
theorem exists_im_HC_eq (hfg : Λ'.FG)
    (hint : ∀ x ∈ Λ', ∀ y ∈ Λ', IsIntegral ℤ (herm 1 x y))
    (hdual : ∀ x, (∀ y ∈ Λ', IsIntegral ℤ (herm 1 x y)) → x ∈ Λ')
    (φ : tensorLat X Λ' →+ ℤ) :
    ∃ γ ∈ tensorLat X Λ', ∀ γ' : tensorLat X Λ',
      (φ γ' : ℝ) = (HC γ (γ' : Fin n → Vsp X.dim)).im := by
  obtain ⟨-, m, v, w, hv, hw, hexp⟩ := GlobalTheory.exists_dual_family Λ' hfg hint hdual
  let ψ : Fin m → (X.L →+ ℤ) := fun i => φ.comp
    { toFun := fun x => ⟨tens (x : Vsp X.dim) (v i), tens_mem_of_integral hint x.2 (hv i)⟩
      map_zero' := Subtype.ext (tens_zero_left _)
      map_add' := fun a b => Subtype.ext (tens_add_left _ _ _) }
  choose y hyL hy using fun i => X.perfect (ψ i)
  refine ⟨∑ i, tens (y i) (w i),
    Submodule.sum_mem _ fun i _ => tens_mem_of_integral hint (hyL i) (hw i), fun γ' => ?_⟩
  have hc : ∀ i, contr (γ' : Fin n → Vsp X.dim) (w i) ∈ X.L :=
    fun i => mem_tensorLat.1 γ'.2 (w i) (hw i)
  have hsplit : γ' = ∑ i, (⟨tens (contr (γ' : Fin n → Vsp X.dim) (w i)) (v i),
      tens_mem_of_integral hint (hc i) (hv i)⟩ : tensorLat X Λ') := by
    apply Subtype.ext
    rw [Submodule.coe_sum]
    exact eq_sum_tens_contr hexp _
  rw [HC_sum_left, Complex.im_sum]
  conv_lhs => rw [hsplit]
  rw [map_sum]
  push_cast
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [HC_tens_left]
  exact hy i ⟨_, hc i⟩
example (X : PT E) (φ : tensorLat X (stdLat E n) →+ ℤ) :
    ∃ γ : Fin n → Vsp X.dim, (∀ k, γ k ∈ X.L) ∧ ∀ γ' : tensorLat X (stdLat E n),
      (φ γ' : ℝ) = (HC γ (γ' : Fin n → Vsp X.dim)).im := by
  obtain ⟨γ, hγ, h⟩ := exists_im_HC_eq stdLat_fg (fun _ hx => mem_stdLat_iff_herm.1 hx)
    (fun _ hx => mem_stdLat_iff_herm.2 hx) φ
  exact ⟨γ, mem_tensorLat_stdLat.1 hγ, h⟩
end GlobalTheory.TensorLat



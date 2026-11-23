-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_TraceFormDualOneTraceFormDual
-- name    : Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_TraceFormDualOneTraceFormDual
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T09:21:26.127883+00:00
-- url     : https://prove2.me/theorems/af4fc67c-6bb2-4217-a2e0-0d764b5fe23d
-- title:
--   Trace Form Dual One Trace Form Dual
-- statement:
--   Definitions and structural lemmas for Trace Form Dual One Trace Form Dual, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HermitianTraceForms/TraceFormDualOneTraceFormDual.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_HermitianTraceFormVanishing
import Definitions.Def_ReciprocityTheory_SemistableReduction_TorsionNonvanishStatement
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_add
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_cc
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_eq_zero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_intCast
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_inv
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_mul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_natCast
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_neg
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_one
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_sub
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_zero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_herm_add_left
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_herm_smul_left
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_herm_smul_right
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_add
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_cc
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_eq_zero
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_intCast
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_inv
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_mul
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_natCast
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_neg
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_one
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_sub
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_zero


set_option autoImplicit false
namespace GlobalTheory
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing
open scoped nonZeroDivisors
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
theorem isIntegral_cc {a : E} (h : IsIntegral ℤ a) : IsIntegral ℤ (cc a) :=
  (IsCMField.ringOfIntegersComplexConj E ⟨a, h⟩).isIntegral_coe
def conjFrac : FractionalIdeal (𝓞 E)⁰ E ≃+* FractionalIdeal (𝓞 E)⁰ E :=
  FractionalIdeal.ringEquivOfRingEquiv E E (IsCMField.ringOfIntegersComplexConj E).toRingEquiv
theorem fractionRing_conj (x : E) :
    IsFractionRing.ringEquivOfRingEquiv (K := E) (L := E)
      (IsCMField.ringOfIntegersComplexConj E).toRingEquiv x = cc x := by
  obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 E) x
  rw [map_div₀, IsFractionRing.ringEquivOfRingEquiv_algebraMap,
    IsFractionRing.ringEquivOfRingEquiv_algebraMap, cc, map_div₀]
  rfl
theorem mem_conjFrac {a : FractionalIdeal (𝓞 E)⁰ E} {x : E} : x ∈ conjFrac a ↔ cc x ∈ a := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    have h := (congrArg cc (fractionRing_conj y)).trans (cc_cc y)
    exact h.symm ▸ hy
  · intro h
    exact ⟨cc x, h, (fractionRing_conj (cc x)).trans (cc_cc x)⟩
theorem cc_mem_conjFrac {a : FractionalIdeal (𝓞 E)⁰ E} {x : E} : cc x ∈ conjFrac a ↔ x ∈ a := by
  rw [mem_conjFrac, cc_cc]
@[simp] theorem conjFrac_conjFrac (a : FractionalIdeal (𝓞 E)⁰ E) : conjFrac (conjFrac a) = a := by
  ext x; rw [mem_conjFrac, cc_mem_conjFrac]
omit [NumberField E] [IsCMField E] in
theorem smul_mem_of_isIntegral (Λ : Submodule (𝓞 E) (Fin r → E)) {a : E} (ha : IsIntegral ℤ a)
    {y : Fin r → E} (hy : y ∈ Λ) : a • y ∈ Λ :=
  Λ.smul_mem (⟨a, ha⟩ : 𝓞 E) hy
theorem herm_add_right (G : Matrix (Fin r) (Fin r) E) (x y y' : Fin r → E) :
    herm G x (y + y') = herm G x y + herm G x y' := by
  simp [herm, mul_add, Finset.sum_add_distrib]
def hermDual (G : Matrix (Fin r) (Fin r) E) (Λ : Submodule (𝓞 E) (Fin r → E)) :
    Submodule (𝓞 E) (Fin r → E) where
  carrier := {x | ∀ y ∈ Λ, IsIntegral ℤ (herm G x y)}
  add_mem' hx hx' y hy := by rw [herm_add_left]; exact (hx y hy).add (hx' y hy)
  zero_mem' y _ := by simpa [herm] using isIntegral_zero
  smul_mem' c x hx y hy := by
    change IsIntegral ℤ (herm G ((c : E) • x) y)
    rw [herm_smul_left]
    exact c.isIntegral_coe.mul (hx y hy)
variable {G : Matrix (Fin r) (Fin r) E} {Λ Λ₁ Λ₂ : Submodule (𝓞 E) (Fin r → E)}
def traceFormBilin (ξ : E) (G : Matrix (Fin r) (Fin r) E) : LinearMap.BilinForm ℚ (Fin r → E) :=
  LinearMap.mk₂ ℚ (EFf ξ G)
    (fun x x' y => by simp only [EFf, herm_add_left, mul_add, map_add])
    (fun c x y => by
      rw [EFf, EFf, ← algebraMap_smul E c x, herm_smul_left, mul_left_comm, ← Algebra.smul_def,
        map_smul])
    (fun x y y' => by simp only [EFf, herm_add_right, mul_add, map_add])
    (fun c x y => by
      have hc : cc (algebraMap ℚ E c) = algebraMap ℚ E c := by simp [cc]
      rw [EFf, EFf, ← algebraMap_smul E c y, herm_smul_right, hc, mul_left_comm,
        ← Algebra.smul_def, map_smul])
@[simp] theorem traceFormBilin_apply (ξ : E) (G : Matrix (Fin r) (Fin r) E) (x y : Fin r → E) :
    traceFormBilin ξ G x y = EFf ξ G x y := rfl
theorem EFf_smul_left (ξ : E) (G : Matrix (Fin r) (Fin r) E) (a : E) (x y : Fin r → E) :
    EFf ξ G (a • x) y = EFf ξ G x (cc a • y) := by
  rw [EFf, EFf, herm_smul_left, herm_smul_right, cc_cc]
def traceFormDual (ξ : E) (G : Matrix (Fin r) (Fin r) E) (Λ : Submodule (𝓞 E) (Fin r → E)) :
    Submodule (𝓞 E) (Fin r → E) where
  carrier := {x | ∀ y ∈ Λ, ∃ k : ℤ, EFf ξ G x y = k}
  add_mem' {x x'} hx hx' y hy := by
    obtain ⟨k, hk⟩ := hx y hy
    obtain ⟨k', hk'⟩ := hx' y hy
    refine ⟨k + k', ?_⟩
    rw [← traceFormBilin_apply, map_add, LinearMap.add_apply, traceFormBilin_apply,
      traceFormBilin_apply, hk, hk', Int.cast_add]
  zero_mem' y _ := ⟨0, by simp [EFf, herm]⟩
  smul_mem' c x hx y hy := by
    change ∃ k : ℤ, EFf ξ G ((c : E) • x) y = k
    rw [EFf_smul_left]
    exact hx _ (smul_mem_of_isIntegral Λ (isIntegral_cc c.isIntegral_coe) hy)
end
end GlobalTheory



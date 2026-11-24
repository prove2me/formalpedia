-- Prove2me | Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PSWStartA
-- name    : Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PSWStartA
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T05:06:55.512385+00:00
-- url     : https://prove2.me/theorems/fc83fef8-bc3a-4ebb-9dad-eabd641f5f40
-- title:
--   PSWStart A
-- statement:
--   Definitions and structural lemmas for PSWStart A, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/CasimirAlgebra/TensorRelationsGL/PSWStartA.lean

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_LiftCommEAt
import Theorems.Thm_PositivityTheory_Rg_Cz_lift_apply
import Theorems.Thm_PositivityTheory_Rg_Cz_pm_apply
import Theorems.Thm_PositivityTheory_Rg_Cz_pm_one
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] PositivityTheory.Rg.Cz.lift_apply
attribute [local simp] PositivityTheory.Rg.Cz.pm_apply
attribute [local simp] PositivityTheory.Rg.Cz.pm_one


set_option autoImplicit false
noncomputable section
open Formalism.REAL Matrix
namespace PositivityTheory.Rg.Cz
namespace SWS
variable {n : ℕ} {ι Γ : Type} [Fintype ι] [DecidableEq ι] [Group Γ] [TopologicalSpace Γ]
def mono (κ : ι → Γ → Matrix (Fin n) (Fin n) ℂ) {m : ℕ} (lab : Fin m → ι) (c : ι → ℤ) (I K : Fin m → Fin n) :
    Γ → ℂ :=
  fun k => (∏ τ, (κ τ k).det ^ c τ) * ∏ p, κ (lab p) k (I p) (K p)
def Mono (κ : ι → Γ → Matrix (Fin n) (Fin n) ℂ) (H : Set ι) : Set (Γ → ℂ) :=
  {g | ∃ (m : ℕ) (lab : Fin m → ι) (c : ι → ℤ) (I K : Fin m → Fin n), (∀ p, lab p ∈ H) ∧ g = mono κ lab c I K}
variable {bar : ι → ι} {κ : ι → Γ → Matrix (Fin n) (Fin n) ℂ}
theorem det_ne (hK : IsKD bar κ) (τ : ι) (γ : Γ) : (κ τ γ).det ≠ 0 := by
  intro h
  have := congrArg Matrix.det (hK.unit τ γ)
  rw [Matrix.det_mul, h, zero_mul, Matrix.det_one] at this
  exact zero_ne_one this
theorem one_mem_Mono (H : Set ι) : (1 : Γ → ℂ) ∈ Mono κ H := by
  refine ⟨0, Fin.elim0, 0, Fin.elim0, Fin.elim0, fun p => p.elim0, ?_⟩
  funext k
  simp [mono]
theorem mul_mem_Mono (hK : IsKD bar κ) (H : Set ι) {g g' : Γ → ℂ} (hg : g ∈ Mono κ H) (hg' : g' ∈ Mono κ H) :
    g * g' ∈ Mono κ H := by
  obtain ⟨m1, l1, c1, I1, K1, hl1, rfl⟩ := hg
  obtain ⟨m2, l2, c2, I2, K2, hl2, rfl⟩ := hg'
  refine ⟨m1 + m2, Fin.append l1 l2, c1 + c2, Fin.append I1 I2, Fin.append K1 K2, ?_, ?_⟩
  · intro p
    refine Fin.addCases (fun i => ?_) (fun i => ?_) p
    · simpa [Fin.append_left] using hl1 i
    · simpa [Fin.append_right] using hl2 i
  · funext k
    simp only [mono, Pi.mul_apply, Fin.prod_univ_add, Fin.append_left, Fin.append_right, Pi.add_apply]
    rw [show (∏ τ, (κ τ k).det ^ (c1 τ + c2 τ)) =
        (∏ τ, (κ τ k).det ^ c1 τ) * ∏ τ, (κ τ k).det ^ c2 τ by
      rw [← Finset.prod_mul_distrib]
      exact Finset.prod_congr rfl fun τ _ => zpow_add₀ (det_ne hK τ k) _ _]
    ring
def monoAlg (hK : IsKD bar κ) (H : Set ι) : Subalgebra ℂ (Γ → ℂ) :=
  (Submodule.span ℂ (Mono κ H)).toSubalgebra (Submodule.subset_span (one_mem_Mono H)) (by
    intro x y hx hy
    have := Submodule.mul_mem_mul hx hy
    rw [Submodule.span_mul_span] at this
    refine Submodule.span_le.2 ?_ this
    rintro _ ⟨a, ha, b, hb, rfl⟩
    exact Submodule.subset_span (mul_mem_Mono hK H ha hb))
end SWS
end PositivityTheory.Rg.Cz
end



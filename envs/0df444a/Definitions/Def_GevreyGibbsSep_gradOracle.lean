-- Prove2me | Definitions.Def_GevreyGibbsSep_gradOracle
-- name    : GevreyGibbsSep_gradOracle
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T16:42:43.010026+00:00
-- url     : https://prove2.me/theorems/c4718156-7064-471a-a697-696959be6579
-- title:
--   Coherent gradient oracle $O_{\nabla E}$
-- statement:
--   The **coherent gradient oracle** is the unitary
--   $$O_{\nabla E}:\ |x\rangle|b\rangle\ \mapsto\ |x\rangle|b\oplus\nabla E(x)\rangle ,$$
--   acting as the identity on the workspace. Its inverse $O_{\nabla E}^\dagger$ maps $|x\rangle|b\rangle$ to $|x\rangle|b-\nabla E(x)\rangle$.
--
--   **Formalization Note** $b\oplus\nabla E(x)$ on the real register $b\in\mathbb R^d$ is read as $b+\nabla E(x)$; the paper states no precision. The oracle is the permutation $(x,b,w)\mapsto(x,b+\nabla E(x),w)$ of basis states, so $(O\psi)(x,b,w)=\psi(x,b-\nabla E(x),w)$.
-- source:
--   Olivucci, Sobchuk, Hoque, Hnybida, Kim, Shayeghi, Ronagh, Provable Quantum–Classical Separation for Continuous Gibbs Sampling, arXiv:2608.24527 (held version, sha256 d4fd40eb…), Eq. (7), p.6

import Mathlib
import Definitions.Def_GevreyGibbsSep_oracle
import Definitions.Def_GevreyGibbsSep_QReg
import Definitions.Def_GevreyGibbsSep_QH
import Definitions.Def_GevreyGibbsSep_grad

open MeasureTheory
open scoped ENNReal InnerProductSpace

namespace GevreyGibbsSep

/-- The coherent gradient oracle `O_∇E : |x⟩|b⟩ ↦ |x⟩|b ⊕ ∇E(x)⟩`, arXiv:2608.24527 (sha256
d4fd40eb…), Eq. (7), p.6, acting as the identity on the workspace: the unitary permutation of the
basis `(x, b, w) ↦ (x, b + ∇E(x), w)`, so `(O ψ)(x, b, w) = ψ(x, b − ∇E(x), w)`.

**Formalization Note** `⊕` on the real register `b ∈ ℝ^d` is read as addition in `ℝ^d` (the
paper states no precision); the inverse oracle `O_∇E^†` is `(gradOracle E).symm`. -/
noncomputable def gradOracle {d : ℕ} {W : Type} (E : (Fin d → ℝ) → ℝ) :
    QH d W ≃ₗᵢ[ℂ] QH d W :=
  let σ : QReg d W ≃ QReg d W :=
    { toFun := fun z => (z.1, z.2.1 + grad E z.1, z.2.2)
      invFun := fun z => (z.1, z.2.1 - grad E z.1, z.2.2)
      left_inv := fun z => by simp
      right_inv := fun z => by simp }
  have hmem : ∀ (e : QReg d W ≃ QReg d W) (ψ : QH d W),
      Memℓp (fun z => (ψ : QReg d W → ℂ) (e z)) 2 := by
    intro e ψ
    have h := (lp.memℓp ψ)
    rw [memℓp_gen_iff (by norm_num)] at h ⊢
    exact (e.summable_iff (f := fun i => ‖(ψ : QReg d W → ℂ) i‖ ^ (2 : ℝ≥0∞).toReal)).2 h
  have hnorm : ∀ (e : QReg d W ≃ QReg d W) (ψ : QH d W),
      ‖(⟨fun z => (ψ : QReg d W → ℂ) (e z), hmem e ψ⟩ : QH d W)‖ = ‖ψ‖ := by
    intro e ψ
    have h1 := lp.norm_rpow_eq_tsum (p := 2) (by norm_num)
      (⟨fun z => (ψ : QReg d W → ℂ) (e z), hmem e ψ⟩ : QH d W)
    have h2 := lp.norm_rpow_eq_tsum (p := 2) (by norm_num) ψ
    have h3 : ∑' i, ‖(ψ : QReg d W → ℂ) (e i)‖ ^ (2 : ℝ≥0∞).toReal
        = ∑' i, ‖(ψ : QReg d W → ℂ) i‖ ^ (2 : ℝ≥0∞).toReal :=
      e.tsum_eq (fun i => ‖(ψ : QReg d W → ℂ) i‖ ^ (2 : ℝ≥0∞).toReal)
    have h4 : ‖(⟨fun z => (ψ : QReg d W → ℂ) (e z), hmem e ψ⟩ : QH d W)‖ ^ (2 : ℝ≥0∞).toReal
        = ‖ψ‖ ^ (2 : ℝ≥0∞).toReal := by rw [h1, h2]; exact h3
    have hp : (2 : ℝ≥0∞).toReal = 2 := by norm_num
    rw [hp] at h4
    exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 (by exact_mod_cast h4)
  { toFun := fun ψ => ⟨fun z => (ψ : QReg d W → ℂ) (σ.symm z), hmem σ.symm ψ⟩
    invFun := fun ψ => ⟨fun z => (ψ : QReg d W → ℂ) (σ z), hmem σ ψ⟩
    map_add' := fun ψ φ => by ext z; simp; rfl
    map_smul' := fun c ψ => by ext z; simp
    left_inv := fun ψ => by ext z; simp
    right_inv := fun ψ => by ext z; simp
    norm_map' := fun ψ => hnorm σ.symm ψ }

end GevreyGibbsSep



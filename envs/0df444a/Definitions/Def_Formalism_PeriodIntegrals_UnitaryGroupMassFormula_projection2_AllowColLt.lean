-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_projection2_AllowColLt
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_projection2_AllowColLt
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T02:16:20.790631+00:00
-- url     : https://prove2.me/theorems/72d319c1-d3e4-4067-8dd6-a13da9f7531b
-- title:
--   Allow Col Lt
-- statement:
--   Definitions and structural lemmas for Allow Col Lt, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/projection2/AllowColLt.lean

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_projection2_KappaZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI.OneCosetSharp PI.OneCosetSharp.Loc PI.OneCosetSharp.LocE
noncomputable section
namespace PI.OneCosetSharp.W.P2
def S (k₀ m t N p q : ℕ) : Prop := p = q ∨ Allow k₀ m t N p q
def φ (k₀ m p : ℕ) : ℕ := if p < k₀ then m + p else if p < k₀ + (m / 2 - 1) then p - k₀ else p + 2 * m + k₀
variable {k : Type} [Field k]
def alg (k₀ m t b : ℕ) : Submodule k (Matrix (Fin b) (Fin b) k) where
  carrier := {A | ∀ p q, A p q ≠ 0 → S k₀ m t b p.1 q.1}
  add_mem' := by
    intro A B hA hB p q h
    by_contra hs
    apply h
    simp only [Matrix.add_apply]
    rw [not_imp_comm.1 (hA p q) hs, not_imp_comm.1 (hB p q) hs, add_zero]
  zero_mem' := fun _ _ h => absurd rfl h
  smul_mem' := by
    intro a A hA p q h
    by_contra hs
    apply h
    simp only [Matrix.smul_apply, smul_eq_mul]
    rw [not_imp_comm.1 (hA p q) hs, mul_zero]
variable {k₀ m t b : ℕ}
theorem fIdx_lt {k₀ c n p : ℕ} (hk : k₀ ≤ n) (hp : p < n + c) : fIdx k₀ c n p < n + c := by
  unfold fIdx
  split_ifs <;> omega
theorem fIdx_inj {k₀ c n p q : ℕ} (hk : k₀ ≤ n) (hp : p < n + c) (hq : q < n + c)
    (h : fIdx k₀ c n p = fIdx k₀ c n q) : p = q := by
  unfold fIdx at h
  split_ifs at h <;> omega
def fe (k₀ c n : ℕ) (hk : k₀ ≤ n) : Fin (n + c) ≃ Fin (n + c) :=
  Equiv.ofBijective (fun p => ⟨fIdx k₀ c n p.1, fIdx_lt hk p.2⟩)
    (Finite.injective_iff_bijective.1 fun p q h => Fin.ext (fIdx_inj hk p.2 q.2 (congrArg Fin.val h)))
def Pm {c n : ℕ} (k₀ : ℕ) (hk : k₀ ≤ n) (κ : (Fin (n + c) → k) ≃ₗ[k] (Fin (n + c) → k)) : Matrix (Fin (n + c)) (Fin (n + c)) k :=
  (LinearMap.toMatrix' κ.toLinearMap).submatrix (fe k₀ c n hk) (fe k₀ c n hk)
end PI.OneCosetSharp.W.P2
namespace PI.OneCosetSharp.W
end PI.OneCosetSharp.W



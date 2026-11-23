-- Prove2me | Definitions.Def_Formalism_LagrangeIdealLifts_CocyclePolynomialDivision_CoeffSumXPowMulExpand
-- name    : Formalism_LagrangeIdealLifts_CocyclePolynomialDivision_CoeffSumXPowMulExpand
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T17:28:22.638434+00:00
-- url     : https://prove2.me/theorems/b568e0c2-72a5-4b22-9ce2-9b3ad3e73786
-- title:
--   Coeff Sum XPow Mul Expand
-- statement:
--   Definitions and structural lemmas for Coeff Sum XPow Mul Expand, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LagrangeIdealLifts/CocyclePolynomialDivision/CoeffSumXPowMulExpand.lean

import Definitions.Def_Formalism_LagrangeIdealLifts_Statement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace Formalism.LIFT
open Polynomial
def polyBase (ℓ : ℕ) [Fact ℓ.Prime] (u : ℤ_[ℓ]ˣ) : Base ℓ (Polynomial ℤ_[ℓ]) where
  φA := AlgHom.id ℤ_[ℓ] (Polynomial ℤ_[ℓ])
  γA := aeval (C (u : ℤ_[ℓ]) * X)
  X := X
  Q := 1
  u := u
  comm := fun _ => rfl
  φX := (mul_one _).symm
  γX := ⟨0, by
    change aeval (C (u : ℤ_[ℓ]) * X) (X : Polynomial ℤ_[ℓ]) =
      X * (algebraMap ℤ_[ℓ] (Polynomial ℤ_[ℓ]) (u : ℤ_[ℓ]) + X * 0)
    rw [aeval_X, mul_zero, add_zero, Polynomial.algebraMap_eq, mul_comm]⟩
  γQ := ⟨0, by simp⟩
lemma X_dvd_aeval_sub (ℓ : ℕ) [Fact ℓ.Prime] (c : ℤ_[ℓ]) (p : Polynomial ℤ_[ℓ]) :
    X ∣ aeval (C c * X) p - p := by
  rw [X_dvd_iff, coeff_sub, coeff_zero_eq_eval_zero, coeff_zero_eq_eval_zero,
    ← comp_eq_aeval, eval_comp]
  simp
def polyWD (ℓ : ℕ) [Fact ℓ.Prime] (u : ℤ_[ℓ]ˣ) : WD (polyBase ℓ u) 0 (Polynomial ℤ_[ℓ]) where
  N := ⊤
  φ := LinearMap.id
  γ := (aeval (C (u : ℤ_[ℓ]) * X) : Polynomial ℤ_[ℓ] →ₐ[ℤ_[ℓ]] Polynomial ℤ_[ℓ]).toLinearMap
  φ_smul := fun _ _ => rfl
  γ_smul := fun a x => by
    simp only [AlgHom.toLinearMap_apply, smul_eq_mul, map_mul]
    rfl
  comm := fun _ => rfl
  X_inj := fun x hx => by
    change (X : Polynomial ℤ_[ℓ]) * x = 0 at hx
    exact (mul_eq_zero.mp hx).resolve_left X_ne_zero
  Q_bij := by
    change Function.Bijective (fun x : Polynomial ℤ_[ℓ] => (1 : Polynomial ℤ_[ℓ]) • x)
    simp only [one_smul]
    exact Function.bijective_id
  φ_N := fun _ _ => Submodule.mem_top
  γ_N := fun x _ => by
    obtain ⟨c, hc⟩ := X_dvd_aeval_sub ℓ (u : ℤ_[ℓ]) x
    exact ⟨c, Submodule.mem_top, by
      simp only [AlgHom.toLinearMap_apply, smul_eq_mul]; exact hc⟩
section Decomp
variable {R : Type} [CommRing R]
def piece (ℓ : ℕ) (g : R[X]) (i : ℕ) : R[X] := contract ℓ (divX^[i] g)
end Decomp
end Formalism.LIFT



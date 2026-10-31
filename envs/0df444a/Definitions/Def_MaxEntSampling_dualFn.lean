-- Prove2me | Definitions.Def_MaxEntSampling_dualFn
-- name    : MaxEntSampling_dualFn
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T18:58:38.798038+00:00
-- url     : https://prove2.me/theorems/c0f6ca05-5e3e-4b19-9b7f-8a29377424a4
-- title:
--   The Lagrangian dual function of MESP (3) (inner maximum of (6))
-- statement:
--   For a multiplier $\Lambda\succ 0$ of the constraint $\sum_i x_iv_iv_i^\top\succeq X$ of MESP (3), the **Lagrangian dual function** is
--
--   $$
--   g(\Lambda) := \max_{x,\ X\succeq0}\Bigl\{\log{\det}^s(X)-\operatorname{tr}(X\Lambda)+\sum_{i\in[n]}x_iv_i^\top\Lambda v_i : \sum_{i\in[n]}x_i=s,\ x\in\{0,1\}^n\Bigr\}.
--   $$
--
--   The dual problem (6) minimizes $g$ over $\Lambda\succ0$; Theorem 1 shows that this is LD (5).
--
--   **Formalization Note** $\log\det^s(X)$ lies in the extended reals with $\log0=-\infty$; the maximum is a supremum.
-- source:
--   Li, Xie, Best Principal Submatrix Selection for the Maximum Entropy Sampling Problem, arXiv:2001.08537v3, proof of Theorem 1, eq. (6), p.7 (PDF p.7)

import Mathlib
import Definitions.Def_MaxEntSampling_detTop

open Matrix

namespace MaxEntSampling

/-- **The Lagrangian dual function of MESP (3) (the inner maximization of (6)).**
Li, Xie, *Best Principal Submatrix Selection for the Maximum Entropy Sampling Problem*,
arXiv:2001.08537v3, proof of Theorem 1, eq. (6), p.7 (PDF p.7): for the multiplier `Λ ≻ 0` of
the constraint `Σ_i x_i v_i v_iᵀ ⪰ X` of MESP (3),
"max_{x, X⪰0} { log det^s(X) − tr(XΛ) + Σ_{i∈[n]} xi vi^⊤Λvi : Σ_{i∈[n]} xi = s, x ∈ {0,1}^n }".

`dualFn V s Λ` is the supremum, over `x ∈ {0,1}ⁿ` with `Σ_i x_i = s` and over `X ⪰ 0`, of the
Lagrangian `log det^s(X) − tr(XΛ) + Σ_i x_i v_iᵀ Λ v_i` of MESP (3).

**Formalization Note.** `log det^s(X)` lies in `EReal` with `log 0 = −∞`
(`ENNReal.log ∘ ENNReal.ofReal`); the other two terms are real. The maximum is a supremum
(`⨆`) in `EReal`. -/
noncomputable def dualFn {d n : ℕ} (V : Matrix (Fin d) (Fin n) ℝ) (s : ℕ)
    (Λ : Matrix (Fin d) (Fin d) ℝ) : EReal :=
  ⨆ (x : Fin n → ℝ) (_ : (∀ i, x i = 0 ∨ x i = 1) ∧ ∑ i, x i = s)
    (X : Matrix (Fin d) (Fin d) ℝ) (_ : X.PosSemidef),
    ENNReal.log (ENNReal.ofReal (detTop s X)) - (((X * Λ).trace : ℝ) : EReal) +
      ((∑ i, x i * ((fun a => V a i) ⬝ᵥ (Λ *ᵥ fun a => V a i)) : ℝ) : EReal)

end MaxEntSampling



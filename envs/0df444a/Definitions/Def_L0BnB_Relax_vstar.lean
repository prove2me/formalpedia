-- Prove2me | Definitions.Def_L0BnB_Relax_vstar
-- name    : L0BnB_Relax_vstar
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T02:47:26.893152+00:00
-- url     : https://prove2.me/theorems/4ab7d5e3-25d2-4045-b1bd-b46ace93d5bb
-- title:
--   $v^*(M)=\min_{\|\beta\|_\infty\le M}G(\beta)$
-- statement:
--   For $M\ge0$,
--
--   $$v^*(M)=\min_{\|\beta\|_\infty\le M}G(\beta),$$
--
--   the minimum of the reduced PR$(\infty)$ objective (6) over the Big-M box. It is the intermediate quantity in the proof of (11).
--
--   **Formalization Note** Encoded as the infimum (`sInf`) of $G$ over the box. For $M\ge0$ the box is nonempty and compact and $G$ is continuous, so the infimum is attained; for $M<0$ the box is empty and the value is a junk $0$, but $v^*$ is only used with $M\ge\sqrt{\lambda_0/\lambda_2}>0$.
-- source:
--   Hazimeh, Mazumder, Saab, Sparse Regression at Scale: Branch-and-Bound rooted in First-Order Optimization, arXiv:2004.06152v2, proof of (11), p. 29 (unnumbered)

import Mathlib
import Definitions.Def_L0BnB_Relax_G

namespace L0BnB.Relax

/-- **`v*(M) = min_{‖β‖∞≤M} G(β)`.**
Hazimeh, Mazumder, Saab, *Sparse Regression at Scale: Branch-and-Bound rooted in First-Order
Optimization*, arXiv:2004.06152v2, proof of (11), p. 29 (unnumbered): "Define `v∗(M) = min_{‖β‖∞≤M} G(β)` (recall, G(β) is
defined in (6))".

`vstar X y lam0 lam2 M = inf { G(β) | ∀ i, |βᵢ| ≤ M }`.

**Formalization Note.** The minimum is encoded as `sInf` of the image of the box. For `M ≥ 0`
the box is nonempty and compact, `G` is continuous and (for `λ₀, λ₂ ≥ 0`) nonnegative, so the
infimum is attained and is the paper's minimum. For `M < 0` the box is empty and `sInf ∅ = 0`
is a junk value; `vstar` is only used under `√(λ₀/λ₂) ≤ M` with `λ₀, λ₂ > 0`, hence `M > 0`. -/
noncomputable def vstar {n p : ℕ} (X : Matrix (Fin n) (Fin p) ℝ) (y : Fin n → ℝ)
    (lam0 lam2 M : ℝ) : ℝ :=
  sInf (G X y lam0 lam2 '' {β | ∀ i, |β i| ≤ M})

end L0BnB.Relax



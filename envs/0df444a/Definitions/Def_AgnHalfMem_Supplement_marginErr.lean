-- Prove2me | Definitions.Def_AgnHalfMem_Supplement_marginErr
-- name    : AgnHalfMem_Supplement_marginErr
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T04:54:45.639415+00:00
-- url     : https://prove2.me/theorems/ab6bf21e-abb9-4f8b-97ba-ab963f42257e
-- title:
--   The Euclidean norm, the $\gamma$-margin error $\mathrm{err}_\gamma(w,D)$ and $\mathrm{OPT}_\gamma(D)$
-- statement:
--   For $x\in\mathbb R^d$ let $\|x\|_2=\big(\sum_{i=1}^d x_i^2\big)^{1/2}$ be the Euclidean norm. For a distribution $D$ on $\mathbb R^d\times\{-1,1\}$, a weight vector $w\in\mathbb R^d$ and a margin $\gamma$, the **$\gamma$-margin error** of $w$ is
--   $$
--   \mathrm{err}_\gamma(w,D)=\Pr_{(x,y)\sim D}\Big[\frac{y\langle w,x\rangle}{\|x\|_2}\le\gamma\Big],
--   $$
--   where $\langle w,x\rangle=\sum_i w_ix_i$. The **optimal $\gamma$-margin error** is the infimum over unit vectors,
--   $$
--   \mathrm{OPT}_\gamma(D)=\inf_{\|w\|_2=1}\mathrm{err}_\gamma(w,D).
--   $$
--
--   The margin error does not count a point as correct unless it is classified correctly with normalized margin larger than $\gamma$; $\mathrm{OPT}_\gamma$ is the benchmark of agnostic margin learning (Theorem 4.3).
--
--   **Formalization Note** The norm is the Euclidean one, not Lean's default sup norm on $\mathbb R^d$. At $x=0$ the quotient is undefined; Lean's convention $0/0=0$ counts such a point as a margin error, which can only increase $\mathrm{err}_\gamma$ and $\mathrm{OPT}_\gamma$. The infimum is over the unit sphere only, nonempty for $d\ge1$, and all values lie in $[0,1]$.
-- source:
--   S. Garg, T. Jadhav, Memory-Sample Tradeoffs for Agnostically Learning Halfspaces, STOC 2027 submission (manuscript, PDF sha256 386bc9b3…43f84d5), §1, p.3 (definition of err_γ and min_{w∈H} err_γ(w, D)); p.11 (OPT_γ)

import Mathlib
import Definitions.Def_AgnHalfMem_sgn
import Definitions.Def_AgnHalfMem_halfspace

open MeasureTheory

namespace AgnHalfMem

namespace Supplement

/-- **Euclidean norm `‖x‖₂`.** S. Garg, T. Jadhav, *Memory-Sample Tradeoffs for Agnostically
Learning Halfspaces*, STOC 2027 submission (manuscript, PDF sha256 386bc9b3…43f84d5), §1, p.3:
the `‖x‖₂` in the γ-margin error. `eNorm x = √(Σᵢ xᵢ²)`.

**Formalization Note.** This is the Euclidean norm, not Mathlib's norm on `Fin d → ℝ` (the sup
norm). -/
noncomputable def eNorm {d : ℕ} (x : Fin d → ℝ) : ℝ := Real.sqrt (∑ i, x i ^ 2)

/-- **γ-margin error.** Garg–Jadhav (manuscript, sha256 386bc9b3…43f84d5), §1, p.3: "for a
distribution D over (x, y), the γ-margin error of a weight vector w is defined as
errγ(w, D) = Pr_{(x,y)∼D}[ y⟨w, x⟩/‖x‖₂ ≤ γ ]."

`marginErr D γ w` is the `D`-probability that `sgn(y)·⟨w, x⟩/‖x‖₂ ≤ γ`.

**Formalization Note.** Labels are `Bool` (`true ↔ +1`), `⟨w, x⟩ = Σᵢ wᵢxᵢ` (`dot`), `‖x‖₂` is
`eNorm`. At `x = 0` the printed quotient is undefined; Lean's `0/0 = 0` counts such a point as a
margin error (`0 ≤ γ` for `γ ≥ 0`), which can only increase `errγ`. -/
noncomputable def marginErr {d : ℕ} (D : Measure ((Fin d → ℝ) × Bool)) (γ : ℝ) (w : Fin d → ℝ) : ℝ :=
  (D {p | sgn p.2 * dot w p.1 / eNorm p.1 ≤ γ}).toReal

/-- **Optimal γ-margin error `OPT_γ(D)`.** Garg–Jadhav (manuscript, sha256 386bc9b3…43f84d5),
§1, p.3: "min_{w∈H}(errγ(w, D))", with `H` the unit vectors (p.2: `‖w‖₂ = 1`); p.11: "optimal
γ-margin error w.r.t. the class of halfspaces (OPTγ)".

**Formalization Note.** The infimum ranges over the unit vectors `Σᵢ wᵢ² = 1` only; this set is
nonempty for `d ≥ 1` and the values lie in `[0, 1]`, so the infimum is the true infimum (and the
printed `min`'s value whenever it is attained). -/
noncomputable def optMargin {d : ℕ} (D : Measure ((Fin d → ℝ) × Bool)) (γ : ℝ) : ℝ :=
  ⨅ w : {w : Fin d → ℝ // ∑ i, w i ^ 2 = 1}, marginErr D γ w.1

end Supplement

end AgnHalfMem



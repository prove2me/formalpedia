-- Prove2me | Definitions.Def_QMCBeyondHK_IsThinningDensity
-- name    : QMCBeyondHK_IsThinningDensity
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:36:09.814917+00:00
-- url     : https://prove2.me/theorems/0d78c1af-3ba6-4ff9-b8e9-1e6834abce24
-- title:
--   Target-density rules of the $(1+\varepsilon)$-online thinning framework
-- statement:
--   A **target-density rule** of the $(1+\varepsilon)$-online thinning framework assigns to every step $t$ a function $\mu_t(\omega, x)$ such that
--
--   1. $\mu_t$ is determined by the randomness of steps $< t$: it is jointly measurable in $(\omega, x)$ for $\mathcal F_t \otimes \mathcal B(\mathbb R^d)$;
--   2. $1 - \varepsilon/2 \le \mu_t(\omega, x) \le 1 + \varepsilon/2$ for every $x \in [0,1)^d$;
--   3. $\int_{[0,1)^d} \mu_t(\omega, x)\,dx = 1$.
--
--   At step $t$ the strategy retains $z_t = x_t$ if $\xi_t \le \mu_t(x_t) - \varepsilon/2$ and $z_t = y_t$ otherwise; the step **rejects** in the second case.
--
--   **Formalization Note** The paper's strategies choose $\mu_t$ as a function of the retained points $A_t$; a rule that may depend on all inputs of the earlier steps covers them. "Target density" includes $\int \mu_t = 1$, as §3.1 confirms ("Thus µ_t is a probability density satisfying the requirement of the (1 + ε)-thinning framework").
-- source:
--   Ezeunala, Jha, Jiang, Quasi-Monte Carlo Beyond Hardy–Krause II: (1 + ε)n Samples Suffice, arXiv:2609.10921 (sha256 bc273e88…), §2.1, p.7 (PDF p.9)

import Mathlib
import Definitions.Def_QMCBeyondHK_IsStreamInput

set_option autoImplicit false

open MeasureTheory

namespace QMCBeyondHK

/-- A target-density rule of the `(1 + ε)`-online thinning framework (arXiv:2609.10921,
sha256 bc273e88…, §2.1, p.7, PDF p.9): at every step `t` a density `μ_t(ω, ·)` on `[0,1)^d`
determined by the randomness of steps `< t`, with `μ_t(x) ∈ [1 − ε/2, 1 + ε/2]` on the cube and
`∫ μ_t = 1`.

**Formalization Note** `μ_t` may depend on the inputs `x_u, ξ_u, y_u` of all steps `u < t`
(jointly measurable in `(ω, x)` for `stepSigma t ⊗ Borel`); the strategies of the paper, whose
density is a function of the retained points `A_t`, are instances. "Target density" includes
`∫ μ_t = 1` (§3.1, p.9: "Thus µ_t is a probability density satisfying the requirement of the
(1 + ε)-thinning framework"). -/
structure IsThinningDensity {d : ℕ} {Ω : Type*} (ε : ℝ) (X : ℕ → Ω → Fin d → ℝ)
    (Ξ : ℕ → Ω → ℝ) (Y : ℕ → Ω → Fin d → ℝ) (μ : ℕ → Ω → (Fin d → ℝ) → ℝ) : Prop where
  measurable : ∀ t, @Measurable (Ω × (Fin d → ℝ)) ℝ
    (@Prod.instMeasurableSpace Ω (Fin d → ℝ) (stepSigma X Ξ Y t) _) _ (fun p => μ t p.1 p.2)
  mem_range : ∀ t ω x, x ∈ cube d → 1 - ε / 2 ≤ μ t ω x ∧ μ t ω x ≤ 1 + ε / 2
  integral_eq_one : ∀ t ω, ∫ x in cube d, μ t ω x = 1

open Classical in
/-- The point `z_t` retained at step `t` by a `(1 + ε)`-online thinning strategy with target
densities `μ` (arXiv:2609.10921, sha256 bc273e88…, §2.1, p.7, PDF p.9): `x_t` if
`ξ_t ≤ μ_t(x_t) − ε/2`, otherwise the fresh sample `y_t`. -/
noncomputable def framePoint {d : ℕ} {Ω : Type*} (ε : ℝ) (μ : ℕ → Ω → (Fin d → ℝ) → ℝ)
    (X : ℕ → Ω → Fin d → ℝ) (Ξ : ℕ → Ω → ℝ) (Y : ℕ → Ω → Fin d → ℝ) (t : ℕ) (ω : Ω) :
    Fin d → ℝ :=
  if Ξ t ω ≤ μ t ω (X t ω) - ε / 2 then X t ω else Y t ω

open Classical in
/-- The number of rejections (steps that draw a second sample `y_t`) among the first `n` steps of
a `(1 + ε)`-online thinning strategy (arXiv:2609.10921, sha256 bc273e88…, Proposition 2.4, p.7). -/
noncomputable def frameRejections {d : ℕ} {Ω : Type*} (ε : ℝ) (μ : ℕ → Ω → (Fin d → ℝ) → ℝ)
    (X : ℕ → Ω → Fin d → ℝ) (Ξ : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) : ℕ :=
  ((Finset.range n).filter (fun t => ¬ (Ξ t ω ≤ μ t ω (X t ω) - ε / 2))).card

end QMCBeyondHK



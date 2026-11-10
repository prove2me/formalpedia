-- Prove2me | Definitions.Def_ThinShellSampling_psAnnAttempt
-- name    : ThinShellSampling_psAnnAttempt
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T04:48:11.479868+00:00
-- url     : https://prove2.me/theorems/2b762582-ca4b-434d-b411-884edb3c70a8
-- title:
--   One attempt of the lifted proximal sampler $\mathsf{PS}_{\mathrm{ann}}$ and its uncapped chain
-- statement:
--   Fix $\sigma^2>0$, $\rho\ge0$, a step size $h>0$, a threshold $\tau$ and $N$ iterations, and write $r=\sigma^2/(h+\sigma^2)$, $h_r=rh$. One attempt of $\mathsf{PS}_{\mathrm{ann}}$ for $\mu_{\sigma^2,\rho}$ starts at $v_0=(x_0,t_0)$ and for $k=0,\dots,N-1$:
--
--   1. **Forward:** $w_{k+1}=(y_{k+1},s_{k+1})\sim N(v_k,hI_{n+1})$.
--   2. **Backward:** draw $v\sim N(ry_{k+1},h_rI_n)\otimes N(s_{k+1}-\rho h,h)$ until $v\in\bar K$, each membership test costing one evaluation query; if the loop exceeds $\tau$ trials, declare failure.
--
--   The attempt outputs $v_N$, or failure. The **uncapped chain** ($\tau=\infty$) is the exact proximal sampler for $\mu_{\sigma^2,\rho}$, whose backward kernel is $\mu_{\sigma^2,\rho}(dv)\,e^{-\|w-v\|^2/(2h)}$ normalized.
--
--   This is the sampler of Proposition 6.5 and the building block of Algorithm 6.6.
--
--   **Formalization Note** The attempt is an oracle program; its inputs are $a=V(0)/n$, $D$, $b$, $\sigma^2,\rho,h,\lfloor\tau\rfloor$, $N$ and the initial point. Gaussians are produced from the uniform stream by the Box–Muller transform at no query cost, and every trial queries $V$ at the proposed $x$ once.
-- source:
--   Kook, Vempala, Thin-Shell Stability and Heat-Adjoint Hypercontractivity: Logconcave Sampling with Sesteric Complexity from a Cold Start, STOC 2027 submission (manuscript sha256 25a041a9…), §6.3.1, p.38 (PDF p.40); Proposition 6.5, p.39 (PDF p.41)

import Mathlib
import Definitions.Def_ThinShellSampling_Prog
import Definitions.Def_ThinShellSampling_proxIter
import Definitions.Def_ThinShellSampling_muAnneal

set_option autoImplicit false

namespace ThinShellSampling

open MeasureTheory ProbabilityTheory
open scoped ENNReal

/-- A standard normal real from two uniforms (Box–Muller): `√(−2 log u₁) · cos(2π u₂)`. Makes no
oracle query. -/
noncomputable def stdNormal (n : ℕ) : Prog n ℝ :=
  .sample fun u₁ => .sample fun u₂ =>
    .pure (Real.sqrt (-2 * Real.log u₁) * Real.cos (2 * Real.pi * u₂))

/-- `m` independent standard normal reals. Makes no oracle query. -/
noncomputable def normals (n : ℕ) : (m : ℕ) → Prog n (Fin m → ℝ)
  | 0 => .pure Fin.elim0
  | m + 1 => (stdNormal n).bind fun g => (normals n m).bind fun gs => .pure (Fin.cons g gs)

/-- A standard Gaussian vector `G ∼ N(0, Iₙ)` of `ℝⁿ`. Makes no oracle query. -/
noncomputable def gaussVec (n : ℕ) : Prog n (EuclideanSpace ℝ (Fin n)) :=
  (normals n n).bind fun g => .pure (WithLp.toLp 2 g)

open Classical in
/-- **The rejection loop of the backward step of `PS_ann`**, with at most `k` trials remaining.

Each trial draws `v = (x, t) ∼ N(r y, h_r Iₙ) ⊗ N(s − ρh, h)` with `r = σ²/(h + σ²)`, `h_r = rh`,
spends **one** oracle query on `V(x)`, and accepts iff `v ∈ K̄`, i.e. `V(x) ≤ nt`, `‖x‖ ≤ D` and
`a − 10 ≤ t ≤ a + b`. After `k` rejected trials it declares failure (`none`).

Kook, Vempala, *Thin-Shell Stability and Heat-Adjoint Hypercontractivity*, STOC 2027 submission
(manuscript sha256 25a041a9…), §6.3.1, p.38 (PDF p.40): "[Backward] … draw
`v_{k+1} ∼ N(r y_{k+1}, h_r Iₙ) ⊗ N(s_{k+1} − ρh, h)` until `v_{k+1} ∈ K̄`. If this rejection loop
exceeds `τ` trials, declare failure." -/
noncomputable def backwardLoop (n : ℕ) (a D b σ2 ρ h : ℝ)
    (w : EuclideanSpace ℝ (Fin n) × ℝ) :
    ℕ → Prog n (Option (EuclideanSpace ℝ (Fin n) × ℝ))
  | 0 => .pure none
  | k + 1 =>
    (gaussVec n).bind fun G => (stdNormal n).bind fun g =>
      let r := σ2 / (h + σ2)
      let x := r • w.1 + Real.sqrt (r * h) • G
      let t := w.2 - ρ * h + Real.sqrt h * g
      .query x fun v =>
        if v ≤ (((n : ℝ) * t : ℝ) : WithTop ℝ) ∧ ‖x‖ ≤ D ∧ a - 10 ≤ t ∧ t ≤ a + b then
          .pure (some (x, t))
        else backwardLoop n a D b σ2 ρ h w k

/-- `N` iterations of `PS_ann` from the point `v`: forward `w ∼ N(v, h I_{n+1})`, then the capped
backward rejection loop with `τ` trials; `none` as soon as one backward step fails. -/
noncomputable def psAnnLoop (n : ℕ) (a D b σ2 ρ h : ℝ) (τ : ℕ) :
    ℕ → EuclideanSpace ℝ (Fin n) × ℝ → Prog n (Option (EuclideanSpace ℝ (Fin n) × ℝ))
  | 0, v => .pure (some v)
  | N + 1, v =>
    (gaussVec n).bind fun G => (stdNormal n).bind fun g =>
      (backwardLoop n a D b σ2 ρ h (v.1 + Real.sqrt h • G, v.2 + Real.sqrt h * g) τ).bind
        fun o => match o with
          | none => .pure none
          | some v' => psAnnLoop n a D b σ2 ρ h τ N v'

/-- **One attempt of `PS_ann`** (the proximal sampler for the annealing law `μ_{σ²,ρ}` with step size
`h` and rejection threshold `τ`), run for `N` iterations from the initial point `z₀`. It returns the
final point, or `none` if failure is declared.

Kook, Vempala, STOC 2027 submission (manuscript sha256 25a041a9…), §6.3.1, p.38 (PDF p.40), and
Proposition 6.5, p.39 (PDF p.41).

**Formalization Note.** The truncation constants `a = V(0)/n`, `D = 1 ∨ Rℓ`, `b = 13ℓ + 5` are inputs
(the program never sees `V` except through queries). Gaussians are produced from the uniform stream by
Box–Muller at no query cost; each membership test `v ∈ K̄` costs exactly one query. -/
noncomputable def psAnnAttempt (n : ℕ) (a D b σ2 ρ h : ℝ) (τ N : ℕ)
    (z₀ : EuclideanSpace ℝ (Fin n) × ℝ) : Prog n (Option (EuclideanSpace ℝ (Fin n) × ℝ)) :=
  psAnnLoop n a D b σ2 ρ h τ N z₀

/-- **The uncapped chain** (`τ = ∞`): the law after `N` exact iterations of the proximal sampler for
the target `μ` on `ℝⁿ × ℝ`, from the initial law `μ₀`. Forward kernel `v ↦ N(v, h I_{n+1})`, backward
kernel `μ(dv) e^{−‖w − v‖²/(2h)}` normalized (the augmented target `μ^{V,W}` of §6.3.1, p.38 = PDF
p.40, Kook–Vempala STOC 2027 submission, manuscript sha256 25a041a9…). -/
noncomputable def psAnnIdeal {n : ℕ} (μ : Measure (EuclideanSpace ℝ (Fin n) × ℝ)) (h : ℝ) (N : ℕ)
    (μ₀ : Measure (EuclideanSpace ℝ (Fin n) × ℝ)) : Measure (EuclideanSpace ℝ (Fin n) × ℝ) :=
  (proxStepGen μ
      (fun v => ((gaussianT n h).prod (gaussianReal 0 h.toNNReal)).map (fun z => v + z))
      (fun v w => ‖v.1 - w.1‖ ^ 2 + (v.2 - w.2) ^ 2) h)^[N] μ₀

end ThinShellSampling



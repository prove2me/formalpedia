-- Prove2me | Definitions.Def_ThinShellSampling_Supplement_psUnifAttempt
-- name    : ThinShellSampling_Supplement_psUnifAttempt
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T07:37:54.572196+00:00
-- url     : https://prove2.me/theorems/cf795f3c-291c-4547-a182-c08d797ec42e
-- title:
--   One attempt of $\mathsf{PS}_{\mathrm{unif}}$ (In-and-Out with a rejection cap $\tau$)
-- statement:
--   Fix a step size $h>0$, a threshold $\tau\in\mathbb N$, an iteration count $N$ and an initial distribution $\pi_0$. One **attempt of $\mathsf{PS}_{\mathrm{unif}}$** for a convex body $\mathcal K$ given by a membership oracle draws $x_0\sim\pi_0$ and then, for $k=0,\dots,N-1$:
--
--   1. **Forward:** $y_{k+1}=x_k+\sqrt h\,G$ with $G\sim\mathcal N(0,I_n)$;
--   2. **Backward:** draw $x'\sim\mathcal N(y_{k+1},hI_n)$ repeatedly until $x'\in\mathcal K$ and set $x_{k+1}=x'$; each check $x'\in\mathcal K$ costs one membership query; if $\tau$ trials are rejected, the attempt declares failure.
--
--   After $N$ successful iterations the attempt returns $x_N$. Conditioned on acceptance, the backward step samples $\pi^{X|Y=y}\propto\gamma_h(\cdot-y)\,1_{\mathcal K}$, so the uncapped chain is the proximal sampler for the uniform distribution on $\mathcal K$.
--
--   This is the attempt of Theorem 1.1; the algorithm of that theorem is its restart-until-success wrapper.
--
--   **Formalization Note** $\pi_0$ enters through a measurable map $g:\mathbb R\to\mathbb R^n$ with $g_\#\mathrm{Uniform}[0,1]=\pi_0$, so drawing $x_0$ costs no query. Gaussian vectors are produced from the uniform stream by Box–Muller (published `gaussVec`). Membership of $x'$ is tested by an evaluation query of the indicator potential (finite value iff $x'\in\mathcal K$).
-- source:
--   Kook, Vempala, Thin-Shell Stability and Heat-Adjoint Hypercontractivity: Logconcave Sampling with Sesteric Complexity from a Cold Start, STOC 2027 submission (manuscript sha256 25a041a9…), §1.1, p.2 (PDF p.4) (definition of PS_unif); §2, p.14 (PDF p.16); §2.2.1, p.17 (PDF p.19)

import Mathlib
import Definitions.Def_ThinShellSampling_psAnnAttempt

set_option autoImplicit false

namespace ThinShellSampling.Supplement

open MeasureTheory

/-- **The rejection loop of the backward step of `PS_unif`** from the point `y`, with at most `k`
trials remaining. Each trial draws `x ∼ N(y, h Iₙ)`, spends **one** membership query at `x`, and
accepts iff `x ∈ K` (the oracle value is not `⊤`). After `k` rejected trials it declares failure
(`none`).

Kook, Vempala, STOC 2027 submission (manuscript sha256 25a041a9…), §1.1, p.2 (PDF p.4):
"[Backward] … draw `x_{k+1} ∼ N(y_{k+1}, hIₙ)` repeatedly until `x_{k+1} ∈ K`. If this rejection
loop exceeds `τ` trials, restart from scratch". -/
noncomputable def unifBackward (n : ℕ) (h : ℝ) (y : EuclideanSpace ℝ (Fin n)) :
    ℕ → Prog n (Option (EuclideanSpace ℝ (Fin n)))
  | 0 => .pure none
  | k + 1 =>
    (gaussVec n).bind fun G =>
      let x := y + Real.sqrt h • G
      .query x fun v => if v ≠ ⊤ then .pure (some x) else unifBackward n h y k

/-- `N` iterations of `PS_unif` from the point `x`: forward `y = x + √h·G` with `G ∼ N(0, Iₙ)`,
then the capped backward rejection loop with `τ` trials; `none` as soon as one backward step
fails. -/
noncomputable def unifLoop (n : ℕ) (h : ℝ) (τ : ℕ) :
    ℕ → EuclideanSpace ℝ (Fin n) → Prog n (Option (EuclideanSpace ℝ (Fin n)))
  | 0, x => .pure (some x)
  | N + 1, x =>
    (gaussVec n).bind fun G =>
      (unifBackward n h (x + Real.sqrt h • G) τ).bind fun o =>
        match o with
        | none => .pure none
        | some x' => unifLoop n h τ N x'

/-- **One attempt of `PS_unif`** (In-and-Out with failure declared at the rejection cap) with step
size `h`, threshold `τ` and `N` iterations, initialized at `x₀ = g(u)` for one uniform `u`. It
returns `x_N`, or `none` if some backward step exceeds `τ` trials.

Kook, Vempala, *Thin-Shell Stability and Heat-Adjoint Hypercontractivity: Logconcave Sampling with
Sesteric Complexity from a Cold Start*, STOC 2027 submission (manuscript sha256 25a041a9…), §1.1,
p.2 (PDF p.4): "starting with `x₀ ∼ π₀^X`, step size `h`, and threshold `τ`, [Forward]
`y_{k+1} ∼ π^{Y|X=x_k} = γ_h(· − x_k)`. [Backward] `x_{k+1} ∼ π^{X|Y=y_{k+1}} ∝ γ_h(· − y_{k+1}) 1_K(·)`
… Note that each check `x_{k+1} ∈ K` incurs a single query to the membership oracle"; §2.2.1, p.17
(PDF p.19).

**Formalization Note.** The initial distribution `π₀` enters through a measurable map `g : ℝ → ℝⁿ`
whose push-forward of `Uniform[0, 1]` is `π₀` (drawing `x₀` costs no query). Gaussians come from the
uniform stream by Box–Muller (`gaussVec`) at no query cost. The program is run against the indicator
potential of `K` (`indicatorPot`), whose evaluation oracle is the membership oracle. -/
noncomputable def psUnifAttempt (n : ℕ) (h : ℝ) (τ N : ℕ) (g : ℝ → EuclideanSpace ℝ (Fin n)) :
    Prog n (Option (EuclideanSpace ℝ (Fin n))) :=
  .sample fun u => unifLoop n h τ N (g u)

end ThinShellSampling.Supplement



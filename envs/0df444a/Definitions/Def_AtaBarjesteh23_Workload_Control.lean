-- Prove2me | Definitions.Def_AtaBarjesteh23_Workload_Control
-- name    : AtaBarjesteh23_Workload_Control
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-15T06:40:38.280816+00:00
-- url     : https://prove2.me/theorems/faa1a443-79e0-4044-bb2e-cd7adc2d4cd6
-- title:
--   §5–§6.1, pp. 15–16 — admissible controls (30)–(32), barrier policies (Definition 1, (34)) and the average cost (29)
-- statement:
--   Fix the data of the `Setting` file, a probability space $(\Omega,\mathcal F,P)$ with filtration $\mathbb F$, and an $\mathbb F$-Brownian motion $B$ with drift $\mu$ and variance $\sigma^2$.
--
--   **Admissible controls** ((30)–(32)). A control $(L,U,\theta)$ with workload $W$ is admissible when
--   1. $\theta$ is progressively measurable on $[0,\infty)$ and each path $s\mapsto\theta(s,\omega)$ is integrable on every $[0,t]$;
--   2. $L$ and $U$ are adapted, with nondecreasing right-continuous paths on $[0,\infty)$ and $L(0)=U(0)=0$ (31);
--   3. for $t\ge0$,
--   $$W(t)=B(t)-\int_0^t\theta(s)\,ds-U(t)+L(t); \tag{30}$$
--   4. $\displaystyle\limsup_{t\to\infty}\frac{\mathbb E|W(t)|}{t}=0.$ (32)
--
--   **Barrier policies** (Definition 1). Given $l<u$, an admissible control is a barrier policy with lower barrier $l$ and upper barrier $u$ if $W(t)\in[l,u]$ for all $t\ge0$ and
--   $$\int_0^t\mathbb 1_{\{W(s)>l\}}\,dL(s)=0\quad\text{and}\quad\int_0^t\mathbb 1_{\{W(s)<u\}}\,dU(s)=0,\qquad t\ge0. \tag{34}$$
--
--   **Cost** ((29)). The expected cumulative cost up to $t$ and its average are
--   $$J(t)=\mathbb E\Big[\int_0^t c(\theta(s))\,ds+\int_0^t h(W(s))\,ds+\kappa L(t)\Big],\qquad \frac{J(t)}t,$$
--   and the EWF asks to minimize $\limsup_{t\to\infty}J(t)/t$ over admissible controls.
--
--   **Formalization Note** The integrals in (34) are Lebesgue–Stieltjes integrals against the path of $L$ (resp. $U$), extended by $0$ to negative times so that there is no atom at $0$; they include the jumps of $L$ and $U$. $J(t)$ is computed in $[0,\infty]$ (all three integrands are nonnegative), so an infinite expected cost is $+\infty$, never a junk value. Progressive measurability is Mathlib's `IsStronglyProgressive` applied to $\theta$ set to $0$ at negative times; integrability of the paths of $\theta$ makes $\int_0^t\theta(s)\,ds$ a genuine Lebesgue integral. Right-continuity of $L,U$, the adaptedness of $L,U$ and the local integrability of $\theta$ are implicit in the paper (RCLL controls).
-- source:
--   Ata and Barjesteh, An Approximate Analysis of Dynamic Pricing, Outsourcing, and Scheduling Policies for a Multiclass Make-to-Stock Queue in the Heavy Traffic Regime, accepted manuscript (SSRN 3464763; published in Operations Research 71(1):341–357, 2023, doi:10.1287/opre.2022.2361), pp. 15–16, (29)–(32), Definition 1, (34)

import Mathlib
import Definitions.Def_AtaBarjesteh23_Workload_Setting
import Definitions.Def_AtaBarjesteh23_Workload_DriftBM

open MeasureTheory Set Filter

namespace AtaBarjesteh23.Workload

/-- An admissible control `(L, U, θ)` of the EWF with workload `W` ((30)–(32)):
`θ` progressively measurable on `[0, ∞)` with locally integrable paths, `L` and `U` adapted with
nondecreasing right-continuous paths on `[0, ∞)` and `L 0 = U 0 = 0` (31),
`W t = B t - ∫₀ᵗ θ s ds - U t + L t` for `t ≥ 0` (30), and `limsup E|W t| / t = 0` (32). -/
def IsAdmissible {Ω : Type*} [mΩ : MeasurableSpace Ω] (𝔽 : Filtration ℝ mΩ) (P : Measure Ω)
    (B θ L U W : ℝ → Ω → ℝ) : Prop :=
  IsStronglyProgressive 𝔽 (fun t ω => if 0 ≤ t then θ t ω else 0) ∧
    (∀ ω t, 0 ≤ t → IntervalIntegrable (fun s => θ s ω) volume 0 t) ∧
    (∀ t, 0 ≤ t → StronglyMeasurable[𝔽 t] (L t) ∧ StronglyMeasurable[𝔽 t] (U t)) ∧
    (∀ ω, MonotoneOn (fun t => L t ω) (Ici 0) ∧ MonotoneOn (fun t => U t ω) (Ici 0) ∧
      (∀ t, 0 ≤ t → ContinuousWithinAt (fun s => L s ω) (Ici t) t) ∧
      (∀ t, 0 ≤ t → ContinuousWithinAt (fun s => U s ω) (Ici t) t) ∧
      L 0 ω = 0 ∧ U 0 ω = 0) ∧
    (∀ t ω, 0 ≤ t → W t ω = B t ω - (∫ s in (0 : ℝ)..t, θ s ω) - U t ω + L t ω) ∧
    limsup (fun t : ℝ => (∫⁻ ω, ‖W t ω‖ₑ ∂P) / ENNReal.ofReal t) atTop = 0

/-- A barrier policy with lower barrier `l` and upper barrier `u` (Definition 1, (34)): an
admissible control with `l < u`, `W t ∈ [l, u]` for `t ≥ 0`, and, for every `t ≥ 0`, the
Lebesgue–Stieltjes measure of the path of `L` (extended by `0` to negative times) gives no mass to
`{s ∈ [0, t] : W s > l}`, and that of `U` gives no mass to `{s ∈ [0, t] : W s < u}`. -/
def IsBarrierPolicy {Ω : Type*} [mΩ : MeasurableSpace Ω] (𝔽 : Filtration ℝ mΩ) (P : Measure Ω)
    (B : ℝ → Ω → ℝ) (l u : ℝ) (θ L U W : ℝ → Ω → ℝ) : Prop :=
  l < u ∧ IsAdmissible 𝔽 P B θ L U W ∧
    (∀ t ω, 0 ≤ t → W t ω ∈ Icc l u) ∧
    ∀ t ω, 0 ≤ t →
      (∃ FL : StieltjesFunction ℝ, (∀ s, FL s = L (max s 0) ω) ∧
        FL.measure ({s | l < W s ω} ∩ Icc 0 t) = 0) ∧
      (∃ FU : StieltjesFunction ℝ, (∀ s, FU s = U (max s 0) ω) ∧
        FU.measure ({s | W s ω < u} ∩ Icc 0 t) = 0)

namespace Model

variable (M : Model)

/-- The expected cumulative cost of (29) up to time `t`, in `ℝ≥0∞`:
`E[∫₀ᵗ c(θ(s)) ds + ∫₀ᵗ h(W(s)) ds + κ L(t)]`. -/
noncomputable def expCost {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (θ L W : ℝ → Ω → ℝ) (t : ℝ) : ENNReal :=
  ∫⁻ ω, ((∫⁻ s in Icc 0 t,
      ENNReal.ofReal (M.cost (θ s ω)) + ENNReal.ofReal (M.hcost (W s ω)))
    + ENNReal.ofReal (M.kappa * L t ω)) ∂P

/-- The average cost `(1/t) E[…]` of (29) at time `t`. -/
noncomputable def avgCost {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (θ L W : ℝ → Ω → ℝ) (t : ℝ) : ENNReal :=
  M.expCost P θ L W t / ENNReal.ofReal t

end Model

end AtaBarjesteh23.Workload



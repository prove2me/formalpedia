-- Prove2me | Definitions.Def_OptStopC1_TimeDeriv_Flow
-- name    : OptStopC1_TimeDeriv_Flow
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T02:30:00.662784+00:00
-- url     : https://prove2.me/theorems/33087ba1-5040-439e-b704-7a0844ad8a91
-- title:
--   §2.1, §2.3–2.4, §4.2 — the time-space stochastic flow, entry and hitting times, and probabilistic regularity
-- statement:
--   This file sets up the process of the finite-horizon optimal stopping problem (2.2) of De Angelis and Peskir in its time-space form, together with the first entry and hitting times and the notion of probabilistic regularity of a boundary point.
--
--   **State space.** Write $d=m+1\ge 1$. The process is $X_s=(t+s,X^x_s)$: its first coordinate is time, and its remaining $d-1$ coordinates live in $\mathbb R^{d-1}$ with the Euclidean norm. The time-space domain of the problem with horizon $T>0$ is $[0,T]\times\mathbb R^{d-1}$.
--
--   **Càdlàg flow.** On a probability space $(\Omega,\mathcal F,P)$ with a filtration $(\mathcal F_s)_{s\ge0}$, the spatial part is a stochastic flow $(X^x_s)_{s\ge 0,\,x\in\mathbb R^{d-1}}$: for every starting point $x$,
--   1. $X^x_0=x$;
--   2. every path $s\mapsto X^x_s(\omega)$ is right-continuous with left limits;
--   3. $X^x$ is adapted to $(\mathcal F_s)$.
--
--   The whole flow is $X^{t,x}_s=(t+s,X^x_s)$, so that $X^{t,x}_0=(t,x)$.
--
--   The paper also assumes left continuity over stopping times: if finite stopping times $\rho_n$ announce $\rho$, then $X^x_{\rho_n}\to X^x_\rho$ almost surely.
--
--   **Strong Markov property.** For every $x$, every finite stopping time $\rho$ and every bounded measurable functional $\Phi$ of the path,
--   $$\mathsf E\big[\Phi(X^x_{\rho+\cdot})\,\big|\,\mathcal F_\rho\big]=\big(y\mapsto \mathsf E[\Phi(X^y_\cdot)]\big)(X^x_\rho)\qquad P\text{-a.s.}$$
--
--   **Continuous flow.** The flow is continuous in the space variable if there is one $P$-null set $N$ such that $x\mapsto X^x_s(\omega)$ is continuous on $\mathbb R^{d-1}$ for every $\omega\notin N$ and every $s\in[0,T]$.
--
--   **Entry and hitting times.** For a set $A\subseteq\mathbb R\times\mathbb R^{d-1}$ and a start $(t,x)$, the first entry time (2.4) and the first hitting time (2.5), with the finite-horizon upper bound, are
--   $$\tau^{t,x}_A=\inf\{s\in[0,T-t] : (t+s,X^x_s)\in A\},\qquad \sigma^{t,x}_A=\inf\{s\in(0,T-t] : (t+s,X^x_s)\in A\},$$
--   with values in $[0,\infty]$ and $\inf\emptyset=\infty$. The standing hypothesis of the paper is that these are stopping times whenever $A$ is open or closed and $(t,x)\in[0,T]\times\mathbb R^{d-1}$.
--
--   **Probabilistic regularity (2.7).** A point $z$ is probabilistically regular for a set $A$ if
--   $$P\big(\sigma^{z}_A=0\big)=1 .$$
--
--   These objects are the language of Theorem 15: the regularity it assumes is probabilistic regularity of a boundary point for the interior $D^\circ$ of the stopping set.
--
--   **Formalization Note** Time is `ℝ≥0`, the spatial space is `EuclideanSpace ℝ (Fin m)`, and the hitting times take values in `WithTop ℝ≥0` (that is, $[0,\infty]$). The paper's $P_x$ and $\mathsf E_x$ are written as $P$ and $\mathsf E$ of the flow started at $x$, following $\mathrm{Law}(X\mid P_x)=\mathrm{Law}(X^x\mid P)$ (p. 6). The path functionals in the strong Markov property are measurable for the product σ-algebra on paths `ℝ≥0 → ℝ^{d−1}`, and $\mathcal F_\rho$ is Mathlib's σ-algebra of a stopping time. At $t=T$ the window $(0,T-t]$ is empty, so $\sigma^{T,x}_A=\infty$ and no point with $t=T$ is probabilistically regular, as in the paper.
-- source:
--   De Angelis & Peskir, Global C¹ Regularity of the Value Function in Optimal Stopping Problems, arXiv:1812.04564v2, pp. 3–6, 9, 15–16, §2.1, (2.4), (2.5), (2.7), §2.4 (continuous stochastic flows), §3 p. 9 (entry/hitting times are stopping times), §4.2 (time-space flow X^{t,x}_s)

import Mathlib

namespace OptStopC1.TimeDeriv

open MeasureTheory Filter Topology
open scoped NNReal ENNReal

/-- The spatial state space `ℝ^{d−1}` of the time-space process `X_s = (t + s, X^x_s)`, with
`d = m + 1` (so `d ≥ 1`; `m = 0` is allowed). Points carry the Euclidean norm. -/
abbrev Space (m : ℕ) : Type := EuclideanSpace ℝ (Fin m)

/-- The time-space domain `[0, T] × ℝ^{d−1}` of the finite-horizon problem (2.2). -/
def domain (m : ℕ) (T : ℝ) : Set (ℝ × Space m) :=
  Set.Icc 0 T ×ˢ Set.univ

variable {m : ℕ} {Ω : Type*} [mΩ : MeasurableSpace Ω]

/-- The spatial part `(X²,…,X^d)` of the process is realised as a stochastic flow
`(X^x_s)_{s ≥ 0, x ∈ ℝ^{d−1}}` on `(Ω, F, P)` (§2.4, p. 6; §4.2, pp. 15–16): `X^x_0 = x`, every
sample path `s ↦ X^x_s(ω)` is right-continuous with left limits, and every `X^x` is adapted to
the common filtration `𝔽`. The time coordinate is `C^t_s = t + s`, so the whole flow is
`X^{t,x}_s = (t + s, X^x_s)`. -/
structure IsCadlagFlow (𝔽 : Filtration ℝ≥0 mΩ) (X : Space m → ℝ≥0 → Ω → Space m) : Prop where
  start : ∀ x ω, X x 0 ω = x
  right_cont : ∀ x ω (s : ℝ≥0), ContinuousWithinAt (fun u => X x u ω) (Set.Ici s) s
  left_lim : ∀ x ω (s : ℝ≥0), 0 < s → ∃ l, Tendsto (fun u => X x u ω) (𝓝[<] s) (𝓝 l)
  adapted : ∀ x, Adapted 𝔽 (X x)

/-- Left continuity over stopping times, part of the paper's standing "standard Markov
process" assumption (p. 3). An announcing sequence of finite stopping times increasing to
`ρ`, strictly before `ρ`, has spatial states converging to the state at `ρ`. -/
def IsQuasiLeftContinuousFlow (P : Measure Ω) (𝔽 : Filtration ℝ≥0 mΩ)
    (X : Space m → ℝ≥0 → Ω → Space m) : Prop :=
  ∀ (x : Space m) (ρ : Ω → ℝ≥0) (ρn : ℕ → Ω → ℝ≥0),
    IsStoppingTime 𝔽 (fun ω => ((ρ ω : ℝ≥0) : WithTop ℝ≥0)) →
    (∀ n, IsStoppingTime 𝔽 (fun ω => ((ρn n ω : ℝ≥0) : WithTop ℝ≥0))) →
    (∀ ω, Monotone (fun n => ρn n ω)) →
    (∀ᵐ ω ∂P, Tendsto (fun n => ρn n ω) atTop (𝓝 (ρ ω))) →
    ∀ᵐ ω ∂P, (∀ n, ρn n ω < ρ ω) →
      Tendsto (fun n => X x (ρn n ω) ω) atTop (𝓝 (X x (ρ ω) ω))

/-- **Strong Markov property in flow form** (the process is a standard Markov process, p. 3):
for every starting point `x`, every finite `𝔽`-stopping time `ρ` and every bounded measurable
functional `Φ` of the path (product σ-algebra on `ℝ≥0 → ℝ^{d−1}`),
`E[Φ(X^x_{ρ+·}) | F_ρ] = (y ↦ E[Φ(X^y_·)])(X^x_ρ)` almost surely. Because the time coordinate
of `X^{t,x}_s = (t + s, X^x_s)` is deterministic and the spatial flow does not depend on `t`,
this is the strong Markov property of the time-space process. -/
def IsStrongMarkovFlow (P : Measure Ω) (𝔽 : Filtration ℝ≥0 mΩ)
    (X : Space m → ℝ≥0 → Ω → Space m) : Prop :=
  ∀ (x : Space m) (ρ : Ω → ℝ≥0) (hρ : IsStoppingTime 𝔽 (fun ω => ((ρ ω : ℝ≥0) : WithTop ℝ≥0)))
    (Φ : (ℝ≥0 → Space m) → ℝ), Measurable Φ → (∃ c : ℝ, ∀ w, |Φ w| ≤ c) →
    P[fun ω => Φ (fun u => X x (ρ ω + u) ω) | hρ.measurableSpace] =ᵐ[P]
      fun ω => ∫ ω', Φ (fun u => X (X x (ρ ω) ω) u ω') ∂P

/-- **Continuous stochastic flow in the space variable** (§2.4, p. 6): there is one `P`-null set
outside of which `x ↦ X^x_s(ω)` is continuous on `ℝ^{d−1}` for every time `s ∈ [0, T]`
(Theorem 15 asks this for `s ∈ [0, T − t]`, `t ∈ [0, T]`). -/
def IsContinuousFlow (P : Measure Ω) (T : ℝ) (X : Space m → ℝ≥0 → Ω → Space m) : Prop :=
  ∀ᵐ ω ∂P, ∀ s : ℝ≥0, (s : ℝ) ≤ T → Continuous (fun x => X x s ω)

/-- The **first entry time** (2.4) of the time-space process started at `p = (t, x)` into a set
`A ⊆ ℝ × ℝ^{d−1}`, with the finite-horizon upper bound of p. 4:
`τ^{t,x}_A = inf { s ∈ [0, T − t] | (t + s, X^x_s) ∈ A }`, valued in `[0, ∞]`, `inf ∅ = ∞`. -/
noncomputable def entryTime (T : ℝ) (X : Space m → ℝ≥0 → Ω → Space m) (A : Set (ℝ × Space m))
    (p : ℝ × Space m) (ω : Ω) : WithTop ℝ≥0 :=
  ⨅ (s : ℝ≥0) (_ : (s : ℝ) ≤ T - p.1 ∧ (p.1 + s, X p.2 s ω) ∈ A), (s : WithTop ℝ≥0)

/-- The **first hitting time** (2.5) of the time-space process started at `p = (t, x)` to a set
`A`, with the finite-horizon upper bound of p. 4:
`σ^{t,x}_A = inf { s ∈ (0, T − t] | (t + s, X^x_s) ∈ A }`, valued in `[0, ∞]`, `inf ∅ = ∞`. -/
noncomputable def hitTime (T : ℝ) (X : Space m → ℝ≥0 → Ω → Space m) (A : Set (ℝ × Space m))
    (p : ℝ × Space m) (ω : Ω) : WithTop ℝ≥0 :=
  ⨅ (s : ℝ≥0) (_ : 0 < s ∧ (s : ℝ) ≤ T - p.1 ∧ (p.1 + s, X p.2 s ω) ∈ A), (s : WithTop ℝ≥0)

/-- Standing hypothesis (p. 9, "the first entry and hitting times of X to Borel (open and closed)
sets are stopping times"): for every open or closed `A` and every start `p ∈ [0, T] × ℝ^{d−1}`,
`τ^{p}_A` and `σ^{p}_A` are `𝔽`-stopping times. -/
def EntryHittingAreStoppingTimes (𝔽 : Filtration ℝ≥0 mΩ) (T : ℝ)
    (X : Space m → ℝ≥0 → Ω → Space m) : Prop :=
  ∀ A : Set (ℝ × Space m), (IsOpen A ∨ IsClosed A) → ∀ p ∈ domain m T,
    IsStoppingTime 𝔽 (entryTime T X A p) ∧ IsStoppingTime 𝔽 (hitTime T X A p)

/-- **Probabilistic regularity** (2.7) of a point `z` for a set `A` (p. 5: "regularity of
`z ∈ ∂C` for the set `A`"): `P_z(σ_A = 0) = 1`, written for the flow started at `z`. -/
def IsProbRegular (P : Measure Ω) (T : ℝ) (X : Space m → ℝ≥0 → Ω → Space m)
    (A : Set (ℝ × Space m)) (z : ℝ × Space m) : Prop :=
  P {ω | hitTime T X A z ω = 0} = 1

end OptStopC1.TimeDeriv



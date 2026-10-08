-- Prove2me | Definitions.Def_CouplingHMC_Lyap_Setting
-- name    : CouplingHMC_Lyap_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T05:26:54.270807+00:00
-- url     : https://prove2.me/theorems/6ec919eb-9792-4c18-bcb8-2f7bfa973efb
-- title:
--   §2.6, §6, pp. 17–19, 42–44 — Assumption 2.3 (C1)–(C3), the Kantorovich distance 𝒲_ρ, δ(C) of (43), πⁿ, and the stopped process M_n of (131)
-- statement:
--   This file fixes the objects of the general Lyapunov–contractivity theorem of Bou-Rabee, Eberle and Zimmer (§2.6). Throughout, $(S,\rho)$ is a complete separable metric space with its Borel $\sigma$-algebra $\mathcal B(S)$, and $\pi(x,dy)$ is a Markov transition kernel on $S$.
--
--   1. **$n$-step kernel.** $\pi^0(x,\cdot)=\delta_x$ and $\pi^{n+1}=\pi\pi^{n}$; for a probability measure $\nu$, $\nu\pi^n=\int\pi^n(x,\cdot)\,\nu(dx)$ is the law after $n$ steps from initial law $\nu$.
--   2. **Kantorovich distance.** For probability measures $\nu,\eta$ on $S$,
--   $$\mathcal W_\rho(\nu,\eta)=\inf_{\gamma\in C(\nu,\eta)}\int\rho(x,y)\,\gamma(dx\,dy)\in[0,\infty],$$
--   the infimum over all couplings $\gamma$ of $\nu$ and $\eta$ (probability measures on $S\times S$ with marginals $\nu$ and $\eta$).
--   3. **Assumption 2.3.** For a constant $C$ and measurable $\psi,\varphi:S\to(0,\infty)$:
--      - (C1) *main Lyapunov condition*: $\lambda\ge1$ and $(\pi\psi)(x)\le\lambda\psi(x)$ for every $x$ with $\psi(x)\le C$;
--      - (C2) *global Lyapunov condition*: $\beta\ge1$, $(\pi\varphi)(x)\le\beta\varphi(x)$ and $\rho(x,y)\le\varphi(x)+\varphi(y)$ for all $x,y$;
--      - (C3) *local contractivity*: a probability space $(\Omega,\mathcal A,P)$, a constant $c>0$ and a measurable map $(x,y,\omega)\mapsto(X'(x,y,\omega),Y'(x,y,\omega))$ such that for all $x,y$ the pair $(X'(x,y,\cdot),Y'(x,y,\cdot))$ is a coupling of $\pi(x,\cdot)$ and $\pi(y,\cdot)$, and $E[\rho(X'(x,y,\cdot),Y'(x,y,\cdot))]\le e^{-c}\rho(x,y)$ whenever $\psi(x)\le C$ and $\psi(y)\le C$.
--   4. **The constant (43).**
--   $$\delta(C)=\sup\Big\{\frac{\varphi(x)+\varphi(y)}{\psi(x)+\psi(y)}:\ x,y\in S,\ \psi(x)>C\text{ or }\psi(y)>C\Big\}\in[0,\infty].$$
--   5. **Path space.** On $(S\times S)^{\mathbb N}$ the coordinate process is $(X_n,Y_n)(\omega)=\omega(n)$ with natural filtration $\mathcal F_n=\sigma((X_i,Y_i):i\le n)$. For a set $A\subseteq S$, $T=\min\{n\ge0:(X_n,Y_n)\notin A\times A\}\in\mathbb N\cup\{\infty\}$, and the stopped process of (131) is $M_n=e^{c(n\wedge T)}\rho(X_{n\wedge T},Y_{n\wedge T})$.
--   6. **Markov properties.** A law $\widetilde P$ on paths is that of a time-homogeneous Markov chain with kernel $K$ if $\widetilde P(F\cap\{\omega(n+1)\in B\})=\int_F K(\omega(n),B)\,d\widetilde P$ for all $n$, measurable $B$ and $F\in\mathcal F_n$. *Both marginals are Markov with kernel $\pi$ w.r.t. the joint filtration* if the same identity holds for $X_{n+1}$ with $\pi(X_n,B)$ and for $Y_{n+1}$ with $\pi(Y_n,B)$, for every $F\in\mathcal F_n$.
--   7. **Generalized supermartingale.** $M$ is a non-negative supermartingale if $E[M_{n+1};F]\le E[M_n;F]$ for every $n$ and $F\in\mathcal F_n$, the expectations being taken in $[0,\infty]$.
--
--   These objects are all that Theorem 2.11 and its proof refer to; nothing about Hamiltonian Monte Carlo is needed.
--
--   **Formalization Note.** $\rho$ is `dist` of a `MetricSpace`; completeness and separability are hypotheses of the theorems. Every expectation of a non-negative quantity is a lower Lebesgue integral in $[0,\infty]$, so an infinite expectation is $+\infty$ and never a junk $0$. $\lambda$ is written `lam`. Couplings are the published `MongeKantorovichYao.transferencePlans`. The exit time is $\mathbb N_\infty$-valued, and `stopIdx A ω n` is $n\wedge T$ (equal to $n$ when the path never leaves $A\times A$). The supermartingale property is stated as the set-integral inequality on $\mathcal F_n$-sets, which needs no integrability, because the page does not assume $\int\rho\,d\gamma<\infty$.
-- source:
--   Bou-Rabee, Eberle, Zimmer, Coupling and convergence for Hamiltonian Monte Carlo, arXiv:1805.00452v2, §2.6, 𝒲_ρ (p. 17), Assumption 2.3 (p. 18), (43) (p. 19), Lemma 6.1 (130)–(131) (p. 42), proof of Theorem 2.11 (pp. 43–44)

import Mathlib
import Definitions.Def_MongeKantorovichYao_Defs

namespace CouplingHMC.Lyap

open MeasureTheory ProbabilityTheory
open scoped ENNReal

variable {S : Type*} [MetricSpace S] [MeasurableSpace S]

/-- The `n`-step transition kernel `πⁿ`: `π⁰ = id` and `πⁿ⁺¹ = π ∘ πⁿ`.
The law after `n` steps from initial law `ν` is `νπⁿ = ν.bind (iterKernel π n)`. -/
noncomputable def iterKernel (π : Kernel S S) : ℕ → Kernel S S
  | 0 => Kernel.id
  | n + 1 => π ∘ₖ iterKernel π n

/-- The Kantorovich (`L¹` Wasserstein) distance `𝒲_ρ(ν, η) = inf_{γ ∈ C(ν,η)} ∫ ρ(x, y) γ(dx dy)`
with `ρ = dist`, valued in `[0, ∞]`; the infimum runs over all couplings of `ν` and `η`. -/
noncomputable def kantorovich (ν η : Measure S) : ℝ≥0∞ :=
  ⨅ γ ∈ MongeKantorovichYao.transferencePlans ν η, ∫⁻ p, ENNReal.ofReal (dist p.1 p.2) ∂γ

/-- (C1) Main Lyapunov condition: `λ ≥ 1` and `(πψ)(x) ≤ λ ψ(x)` for every `x` with `ψ(x) ≤ C`. -/
def MainLyapunov (π : Kernel S S) (ψ : S → ℝ) (C lam : ℝ) : Prop :=
  1 ≤ lam ∧ ∀ x, ψ x ≤ C → ∫⁻ y, ENNReal.ofReal (ψ y) ∂(π x) ≤ ENNReal.ofReal (lam * ψ x)

/-- (C2) Additional global Lyapunov condition: `β ≥ 1`, `(πφ)(x) ≤ β φ(x)` for every `x`,
and `ρ(x, y) ≤ φ(x) + φ(y)` for all `x, y`. -/
def GlobalLyapunov (π : Kernel S S) (φ : S → ℝ) (β : ℝ) : Prop :=
  1 ≤ β ∧ (∀ x, ∫⁻ y, ENNReal.ofReal (φ y) ∂(π x) ≤ ENNReal.ofReal (β * φ x)) ∧
    ∀ x y, dist x y ≤ φ x + φ y

/-- (C3) Local contractivity: `P` is a probability measure on `Ω`, the map
`(x, y, ω) ↦ (X'(x,y,ω), Y'(x,y,ω))` is measurable, `c > 0`, for all `x, y` the pair
`(X'(x,y,·), Y'(x,y,·))` is a coupling of `π(x, ·)` and `π(y, ·)`, and
`E[ρ(X'(x,y,·), Y'(x,y,·))] ≤ e^{-c} ρ(x, y)` whenever `ψ(x) ≤ C` and `ψ(y) ≤ C`. -/
def LocalContractivity (π : Kernel S S) (ψ : S → ℝ) (C : ℝ) {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (XY : S × S × Ω → S × S) (c : ℝ) : Prop :=
  IsProbabilityMeasure P ∧ Measurable XY ∧ 0 < c ∧
    (∀ x y, P.map (fun ω => (XY (x, y, ω)).1) = π x ∧ P.map (fun ω => (XY (x, y, ω)).2) = π y) ∧
    ∀ x y, ψ x ≤ C → ψ y ≤ C →
      ∫⁻ ω, ENNReal.ofReal (dist (XY (x, y, ω)).1 (XY (x, y, ω)).2) ∂P ≤
        ENNReal.ofReal (Real.exp (-c) * dist x y)

/-- (43) `δ(C) = sup { (φ(x) + φ(y)) / (ψ(x) + ψ(y)) : ψ(x) > C or ψ(y) > C }`, in `[0, ∞]`
(the supremum of the empty family is `0`). -/
noncomputable def deltaC (ψ φ : S → ℝ) (C : ℝ) : ℝ≥0∞ :=
  ⨆ (x : S) (y : S) (_ : C < ψ x ∨ C < ψ y), ENNReal.ofReal ((φ x + φ y) / (ψ x + ψ y))

/-- The natural filtration of the coordinate process `(X_n, Y_n) = ω n` on the path space
`ℕ → S × S`: `ℱ_n = σ((X_i, Y_i) : 0 ≤ i ≤ n)`. -/
def natFilt : Filtration ℕ (MeasurableSpace.pi : MeasurableSpace (ℕ → S × S)) :=
  Filtration.piLE (X := fun _ : ℕ => S × S)

open Classical in
/-- The exit time `T(ω) = min{n ≥ 0 : (X_n, Y_n) ∉ A × A}` in `ℕ∞`, with `T = ∞` if the path
never leaves `A × A`. -/
noncomputable def exitTime (A : Set S) (ω : ℕ → S × S) : ℕ∞ :=
  if h : ∃ k, ω k ∉ A ×ˢ A then (Nat.find h : ℕ∞) else ⊤

open Classical in
/-- The stopped index `n ∧ T`: the first `k ≤ n` with `(X_k, Y_k) ∉ A × A`, or `n` if there is none. -/
noncomputable def stopIdx (A : Set S) (ω : ℕ → S × S) (n : ℕ) : ℕ :=
  if h : ∃ k ≤ n, ω k ∉ A ×ˢ A then Nat.find h else n

/-- The process `M_n = e^{c (n∧T)} ρ(X_{n∧T}, Y_{n∧T})` of (131). -/
noncomputable def stoppedM (A : Set S) (c : ℝ) (ω : ℕ → S × S) (n : ℕ) : ℝ :=
  Real.exp (c * (stopIdx A ω n : ℝ)) *
    dist (ω (stopIdx A ω n)).1 (ω (stopIdx A ω n)).2

/-- A probability law `P̃` on paths `ℕ → X` is the law of a time-homogeneous Markov chain with
transition kernel `K` (w.r.t. its natural filtration): for every `n`, every measurable `B` and
every `F ∈ σ(ω 0, …, ω n)`, `P̃(F ∩ {ω (n+1) ∈ B}) = ∫_F K(ω n, B) dP̃`. -/
def IsMarkovChainLaw {X : Type*} [MeasurableSpace X] (K : Kernel X X) (Pt : Measure (ℕ → X)) :
    Prop :=
  ∀ n (B : Set X), MeasurableSet B → ∀ F : Set (ℕ → X),
    MeasurableSet[Filtration.piLE (X := fun _ : ℕ => X) n] F →
      Pt (F ∩ {ω | ω (n + 1) ∈ B}) = ∫⁻ ω in F, K (ω n) B ∂Pt

/-- Both marginal processes `(X_n)` and `(Y_n)` of the coordinate process on `ℕ → S × S` are
Markov chains with transition kernel `π` with respect to the joint filtration `ℱ_n` of the pair:
for every `n`, measurable `B ⊆ S` and `F ∈ ℱ_n`,
`P̃(F ∩ {X_{n+1} ∈ B}) = ∫_F π(X_n, B) dP̃` and likewise for `Y`. -/
def IsMarginalMarkov (π : Kernel S S) (Pt : Measure (ℕ → S × S)) : Prop :=
  ∀ n (B : Set S), MeasurableSet B → ∀ F : Set (ℕ → S × S), MeasurableSet[natFilt n] F →
    Pt (F ∩ {ω | (ω (n + 1)).1 ∈ B}) = ∫⁻ ω in F, π (ω n).1 B ∂Pt ∧
    Pt (F ∩ {ω | (ω (n + 1)).2 ∈ B}) = ∫⁻ ω in F, π (ω n).2 B ∂Pt

/-- `M_n` of (131) is a non-negative supermartingale w.r.t. `ℱ_n` in the generalized
(`[0, ∞]`-valued) sense: `E[M_{n+1}; F] ≤ E[M_n; F]` for every `n` and `F ∈ ℱ_n`.
No integrability of `M_n` is required. -/
def IsStoppedSupermartingale (A : Set S) (c : ℝ) (Pt : Measure (ℕ → S × S)) : Prop :=
  ∀ n (F : Set (ℕ → S × S)), MeasurableSet[natFilt n] F →
    ∫⁻ ω in F, ENNReal.ofReal (stoppedM A c ω (n + 1)) ∂Pt ≤
      ∫⁻ ω in F, ENNReal.ofReal (stoppedM A c ω n) ∂Pt

end CouplingHMC.Lyap



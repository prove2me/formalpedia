-- Prove2me | Definitions.Def_HarrisContact_Extinction_Model
-- name    : HarrisContact_Extinction_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T11:28:26.367986+00:00
-- url     : https://prove2.me/theorems/aeb6401b-729b-4c90-87a8-9f51887e37ac
-- title:
--   §§1, 2(b), 4, 5.1 — the contact process on Z_d as a chain on finite sets: rates (4.4)–(4.5), jump chain r, minimal transition function, p_t, p_∞, m_t
-- statement:
--   This file fixes the model of Harris's *Contact Interactions on a Lattice* (1974) for finite initial configurations.
--
--   1. **Lattice.** $Z_d=\mathbb Z^d$ is the $d$-dimensional integer lattice. Two sites $x,y$ are **neighbours**, $x\sim y$, if $\sum_i |x^i-y^i|=1$; $N_x$ is the set of the $2d$ neighbours of $x$. A state is a finite set $\xi\subset Z_d$ (an element of $\Xi_0$); $\xi(N_x)=|\xi\cap N_x|$ is the number of occupied neighbours of $x$, and a site $x$ is a neighbour of $\xi$ ($x\sim\xi$) if $x\notin\xi$ and $x\sim y$ for some $y\in\xi$.
--   2. **Rates.** Given a recovery rate $\mu$ and infection rates $\lambda_0,\lambda_1,\dots,\lambda_{2d}$, the total exit rate of $\xi$ is
--   $$q_\xi=\mu|\xi|+\sum_{x\sim\xi}\lambda_{\xi(N_x)}\qquad(4.4)$$
--   and the jump rates are $q_{\xi\eta}=\mu$ if $\eta=\xi\setminus x$ with $x\in\xi$, $q_{\xi\eta}=\lambda_{\xi(N_x)}$ if $\eta=\xi\cup x$ with $x\sim\xi$, and $0$ otherwise (4.5).
--   3. **Jump chain.** $r(\xi,\eta)=q_{\xi\eta}/q_\xi$ when $q_\xi\neq0$; a state with $q_\xi=0$ (for instance $\varnothing$) is absorbing, $r(\xi,\xi)=1$. $r^{(n)}$ is its $n$-step transition matrix.
--   4. **Transition function.** $P_t(\xi,\eta)$ is the minimal (Feller) transition function of these rates: the increasing limit, as $n\to\infty$, of the probability $P^{(n)}_t(\xi,\eta)$ of being at $\eta$ at time $t$ having made at most $n$ jumps, where $P^{(0)}_t(\xi,\eta)=\delta_{\xi\eta}e^{-q_\xi t}$ and
--   $$P^{(n+1)}_t(\xi,\eta)=P^{(0)}_t(\xi,\eta)+\int_0^t e^{-q_\xi s}\sum_{\zeta\neq\xi}q_{\xi\zeta}\,P^{(n)}_{t-s}(\zeta,\eta)\,ds .$$
--   5. **Survival and size.** $p_t(\xi)=P_\xi\{\xi_t\neq\varnothing\}$ is taken to be $1-P_t(\xi,\varnothing)$; $p_\infty(\xi)=\inf_{t\ge0}p_t(\xi)$; and $m_t(\xi)=\mathscr E_\xi|\xi_t|=\sum_\eta P_t(\xi,\eta)\,|\eta|$ (4.6), (5.1).
--
--   The **contact process** is the case $\lambda_0=0$, $\mu\ge0$, $\lambda_1,\dots,\lambda_{2d}\ge0$; every theorem of the mission states these hypotheses.
--
--   **Formalization Note** The paper constructs $\{\xi_t\}$ as a Feller process on all subsets of $Z_d$ (§2) and then observes (§4, p. 975) that, started from a finite set, it is a countable-state chain on $\Xi_0$ with the rates above and $\varnothing$ absorbing. This file formalizes that chain directly, with no measure-theoretic process object; Theorem 4.1 ($\Xi_0$ is stochastically closed) is therefore built in. Sites are `Fin d → ℤ`, states are `Finset`s; the rates are real, while $P_t$, $p_t$, $p_\infty$ and $m_t$ take values in $[0,\infty]$, so that no sum, integral or infimum has a junk value. Because $p_t=1-P_t(\cdot,\varnothing)$, $p_\infty=0$ means absorption at $\varnothing$ and cannot be produced by explosion. The infection rates are a sequence `lam : ℕ → ℝ`; only $\lambda_0,\dots,\lambda_{2d}$ ever enter.
-- source:
--   Harris (Ann. Probab. 2, 1974), §1, p. 969; §2(b), p. 971; §4, (4.4)–(4.6), p. 975; (5.1), p. 976; §7, p. 980

import Mathlib

namespace HarrisContact.Extinction
open MeasureTheory
open scoped ENNReal NNReal

/-- Z_d: the d-dimensional integer lattice. -/
abbrev Site (d : ℕ) := Fin d → ℤ

/-- Ξ₀: the finite subsets of Z_d (the states of the chain of §4). -/
abbrev Config (d : ℕ) := Finset (Site d)

/-- N_x = {y : Σ_i |x^i − y^i| = 1}, enumerated inside the box Π_i [x^i − 1, x^i + 1]. -/
noncomputable def nbrs {d : ℕ} (x : Site d) : Config d :=
  (Fintype.piFinset fun i => Finset.Icc (x i - 1) (x i + 1)).filter (fun y => ∑ i, |x i - y i| = 1)

/-- ξ(N_x): the number of points of ξ among the neighbours of x. -/
noncomputable def occ {d : ℕ} (ξ : Config d) (x : Site d) : ℕ := (ξ ∩ nbrs x).card

/-- {x : x ∼ ξ}: sites outside ξ with a neighbour in ξ. -/
noncomputable def bdry {d : ℕ} (ξ : Config d) : Config d := ξ.biUnion nbrs \ ξ

/-- (4.4) q_ξ = μ|ξ| + Σ_{x∼ξ} λ_{ξ(N_x)}. -/
noncomputable def exitRate {d : ℕ} (μ : ℝ) (lam : ℕ → ℝ) (ξ : Config d) : ℝ :=
  μ * ξ.card + ∑ x ∈ bdry ξ, lam (occ ξ x)

/-- (4.5) q_{ξη} for η ≠ ξ (0 except at the listed η). -/
noncomputable def rate {d : ℕ} (μ : ℝ) (lam : ℕ → ℝ) (ξ η : Config d) : ℝ :=
  (∑ x ∈ ξ, if η = ξ.erase x then μ else 0) +
    ∑ x ∈ bdry ξ, if η = insert x ξ then lam (occ ξ x) else 0

/-- The states reachable from ξ in one jump. -/
noncomputable def succ {d : ℕ} (ξ : Config d) : Finset (Config d) :=
  ξ.image (fun x => ξ.erase x) ∪ (bdry ξ).image (fun x => insert x ξ)

/-- r(ξ, η), the imbedded jump chain; a state with q_ξ = 0 (e.g. ∅) is absorbing. -/
noncomputable def jump {d : ℕ} (μ : ℝ) (lam : ℕ → ℝ) (ξ η : Config d) : ℝ :=
  if exitRate μ lam ξ = 0 then (if η = ξ then 1 else 0) else rate μ lam ξ η / exitRate μ lam ξ

/-- r^{(n)}(ξ, η), the n-step transition matrix of the jump chain. -/
noncomputable def jumpPow {d : ℕ} (μ : ℝ) (lam : ℕ → ℝ) : ℕ → Config d → Config d → ℝ
  | 0, ξ, η => if ξ = η then 1 else 0
  | n + 1, ξ, η => ∑ ζ ∈ insert ξ (succ ξ), jump μ lam ξ ζ * jumpPow μ lam n ζ η

/-- Feller's backward recursion: P^{(n)}_t(ξ, η) = probability of being at η at time t after at
most n jumps. -/
noncomputable def transN {d : ℕ} (μ : ℝ) (lam : ℕ → ℝ) : ℕ → ℝ → Config d → Config d → ℝ≥0∞
  | 0, t, ξ, η => if ξ = η then ENNReal.ofReal (Real.exp (-(exitRate μ lam ξ * t))) else 0
  | n + 1, t, ξ, η => transN μ lam 0 t ξ η +
      ∫⁻ s in Set.Icc 0 t, ENNReal.ofReal (Real.exp (-(exitRate μ lam ξ * s))) *
        ∑ ζ ∈ succ ξ, ENNReal.ofReal (rate μ lam ξ ζ) * transN μ lam n (t - s) ζ η

/-- P_t(ξ, η): the minimal transition function of the rates (4.4)–(4.5). -/
noncomputable def trans {d : ℕ} (μ : ℝ) (lam : ℕ → ℝ) (t : ℝ) (ξ η : Config d) : ℝ≥0∞ :=
  ⨆ n, transN μ lam n t ξ η

/-- (5.1) p_t(ξ) = P_ξ{ξ_t ≠ ∅}, as 1 − P_t(ξ, ∅). -/
noncomputable def surv {d : ℕ} (μ : ℝ) (lam : ℕ → ℝ) (t : ℝ) (ξ : Config d) : ℝ≥0∞ :=
  1 - trans μ lam t ξ ∅

/-- (5.1) p_∞(ξ), as the infimum over t ≥ 0 of p_t(ξ). -/
noncomputable def survInf {d : ℕ} (μ : ℝ) (lam : ℕ → ℝ) (ξ : Config d) : ℝ≥0∞ :=
  ⨅ t : ℝ≥0, surv μ lam t ξ

/-- (4.6) m_t(ξ) = 𝓔_ξ |ξ_t|. -/
noncomputable def meanSize {d : ℕ} (μ : ℝ) (lam : ℕ → ℝ) (t : ℝ) (ξ : Config d) : ℝ≥0∞ :=
  ∑' η : Config d, trans μ lam t ξ η * (η.card : ℝ≥0∞)

end HarrisContact.Extinction



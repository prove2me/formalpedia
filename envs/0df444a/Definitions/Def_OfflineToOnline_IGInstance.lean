-- Prove2me | Definitions.Def_OfflineToOnline_IGInstance
-- name    : OfflineToOnline_IGInstance
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T11:33:16.491551+00:00
-- url     : https://prove2.me/theorems/202e995a-8438-4dc6-a7b9-fa8f6dbe128c
-- title:
--   Instance of the offline iterative greedy algorithm Offline-IG
-- statement:
--   An instance $\textsc{Offline-IG}(\mathcal C,\mathcal F,\mathcal D,\Theta)$ of Algorithm 1 consists of:
--
--   1. a domain $\mathcal D$ (with a $\sigma$-algebra), a feasible region $\mathcal C\subseteq\mathcal D$ and an initial feasible point $z^{(0)}\in\mathcal C$;
--   2. a function space $\mathcal F$ of measurable objectives $f:\mathcal D\to[0,1]$;
--   3. $N$ subproblems sharing a parameter space $\Theta\subseteq\mathbb R^{d_{\mathrm{param}}}$ (Remark 3);
--   4. a parameter payoff $\textsc{Payoff}:\Theta\times\mathcal D\times\mathcal F\to\mathbb R^{d_{\mathrm{payoff}}}$, measurable in $(\theta,z)$ for each $f$;
--   5. a randomized local update $\textsc{Local-update}:\Theta\times\mathcal D\to\Delta(\mathcal C)$, represented as a measurable map $(\theta,z,\omega)\mapsto\mathrm{update}(\theta,z,\omega)$ of a random seed $\omega$, with values in $\mathcal C$ whenever $\theta\in\Theta$ and $z\in\mathcal C$.
--
--   In subproblem $i$ the algorithm picks $\theta^{(i)}\in\Theta$ with $\textsc{Payoff}(\theta^{(i)},z^{(i-1)},f)\ge0$ and moves to $z^{(i)}=\textsc{Local-update}(\theta^{(i)},z^{(i-1)})$; it returns $z^{(N)}$. The objects listed here are the data of that procedure, and robustness (Definition 6) and Blackwell reducibility (Definition 7) are properties of them.
--
--   **Formalization Note** The paper's standing assumption that $\mathcal F$ is closed under addition (p.10) is not included: with $f:\mathcal D\to[0,1]$ it would force $\mathcal F\subseteq\{0\}$, and no result of the mission uses it. The law of the seed is passed separately. Measurability of $f$, $\textsc{Payoff}$ and the update is what makes the expectations of Definition 6 and Theorem 2 exist.
-- source:
--   Niazadeh, Golrezaei, Wang, Susan & Badanidiyuru, Online Learning via Offline Greedy Algorithms: Applications in Market Design and Optimization, arXiv:2102.11050v4, problem (1), p.10; Algorithm 1 and Remark 3, p.14

import Mathlib

namespace OfflineToOnline

/-- An instance `Offline-IG(C, F, D, Θ)` of Algorithm 1 (p.14) for the offline problem (1), p.10.

* `D` is the domain (with a σ-algebra), `C ⊆ D` the feasible region, `F` the function space: each
  `f ∈ F` is a measurable `f : D → [0, 1]`.
* `N` subproblems, an initial feasible point `z₀ = z^(0) ∈ C`.
* `Θ ⊆ ℝ^{d_param}` (here `Fin m → ℝ`) the update parameters, the same for every subproblem
  (Remark 3, p.14).
* `payoff : Θ × D × F → ℝ^{d_payoff}` (here `Fin d → ℝ`), measurable in `(θ, z)` for each `f ∈ F`.
* `update` is the randomized Local-update `Θ × D → Δ(C)`, represented as a measurable map
  `(θ, z, ω) ↦ update θ z ω` of a random seed `ω ∈ Ω`, with values in `C` when `θ ∈ Θ`, `z ∈ C`.
  The law `ν` of the seed is passed separately.

Niazadeh, Golrezaei, Wang, Susan & Badanidiyuru, arXiv:2102.11050v4, (1), p.10; Algorithm 1 and Remark 3, p.14.

Formalization Note: the paper's standing assumption "F is closed under addition" (p.10) is not
included: together with `f : D → [0, 1]` it forces `F ⊆ {0}`. Measurability of `f`, `payoff`
and `update` is what makes the expectations of Definition 6 and Theorem 2 exist. A kernel
`Θ × D → Δ(C)` into a standard Borel space has this seed representation. -/
structure IGInstance (D : Type*) [MeasurableSpace D] (Ω : Type*) [MeasurableSpace Ω] (m d : ℕ) where
  /-- the feasible region `C ⊆ D` -/
  C : Set D
  /-- the function space `F` -/
  F : Set (D → ℝ)
  /-- the parameter space `Θ ⊆ ℝ^{d_param}` -/
  Θ : Set (Fin m → ℝ)
  /-- the number of subproblems -/
  N : ℕ
  /-- the initial feasible point `z^(0)` -/
  z₀ : D
  /-- `Payoff(θ, z, f) ∈ ℝ^{d_payoff}` -/
  payoff : (Fin m → ℝ) → D → (D → ℝ) → (Fin d → ℝ)
  /-- `Local-update(θ, z)` driven by the random seed `ω` -/
  update : (Fin m → ℝ) → D → Ω → D
  z₀_mem : z₀ ∈ C
  F_meas : ∀ f ∈ F, Measurable f
  F_range : ∀ f ∈ F, ∀ z, f z ∈ Set.Icc (0 : ℝ) 1
  payoff_meas : ∀ f ∈ F, Measurable (fun q : (Fin m → ℝ) × D => payoff q.1 q.2 f)
  update_meas : Measurable (fun q : ((Fin m → ℝ) × D) × Ω => update q.1.1 q.1.2 q.2)
  update_mem : ∀ θ ∈ Θ, ∀ z ∈ C, ∀ ω, update θ z ω ∈ C

end OfflineToOnline



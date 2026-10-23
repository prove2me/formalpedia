-- Prove2me | Definitions.Def_ExactPenGNEP_NonShared_Setting
-- name    : ExactPenGNEP_NonShared_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-23T03:53:48.737976+00:00
-- url     : https://prove2.me/theorems/89ad73ba-a6d6-4ab0-9b0b-cf933b565b45
-- title:
--   §2.1–§2.3, §5, pp. 3–8, 17–18 — GNEP (C, X; θ), graph(X), T-residual functions, the sets (16), the ℓq residual (4)/(17) and the Slater-type condition of Theorem 11 (b)
-- statement:
--   This file fixes the objects of Ba and Pang's exact penalization theory for generalized Nash equilibrium problems (GNEPs).
--
--   **Players and profiles.** There are $N$ players $\nu \in [N]$. Player $\nu$ chooses $x^\nu \in \mathbb R^{n_\nu}$, equipped with the Euclidean norm $\|\cdot\|_2$. A profile is $x = (x^\nu)_{\nu\in[N]}$, and $x^{-\nu} = (x^{\nu'})_{\nu'\ne\nu}$ denotes the rivals' strategies. Player $\nu$'s deviation to $y$ is the profile $(y, x^{-\nu})$.
--
--   **The GNEP $(C, X; \theta)$.** Each player has a private strategy set $C^\nu \subseteq \mathbb R^{n_\nu}$, a coupled constraint set $X^\nu(x^{-\nu}) \subseteq \mathbb R^{n_\nu}$ depending on the rivals, and a cost $\theta_\nu(x^\nu, x^{-\nu})$. A profile $x$ belongs to the graph of $X$ if $x^\nu \in X^\nu(x^{-\nu})$ for all $\nu$. A profile $x^*$ is an equilibrium of the GNEP if for every $\nu$
--
--   $$x^{*,\nu} \in \operatorname*{argmin}_{x^\nu \in C^\nu \cap X^\nu(x^{*,-\nu})} \theta_\nu(x^\nu, x^{*,-\nu}),$$
--
--   that is, $x^{*,\nu}$ is feasible and no feasible deviation lowers player $\nu$'s cost.
--
--   **NEPs.** For costs $f = (f_\nu)$, a profile $x$ is an equilibrium of the Nash equilibrium problem $(C; f)$ if $x^\nu \in C^\nu$ and $f_\nu(x) \le f_\nu(y, x^{-\nu})$ for all $y \in C^\nu$ and all $\nu$: players face only their private constraints.
--
--   **Residual functions.** A function $r \ge 0$ is a $T$-residual function of a set $S$ if, for all $x \in T$, $r(x) = 0$ exactly when $x \in S$.
--
--   **Finitely representable coupled sets (16).** Given functions $g^\nu_i$, $i \in [m_\nu]$, of the whole profile and affine functions $h^\nu_j$, $j \in [p_\nu]$, of the whole profile,
--
--   $$X^\nu(x^{-\nu}) = \{ x^\nu \in \mathbb R^{n_\nu} \mid g^\nu(x^\nu, x^{-\nu}) \le 0,\ h^\nu(x^\nu, x^{-\nu}) = 0 \}.$$
--
--   **The $\ell_q$ residual (4)/(17).** For a system $g \le 0$, $h = 0$ and $q > 0$,
--
--   $$r_q(x) = \left\| \begin{pmatrix} \max(g(x), 0) \\ h(x) \end{pmatrix} \right\|_q = \Big( \sum_{i} \max(g_i(x), 0)^q + \sum_j |h_j(x)|^q \Big)^{1/q}.$$
--
--   Player $\nu$'s residual $r_{\nu;q}$ is this function for $(g^\nu, h^\nu)$.
--
--   **The Slater-type condition of Theorem 11 (b).** There is $\alpha > 0$ such that for every $x \in C$ outside the graph of $X$ there are $\hat x \in C$ and a player $\hat\nu$ with $x^{\hat\nu} \notin X^{\hat\nu}(x^{-\hat\nu})$ such that
--
--   $$\nabla_{x^{\hat\nu}} g^{\hat\nu}_i(x)^T(\hat x^{\hat\nu} - x^{\hat\nu}) \le -\alpha \ \text{ if } g^{\hat\nu}_i(x) > 0, \qquad [\operatorname{sgn} h^{\hat\nu}_j(x)]\, \nabla_{x^{\hat\nu}} h^{\hat\nu}_j(x)^T(\hat x^{\hat\nu} - x^{\hat\nu}) \le -\alpha \ \text{ if } h^{\hat\nu}_j(x) \ne 0.$$
--
--   These definitions are shared by every statement of the mission.
--
--   **Formalization Note** Players, strategy spaces `Strat n ν` = `EuclideanSpace ℝ (Fin (n ν))`, profiles (dependent functions) and NEP equilibria (`IsNashEq`: membership in $\prod_\nu C^\nu$ plus no profitable unilateral deviation within $C^\nu$) are taken from the published definition `LeiBR.Sync.NashGame`; $(y, x^{-\nu})$ is `Function.update x ν y`. A coupled multifunction is a family `X ν x` read as $X^\nu(x^{-\nu})$. `IsGNE` includes feasibility $x^\nu \in C^\nu \cap X^\nu(x^{-\nu})$. `IsResidual` omits the paper's wording "closed subsets $S$, $T$", which is a standing assumption of the setting, not part of the property; the results using it state their own closedness hypotheses. The $\ell_q$ norm is written as an explicit sum of real powers (all bases are nonnegative). The numbers of constraints $m_\nu, p_\nu$ are natural numbers and may be $0$, while (2) says "positive integers"; zero constraints make $X^\nu$ the whole space. Partial gradients applied to a direction $d$ are Fréchet derivatives of the function of player $\hat\nu$'s block applied to $d$; sgn is `Real.sign` ($\operatorname{sgn} 0 = 0$, as on p. 5).
-- source:
--   Ba & Pang, Exact penalization of generalized Nash equilibrium problems, arXiv:1811.10674v2, pp. 3–8 and 17–18, §2.1–§2.3, §5, Equations (1), (2), (4), (11), (16), (17), Theorem 11 (b)

import Mathlib
import Definitions.Def_LeiBR_Sync_NashGame

open LeiBR.Sync

namespace ExactPenGNEP.NonShared

/-! Player `ν`'s strategy space `Strat n ν = ℝ^{n_ν}` (Euclidean norm), profiles `Profile n`, and
equilibria of a NEP (`IsNashEq`) come from the published definition `LeiBR.Sync.NashGame`.
Player `ν`'s deviation to `y`, written `(y, x^{-ν})` in the paper, is `Function.update x ν y`. -/

variable {N : ℕ} {n : Fin N → ℕ}

/-- `x ∈ graph(X)` (p. 4, Proposition 3 (a)): `x^ν ∈ X^ν(x^{-ν})` for every player `ν`.
A coupled-constraint multifunction `X ν x` stands for `X^ν(x^{-ν})`. -/
def inGraph (X : ∀ ν, Profile n → Set (Strat n ν)) (x : Profile n) : Prop :=
  ∀ ν, x ν ∈ X ν x

/-- `x` is an equilibrium (NE) of the GNEP `(C, X; θ)` (§2.1, p. 4): for every player `ν`,
`x^ν` is feasible, `x^ν ∈ C^ν ∩ X^ν(x^{-ν})`, and minimizes `θ_ν(·, x^{-ν})` over that set. -/
def IsGNE (C : ∀ ν, Set (Strat n ν)) (X : ∀ ν, Profile n → Set (Strat n ν))
    (θ : Fin N → Profile n → ℝ) (x : Profile n) : Prop :=
  ∀ ν, x ν ∈ C ν ∩ X ν x ∧ ∀ y ∈ C ν ∩ X ν x, θ ν x ≤ θ ν (Function.update x ν y)

/-- `r` is a `T`-residual function of `S` (§2.2, p. 5): `r ≥ 0`, and for all `x ∈ T`,
`r x = 0 ↔ x ∈ S`. -/
def IsResidual {E : Type*} (r : E → ℝ) (S T : Set E) : Prop :=
  (∀ x, 0 ≤ r x) ∧ ∀ x ∈ T, (r x = 0 ↔ x ∈ S)

/-- The `ℓ_q` residual (4)/(17) of the system `g ≤ 0`, `h = 0`:
`‖(max(g(x), 0); h(x))‖_q = (∑_i max(g_i(x), 0)^q + ∑_j |h_j(x)|^q)^{1/q}` (real powers). -/
noncomputable def lqRes {α : Type*} {m p : ℕ} (g : Fin m → α → ℝ) (h : Fin p → α → ℝ) (q : ℝ)
    (x : α) : ℝ :=
  (∑ i, (max (g i x) 0) ^ q + ∑ j, |h j x| ^ q) ^ (1 / q)

/-- The finitely representable coupled set (16):
`X^ν(x^{-ν}) = {x^ν | g^ν(x^ν, x^{-ν}) ≤ 0 and h^ν(x^ν, x^{-ν}) = 0}`, with `h^ν` affine. -/
def frSet {m p : Fin N → ℕ} (g : ∀ ν, Fin (m ν) → Profile n → ℝ)
    (h : ∀ ν, Fin (p ν) → Profile n →ᵃ[ℝ] ℝ) (ν : Fin N) (x : Profile n) : Set (Strat n ν) :=
  {y | (∀ i, g ν i (Function.update x ν y) ≤ 0) ∧ ∀ j, h ν j (Function.update x ν y) = 0}

/-- The Slater-type hypothesis of Theorem 11 (b), pp. 17–18: there is `α > 0` such that for every
`x ∈ C` not in `graph(X)` there exist `x̂ ∈ C` and a player `ν̂` with `x^ν̂ ∉ X^ν̂(x^{-ν̂})` such that
`∇_{x^ν̂} g^ν̂_i(x)ᵀ(x̂^ν̂ − x^ν̂) ≤ −α` whenever `g^ν̂_i(x) > 0`, and
`[sgn h^ν̂_j(x)] ∇_{x^ν̂} h^ν̂_j(x)ᵀ(x̂^ν̂ − x^ν̂) ≤ −α` whenever `h^ν̂_j(x) ≠ 0`.
The partial gradient applied to `d` is the Fréchet derivative of the function of player `ν̂`'s block. -/
def SlaterTypeCQ {m p : Fin N → ℕ} (C : ∀ ν, Set (Strat n ν))
    (g : ∀ ν, Fin (m ν) → Profile n → ℝ) (h : ∀ ν, Fin (p ν) → Profile n →ᵃ[ℝ] ℝ) : Prop :=
  ∃ α > (0 : ℝ), ∀ x : Profile n, (∀ ν, x ν ∈ C ν) → ¬ inGraph (frSet g h) x →
    ∃ xh : Profile n, (∀ ν, xh ν ∈ C ν) ∧ ∃ νh : Fin N, x νh ∉ frSet g h νh x ∧
      (∀ i, 0 < g νh i x →
        fderiv ℝ (fun y => g νh i (Function.update x νh y)) (x νh) (xh νh - x νh) ≤ -α) ∧
      (∀ j, h νh j x ≠ 0 →
        Real.sign (h νh j x) *
          fderiv ℝ (fun y => h νh j (Function.update x νh y)) (x νh) (xh νh - x νh) ≤ -α)

end ExactPenGNEP.NonShared



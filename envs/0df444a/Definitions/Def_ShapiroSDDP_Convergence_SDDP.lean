-- Prove2me | Definitions.Def_ShapiroSDDP_Convergence_SDDP
-- name    : ShapiroSDDP_Convergence_SDDP
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T09:34:17.180006+00:00
-- url     : https://prove2.me/theorems/bc4f23bf-6a1b-4de0-b39d-e9cc130e3158
-- title:
--   The SDDP method on the SAA problem: cut LPs (3.11)/(3.13)/(3.14), their duals, basic optimal duals, the cut (3.17), forward policy, runs, (A1)
-- statement:
--   This file encodes the stochastic dual dynamic programming (SDDP) method applied to the SAA problem, Shapiro §3, pp. 7–9, and §3.1, p. 10.
--
--   **Cut LPs.** A **cutting plane** is an affine function $\ell(x)=\alpha+\beta^\top x$. For a finite set $C$ of cuts, the approximation $\mathfrak Q(x)=\max_{(\alpha,\beta)\in C}(\alpha+\beta^\top x)$ enters the linear program
--   $$\min_{y,\theta}\ c^\top y+\theta\quad\text{s.t.}\quad Ay=h,\ y\ge0,\ \theta\ge\alpha+\beta^\top y\ \ \forall(\alpha,\beta)\in C,$$
--   which is the LP form of (3.11), (3.13) and (3.14). It **has a finite optimal value** if it is feasible and its objective is bounded below. Its dual (with multipliers $\pi$ for $Ay=h$ and $\rho_a$ for the cut $a=(\alpha_a,\beta_a)\in C$) is
--   $$\max_{\pi,\rho}\ \pi^\top h+\sum_{a\in C}\rho_a\alpha_a\quad\text{s.t.}\quad A^\top\pi-\sum_{a\in C}\rho_a\beta_a\le c,\ \ \sum_{a\in C}\rho_a=1,\ \ \rho\ge0 .$$
--   A **basic optimal solution** of the dual (p. 10) is an extreme point (basic feasible solution) of the dual feasible region that maximizes the dual objective.
--
--   **Approximations.** At stage $t$ the method keeps a finite set of cuts whose maximum $\mathfrak Q_{t+1}$ approximates $\widetilde{\mathcal Q}_{t+1}$. The initial sets $C_0$ are **valid**: at stage $T$ the set is $\{(0,0)\}$, so that $\mathfrak Q_{T+1}\equiv 0$; at stages $1\le t\le T-1$ it is nonempty and every cut lies below $\widetilde{\mathcal Q}_{t+1}$ on reachable decisions.
--
--   **Oracle and forward policy.** A deterministic **oracle** returns a solution of (3.13) for a given cut set, and of (3.14) for a given stage, cut set, previous decision and outcome; its specification is that it returns (the decision part of) an optimal solution whenever the problem has one. The **forward policy** (3.13)–(3.14) of a family of cut sets takes $\bar x_1$ from (3.13) and, along a scenario, $\bar x_{t}$ from (3.14) at stage $t$ with the previous decision $\bar x_{t-1}$ and the scenario's outcome.
--
--   **The cut (3.17).** At a trial decision $\bar x$ of stage $t$, with one dual solution $(\pi_j,\rho_j)$ of the stage-$(t+1)$ problem for each outcome $j=1,\dots,N_{t+1}$ and the stage-$(t+1)$ cut set $C$, the cut is
--   $$\ell(x)=\underline{\widetilde{\mathcal Q}}_{t+1}(\bar x)+\tilde g^\top(x-\bar x),\qquad \tilde g=-\frac1{N_{t+1}}\sum_{j}\tilde B_{t+1,j}^\top\pi_j,\qquad \underline{\widetilde{\mathcal Q}}_{t+1}(\bar x)=\frac1{N_{t+1}}\sum_j\Big(\pi_j^\top(\tilde b_{t+1,j}-\tilde B_{t+1,j}\bar x)+\sum_{a\in C}\rho_{j,a}\alpha_a\Big),$$
--   the average dual objective at $\bar x$, which equals the average optimal value of the stage-$(t+1)$ problems with cuts when the duals are optimal.
--
--   **Runs.** With $M\ge1$ forward scenarios per iteration, a **run** is a sequence of cut sets starting from $C_0$. Iteration $k=0,1,\dots$ is a forward step, giving trial points $\bar x^{k,i}_t$ along the $i$-th sampled scenario with the current cut sets, followed by a backward step for $t=T-1$ down to $1$: for each $i$ and each outcome $j$ a basic optimal dual solution of the stage-$(t+1)$ problem at $\bar x^{k,i}_t$ is chosen, using the stage-$(t+1)$ cut set already updated in this backward step (p. 7), and the cuts (3.17) are added to the stage-$t$ set. The dual choices are arbitrary among basic optimal ones.
--
--   **(A1)** (p. 10): "Problem (3.13) and problems (3.14), $t=2,\dots,T$, have finite optimal values for all realizations (scenarios) of the data used in the SAA problem", read along a run: at every iteration, (3.13) and every (3.14) at the forward decisions of every scenario have finite optimal values.
--
--   **Formalization Note** The cut set of stage $t$ (`cuts k t`) approximates `V t` $=\widetilde{\mathcal Q}_{t+1}$, the paper's $\mathfrak Q_{t+1}$; stage $T$ keeps $\{(0,0)\}$. Cut sets are `Finset`s and the oracle reads the set, so repeated cuts cannot change its answer; the paper does not say which optimal solution is taken, and a deterministic choice is assumed. The dual multipliers $\rho$ are indexed by the elements of the cut set. The cut is returned as the pair $(\underline{\widetilde{\mathcal Q}}(\bar x)-\tilde g^\top\bar x,\ \tilde g)$, its value at $\bar x$ being the averaged dual objective. Iterations are numbered from $0$, and within an iteration the forward step precedes the backward step. The initial cut sets are an explicit parameter (the paper does not specify them); without a nonempty initial set (3.13) would be unbounded and (A1) would fail. If some $\tilde A_{t,j}$ lacks full row rank, the dual feasible region has no extreme point, no run exists, and statements quantified over runs are vacuous for that instance; the paper presupposes that basic optimal solutions exist.
-- source:
--   Shapiro, Analysis of Stochastic Dual Dynamic Programming Method, Optimization Online 2009/12/2509, pp. 2, 7–10, (3.8)–(3.14), (3.17), (A1)

import Mathlib
import Definitions.Def_ShapiroSDDP_Convergence_Model

open Matrix

namespace ShapiroSDDP.Convergence

/-! ### Linear programs with a cutting-plane epigraph variable (generic) -/

section CutLP

variable {n m : ℕ}

/-- The value `α + βᵀ x` of the affine function (cutting plane) `a = (α, β)` at `x`. -/
def cutEval (a : ℝ × (Fin n → ℝ)) (x : Fin n → ℝ) : ℝ := a.1 + a.2 ⬝ᵥ x

/-- The feasible set of the linear program "minimize `cᵀ y + θ` subject to `A y = h`, `y ≥ 0`,
`θ ≥ α + βᵀ y` for every `(α, β) ∈ C`", the LP form of (3.11), (3.13), (3.14) with the
approximation `𝔔(y) = max_{(α,β) ∈ C} (α + βᵀ y)`. Points are pairs `(y, θ)`. -/
def CutLPFeas (A : Matrix (Fin m) (Fin n) ℝ) (h : Fin m → ℝ) (C : Finset (ℝ × (Fin n → ℝ))) :
    Set ((Fin n → ℝ) × ℝ) :=
  {p | 0 ≤ p.1 ∧ A *ᵥ p.1 = h ∧ ∀ a ∈ C, cutEval a p.1 ≤ p.2}

/-- The objective `cᵀ y + θ`. -/
def cutLPObj (c : Fin n → ℝ) (p : (Fin n → ℝ) × ℝ) : ℝ := c ⬝ᵥ p.1 + p.2

/-- The LP has a finite optimal value: it is feasible and its objective is bounded below on the
feasible set. -/
def CutLPFinite (A : Matrix (Fin m) (Fin n) ℝ) (h : Fin m → ℝ) (C : Finset (ℝ × (Fin n → ℝ)))
    (c : Fin n → ℝ) : Prop :=
  (CutLPFeas A h C).Nonempty ∧ BddBelow (cutLPObj c '' CutLPFeas A h C)

/-- `p` is an optimal solution of the LP. -/
def IsCutLPOpt (A : Matrix (Fin m) (Fin n) ℝ) (h : Fin m → ℝ) (C : Finset (ℝ × (Fin n → ℝ)))
    (c : Fin n → ℝ) (p : (Fin n → ℝ) × ℝ) : Prop :=
  p ∈ CutLPFeas A h C ∧ ∀ q ∈ CutLPFeas A h C, cutLPObj c p ≤ cutLPObj c q

/-- The optimal value of the LP (a real infimum; meaningful when `CutLPFinite` holds). -/
noncomputable def cutLPVal (A : Matrix (Fin m) (Fin n) ℝ) (h : Fin m → ℝ)
    (C : Finset (ℝ × (Fin n → ℝ))) (c : Fin n → ℝ) : ℝ :=
  sInf (cutLPObj c '' CutLPFeas A h C)

/-- A dual vector of the LP: `π ∈ ℝ^m` for the equality constraints and `ρ`, indexed by the
elements of the cut set `C`, for the cut constraints. -/
abbrev CutDual (m : ℕ) (C : Finset (ℝ × (Fin n → ℝ))) := (Fin m → ℝ) × (C → ℝ)

/-- The dual feasible region: `Aᵀ π − Σ_{a ∈ C} ρ_a β_a ≤ c`, `Σ_{a ∈ C} ρ_a = 1`, `ρ ≥ 0`. -/
def CutDualFeas (A : Matrix (Fin m) (Fin n) ℝ) (C : Finset (ℝ × (Fin n → ℝ))) (c : Fin n → ℝ) :
    Set (CutDual m C) :=
  {d | Aᵀ *ᵥ d.1 - ∑ a : C, d.2 a • (a : ℝ × (Fin n → ℝ)).2 ≤ c ∧ ∑ a : C, d.2 a = 1 ∧
    ∀ a, 0 ≤ d.2 a}

/-- The dual objective `πᵀ h + Σ_{a ∈ C} ρ_a α_a`. -/
def cutDualObj (h : Fin m → ℝ) (C : Finset (ℝ × (Fin n → ℝ))) (d : CutDual m C) : ℝ :=
  d.1 ⬝ᵥ h + ∑ a : C, d.2 a * (a : ℝ × (Fin n → ℝ)).1

/-- `d` is a basic optimal solution of the dual problem (p. 10): an extreme point (basic feasible
solution) of the dual feasible region that maximizes the dual objective over it. -/
def IsBasicOptDual (A : Matrix (Fin m) (Fin n) ℝ) (h : Fin m → ℝ) (C : Finset (ℝ × (Fin n → ℝ)))
    (c : Fin n → ℝ) (d : CutDual m C) : Prop :=
  d ∈ Set.extremePoints ℝ (CutDualFeas A C c) ∧
    ∀ d' ∈ CutDualFeas A C c, cutDualObj h C d' ≤ cutDualObj h C d

end CutLP

/-! ### The SDDP method on the SAA problem -/

variable (I : Instance)

/-- A cutting plane at stage `t`: an affine function `x_t ↦ α + βᵀ x_t` approximating
`𝒬̃_{t+1}(x_t) = V t x_t` from below. The paper's approximation `𝔔_{t+1}` is the maximum of a
finite nonempty set of such cuts. -/
abbrev Cut (t : ℕ) := ℝ × (Fin (I.n t) → ℝ)

/-- Valid initial approximations: the stage-`T` set is `{(0, 0)}` (so `𝔔_{T+1} ≡ 0` exactly), and
for `1 ≤ t ≤ T − 1` the initial set of cuts is nonempty and every cut lies below `𝒬̃_{t+1}` on
reachable stage-`t` decisions. -/
def ValidInit (C₀ : (t : ℕ) → Finset (Cut I t)) : Prop :=
  C₀ I.T = {(0, 0)} ∧
    ∀ t, 1 ≤ t → t + 1 ≤ I.T → (C₀ t).Nonempty ∧ ∀ a ∈ C₀ t, ∀ x ∈ Reach I t, cutEval a x ≤ V I t x

/-- A deterministic primal LP oracle. `first C` is a first-stage decision for problem (3.13) with the
cut set `C` (approximating `𝒬̃₂`); `next t C x j` is a stage-`(t+1)` decision for problem (3.14) at
stage `t + 1`, previous decision `x = x_t`, outcome `j`, and the stage-`(t+1)` cut set `C`. The
answers depend on the cut *set* only. -/
structure Oracle where
  first : Finset (Cut I 1) → Fin (I.n 1) → ℝ
  next : (t : ℕ) → Finset (Cut I (t + 1)) → (Fin (I.n t) → ℝ) → Fin (I.N (t + 1)) →
    Fin (I.n (t + 1)) → ℝ

/-- Specification of the oracle: whenever problem (3.13) (resp. (3.14) at a stage `2 ≤ t + 1 ≤ T`)
has an optimal solution, the oracle returns the decision part of one. -/
def OracleSpec (sol : Oracle I) : Prop :=
  (∀ C : Finset (Cut I 1), (∃ p, IsCutLPOpt I.A₁ I.b₁ C I.c₁ p) →
      ∃ θ, IsCutLPOpt I.A₁ I.b₁ C I.c₁ (sol.first C, θ)) ∧
    ∀ t, 1 ≤ t → t + 1 ≤ I.T → ∀ (C : Finset (Cut I (t + 1))) (x : Fin (I.n t) → ℝ)
      (j : Fin (I.N (t + 1))),
      (∃ p, IsCutLPOpt (I.A t j) (rhs I t x j) C (I.c t j) p) →
        ∃ θ, IsCutLPOpt (I.A t j) (rhs I t x j) C (I.c t j) (sol.next t C x j, θ)

/-- The forward step policy (3.13)–(3.14) defined by the cut sets `C`: `x̄₁ = first (C 1)` and, along
a scenario `s`, `x̄_{t+1} = next t (C (t+1)) x̄_t j_{t+1}` for `2 ≤ t + 1 ≤ T`. It is implementable by
construction. Values at stage `0` and beyond `T` are `0` and never used. -/
noncomputable def fwd (sol : Oracle I) (C : (t : ℕ) → Finset (Cut I t)) : Policy I
  | 0 => fun _ => 0
  | 1 => fun _ => sol.first (C 1)
  | t + 2 => fun s =>
    if h : t < I.T - 1 then sol.next (t + 1) (C (t + 2)) (fwd sol C (t + 1) s) (s ⟨t, h⟩) else 0

/-- The cutting plane (3.17) at stage `t` (approximating `𝒬̃_{t+1}`), computed at the trial point
`x̄ = x̄_t` from one dual solution `d j = (π_j, ρ_j)` of the stage-`(t+1)` problem per outcome `j`,
with the stage-`(t+1)` cut set `C`:
`ℓ(x) = 𝒬̲̃(x̄) + g̃ᵀ (x − x̄)` with `g̃ = −(1/N_{t+1}) Σ_j B̃_{t+1,j}ᵀ π_j` (3.10) and
`𝒬̲̃(x̄) = (1/N_{t+1}) Σ_j (π_jᵀ (b̃_{t+1,j} − B̃_{t+1,j} x̄) + Σ_{a ∈ C} ρ_{j,a} α_a)`, the average
dual objective value at `x̄` (equal to the average optimal value of the stage-`(t+1)` problems when
the `d j` are optimal duals). Returned as the pair `(𝒬̲̃(x̄) − g̃ᵀ x̄, g̃)`. -/
noncomputable def cutAt (t : ℕ) (x : Fin (I.n t) → ℝ) (C : Finset (Cut I (t + 1)))
    (d : Fin (I.N (t + 1)) → CutDual (I.m (t + 1)) C) : Cut I t :=
  let g : Fin (I.n t) → ℝ := -((1 / (I.N (t + 1) : ℝ)) • ∑ j, (I.B t j)ᵀ *ᵥ (d j).1)
  let v : ℝ := (1 / (I.N (t + 1) : ℝ)) * ∑ j, cutDualObj (rhs I t x j) C (d j)
  (v - g ⬝ᵥ x, g)

/-- A run of the SDDP method with `M` forward scenarios per iteration (pp. 7–9). `ω k i` is the
`i`-th scenario sampled in the forward step of iteration `k = 0, 1, …`, and `cuts k t` is the
stage-`t` cut set (approximating `𝒬̃_{t+1}`) at the start of iteration `k`; `cuts 0 = C₀`.
Iteration `k` is a forward step followed by a backward step:

* forward step: the trial points are `x̄^{k,i}_t = fwd sol (cuts k) t (ω k i)`;
* backward step, for `t = T − 1` down to `1`: for each `i` and each outcome `j` of stage `t + 1`, a
  basic optimal dual solution `d i j` of the stage-`(t+1)` problem at `x̄^{k,i}_t` is chosen, with
  the stage-`(t+1)` cut set already updated in this backward step, `cuts (k+1) (t+1)`; the cuts
  (3.17) built from them are added: `cuts (k+1) t = cuts k t ∪ {cutAt t x̄^{k,i}_t … (d i) | i}`.

All other stages (in particular stage `T`, whose set stays `C₀ T = {(0, 0)}`) are unchanged. The
dual choices are existential: any basic optimal duals may be used. If some `Ã_{t+1,j}` lacks full row
rank the dual region has no extreme point, no run exists, and statements quantified over runs are
vacuous for that instance; the paper presupposes that basic optimal solutions exist. -/
def IsRun (C₀ : (t : ℕ) → Finset (Cut I t)) (sol : Oracle I) {M : ℕ} (ω : ℕ → Fin M → Scen I)
    (cuts : ℕ → (t : ℕ) → Finset (Cut I t)) : Prop :=
  cuts 0 = C₀ ∧
    ∀ k t,
      if 1 ≤ t ∧ t + 1 ≤ I.T then
        ∃ d : Fin M → (j : Fin (I.N (t + 1))) → CutDual (I.m (t + 1)) (cuts (k + 1) (t + 1)),
          (∀ i j, IsBasicOptDual (I.A t j) (rhs I t (fwd I sol (cuts k) t (ω k i)) j)
            (cuts (k + 1) (t + 1)) (I.c t j) (d i j)) ∧
          cuts (k + 1) t = cuts k t ∪
            Finset.univ.image (fun i => cutAt I t (fwd I sol (cuts k) t (ω k i))
              (cuts (k + 1) (t + 1)) (d i))
      else cuts (k + 1) t = cuts k t

/-- Assumption (A1), p. 10, along a run: at every iteration `k`, problem (3.13) with the cut set
`cuts k 1` and problems (3.14), `t = 2, …, T`, with the cut sets `cuts k t` at the forward decisions
of every scenario of the SAA problem have finite optimal values (feasible and bounded below). -/
def A1 (sol : Oracle I) (cuts : ℕ → (t : ℕ) → Finset (Cut I t)) : Prop :=
  ∀ k, CutLPFinite I.A₁ I.b₁ (cuts k 1) I.c₁ ∧
    ∀ (s : Scen I) (u : Fin (I.T - 1)),
      CutLPFinite (I.A ((u : ℕ) + 1) (s u))
        (rhs I ((u : ℕ) + 1) (fwd I sol (cuts k) ((u : ℕ) + 1) s) (s u))
        (cuts k ((u : ℕ) + 2)) (I.c ((u : ℕ) + 1) (s u))

end ShapiroSDDP.Convergence



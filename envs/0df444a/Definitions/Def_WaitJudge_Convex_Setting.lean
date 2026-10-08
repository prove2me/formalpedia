-- Prove2me | Definitions.Def_WaitJudge_Convex_Setting
-- name    : WaitJudge_Convex_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T04:45:18.294423+00:00
-- url     : https://prove2.me/theorems/e807b3b7-bff8-4616-ab08-a50073394197
-- title:
--   Sect. 1, 3 and (10), (11), (12), pp. 2–13 — scenario programs with tie-break, support constraints, Assumptions 1–2, F_k, problem (10)
-- statement:
--   This file sets up the convex scenario programs of Campi and Garatti's *wait-and-judge* analysis.
--
--   **Data.** The decision variable is $x\in\mathbb R^d$. A problem consists of a cost vector $c\in\mathbb R^d$, a convex domain $\mathcal X\subseteq\mathbb R^d$, a family of convex constraint sets $\mathcal X_\delta\subseteq\mathbb R^d$ indexed by an uncertain parameter $\delta$ in a probability space $(\Delta,\mathcal F,\mathbb P)$, and finitely many tie-break functions $t_1,\dots,t_p:\mathbb R^d\to\mathbb R$.
--
--   1. **Programs with selected constraints.** For a sample $\omega=(\delta^{(1)},\dots,\delta^{(m)})$ and an index set $I\subseteq\{1,\dots,m\}$, the feasible set is $\mathcal X\cap\bigcap_{i\in I}\mathcal X_{\delta^{(i)}}$. With $I$ the whole index set this is the feasible set of the scenario program (9); with $m=0$ it is $\mathcal X$.
--   2. **Tie-broken solution.** A point $x$ of a feasible set $F$ is a tie-broken solution if it minimises the key $(c^{\mathsf T}x,\,t_1(x),\dots,t_p(x))$ lexicographically over $F$: it minimises the cost, then $t_1$ among the minimisers of the cost, and so on. The solution $\operatorname{sol}(F)$ is the unique such point when it exists; it depends only on $F$. The solution of (9) is $x^*_m=\operatorname{sol}\big(\mathcal X\cap\bigcap_{i=1}^m\mathcal X_{\delta^{(i)}}\big)$.
--   3. **Support constraints** (Definition 2). Constraint $i$ is of support if removing it changes the solution. $s^*_m$ is the number of support constraints.
--   4. **Assumption 1.** For every $m$ and every sample of size $m$, program (9) has exactly one tie-broken solution.
--   5. **Assumption 2.** For every $m$, with $\mathbb P^m$-probability one, the solution of the program that keeps only the support constraints equals $x^*_m$.
--   6. **Measurability.** The set $\{(x,\delta):x\in\mathcal X_\delta\}$ is measurable in $\mathbb R^d\times\Delta$, and every solution map $\omega\mapsto x^*_m(\omega)$ is Borel measurable.
--   7. **The distributions $F_k$ of (12).** $F_k$ is the finite measure on $\mathbb R$ given by the law of $V(x^*_k)$ under $\mathbb P^k$ restricted to the event $\{s^*_k=k\}$, where $V$ is the violation (Definition 1). Its distribution function is
--   $$F_k(v)=\mathbb P^k\{V(x^*_k)\le v\ \wedge\ s^*_k=k\}.$$
--   8. **Problem (10).** A function $\xi$ is feasible if $\xi\in C^d[0,1]$ and
--   $$\frac1{k!}\frac{\mathrm d^k}{\mathrm dt^k}\xi(t)\ \ge\ \binom Nk t^{N-k}\,\mathbf 1_{[0,1-\epsilon(k))}(t),\qquad t\in[0,1],\ k=0,1,\dots,d,$$
--   and $\gamma^*$ is the infimum of $\xi(1)$ over the feasible $\xi$.
--   9. **Equation (11).** $\varphi_k(t)=\frac{\beta}{N+1}\sum_{m=k}^N\binom mk t^{m-k}-\binom Nk t^{N-k}$.
--
--   These objects are shared by every statement of the mission: Theorem 1 bounds $\mathbb P^N\{V(x^*_N)>\epsilon(s^*_N)\}$ by $\gamma^*$, and its proof expresses that probability through $F_0,\dots,F_d$.
--
--   **Formalization Note** Samples are indexed from $0$ (`Fin m`). The tie-break is the lexicographic order on $\mathbb R^{p+1}$; $p=0$ means no tie-break. When no unique tie-broken solution exists, `sol` returns the junk value $0$; Assumption 1 rules this out for every program used. A support constraint is one whose removal *changes the solution* (the paper's Definition 2), not one whose removal lowers the cost. $F_k$ is a measure, so the paper's Stieltjes integral $\int g\,\mathrm dF_k$ is the Lebesgue integral against it. In (10), $C^d[0,1]$ is `ContDiffOn ℝ d ξ (Icc 0 1)` and derivatives are taken within $[0,1]$ (one-sided at the endpoints); only the values of $\xi$ on $[0,1]$ matter. $\gamma^*$ is a real `sInf`; its defining set is nonempty ($\xi(t)=t^N$) and bounded below by $0$.
-- source:
--   Campi & Garatti, Wait-and-judge scenario optimization, Math. Program. (2018), doi:10.1007/s10107-016-1056-9 (accepted manuscript), PDF pp. 2–4 ((1), tie-break rule, Definitions 1–2, footnote 1), pp. 8–9 ((9), Assumptions 1–2), p. 10 ((10)), p. 11 ((11)), p. 13 ((12)), p. 20 (φ_k)

import Mathlib
import Definitions.Def_ScenarioApproach_Generalization_violation

namespace WaitJudge.Convex

open MeasureTheory ScenarioApproach.Generalization

/-- The decision space `ℝ^d` (Euclidean, with its Borel σ-algebra). -/
abbrev E (d : ℕ) : Type := EuclideanSpace ℝ (Fin d)

/-- Feasible set of the scenario program (9) in which only the constraints with index in `I`
are kept: `𝒳 ∩ ⋂_{i ∈ I} 𝒳_{δ⁽ⁱ⁾}`. With `I = univ` it is the feasible set of (9);
for `m = 0` it is the domain `𝒳` (program (9a)). Samples are indexed `0, …, m-1`. -/
def feasibleOn {d m : ℕ} {Δ : Type*} (X : Set (E d)) (Xδ : Δ → Set (E d))
    (ω : Fin m → Δ) (I : Finset (Fin m)) : Set (E d) :=
  X ∩ {x | ∀ i ∈ I, x ∈ Xδ (ω i)}

/-- Lexicographic key `(cᵀx, t₁(x), …, t_p(x))` of the cost followed by the tie-break functions. -/
noncomputable def key {d p : ℕ} (c : E d) (tb : Fin p → E d → ℝ) (x : E d) : Fin (p + 1) → ℝ :=
  Fin.cons (inner ℝ c x) (fun j => tb j x)

/-- `x` solves the program with feasible set `F` after the tie-break (p. 3): it minimises the
cost over `F`, then `t₁` among the minimisers, and so on, i.e. it is a lexicographic minimiser
of `key`. -/
def IsTBSolution {d p : ℕ} (c : E d) (tb : Fin p → E d → ℝ) (F : Set (E d)) (x : E d) : Prop :=
  x ∈ F ∧ ∀ y ∈ F, toLex (key c tb x) ≤ toLex (key c tb y)

/-- The solution of the program with feasible set `F`: the unique tie-broken solution when it
exists (Assumption 1 guarantees this), and the junk value `0` otherwise. It depends only on `F`. -/
noncomputable def sol {d p : ℕ} (c : E d) (tb : Fin p → E d → ℝ) (F : Set (E d)) : E d := by
  classical
  exact if h : ∃! x, IsTBSolution c tb F x then h.exists.choose else 0

/-- `x*_m`: the solution of the scenario program (9) built on the sample `ω` of size `m`. -/
noncomputable def xstar {d m p : ℕ} {Δ : Type*} (c : E d) (X : Set (E d)) (Xδ : Δ → Set (E d))
    (tb : Fin p → E d → ℝ) (ω : Fin m → Δ) : E d :=
  sol c tb (feasibleOn X Xδ ω Finset.univ)

/-- Definition 2 (p. 4, and p. 9 for (9)): constraint `i` is a support constraint if its removal
changes the solution. -/
def IsSupport {d m p : ℕ} {Δ : Type*} (c : E d) (X : Set (E d)) (Xδ : Δ → Set (E d))
    (tb : Fin p → E d → ℝ) (ω : Fin m → Δ) (i : Fin m) : Prop :=
  sol c tb (feasibleOn X Xδ ω (Finset.univ.erase i)) ≠ sol c tb (feasibleOn X Xδ ω Finset.univ)

/-- The set of indices of the support constraints of (9). -/
noncomputable def supportSet {d m p : ℕ} {Δ : Type*} (c : E d) (X : Set (E d))
    (Xδ : Δ → Set (E d)) (tb : Fin p → E d → ℝ) (ω : Fin m → Δ) : Finset (Fin m) := by
  classical
  exact Finset.univ.filter (IsSupport c X Xδ tb ω)

/-- `s*_m`: the number of support constraints of (9). -/
noncomputable def sstar {d m p : ℕ} {Δ : Type*} (c : E d) (X : Set (E d)) (Xδ : Δ → Set (E d))
    (tb : Fin p → E d → ℝ) (ω : Fin m → Δ) : ℕ :=
  (supportSet c X Xδ tb ω).card

/-- Assumption 1 (existence and uniqueness, p. 9): for every `m` and **every** sample of size
`m`, program (9) has exactly one tie-broken solution. -/
def Assumption1 {d p : ℕ} {Δ : Type*} (c : E d) (X : Set (E d)) (Xδ : Δ → Set (E d))
    (tb : Fin p → E d → ℝ) : Prop :=
  ∀ (m : ℕ) (ω : Fin m → Δ), ∃! x, IsTBSolution c tb (feasibleOn X Xδ ω Finset.univ) x

/-- Assumption 2 (non-degeneracy, p. 9): for every `m`, with `ℙ^m`-probability one the solution
with all constraints coincides with the solution where only the support constraints are kept. -/
def Assumption2 {d p : ℕ} {Δ : Type*} [MeasurableSpace Δ] (c : E d) (X : Set (E d))
    (Xδ : Δ → Set (E d)) (tb : Fin p → E d → ℝ) (P : Measure Δ) : Prop :=
  ∀ m : ℕ, ∀ᵐ ω ∂(Measure.pi fun _ : Fin m => P),
    sol c tb (feasibleOn X Xδ ω (supportSet c X Xδ tb ω)) = xstar c X Xδ tb ω

/-- The measurability the paper takes for granted (footnote 1, p. 4), pinned down as:
(a) the constraint relation `{(x, δ) | x ∈ 𝒳_δ}` is jointly measurable, and (b) for every `m`
the solution map `ω ↦ x*_m(ω)` is measurable (Borel σ-algebra on `ℝ^d`). -/
def MeasurabilityPins {d p : ℕ} {Δ : Type*} [MeasurableSpace Δ] (c : E d) (X : Set (E d))
    (Xδ : Δ → Set (E d)) (tb : Fin p → E d → ℝ) : Prop :=
  MeasurableSet {q : E d × Δ | q.1 ∈ Xδ q.2} ∧
    ∀ m : ℕ, Measurable (fun ω : Fin m → Δ => xstar c X Xδ tb ω)

/-- The first `k` scenarios of a sample of size `N ≥ k`. -/
def firstK {N k : ℕ} {Δ : Type*} (hk : k ≤ N) (ω : Fin N → Δ) : Fin k → Δ :=
  fun j => ω (Fin.castLE hk j)

/-- (12), p. 13: the generalized distribution `F_k`, as the finite measure on `ℝ` with
`F_k(v) = Fk k (Iic v) = ℙ^k{V(x*_k) ≤ v ∧ s*_k = k}` (not normalised). -/
noncomputable def Fk {d p : ℕ} {Δ : Type*} [MeasurableSpace Δ] (P : Measure Δ) (c : E d)
    (X : Set (E d)) (Xδ : Δ → Set (E d)) (tb : Fin p → E d → ℝ) (k : ℕ) : Measure ℝ :=
  ((Measure.pi fun _ : Fin k => P).restrict {ω | sstar c X Xδ tb ω = k}).map
    (fun ω => violation P Xδ (xstar c X Xδ tb ω))

/-- Feasibility for problem (10), p. 10: `ξ ∈ C^d[0,1]` and, for `k = 0, …, d` and `t ∈ [0,1]`,
`(1/k!) ξ⁽ᵏ⁾(t) ≥ C(N,k) t^{N-k} 𝟏_{[0,1-ε(k))}(t)` (derivatives within `[0,1]`). -/
def IsFeasible10 (N d : ℕ) (ε : ℕ → ℝ) (ξ : ℝ → ℝ) : Prop :=
  ContDiffOn ℝ d ξ (Set.Icc 0 1) ∧
    ∀ k ≤ d, ∀ t ∈ Set.Icc (0 : ℝ) 1,
      (N.choose k : ℝ) * t ^ (N - k) * Set.indicator (Set.Ico 0 (1 - ε k)) 1 t ≤
        (1 / (k.factorial : ℝ)) * iteratedDerivWithin k ξ (Set.Icc 0 1) t

/-- `γ*` of (10), p. 10: the infimum of `ξ(1)` over the feasible `ξ`. -/
noncomputable def gammaStar (N d : ℕ) (ε : ℕ → ℝ) : ℝ :=
  sInf {y | ∃ ξ, IsFeasible10 N d ε ξ ∧ y = ξ 1}

/-- The left-hand side of the polynomial equation (11), p. 11 (the function `φ_k` of Sect. 5.3,
p. 20): `β/(N+1) · Σ_{m=k}^{N} C(m,k) t^{m-k} − C(N,k) t^{N-k}`. -/
noncomputable def poly11 (N : ℕ) (β : ℝ) (k : ℕ) (t : ℝ) : ℝ :=
  β / ((N : ℝ) + 1) * ∑ m ∈ Finset.Icc k N, (m.choose k : ℝ) * t ^ (m - k) -
    (N.choose k : ℝ) * t ^ (N - k)

end WaitJudge.Convex



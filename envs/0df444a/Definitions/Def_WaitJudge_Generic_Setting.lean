-- Prove2me | Definitions.Def_WaitJudge_Generic_Setting
-- name    : WaitJudge_Generic_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T04:57:18.118991+00:00
-- url     : https://prove2.me/theorems/0cf5c80e-ed27-4601-a8dc-727b28feab77
-- title:
--   Generic scenario program, support constraints, Assumptions 1–2, F_k and (31)
-- statement:
--   Let S be a set of decisions, X ⊆ S the decision domain, and X_δ ⊆ S the constraint imposed by an uncertain outcome δ. A finite sample ω has constraints indexed by a finite set I. The feasible set keeps precisely those indexed constraints. A real cost f and a finite list of real tie-break functions select the lexicographically least feasible cost vector, whenever it exists uniquely. The full-sample solution is x*_m(ω). A constraint is a support constraint precisely when removing it changes that selected solution, and s*_m is the number of such constraints.
--
--   Assumption 1 requires a unique selected solution for every finite sample, including the empty sample. Assumption 2 says that, almost surely, retaining only support constraints gives the same selected solution. The measure F_k is the distribution of the violation V(x*_k) restricted to samples with s*_k = k. The variational value in (31) is
--
--   $$
--   \gamma^*=\inf\left\{q(1):\deg q\le N,\quad \frac{q^{(k)}(t)}{k!}\ge {N\choose k}t^{N-k}{\bf1}_{[0,1-\varepsilon(k))}(t)\quad(0\le k\le N,\ 0\le t\le1)\right\}.
--   $$
--
--   These definitions supply the common mathematical objects for both the tail bound and its proof milestones.
--
--   **Formalization Note** Samples use zero-based `Fin` indices, so an m-sample has indices 0 through m−1. The fallback value of the solution selector is irrelevant under Assumption 1. The finite tie-break list is the pinned form of the paper's tie-break rule; no convexity is assumed. The measure F_k encodes the paper's generalized distribution function. `P_N` is read as degree at most N, as confirmed by the coefficient representation in (36). Measurability of the constraint relation, every solution map, and every support event pins down the convention of footnote 1. The coefficient dual value and root polynomial are also defined here for (36), (39), and (32).
-- source:
--   Campi & Garatti, Wait-and-judge scenario optimization, Math. Program. (2018), doi:10.1007/s10107-016-1056-9 (accepted manuscript), PDF pp. 3–4, Definitions 1–2; p. 9, Assumptions 1–2; p. 13, (12); pp. 21–22, (30)–(31); pp. 25–27, (36), (39)

import Mathlib
import Definitions.Def_ScenarioApproach_Nonconvex_violation

namespace WaitJudge.Generic

open MeasureTheory
open scoped Pi.Lex

/-- The feasible set when only the constraints indexed by `I` are kept. -/
def feasibleOn {S Δ : Type*} {m : ℕ} (X : Set S) (Xδ : Δ → Set S)
    (ω : Fin m → Δ) (I : Finset (Fin m)) : Set S :=
  X ∩ {x | ∀ i ∈ I, x ∈ Xδ (ω i)}

/-- The cost followed by the finite sequence of tie-break costs. -/
def key {S : Type*} {p : ℕ} (f : S → ℝ) (tb : Fin p → S → ℝ) (x : S) :
    Fin (p + 1) → ℝ :=
  Fin.cons (f x) (fun j => tb j x)

/-- The lexicographically selected minimizer of a feasible set. -/
def IsTBSolution {S : Type*} {p : ℕ} (f : S → ℝ) (tb : Fin p → S → ℝ)
    (F : Set S) (x : S) : Prop :=
  x ∈ F ∧ ∀ y ∈ F, toLex (key f tb x) ≤ toLex (key f tb y)

/-- Selected solution; the fallback is used only when unique existence fails. -/
noncomputable def sol {S : Type*} [Nonempty S] {p : ℕ} (f : S → ℝ)
    (tb : Fin p → S → ℝ) (F : Set S) : S := by
  classical
  exact if h : ∃! x, IsTBSolution f tb F x then h.exists.choose else Classical.choice ‹Nonempty S›

/-- Solution of the full sample program. -/
noncomputable def xstar {S Δ : Type*} [Nonempty S] {p m : ℕ}
    (f : S → ℝ) (X : Set S) (Xδ : Δ → Set S) (tb : Fin p → S → ℝ)
    (ω : Fin m → Δ) : S :=
  sol f tb (feasibleOn X Xδ ω Finset.univ)

/-- A constraint supports the solution if deleting it changes the selected solution. -/
def IsSupport {S Δ : Type*} [Nonempty S] {p m : ℕ}
    (f : S → ℝ) (X : Set S) (Xδ : Δ → Set S) (tb : Fin p → S → ℝ)
    (ω : Fin m → Δ) (i : Fin m) : Prop :=
  sol f tb (feasibleOn X Xδ ω (Finset.univ.erase i)) ≠ xstar f X Xδ tb ω

/-- The indices of support constraints. -/
noncomputable def supportSet {S Δ : Type*} [Nonempty S] {p m : ℕ}
    (f : S → ℝ) (X : Set S) (Xδ : Δ → Set S) (tb : Fin p → S → ℝ)
    (ω : Fin m → Δ) : Finset (Fin m) := by
  classical
  exact Finset.univ.filter (fun i => IsSupport f X Xδ tb ω i)

/-- Number of support constraints. -/
noncomputable def sstar {S Δ : Type*} [Nonempty S] {p m : ℕ}
    (f : S → ℝ) (X : Set S) (Xδ : Δ → Set S) (tb : Fin p → S → ℝ)
    (ω : Fin m → Δ) : ℕ :=
  (supportSet f X Xδ tb ω).card

/-- Assumption 1: every finite sample program has exactly one selected solution. -/
def Assumption1 {S Δ : Type*} [Nonempty S] {p : ℕ}
    (f : S → ℝ) (X : Set S) (Xδ : Δ → Set S) (tb : Fin p → S → ℝ) : Prop :=
  ∀ m : ℕ, ∀ ω : Fin m → Δ,
    ∃! x, IsTBSolution f tb (feasibleOn X Xδ ω Finset.univ) x

/-- Assumption 2: almost surely the support constraints alone select the full solution. -/
def Assumption2 {S Δ : Type*} [Nonempty S] [MeasurableSpace Δ] {p : ℕ}
    (f : S → ℝ) (X : Set S) (Xδ : Δ → Set S) (tb : Fin p → S → ℝ)
    (P : Measure Δ) : Prop :=
  ∀ m : ℕ, ∀ᵐ ω : Fin m → Δ ∂(Measure.pi fun _ : Fin m => P),
    sol f tb (feasibleOn X Xδ ω (supportSet f X Xδ tb ω)) = xstar f X Xδ tb ω

/-- The measurability conventions implicit in footnote 1, including support events. -/
def MeasurabilityPins {S Δ : Type*} [Nonempty S] [MeasurableSpace S]
    [MeasurableSpace Δ] {p : ℕ} (f : S → ℝ) (X : Set S)
    (Xδ : Δ → Set S) (tb : Fin p → S → ℝ) : Prop :=
  MeasurableSet {q : S × Δ | q.1 ∈ Xδ q.2} ∧
  (∀ m : ℕ, Measurable (fun ω : Fin m → Δ => xstar f X Xδ tb ω)) ∧
  (∀ m : ℕ, ∀ i : Fin m,
    MeasurableSet {ω : Fin m → Δ | i ∈ supportSet f X Xδ tb ω})

/-- Restriction of a sample to its first `k` coordinates. -/
def firstK {Δ : Type*} {m : ℕ} (ω : Fin m → Δ) (k : ℕ) (hk : k ≤ m) :
    Fin k → Δ :=
  fun i => ω ⟨i.1, lt_of_lt_of_le i.2 hk⟩

/-- The finite measure whose distribution function is the paper's `F_k`. -/
noncomputable def Fk {S Δ : Type*} [Nonempty S] [MeasurableSpace Δ]
    {p : ℕ} (f : S → ℝ) (X : Set S) (Xδ : Δ → Set S)
    (tb : Fin p → S → ℝ) (P : Measure Δ) (k : ℕ) : Measure ℝ :=
  ((Measure.pi fun _ : Fin k => P).restrict
    {ω : Fin k → Δ | sstar f X Xδ tb ω = k}).map
    (fun ω => ScenarioApproach.Nonconvex.violation P Xδ (xstar f X Xδ tb ω))

/-- Feasibility in the variational problem (31); `P_N` means degree at most `N`. -/
def IsFeasible31 (N : ℕ) (ε : ℕ → ℝ) (q : Polynomial ℝ) : Prop :=
  q.natDegree ≤ N ∧
  ∀ k ≤ N, ∀ t ∈ Set.Icc (0 : ℝ) 1,
    (N.choose k : ℝ) * t ^ (N - k) *
      Set.indicator (Set.Ico 0 (1 - ε k)) (fun _ => (1 : ℝ)) t ≤
    (1 / (k.factorial : ℝ)) * ((Polynomial.derivative^[k] q).eval t)

/-- The infimum of feasible values of `ξ(1)` in (31). -/
noncomputable def gammaStar31 (N : ℕ) (ε : ℕ → ℝ) : ℝ :=
  sInf {y : ℝ | ∃ q : Polynomial ℝ, IsFeasible31 N ε q ∧ y = q.eval 1}

/-- The coefficient form of the dual constraints (36) with `M = N`. -/
def IsFeasibleDualN (N : ℕ) (ε : ℕ → ℝ) (lam : ℕ → ℝ) : Prop :=
  ∀ k ≤ N, ∀ t ∈ Set.Icc (0 : ℝ) 1,
    (N.choose k : ℝ) * t ^ (N - k) *
      Set.indicator (Set.Ico 0 (1 - ε k)) (fun _ => (1 : ℝ)) t ≤
    ∑ m ∈ Finset.Icc k N, lam m * (m.choose k : ℝ) * t ^ (m - k)

/-- The dual optimum `γ_N*` in (36). -/
noncomputable def gammaStarDualN (N : ℕ) (ε : ℕ → ℝ) : ℝ :=
  sInf {y : ℝ | ∃ lam : ℕ → ℝ,
    IsFeasibleDualN N ε lam ∧ y = ∑ m ∈ Finset.range (N + 1), lam m}

/-- Difference of the two sides of the root equation (32). -/
noncomputable def phi (N k : ℕ) (β t : ℝ) : ℝ :=
  β / (N + 1) *
    (∑ m ∈ Finset.Icc k N, (m.choose k : ℝ) * t ^ (m - k)) -
    (N.choose k : ℝ) * t ^ (N - k)

end WaitJudge.Generic



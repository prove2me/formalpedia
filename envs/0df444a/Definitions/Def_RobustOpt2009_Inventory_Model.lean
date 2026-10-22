-- Prove2me | Definitions.Def_RobustOpt2009_Inventory_Model
-- name    : RobustOpt2009_Inventory_Model
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-22T03:44:04.419215+00:00
-- url     : https://prove2.me/theorems/f16105cb-dec6-447d-8f01-60312899b239
-- title:
--   Lemma 15.2.1: multistage convex problem and extended optimal value
-- statement:
--   At each stage $t=1,\ldots,T+1$, the decision $S_t$ is a vector in $\mathbb R^{m_t}$ chosen as a function of the observed history $(d_0,\ldots,d_{t-1})$. Observation $d_j$ belongs to $\mathbb R^{n_j}$. The data are fixed linear maps $A_t,B_{t+1},C_{t+1}$, vectors $b_t$, stage costs $f_t$, and a real bound $R$. The map $B_{t+1}$ acts on the full history $d^t=(d_0,\ldots,d_t)$.
--
--   For scenario sets $F_0,\ldots,F_T$, a policy and real number $E$ are feasible when, for every trajectory in their Cartesian product,
--   $$\sum_{t=1}^{T+1}f_t(S_t(d^{t-1}))\le E,\qquad A_1S_1(d^0)\ge b_1,$$
--   $$A_{t+1}S_{t+1}(d^t)\ge B_{t+1}d^t+C_{t+1}S_t(d^{t-1})+b_{t+1}\quad(1\le t\le T),$$
--   $$\|S_t(d^{t-1})\|_\infty\le R\quad(1\le t\le T).$$
--   The optimal value is the extended-real infimum of all such real $E$, over all policies. A nonempty polytope is the convex hull of a nonempty finite set. Regular costs take values in $\mathbb R\cup\{+\infty\}$, are lower semicontinuous and convex on their effective domains, and have domains described by finitely many nonstrict linear inequalities. The data structure itself imposes no regularity assumptions; these are separate predicates for the theorem.
--
--   This gives a reusable model of problem (P), including nonanticipativity and terminal recourse.
--
--   **Formalization Note** Histories are finite dependent tuples. Dimensions and data are indexed by natural numbers, with only the displayed stage ranges used. Linear maps represent matrices without selecting a basis for the stacked history. The ordinary norm on a finite real function space is the infinity norm. Costs use `EReal`, with $-\infty$ excluded by the regularity predicate. The infimum is $+\infty$ when no finite objective bound is achievable and $-\infty$ when such bounds are unbounded below. No terminal norm bound or attainment assertion is added.
-- source:
--   Ben-Tal, El Ghaoui and Nemirovski, Robust Optimization, Princeton University Press, 2009, https://doi.org/10.1515/9781400831050, Lemma 15.2.1, problem (P), printed p. 430 (PDF p. 456).

import Mathlib

open scoped BigOperators

namespace RobustOpt2009.Inventory

/-- A history of length `t` contains the data `d₀, …, dₜ₋₁`. -/
abbrev History (n : ℕ → ℕ) (t : ℕ) := (j : Fin t) → Fin (n j.val) → ℝ

/-- Restrict a history to its first `t` observations. -/
def takeHistory {n : ℕ → ℕ} {u : ℕ} (d : History n u) (t : ℕ) (h : t ≤ u) :
    History n t := fun j => d ⟨j.val, lt_of_lt_of_le j.isLt h⟩

/-- Decision `S_t` sees exactly `d₀, …, dₜ₋₁`; unused stages are immaterial. -/
abbrev Policy (n m : ℕ → ℕ) := (t : ℕ) → History n t → (Fin (m t) → ℝ)

/-- Concrete data of problem (P), Lemma 15.2.1. `B t` is the printed `B_{t+1}`
acting on the whole prefix `d^t`; `C t` is the printed `C_{t+1}`. -/
structure Model (n m k : ℕ → ℕ) where
  A : (t : ℕ) → (Fin (m t) → ℝ) →ₗ[ℝ] (Fin (k t) → ℝ)
  B : (t : ℕ) → History n (t + 1) →ₗ[ℝ] (Fin (k (t + 1)) → ℝ)
  C : (t : ℕ) → (Fin (m t) → ℝ) →ₗ[ℝ] (Fin (k (t + 1)) → ℝ)
  b : (t : ℕ) → Fin (k t) → ℝ
  f : (t : ℕ) → (Fin (m t) → ℝ) → EReal
  R : ℝ

/-- A polyhedral domain is the solution set of finitely many nonstrict linear inequalities. -/
def PolyhedralDomain {m : ℕ} (f : (Fin m → ℝ) → EReal) : Prop :=
  ∃ (q : ℕ) (G : Matrix (Fin q) (Fin m) ℝ) (g : Fin q → ℝ),
    {x | f x ≠ ⊤} = {x | G.mulVec x ≤ g}

/-- Real-valued on its effective domain, extended by `+∞`, lower semicontinuous,
convex there, with a polyhedral domain. No polyhedral-epigraph hypothesis is imposed. -/
def RegularCost {m : ℕ} (f : (Fin m → ℝ) → EReal) : Prop :=
  (∀ x, f x ≠ ⊥) ∧ LowerSemicontinuous f ∧
    ConvexOn ℝ {x | f x ≠ ⊤} (fun x => (f x).toReal) ∧ PolyhedralDomain f

/-- Nonempty polytopes, allowing lower-dimensional and singleton polytopes. -/
def NonemptyPolytope {n : ℕ} (D : Set (Fin n → ℝ)) : Prop :=
  ∃ V : Finset (Fin n → ℝ), V.Nonempty ∧ D = convexHull ℝ (V : Set (Fin n → ℝ))

/-- The product uncertainty set `F₀ × ⋯ × F_T`. -/
def Scenarios {n : ℕ → ℕ} (T : ℕ) (F : (t : ℕ) → Set (Fin (n t) → ℝ)) :
    Set (History n (T + 1)) := {d | ∀ j, d j ∈ F j.val}

/-- Epigraph feasibility of problem (P). The terminal cost and terminal recourse
are included; the printed norm bound applies only to stages `1, …, T`. -/
def FeasibleBound {n m k : ℕ → ℕ} (M : Model n m k) (T : ℕ)
    (F : (t : ℕ) → Set (Fin (n t) → ℝ)) (S : Policy n m) (E : ℝ) : Prop :=
  ∀ d ∈ Scenarios T F,
    (∑ t : Fin (T + 1), M.f (t.val + 1)
      (S (t.val + 1) (takeHistory d (t.val + 1) (Nat.succ_le_of_lt t.isLt)))) ≤ (E : EReal) ∧
    M.b 1 ≤ M.A 1 (S 1 (takeHistory d 1 (Nat.succ_le_succ (Nat.zero_le T)))) ∧
    (∀ t : ℕ, ∀ _ht : 1 ≤ t, ∀ hT : t ≤ T,
      M.B t (takeHistory d (t + 1) (Nat.succ_le_succ hT)) +
        M.C t (S t (takeHistory d t (Nat.le_trans hT (Nat.le_succ T)))) + M.b (t + 1) ≤
        M.A (t + 1) (S (t + 1) (takeHistory d (t + 1) (Nat.succ_le_succ hT)))) ∧
    (∀ t : ℕ, ∀ _ht : 1 ≤ t, ∀ hT : t ≤ T,
      ‖S t (takeHistory d t (Nat.le_trans hT (Nat.le_succ T)))‖ ≤ M.R)

/-- Optimal value of (P): extended-real infimum of all feasible real epigraph
bounds. It is `+∞` if no finite bound is achievable and `−∞` if unbounded below. -/
noncomputable def optimalValue {n m k : ℕ → ℕ} (M : Model n m k) (T : ℕ)
    (F : (t : ℕ) → Set (Fin (n t) → ℝ)) : EReal :=
  sInf {v : EReal | ∃ E : ℝ, v = (E : EReal) ∧ ∃ S : Policy n m, FeasibleBound M T F S E}

end RobustOpt2009.Inventory



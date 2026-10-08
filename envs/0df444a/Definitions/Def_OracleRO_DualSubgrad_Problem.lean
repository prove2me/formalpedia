-- Prove2me | Definitions.Def_OracleRO_DualSubgrad_Problem
-- name    : OracleRO_DualSubgrad_Problem
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-05T08:46:44.110949+00:00
-- url     : https://prove2.me/theorems/c9b0dae3-5940-4cde-bb71-235d800c8d20
-- title:
--   Robust feasibility problem (3), its ε-approximate solutions, and the oracle $\mathcal O_\epsilon$ of Figure 1
-- statement:
--   Let $\mathcal D\subseteq\mathbb R^n$ be the domain, $\mathcal U\subseteq\mathbb R^d$ the uncertainty set, and $f_1,\dots,f_m:\mathbb R^n\times\mathbb R^d\to\mathbb R$ the constraint functions. Problem (3) asks whether
--
--   $$
--   \exists\, x\in\mathcal D:\quad f_i(x,u_i)\le 0\quad\forall u_i\in\mathcal U,\ i=1,\dots,m .
--   $$
--
--   This file defines three notions.
--
--   1. **Robust feasibility**: some $x\in\mathcal D$ satisfies $f_i(x,u)\le 0$ for every $i$ and every $u\in\mathcal U$.
--   2. **$\epsilon$-approximate solution** (p. 4): a point $x\in\mathcal D$ that meets each constraint up to $\epsilon$, i.e. $f_i(x,u)\le\epsilon$ for all $u\in\mathcal U$ and $i=1,\dots,m$.
--   3. **$\epsilon$-approximate optimization oracle** $\mathcal O_\epsilon$ (Figure 1): a procedure that, on input a noise vector $u=(u_1,\dots,u_m)$ with every $u_i\in\mathcal U$, either outputs a vector $x\in\mathcal D$ with $f_i(x,u_i)\le\epsilon$ for $i=1,\dots,m$, or outputs "infeasible", and the latter only if there is no $x\in\mathcal D$ with $f_i(x,u_i)\le 0$ for $i=1,\dots,m$.
--
--   The oracle solves the original, non-robust problem approximately for a fixed noise vector; the algorithms of the paper reduce the robust problem (3) to calls of this oracle.
--
--   **Formalization Note** The oracle is a function from $m$-tuples of noise vectors to `Option` points, with `none` meaning "infeasible"; the predicate constrains its answers only on inputs in $\mathcal U^m$. When both answers are allowed (the nominal problem is $\epsilon$-feasible but not $0$-feasible), either is permitted. The uncertainty set is one set $\mathcal U$ shared by all constraints, as in the paper's $\boldsymbol{\mathcal U}=\mathcal U^m$.
-- source:
--   Ben-Tal, Hazan, Koren, Mannor, Oracle-Based Robust Optimization via Online Learning, arXiv:1402.6361v1, p. 4, problem (3) and the definition of an ε-approximate solution; p. 6, Figure 1

import Mathlib

namespace OracleRO.DualSubgrad

/-- The robust feasibility problem (3) (p. 4) is feasible: some `x ∈ 𝒟` satisfies
`f i x u ≤ 0` for every constraint `i` and every `u ∈ 𝒰`. -/
def RobustFeasible {m n d : ℕ} (Dom : Set (EuclideanSpace ℝ (Fin n)))
    (U : Set (EuclideanSpace ℝ (Fin d)))
    (f : Fin m → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin d) → ℝ) : Prop :=
  ∃ x ∈ Dom, ∀ i, ∀ u ∈ U, f i x u ≤ 0

/-- `x` is an `ε`-approximate solution of problem (3) (p. 4): `x ∈ 𝒟` and
`f i x u ≤ ε` for every constraint `i` and every `u ∈ 𝒰`. -/
def IsApproxSolution {m n d : ℕ} (Dom : Set (EuclideanSpace ℝ (Fin n)))
    (U : Set (EuclideanSpace ℝ (Fin d)))
    (f : Fin m → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin d) → ℝ) (ε : ℝ)
    (x : EuclideanSpace ℝ (Fin n)) : Prop :=
  x ∈ Dom ∧ ∀ i, ∀ u ∈ U, f i x u ≤ ε

/-- The `ε`-approximate optimization oracle `O_ε` of Figure 1 (p. 6). On every noise vector
`u = (u₁, …, u_m)` with each `uᵢ ∈ 𝒰`, the answer `O u = some x` is a point `x ∈ 𝒟` with
`f i x (u i) ≤ ε` for all `i`, and the answer `O u = none` ("infeasible") is given only when
no `x ∈ 𝒟` satisfies `f i x (u i) ≤ 0` for all `i`. -/
def IsApproxOracle {m n d : ℕ} (Dom : Set (EuclideanSpace ℝ (Fin n)))
    (U : Set (EuclideanSpace ℝ (Fin d)))
    (f : Fin m → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin d) → ℝ) (ε : ℝ)
    (O : (Fin m → EuclideanSpace ℝ (Fin d)) → Option (EuclideanSpace ℝ (Fin n))) : Prop :=
  ∀ u : Fin m → EuclideanSpace ℝ (Fin d), (∀ i, u i ∈ U) →
    (∀ x, O u = some x → x ∈ Dom ∧ ∀ i, f i x (u i) ≤ ε) ∧
    (O u = none → ¬ ∃ x ∈ Dom, ∀ i, f i x (u i) ≤ 0)

end OracleRO.DualSubgrad



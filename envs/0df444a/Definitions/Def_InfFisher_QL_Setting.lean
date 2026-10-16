-- Prove2me | Definitions.Def_InfFisher_QL_Setting
-- name    : InfFisher_QL_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-16T08:04:28.433275+00:00
-- url     : https://prove2.me/theorems/48b91c55-d6ba-4e2a-8261-b003abbd435b
-- title:
--   §6 — quasilinear demand, equilibrium, and primal and dual programs
-- statement:
--   For a buyer with valuation density $v_i$, budget $B_i$, and price density $p$, **quasilinear demand** maximizes $\langle v_i-p,y\rangle$ among nonnegative essentially bounded bundles $y$ with $\langle p,y\rangle\le B_i$. A **quasilinear market equilibrium** consists of a supply-feasible allocation $x$, a nonnegative integrable price $p$, buyer-optimal bundles $x_i$, and market clearance $\langle p,1-\sum_i x_i\rangle=0$.
--
--   For the quasilinear primal program, set $u_i=\langle v_i,x_i\rangle+\delta_i$, where $\delta_i\ge0$. Its objective is
--   $$\sum_i\bigl(B_i\log(\langle v_i,x_i\rangle+\delta_i)-\delta_i\bigr).$$
--   The dual minimizes $\langle p,1\rangle-\sum_i B_i\log\beta_i$ subject to $p\ge\beta_i v_i$ and $0\le\beta_i\le1$. This module defines their feasible and optimal points and the reduced dual objective obtained by taking $p=\max_i\beta_i v_i$.
--
--   **Formalization Note** Supply feasibility is included in equilibrium because otherwise Theorem 10(d) is false; the printed QLME definition omits it, whereas the linear equilibrium definition includes it. The primal is expressed in $(x,\delta)$ with $u$ set to its largest feasible value; otherwise the printed KKT list does not characterize optimality. Positive logarithm arguments are required in the optimality predicates.
-- source:
--   Gao & Kroer, Infinite-Dimensional Fisher Markets and Tractable Fair Division, arXiv:2010.03025v5, §6, pp. 29–30; proof of Theorem 10, p. a21

import Mathlib
import Definitions.Def_InfFisher_EG_Market
import Definitions.Def_InfFisher_EG_Setting

namespace InfFisher.QL

open MeasureTheory

variable {α : Type*} [MeasurableSpace α]

/-- A budget-feasible quasilinear utility maximizing bundle. -/
def InQLDemand (μ : Measure α) {n : ℕ} (v : Fin n → α → ℝ)
    (B : Fin n → ℝ) (p : α → ℝ) (i : Fin n) (y : α → ℝ) : Prop :=
  InfFisher.EG.IsBundle μ y ∧ InfFisher.EG.pair μ p y ≤ B i ∧
    ∀ y', InfFisher.EG.IsBundle μ y' → InfFisher.EG.pair μ p y' ≤ B i →
      InfFisher.EG.pair μ (fun θ => v i θ - p θ) y' ≤
        InfFisher.EG.pair μ (fun θ => v i θ - p θ) y

/-- Quasilinear equilibrium, including unit-supply feasibility as in the
linear market equilibrium of §2. -/
def IsQLME (μ : Measure α) {n : ℕ} (v : Fin n → α → ℝ)
    (B : Fin n → ℝ) (x : Fin n → α → ℝ) (p : α → ℝ) : Prop :=
  InfFisher.EG.IsPrice μ p ∧ InfFisher.EG.IsAllocation μ x ∧
    (∀ i, InQLDemand μ v B p i (x i)) ∧
    InfFisher.EG.pair μ p (fun θ => 1 - ∑ i, x i θ) = 0

/-- Quasilinear primal feasibility after eliminating u at its largest feasible value. -/
def IsPQLFeasible (μ : Measure α) {n : ℕ} (x : Fin n → α → ℝ)
    (δ : Fin n → ℝ) : Prop :=
  InfFisher.EG.IsAllocation μ x ∧ ∀ i, 0 ≤ δ i

/-- Quasilinear Eisenberg-Gale primal objective. -/
noncomputable def pqlObj (μ : Measure α) {n : ℕ} (v : Fin n → α → ℝ)
    (B : Fin n → ℝ) (x : Fin n → α → ℝ) (δ : Fin n → ℝ) : ℝ :=
  ∑ i, (B i * Real.log (InfFisher.EG.pair μ (v i) (x i) + δ i) - δ i)

/-- Optimality in the domain of positive logarithm arguments. -/
def IsPQLOptimal (μ : Measure α) {n : ℕ} (v : Fin n → α → ℝ)
    (B : Fin n → ℝ) (x : Fin n → α → ℝ) (δ : Fin n → ℝ) : Prop :=
  IsPQLFeasible μ x δ ∧
    (∀ i, 0 < InfFisher.EG.pair μ (v i) (x i) + δ i) ∧
    ∀ x' δ', IsPQLFeasible μ x' δ' →
      (∀ i, 0 < InfFisher.EG.pair μ (v i) (x' i) + δ' i) →
      pqlObj μ v B x' δ' ≤ pqlObj μ v B x δ

/-- Dual feasibility adds the quasilinear bound beta_i ≤ 1. -/
def IsDQLFeasible (μ : Measure α) {n : ℕ} (v : Fin n → α → ℝ)
    (p : α → ℝ) (β : Fin n → ℝ) : Prop :=
  InfFisher.EG.IsDEGFeasible μ v p β ∧ ∀ i, β i ≤ 1

/-- Dual optimality with strictly positive beta coordinates. -/
def IsDQLOptimal (μ : Measure α) {n : ℕ} (v : Fin n → α → ℝ)
    (B : Fin n → ℝ) (p : α → ℝ) (β : Fin n → ℝ) : Prop :=
  IsDQLFeasible μ v p β ∧ (∀ i, 0 < β i) ∧
    ∀ p' β', IsDQLFeasible μ v p' β' → (∀ i, 0 < β' i) →
      InfFisher.EG.degObj μ B p β ≤ InfFisher.EG.degObj μ B p' β'

end InfFisher.QL



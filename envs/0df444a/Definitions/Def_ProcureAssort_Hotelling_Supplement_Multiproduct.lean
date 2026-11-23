-- Prove2me | Definitions.Def_ProcureAssort_Hotelling_Supplement_Multiproduct
-- name    : ProcureAssort_Hotelling_Supplement_Multiproduct
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T12:29:10.957213+00:00
-- url     : https://prove2.me/theorems/326ea58d-ee8a-46ec-8f5d-2e7cefc0bf4b
-- title:
--   Supplier-tagged products, scalar reports, modified virtual costs and multiproduct mechanisms
-- statement:
--   Supplier $i$ owns a finite set $P_i$ of products and reports a single scalar type. The known cost function $c_{ip}(t)$ determines each product's cost. Modified virtual costs are
--
--   $$v_{ip}(t)=c_{ip}(t)+\frac{F_i(\rho_i(t))}{f_i(t)}\bigl(c_{ip}(t)-c_{ip}(\rho_i(t))\bigr).$$
--
--   Supplier profit is $t_i-\sum_{p\in P_i}c_{ip}(\theta_i)x_{ip}$, and interim utility averages this supplier-total profit over other suppliers' reports. Centralized feasibility imposes Bayesian IC, interim IR and unit total product consumption. Under linear pricing the supplier's total transfer is $\sum_{p\in P_i}p_{ip}x_{ip}$ and quantities maximize the same quadratic consumer surplus on the product assortment. The objective subtracts supplier-total transfers once. The two optimal values are the suprema of their actual feasible objective sets.
--
--   The increasing-differences predicate is stated on the source's full real quantity and scalar-type domain. Demand and active sets use the unchanged quadratic market on tagged product coordinates; products do not become independently reporting suppliers. The type neighborhood is the coordinate sup norm in scalar types, not in virtual costs.
-- source:
--   Saban & Weintraub, Procurement Mechanisms for Assortments of Differentiated Products, SSRN 3453144 (author version of 2020-03-03; Oper. Res. doi:10.1287/opre.2020.2053), Appendix J and L.2.2, pp. 61–63, 71–75

import Mathlib
import Definitions.Def_ProcureAssort_Hotelling_Supplement_Types
import Definitions.Def_ProcureAssort_Hotelling_Supplement_QuadraticMarket

namespace ProcureAssort.Hotelling.Supplement

/-- Products retain their supplier tag; reports have one scalar per supplier. -/
abbrev Product {n : ℕ} (m : Fin n → ℕ) := (i : Fin n) × Fin (m i)

variable {n : ℕ} (m : Fin n → ℕ) (Θ : Fin n → Finset ℝ) (f : Fin n → ℝ → ℝ)

/-- Modified virtual cost, Appendix J, p. 62. -/
noncomputable def multiVirtual (cost : (i : Fin n) → Fin (m i) → ℝ → ℝ)
    (i : Fin n) (p : Fin (m i)) (c : ℝ) : ℝ :=
  cost i p c + cdfF Θ f i (pred Θ i c) / f i c *
    (cost i p c - cost i p (pred Θ i c))

/-- Supplier i's total production cost h_i, whose domain is all real product quantities. -/
def supplierCost (cost : (i : Fin n) → Fin (m i) → ℝ → ℝ)
    (i : Fin n) (x : Fin (m i) → ℝ) (c : ℝ) : ℝ := ∑ p, cost i p c * x p

/-- The increasing-differences assumption of p. 62 on its stated ℝ^{|P_i|}×ℝ domain. -/
def IncreasingCostDifferences (cost : (i : Fin n) → Fin (m i) → ℝ → ℝ) : Prop :=
  ∀ i, ∀ x y : Fin (m i) → ℝ, x ≤ y → ∀ a b : ℝ, a ≤ b →
    supplierCost m cost i y a - supplierCost m cost i x a ≤
      supplierCost m cost i y b - supplierCost m cost i x b

noncomputable def multiVvec (cost : (i : Fin n) → Fin (m i) → ℝ → ℝ)
    (θ : Profile Θ) (p : Product m) : ℝ := multiVirtual m Θ f cost p.1 p.2 (θ p.1)

/-- Supplier-total interim utility. Transfers t_i are supplier totals, not product reports. -/
noncomputable def multiUtility (cost : (i : Fin n) → Fin (m i) → ℝ → ℝ)
    (x : Profile Θ → Product m → ℝ) (t : Profile Θ → Fin n → ℝ)
    (i : Fin n) (report truth : ℝ) : ℝ :=
  interim f (fun θ => t θ i - ∑ p, cost i p truth * x θ ⟨i,p⟩) i report

def MultiCentFeasible (cost : (i : Fin n) → Fin (m i) → ℝ → ℝ)
    (x : Profile Θ → Product m → ℝ) (t : Profile Θ → Fin n → ℝ) : Prop :=
  (∀ i, ∀ a ∈ Θ i, ∀ b ∈ Θ i, multiUtility m Θ f cost x t i b a ≤ multiUtility m Θ f cost x t i a a) ∧
  (∀ i, ∀ a ∈ Θ i, 0 ≤ multiUtility m Θ f cost x t i a a) ∧
  (∀ θ, x θ ∈ productSimplex (Product m))

noncomputable def multiCentObj (M : QuadraticMarket (Product m))
    (x : Profile Θ → Product m → ℝ) (t : Profile Θ → Fin n → ℝ) : ℝ :=
  expect f (fun θ => M.gcs (x θ) - ∑ i, t θ i)

noncomputable def multiTransfer (p x : Profile Θ → Product m → ℝ)
    (θ : Profile Θ) (i : Fin n) : ℝ := ∑ k, p θ ⟨i,k⟩ * x θ ⟨i,k⟩

def MultiDecFeasible (M : QuadraticMarket (Product m))
    (cost : (i : Fin n) → Fin (m i) → ℝ → ℝ)
    (q : Profile Θ → Finset (Product m)) (p x : Profile Θ → Product m → ℝ) : Prop :=
  MultiCentFeasible m Θ f cost x (multiTransfer m Θ p x) ∧
  ∀ θ, M.IsDemand (q θ) (p θ) (x θ)

noncomputable def multiCentValues (M : QuadraticMarket (Product m))
    (cost : (i : Fin n) → Fin (m i) → ℝ → ℝ) : Set ℝ :=
  {r | ∃ x t, MultiCentFeasible m Θ f cost x t ∧ r = multiCentObj m Θ f M x t}

noncomputable def multiDecValues (M : QuadraticMarket (Product m))
    (cost : (i : Fin n) → Fin (m i) → ℝ → ℝ) : Set ℝ :=
  {r | ∃ q p x, MultiDecFeasible m Θ f M cost q p x ∧
    r = multiCentObj m Θ f M x (multiTransfer m Θ p x)}

noncomputable def multiQ (M : QuadraticMarket (Product m))
    (cost : (i : Fin n) → Fin (m i) → ℝ → ℝ) (θ : Profile Θ) : Finset (Product m) :=
  M.active (multiVvec m Θ f cost θ)

/-- Type sup-norm neighborhood of J.1, not a virtual-cost neighborhood. -/
def TypeDistanceLE (θ θ' : Profile Θ) (r : ℝ) : Prop :=
  ∀ i, |(θ i : ℝ) - (θ' i : ℝ)| ≤ r

end ProcureAssort.Hotelling.Supplement



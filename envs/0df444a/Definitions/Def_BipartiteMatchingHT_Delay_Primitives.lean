-- Prove2me | Definitions.Def_BipartiteMatchingHT_Delay_Primitives
-- name    : BipartiteMatchingHT_Delay_Primitives
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-30T19:11:46.349987+00:00
-- url     : https://prove2.me/theorems/4af7afbb-ec0e-4ce8-a968-18406b22655f
-- title:
--   Matching primitives, capacity slack, and residual edges
-- statement:
--   There are arbitrary positive finite numbers $n,m$ of customer classes and individual servers, with binary compatibility $M$, strictly positive real nominal arrival rates $\widetilde\lambda_i$, strictly positive service rates $\mu_j$, and equal total nominal demand and capacity. At load $\rho$, arrivals have rates $\rho\widetilde\lambda_i$. Rewards are omitted because they do not affect any delay or transition.
--
--   For a server set $A$, $U_A$ contains classes whose every compatible server lies in $A$, while $C_A$ contains classes with at least one compatible server in $A$. The definitions include their literal empty-set behavior. Slack is $\Delta_\rho(A)=\mu_A-\rho\widetilde\lambda_{U_A}$. The paper's flow network instantiates the general transportation definition. A residual edge is one positive in some saturated nominal flow, taking the union over all such flows. Neither stability nor complete-resource-pooling properties are assumptions of this model.
-- source:
--   Afèche, Caldentey and Gupta, On the Optimal Design of a Bipartite Matching Queueing System, Operations Research (catalog 2021), https://doi.org/10.1287/opre.2020.2027; acquired artifact dated November 3, 2019; citation_basis published; printed/PDF pp. 7–8, 11–14, (5)–(6), Definition 3

import Definitions.Def_BipartiteMatchingHT_Delay_Transportation

open scoped BigOperators
noncomputable section

namespace BipartiteMatchingHT.Delay

/-- Fixed positive real rates and arbitrary binary compatibility; rewards play
no role in the delay theorem. No stability or derived law is a field. -/
structure Model (n m : ℕ) where
  classes_pos : 0 < n
  servers_pos : 0 < m
  compatible : Fin n → Fin m → Bool
  nominal : Fin n → ℝ
  service : Fin m → ℝ
  nominal_pos : ∀ i, 0 < nominal i
  service_pos : ∀ j, 0 < service j
  balance : ∑ i, nominal i = ∑ j, service j

variable {n m : ℕ}

def onlyClasses (R : Fin n → Fin m → Prop) (A : Finset (Fin m)) : Finset (Fin n) := by
  classical
  exact Finset.univ.filter (fun i => ∀ j, R i j → j ∈ A)

def someClasses (R : Fin n → Fin m → Prop) (A : Finset (Fin m)) : Finset (Fin n) := by
  classical
  exact Finset.univ.filter (fun i => ∃ j ∈ A, R i j)

def Model.edge (D : Model n m) (i : Fin n) (j : Fin m) : Prop := D.compatible i j = true
def Model.demand (D : Model n m) (A : Finset (Fin n)) : ℝ := ∑ i ∈ A, D.nominal i
def Model.capacity (D : Model n m) (A : Finset (Fin m)) : ℝ := ∑ j ∈ A, D.service j
def Model.slack (D : Model n m) (ρ : ℝ) (A : Finset (Fin m)) : ℝ :=
  D.capacity A - ρ * D.demand (onlyClasses D.edge A)

def Model.network (D : Model n m) (ρ : ℝ) : Transportation (Fin n) (Fin m) :=
  ⟨D.edge, fun i => ρ * D.nominal i, D.service⟩

/-- The full union of positive supports of saturated nominal flows. -/
def Model.residual (D : Model n m) (i : Fin n) (j : Fin m) : Prop :=
  ∃ f : Fin n → Fin m → ℝ, (D.network 1).Saturated f ∧ 0 < f i j

end BipartiteMatchingHT.Delay



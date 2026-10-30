-- Prove2me | Definitions.Def_RobustMarkovAssort_Duality_GeneralPrograms
-- name    : RobustMarkovAssort_Duality_GeneralPrograms
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-29T23:16:23.183459+00:00
-- url     : https://prove2.me/theorems/3571a37e-00c7-4c73-9489-1b1eba137f24
-- title:
--   General separated programs and Assumptions 5–6
-- statement:
--   RowMin and WeightMin express attained minima over the specified parameter set. DualFeasible imposes v>=r and Av>=b. SeparatedDual replaces each row constraint with its attained row minimum; SeparatedBalance imposes v_i=r_i on S and v_i equal to its attained row minimum off S. Objective sets are formed from these explicit constraints. Assumptions 5 and 6 assert a common attained least value for the joint and separated programs and definedness of the inner weight minimum at every separated-feasible vector. This reads equivalence as equality of attained optimal values, not existence of a simultaneous minimizing scenario for every vector. A missing row minimum makes the corresponding relational constraint false, rather than supplying a numerical default. fixedMap takes the componentwise maximum of the price and a specified continuation-minimum vector; the theorem conclusions bind that vector to the actual minima.
-- source:
--   Désir, Goyal, Jiang, Xie and Zhang, Robust Assortment Optimization Under the Markov Chain Choice Model, Operations Research (2023), DOI 10.1287/opre.2022.2420; canonical artifact pp. 11–12 and 17–18, Assumptions 5–6 and equations (4), (13)–(16)

import Definitions.Def_RobustMarkovAssort_Duality_Extrema
import Definitions.Def_RobustMarkovAssort_Duality_GeneralModel

namespace RobustMarkovAssort.Duality

def RowMin {n : ℕ} {α : Type*} (G : GeneralModel n α)
    (v : Vec n) (i : Fin n) (z : ℝ) : Prop :=
  MinValue G.U (fun u => rowExpression G u v i) z

def WeightMin {n : ℕ} {α : Type*} (G : GeneralModel n α)
    (v : Vec n) (z : ℝ) : Prop :=
  MinValue G.U (fun u => ∑ i, G.lam u i * v i) z

def DualFeasible {n : ℕ} {α : Type*} (G : GeneralModel n α)
    (u : α) (v : Vec n) : Prop :=
  (∀ i, G.r i ≤ v i) ∧ (∀ i, G.b u i ≤ ∑ j, G.A u i j * v j)

def SeparatedDual {n : ℕ} {α : Type*} (G : GeneralModel n α)
    (v : Vec n) : Prop :=
  (∀ i, G.r i ≤ v i) ∧ (∀ i, ∃ t, RowMin G v i t ∧ t ≤ v i)

def SeparatedBalance {n : ℕ} {α : Type*} (G : GeneralModel n α)
    (S : Assortment n) (v : Vec n) : Prop :=
  (∀ i ∈ S, v i = G.r i) ∧ (∀ i, i ∉ S → RowMin G v i (v i))

def jointDualObjectives {n : ℕ} {α : Type*} (G : GeneralModel n α) : Set ℝ :=
  {z | ∃ u ∈ G.U, ∃ v, DualFeasible G u v ∧ z = ∑ i, G.lam u i * v i}

def separatedObjectives {n : ℕ} {α : Type*} (G : GeneralModel n α)
    (F : Vec n → Prop) : Set ℝ :=
  {z | ∃ v, F v ∧ WeightMin G v z}

def jointBalanceObjectives {n : ℕ} {α : Type*} (G : GeneralModel n α)
    (S : Assortment n) : Set ℝ :=
  {z | ∃ u ∈ G.U, ∃ v, Balance G.r (G.A u) (G.b u) S v ∧
    z = ∑ i, G.lam u i * v i}

def Assumption5 {n : ℕ} {α : Type*} (G : GeneralModel n α) : Prop :=
  (∀ v, SeparatedDual G v → ∃ w, WeightMin G v w) ∧
  ∃ z, IsLeast (jointDualObjectives G) z ∧
    IsLeast (separatedObjectives G (SeparatedDual G)) z

def Assumption6 {n : ℕ} {α : Type*} (G : GeneralModel n α) : Prop :=
  ∀ S : Assortment n,
    (∀ v, SeparatedBalance G S v → ∃ w, WeightMin G v w) ∧
    ∃ z, IsLeast (jointBalanceObjectives G S) z ∧
      IsLeast (separatedObjectives G (SeparatedBalance G S)) z

def fixedMap {n : ℕ} (r : Vec n) (m : Vec n → Vec n) (v : Vec n) : Vec n :=
  fun i => max (r i) (m v i)

end RobustMarkovAssort.Duality



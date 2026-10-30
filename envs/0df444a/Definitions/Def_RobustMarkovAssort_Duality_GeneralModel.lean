-- Prove2me | Definitions.Def_RobustMarkovAssort_Duality_GeneralModel
-- name    : RobustMarkovAssort_Duality_GeneralModel
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-29T23:15:40.646224+00:00
-- url     : https://prove2.me/theorems/01bbf5a5-732e-4889-9108-f98f1a761c67
-- title:
--   General assortment model, balance equations and continuation revenue
-- statement:
--   Products are Fin n, assortments are all finite subsets, prices are nonnegative, and the parameter set is nonempty with otherwise arbitrary real functions lambda, A and b. Assumption3 is strict positivity of arrival weights. Assumption4 requires positive diagonal entries, nonpositive off-diagonal entries and positive row sums. Balance imposes v_i=r_i on the offered set and (Av)_i=b_i off it. balanceValue is the inverse of the matrix with identity rows on the offered set and A rows elsewhere, applied to the matching right-hand side. Under Assumption4 this is the unique balance solution; the revenue is lambda dot v. tightSet includes every equality v_i=r_i. rowExpression is the sum over j different from i of -A_ij/A_ii times v_j, plus b_i/A_ii. Outside these standing hypotheses matrix inverse and division remain total Lean operations; no theorem interprets those outputs as revenue.
-- source:
--   Désir, Goyal, Jiang, Xie and Zhang, Robust Assortment Optimization Under the Markov Chain Choice Model, Operations Research (2023), DOI 10.1287/opre.2022.2420; canonical artifact pp. 6, 10–12, equation (3), Rev General, Assumptions 3–4 and equation (4)

import Mathlib

namespace RobustMarkovAssort.Duality

abbrev Vec (n : ℕ) := Fin n → ℝ
abbrev Mat (n : ℕ) := Matrix (Fin n) (Fin n) ℝ
abbrev Assortment (n : ℕ) := Finset (Fin n)

structure GeneralModel (n : ℕ) (α : Type*) where
  r : Vec n
  r_nonneg : ∀ i, 0 ≤ r i
  U : Set α
  U_nonempty : U.Nonempty
  lam : α → Vec n
  A : α → Mat n
  b : α → Vec n

def Assumption3 {n : ℕ} {α : Type*} (G : GeneralModel n α) : Prop :=
  ∀ u ∈ G.U, ∀ i, 0 < G.lam u i

def Assumption4 {n : ℕ} {α : Type*} (G : GeneralModel n α) : Prop :=
  ∀ u ∈ G.U, (∀ i, 0 < G.A u i i) ∧
    (∀ i j, i ≠ j → G.A u i j ≤ 0) ∧ (∀ i, 0 < ∑ j, G.A u i j)

def Balance {n : ℕ} (r : Vec n) (A : Mat n) (b : Vec n)
    (S : Assortment n) (v : Vec n) : Prop :=
  (∀ i ∈ S, v i = r i) ∧ (∀ i, i ∉ S → ∑ j, A i j * v j = b i)

def balanceMatrix {n : ℕ} (A : Mat n) (S : Assortment n) : Mat n :=
  fun i j => if i ∈ S then (if i = j then 1 else 0) else A i j

def balanceRHS {n : ℕ} (r b : Vec n) (S : Assortment n) : Vec n :=
  fun i => if i ∈ S then r i else b i

noncomputable def balanceValue {n : ℕ} (r : Vec n) (A : Mat n) (b : Vec n)
    (S : Assortment n) : Vec n :=
  (balanceMatrix A S)⁻¹.mulVec (balanceRHS r b S)

noncomputable def revenue {n : ℕ} {α : Type*} (G : GeneralModel n α)
    (S : Assortment n) (u : α) : ℝ :=
  ∑ i, G.lam u i * balanceValue G.r (G.A u) (G.b u) S i

noncomputable def tightSet {n : ℕ} (r v : Vec n) : Assortment n :=
  Finset.univ.filter (fun i => v i = r i)

noncomputable def rowExpression {n : ℕ} {α : Type*} (G : GeneralModel n α)
    (u : α) (v : Vec n) (i : Fin n) : ℝ :=
  (∑ j ∈ Finset.univ.erase i, (-G.A u i j / G.A u i i) * v j) +
    G.b u i / G.A u i i

end RobustMarkovAssort.Duality



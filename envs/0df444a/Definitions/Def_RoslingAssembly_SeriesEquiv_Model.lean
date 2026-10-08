-- Prove2me | Definitions.Def_RoslingAssembly_SeriesEquiv_Model
-- name    : RoslingAssembly_SeriesEquiv_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T15:44:41.53298+00:00
-- url     : https://prove2.me/theorems/959516de-044c-4578-be6c-8b628f77d0ed
-- title:
--   Assembly system data and equivalent series system
-- statement:
--   An assembly system has items $1,\ldots,N$ on a tree rooted at end item $1$. Each item $i>1$ has immediate successor $s(i)<i$, lead time $l_i$, and echelon holding coefficient $h_i$. The model also stores backlog cost $p$, installation cost $H_1$, discount factor $\alpha$, and the common demand law $\nu$.
--
--   $$M_i=l_i+\sum_{k\in A(i)}l_k,\qquad L_i=M_i-M_{i-1}.$$
--
--   The equivalent pure series system has successor $i-1$, lead time $L_i$, and holding coefficient $h_i\alpha^{l_i-L_i}$. It is built as another assembly model so its constraints and objective retain their usual meanings.
--
--   **Formalization Note** Items outside $1,\ldots,N$ are unused. The customer node $0$ is absorbing when the successors $A(i)$ are collected, so the unconstrained value $s(0)$ never enters $M_i$. The demand validity predicate requires a nonnegative law with density and finite positive mean.
-- source:
--   Rosling, Optimal Inventory Policies for Assembly Systems under Random Demands, Oper. Res. 37(4), 1989, pp. 566–568, §§1–2; p. 569, Theorem 2

import Mathlib

namespace RoslingAssembly.SeriesEquiv
open MeasureTheory

/-- Primitive data for Rosling's assembly system. Item indices are `1,...,N`,
and `succ 1 = 0` denotes the customer. -/
structure Model where
  N : ℕ
  succ : ℕ → ℕ
  lead : ℕ → ℕ
  h : ℕ → ℝ
  p : ℝ
  H1 : ℝ
  α : ℝ
  ν : MeasureTheory.Measure ℝ

namespace Model

/-- The successor map with the customer node `0` absorbing, so that the
unconstrained value `succ 0` is never consulted. -/
def succStop (S : Model) (j : ℕ) : ℕ :=
  if j = 0 then 0 else S.succ j

/-- All successors of item `i` in the rooted product tree: the items on the
path from `i` to the customer node `0`, excluding `i` itself. -/
def successors (S : Model) (i : ℕ) : Finset ℕ :=
  ((Finset.Icc 1 S.N).biUnion (fun n => {(S.succStop^[n]) i})) ∩ Finset.Icc 1 S.N

/-- Immediate predecessors of `i`, including the raw suppliers as leaves. -/
def predecessors (S : Model) (i : ℕ) : Finset ℕ :=
  (Finset.Icc 1 S.N).filter (fun k => S.succ k = i)

/-- Total lead time along the unique path from item `i` to the customer. -/
noncomputable def M (S : Model) (i : ℕ) : ℕ :=
  if i = 0 then 0 else S.lead i + ∑ k ∈ S.successors i, S.lead k

/-- The equivalent series lead time `L_i = M_i - M_(i-1)`. -/
noncomputable def L (S : Model) (i : ℕ) : ℕ := S.M i - S.M (i - 1)

/-- The paper's tree and lead-time indexing conventions. -/
def ValidTree (S : Model) : Prop :=
  1 ≤ S.N ∧ S.succ 1 = 0 ∧
    (∀ i ∈ Finset.Icc 2 S.N, 1 ≤ S.succ i ∧ S.succ i < i) ∧
    ∀ i ∈ Finset.Icc 1 S.N, S.M (i - 1) ≤ S.M i

/-- The iid nonnegative demand law has a density and strictly positive finite mean. -/
def ValidDemand (S : Model) : Prop :=
  S.ν (Set.Iio 0) = 0 ∧ S.ν ≪ volume ∧
    MeasureTheory.Integrable (fun x : ℝ => x) S.ν ∧
    0 < ∫ x, x ∂S.ν

/-- Rosling's Assumption on the echelon holding coefficients, equation following (5). -/
def Assumption (S : Model) : Prop :=
  (∀ i ∈ Finset.Icc 1 S.N, 0 < S.h i) ∧
    (∑ i ∈ Finset.Icc 1 S.N,
      S.h i * (S.α ^ S.M (S.succ i))⁻¹) < S.p + S.H1

/-- The pure series system specified by Theorem 2. Its constraints and costs are
obtained from the general assembly model, not imposed by this definition. -/
noncomputable def series (S : Model) : Model where
  N := S.N
  succ := fun i => i - 1
  lead := S.L
  h := fun i => S.h i * S.α ^ (S.lead i - S.L i)
  p := S.p
  H1 := S.H1
  α := S.α
  ν := S.ν

end Model
end RoslingAssembly.SeriesEquiv



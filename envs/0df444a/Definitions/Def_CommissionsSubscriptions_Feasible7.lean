-- Prove2me | Definitions.Def_CommissionsSubscriptions_Feasible7
-- name    : CommissionsSubscriptions_Feasible7
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T01:31:52.161484+00:00
-- url     : https://prove2.me/theorems/b2ce3099-8f65-48f6-92f2-615a174c1e37
-- title:
--   Feasible set of the relaxation (7)
-- statement:
--   A triple $(x,q^s,q^b)$ is **feasible in (7)** if
--   $$\sum_{i:(i,j)\in E}x_{ij}-q^b_j=0\ (7b),\qquad q^s_i-\sum_{j:(i,j)\in E}x_{ij}=0\ (7c),\qquad q^b_j\le b_j\ (7d),\qquad q^s_i\le s_i\ (7e),\qquad x_{ij}\ge0\ \text{on }E\ (7f).$$
--   These keep the flow-conservation part of the equilibrium conditions and the capacity bounds implied by (2a)–(2b), and drop prices and fees.
--
--   **Formalization Note** Only the entries of $x$ on $E$ are read.
-- source:
--   Birge, Candogan, Chen, Saban, Optimal Commissions and Subscriptions in Networked Markets, SSRN abstract 3259716 (version of 2019-09-13), (7b)–(7f), p. 12

import Mathlib
import Definitions.Def_CommissionsSubscriptions_Market

namespace CommissionsSubscriptions

/-- **Feasible set of the relaxation (7), constraints (7b)–(7f).**
Birge, Candogan, Chen, Saban, *Optimal Commissions and Subscriptions in Networked Markets*,
SSRN 3259716 (version of 2019-09-13), (7b)–(7f), p. 12:
* (7b) `Σ_{i:(i,j)∈E} x_{ij} − q^b_j = 0` for every `j ∈ B`;
* (7c) `q^s_i − Σ_{j:(i,j)∈E} x_{ij} = 0` for every `i ∈ S`;
* (7d) `q^b_j ≤ b_j`; (7e) `q^s_i ≤ s_i`; (7f) `x_{ij} ≥ 0` for `(i,j) ∈ E`.

**Formalization Note (Reading 6).** Only the entries of `x` on `E` are read. -/
def Feasible7 {S B : Type} [Fintype S] [Fintype B] [DecidableEq S] [DecidableEq B]
    (M : Market S B) (x : S → B → ℝ) (qs : S → ℝ) (qb : B → ℝ) : Prop :=
  (∀ j, ∑ i ∈ Finset.univ.filter (fun i => (i, j) ∈ M.E), x i j - qb j = 0) ∧
    (∀ i, qs i - ∑ j ∈ Finset.univ.filter (fun j => (i, j) ∈ M.E), x i j = 0) ∧
    (∀ j, qb j ≤ M.b j) ∧ (∀ i, qs i ≤ M.s i) ∧ (∀ e ∈ M.E, 0 ≤ x e.1 e.2)

end CommissionsSubscriptions



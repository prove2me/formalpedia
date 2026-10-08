-- Prove2me | Definitions.Def_SPHardness_OrderPolytope_Core
-- name    : SPHardness_OrderPolytope_Core
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T20:08:29.700652+00:00
-- url     : https://prove2.me/theorems/33b50ca4-ea94-4d64-be1b-fecdf4c51439
-- title:
--   §3, pp. 10–11 — finite-poset order polytope, volume, and linear-extension count
-- statement:
--   Let $P$ be a finite partially ordered set with $k=|P|$. Its **unit cube** is $C=[0,1]^P$, and its **order polytope** is
--
--   $$
--   O(P)=\{\xi\in C:\xi_i\le\xi_j\text{ whenever }i\le_P j\}.
--   $$
--
--   The **order-polytope volume** $V(P)$ is its Lebesgue volume. A **linear extension** is an ordering of the elements of $P$ compatible with its partial order, and $N(P)$ counts these orderings. These are the geometric and combinatorial objects used in Lemma 3 and Theorem 3.
--
--   **Formalization Note** The paper labels its elements $S=\{1,\ldots,k\}$; the general finite type $P$ represents the same objects up to relabeling. The count uses the published `FCP.Order.LinearExtensions` definition, which records an extension as an order-preserving bijection to the positions $0,\ldots,k-1$. The empty poset has a one-point zero-dimensional cube and one linear extension.
-- source:
--   Hanasusanto, Kuhn & Wiesemann, A comment on "computational complexity of stochastic programming problems", Optimization Online preprint 2015/03/4825 (version of October 6, 2015), p. 10, order-polytope definition and #LinearExtension instance; p. 11, compatible permutation. https://optimization-online.org/wp-content/uploads/2015/03/4825.pdf

import Mathlib
import Definitions.Def_FCP_LinearExtensions

namespace SPHardness.OrderPolytope

open MeasureTheory

/-- The unit cube for a finite coordinate set. -/
def cube (P : Type) [Fintype P] : Set (P → ℝ) :=
  Set.pi Set.univ (fun _ => Set.Icc (0 : ℝ) 1)

/-- The order polytope of a finite partially ordered set. -/
def orderPolytope (P : Type) [Fintype P] [PartialOrder P] : Set (P → ℝ) :=
  {ξ | ξ ∈ cube P ∧ ∀ i j : P, i ≤ j → ξ i ≤ ξ j}

/-- Lebesgue volume of the order polytope. -/
noncomputable def volOrder (P : Type) [Fintype P] [PartialOrder P] : ℝ :=
  (volume (orderPolytope P)).toReal

/-- Number of linear extensions of the finite poset. -/
noncomputable def numLinExt (P : Type) [Fintype P] [PartialOrder P] : ℕ :=
  (FCP.Order.LinearExtensions P).ncard

end SPHardness.OrderPolytope



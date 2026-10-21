-- Prove2me | Definitions.Def_ClearingUnique_Cycles_Model
-- name    : ClearingUnique_Cycles_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-20T05:50:08.063633+00:00
-- url     : https://prove2.me/theorems/f5c4c59e-3224-4c28-8910-1175db4c27e2
-- title:
--   Definitions 2.1–2.2 and §4 — clearing matrices, monotonicity, and liability cycles
-- statement:
--   For a network $N=(I,z,L,d)$, a payment matrix $P$ has nonnegative entries and a zero diagonal. The **asset value** and **equity** of agent $i$ are
--
--   $$
--   a_i(P)=z_i+\sum_jP_{ji},\qquad e_i(P)=a_i(P)-\sum_jP_{ij}.
--   $$
--
--   A row is feasible when it equals $d^i(E)$ for some $E\ge0$. A **clearing payment matrix** is feasible, has $e_i(P)\ge0$ for every agent, and has $e_i(P)=0$ whenever its row is strictly below the liability row $L_i$ in the coordinatewise order. This is Definition 2.2; it does not define clearing through a fixed-point equation.
--
--   For a positive claim $L_{ij}>0$, the payment-start threshold $\underline a_{ij}$ separates estates with zero and positive payment to $j$. Strict monotonicity requires $d^i_j(E)<d^i_j(E')$ throughout $0\le E<E'\le\bar L_i$; positive monotonicity requires it for $\underline a_{ij}\le E<E'\le\bar L_i$. Positive liability edges define strongly connected components $O(i)$; agent $i$ is cyclical when $|O(i)|\ge2$, and a component has no successors when no positive liability leaves it.
--
--   These definitions supply the common meaning of every theorem in the mission.
--
--   **Formalization Note** Matrices are functions $I\to I\to\mathbb R$ in the entrywise order. The threshold is the supremum of nonnegative estates where payment to $j$ is zero; it is used only for positive claims. Reachability uses finite positive-edge walks, which agree with the paper's distinct-vertex paths between different agents.
-- source:
--   Csóka & Herings, Uniqueness of Clearing Payment Matrices in Financial Networks, GSBE Research Memorandum RM/21/014 (Maastricht University, 8 Sep 2021; doi:10.26481/umagsb.2021014), pp. 6–8, 14 (PDF 8–10, 16), Definitions 2.1–2.2 and §4

import Mathlib
import Definitions.Def_ClearingUnique_Cycles_Network

namespace ClearingUnique.Cycles

variable {I : Type*} [Fintype I] [DecidableEq I]

/-- The paper's set 𝓜 of nonnegative payment matrices with zero diagonal. -/
def InM (P : I → I → ℝ) : Prop := (∀ i j, 0 ≤ P i j) ∧ ∀ i, P i i = 0

/-- Asset value aᵢ(P), including incoming payments. -/
def assetValue (N : FinNetwork I) (P : I → I → ℝ) (i : I) : ℝ :=
  N.z i + ∑ j, P j i

/-- Equity eᵢ(P) after outgoing payments. -/
def equity (N : FinNetwork I) (P : I → I → ℝ) (i : I) : ℝ :=
  assetValue N P i - ∑ j, P i j

/-- The strict coordinatewise order on rows, not on total liabilities. -/
def RowLt (P Q : I → I → ℝ) (i : I) : Prop :=
  (∀ j, P i j ≤ Q i j) ∧ ∃ j, P i j < Q i j

/-- Feasibility means each row is the output of its agent's division rule. -/
def Feasible (N : FinNetwork I) (P : I → I → ℝ) : Prop :=
  InM P ∧ ∀ i, ∃ E : ℝ, 0 ≤ E ∧ ∀ j, P i j = N.d i E j

/-- Definition 2.2: feasibility, limited liability, and priority of creditors. -/
def IsClearing (N : FinNetwork I) (P : I → I → ℝ) : Prop :=
  Feasible N P ∧ (∀ i, 0 ≤ equity N P i) ∧
    (∀ i, RowLt P N.L i → equity N P i = 0)

/-- The payment-start threshold a̲ᵢⱼ, used only when Lᵢⱼ > 0. -/
noncomputable def aLow (N : FinNetwork I) (i j : I) : ℝ :=
  sSup {E : ℝ | 0 ≤ E ∧ N.d i E j = 0}

/-- Definition 2.1, strict monotonicity up to total liabilities. -/
def StrictlyMonotonic (N : FinNetwork I) (i : I) : Prop :=
  ∀ j, 0 < N.L i j → ∀ E E' : ℝ,
    0 ≤ E → E < E' → E' ≤ N.Lbar i → N.d i E j < N.d i E' j

/-- Definition 2.1, positive monotonicity after the payment-start threshold. -/
def PositiveMonotonic (N : FinNetwork I) (i : I) : Prop :=
  ∀ j, 0 < N.L i j → ∀ E E' : ℝ,
    0 ≤ E → aLow N i j ≤ E → E < E' → E' ≤ N.Lbar i →
      N.d i E j < N.d i E' j

/-- Directed reachability along positive liabilities. -/
def FinNetwork.Reach (N : FinNetwork I) : I → I → Prop :=
  Relation.TransGen (fun i j => 0 < N.L i j)

/-- The strongly connected component O(i), including i itself. -/
noncomputable def FinNetwork.comp (N : FinNetwork I) (i : I) : Finset I :=
  by classical exact Finset.univ.filter (fun j => j = i ∨ (N.Reach i j ∧ N.Reach j i))

/-- A cyclical agent belongs to a component with at least two agents. -/
def FinNetwork.Cyclical (N : FinNetwork I) (i : I) : Prop :=
  2 ≤ (N.comp i).card

/-- A component has no successors when no positive liability leaves it. -/
def FinNetwork.NoSuccessors (N : FinNetwork I) (O : Finset I) : Prop :=
  ∀ a ∈ O, ∀ b, 0 < N.L a b → b ∈ O

end ClearingUnique.Cycles



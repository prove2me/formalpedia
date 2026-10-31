-- Prove2me | Definitions.Def_BipartiteMatchingHT_Delay_Components
-- name    : BipartiteMatchingHT_Delay_Components
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-30T19:12:28.963992+00:00
-- url     : https://prove2.me/theorems/6dbfda26-b8a3-4655-9c56-3bd3628e41be
-- title:
--   Residual components, reversed orders, and heavy-traffic weights
-- statement:
--   Complete-resource-pooling components are the actual connected components of the undirected residual bipartite graph. Their customer and server sets are the fibers of the quotient map. An arc from component $k$ to $h$ means some original compatible edge from its customers to the other's servers is absent in the residual graph; acyclicity is not assumed. Orders enumerate every component once and require the destination of each arc to occur before its origin. Every such enumeration appears once in the finite set of orders.
--
--   The server permutations induced by an order have consecutive whole-component server blocks, with all internal permutations allowed. Prefix sets, cumulative component capacities, and complete-block endpoint indices are defined explicitly. For order $\sigma$, write $c_{\sigma,r}=\sum_{\ell=1}^r\mu_{\mathcal S_{\sigma(\ell)}}$. Then $Q_\sigma=\prod_{r=1}^K c_{\sigma,r}^{-1}$, $w_{\sigma,k}=\sum_{r=\sigma^{-1}(k)}^K c_{\sigma,r}^{-1}$, and the proposed limiting formula is $\sum_\sigma Q_\sigma w_{\sigma,k}/\sum_\tau Q_\tau$. The internal factor $\theta_\sigma(\rho)$ sums, over all induced server permutations, the products of reciprocal original-matrix slacks at every non-boundary prefix. These are formula definitions, not definitions of stochastic waiting times or equilibrium probabilities. Empty products are one; positivity and existence of orders are theorem conclusions.
-- source:
--   Afèche, Caldentey and Gupta, On the Optimal Design of a Bipartite Matching Queueing System, Operations Research (catalog 2021), https://doi.org/10.1287/opre.2020.2027; acquired artifact dated November 3, 2019; citation_basis published; printed/PDF pp. 14–19, Definitions 4–7; pp. 45–46, (A.1)–(A.2)

import Definitions.Def_BipartiteMatchingHT_Delay_Primitives

open scoped BigOperators
noncomputable section

namespace BipartiteMatchingHT.Delay
variable {n m : ℕ}

def residualAdj (D : Model n m) : (Fin n ⊕ Fin m) → (Fin n ⊕ Fin m) → Prop
  | .inl i, .inr j => D.residual i j
  | .inr j, .inl i => D.residual i j
  | _, _ => False

def residualGraph (D : Model n m) : SimpleGraph (Fin n ⊕ Fin m) where
  Adj := residualAdj D
  symm := ⟨by intro a b; cases a <;> cases b <;> simp [residualAdj]⟩
  loopless := ⟨by intro a; cases a <;> simp [residualAdj]⟩

abbrev Component (D : Model n m) := (residualGraph D).ConnectedComponent

noncomputable instance componentFintype (D : Model n m) : Fintype (Component D) :=
  Fintype.ofFinite _

def customerComponent (D : Model n m) (i : Fin n) : Component D :=
  (residualGraph D).connectedComponentMk (.inl i)

def serverComponent (D : Model n m) (j : Fin m) : Component D :=
  (residualGraph D).connectedComponentMk (.inr j)

def componentClasses (D : Model n m) (k : Component D) : Finset (Fin n) := by
  classical
  exact Finset.univ.filter (fun i => customerComponent D i = k)

def componentServers (D : Model n m) (k : Component D) : Finset (Fin m) := by
  classical
  exact Finset.univ.filter (fun j => serverComponent D j = k)

/-- Definition 5, including every original edge absent from the residual graph.
Acyclicity, including exclusion of self loops, is a theorem. -/
def componentArc (D : Model n m) (k h : Component D) : Prop :=
  ∃ i ∈ componentClasses D k, ∃ j ∈ componentServers D h,
    D.edge i j ∧ ¬ D.residual i j

def componentCount (D : Model n m) : ℕ := Fintype.card (Component D)

/-- A listing of every component exactly once. Fin indices are zero-based. -/
abbrev ComponentOrder (D : Model n m) := Fin (componentCount D) ≃ Component D

def IsTopological (D : Model n m) (σ : ComponentOrder D) : Prop :=
  ∀ k h, componentArc D k h → σ.symm h < σ.symm k

def orders (D : Model n m) : Finset (ComponentOrder D) := by
  classical
  exact Finset.univ.filter (IsTopological D)

def prefixServers (D : Model n m) (σ : ComponentOrder D) (r : ℕ) : Finset (Fin m) := by
  classical
  exact Finset.univ.filter (fun j => (σ.symm (serverComponent D j)).val < r)

def prefixClasses (D : Model n m) (σ : ComponentOrder D) (r : ℕ) : Finset (Fin n) := by
  classical
  exact Finset.univ.filter (fun i => (σ.symm (customerComponent D i)).val < r)

def blockEnd (D : Model n m) (σ : ComponentOrder D) (r : ℕ) : ℕ :=
  ∑ a : Fin (componentCount D), if a.val < r then (componentServers D (σ a)).card else 0

def Induced (D : Model n m) (σ : ComponentOrder D) (s : Equiv.Perm (Fin m)) : Prop :=
  ∀ r : Fin (componentCount D), ∀ a : Fin m,
    blockEnd D σ r.val ≤ a.val → a.val < blockEnd D σ (r.val + 1) →
      s a ∈ componentServers D (σ r)

def inducedServers (D : Model n m) (σ : ComponentOrder D) : Finset (Equiv.Perm (Fin m)) := by
  classical
  exact Finset.univ.filter (Induced D σ)

def serverPrefix (s : Equiv.Perm (Fin m)) (r : ℕ) : Finset (Fin m) :=
  Finset.univ.filter (fun j => (s.symm j).val < r)

def serverSuffix (s : Equiv.Perm (Fin m)) (r : ℕ) : Finset (Fin m) :=
  Finset.univ.filter (fun j => r ≤ (s.symm j).val)

def orderCapacity (D : Model n m) (σ : ComponentOrder D) (r : ℕ) : ℝ :=
  ∑ a : Fin (componentCount D),
    if a.val < r then D.capacity (componentServers D (σ a)) else 0

def Q (D : Model n m) (σ : ComponentOrder D) : ℝ :=
  ∏ r : Fin (componentCount D), (orderCapacity D σ (r.val + 1))⁻¹

def totalQ (D : Model n m) : ℝ := ∑ σ ∈ orders D, Q D σ

def orderWait (D : Model n m) (σ : ComponentOrder D) (k : Component D) : ℝ :=
  ∑ r : Fin (componentCount D),
    if σ.symm k ≤ r then (orderCapacity D σ (r.val + 1))⁻¹ else 0

def limitingWait (D : Model n m) (k : Component D) : ℝ :=
  ∑ σ ∈ orders D, (Q D σ / totalQ D) * orderWait D σ k

def boundaries (D : Model n m) (σ : ComponentOrder D) : Finset ℕ :=
  Finset.univ.image (fun r : Fin (componentCount D) => blockEnd D σ (r.val + 1))

/-- Equation (A.2), including all within-component server permutations and
excluding exactly the complete-block boundary indices. -/
def theta (D : Model n m) (σ : ComponentOrder D) (ρ : ℝ) : ℝ :=
  ∑ s ∈ inducedServers D σ,
    ∏ r ∈ (Finset.Icc 1 m \ boundaries D σ), (D.slack ρ (serverPrefix s r))⁻¹

end BipartiteMatchingHT.Delay



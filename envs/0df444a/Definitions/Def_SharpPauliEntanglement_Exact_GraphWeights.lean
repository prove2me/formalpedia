-- Prove2me | Definitions.Def_SharpPauliEntanglement_Exact_GraphWeights
-- name    : SharpPauliEntanglement_Exact_GraphWeights
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T08:52:27.4457+00:00
-- url     : https://prove2.me/theorems/0604caa7-2c8d-4b9f-96e8-e2f255791dad
-- title:
--   Exact threshold, overlap graphs, red weights, and component polynomials
-- statement:
--   For an integer degree bound $\Delta\ge2$, put $b=\Delta-1$ and define the exact source parameters
--
--   $$x=\sqrt{b^2+1}-b,\quad t=x\left(\frac{1-x}{1+x}\right)^b,\quad z=\operatorname{arctanh}t,\quad \alpha=1+\frac{x}{2},\quad \eta=\frac13+\frac{x}{2},\quad u=\frac{t}{(1-x)^b}.$$
--
--   The term-overlap graph $G$ joins distinct Hamiltonian labels whose nonidentity supports intersect. The anticommutation graph $A$ joins anticommuting pairs. Connected sets are nonempty connected induced vertex sets; components include isolated selected vertices. With $\mathcal C(A[U])$ the components on $U$, set
--
--   $$w_A(U)=\prod_{C\in\mathcal C(A[U]),\ |C|\ge2}\eta\alpha^{|C|-1},\qquad Q_{G,A,S}(s)=\sum_{U\subseteq S}(-1)^{|\mathcal C(G[U])|}s^{|U|}w_A(U).$$
--
--   The unweighted component polynomial omits $w_A(U)$. The connected sum through $v$ sums $u^{|U|}w_A(U)$ over connected $U\subseteq S$ containing $v$. Empty products are one, so each polynomial at $S=\varnothing$ is one. These are graph polynomials, distinct from the physical partition function.
--
--   This layer fixes the parameters once for the original degree bound, including on residual graphs. Components are computed from the graph rather than supplied as certified data.
--
--   **Formalization Note** Finite components are enumerated as nonempty connected subsets with no outgoing edge inside $U$. All graph sums are finite. The radical defines the exact source constant; it is not a numerical approximation or an unbounded real supremum.
-- source:
--   Bobak T. Kiani, Sharp universal death of entanglement threshold for Pauli Hamiltonians, STOC 2027 submission #159 (October 2026), pp. 2–3, 8, 10–14, Eqs. (1.2), (1.4), (2.4)–(2.5), (3.7), (3.9), (3.20)–(3.24)

import Definitions.Def_SharpPauliEntanglement_Exact_PauliModel

set_option autoImplicit false
noncomputable section

attribute [local instance] Classical.decEq Classical.propDecidable
open scoped BigOperators
namespace SharpPauliEntanglement.Exact

/-- Eqs. (1.2), (1.4), (2.4), (2.5); all uses of the threshold assume Δ ≥ 2. -/
def criticalX (Δ : ℕ) : ℝ := Real.sqrt (((Δ - 1 : ℕ) : ℝ) ^ 2 + 1) - (Δ - 1 : ℕ)
def criticalT (Δ : ℕ) : ℝ := criticalX Δ * ((1 - criticalX Δ) / (1 + criticalX Δ)) ^ (Δ - 1)
def criticalZ (Δ : ℕ) : ℝ := Real.artanh (criticalT Δ)
def alpha (Δ : ℕ) : ℝ := 1 + criticalX Δ / 2
def eta (Δ : ℕ) : ℝ := 1 / 3 + criticalX Δ / 2
def treeActivity (Δ : ℕ) : ℝ := criticalT Δ / (1 - criticalX Δ) ^ (Δ - 1)

/-- Nonempty connected induced vertex set. -/
def ConnectedSet {V : Type} (G : SimpleGraph V) (U : Finset V) : Prop :=
  U.Nonempty ∧ (G.induce (U : Set V)).Preconnected

/-- Finite components of the induced graph, including singletons and excluding ∅. -/
def components {V : Type} [DecidableEq V] (G : SimpleGraph V) (U : Finset V) :
    Finset (Finset V) := by
  classical
  exact U.powerset.filter (fun C => ConnectedSet G C ∧
    ∀ i ∈ C, ∀ j ∈ U, G.Adj i j → j ∈ C)

def degree {V : Type} [Fintype V] (G : SimpleGraph V) (v : V) : ℕ := by
  classical
  exact (Finset.univ.filter (G.Adj v)).card

def DegreeBound {V : Type} [Fintype V] (G : SimpleGraph V) (Δ : ℕ) : Prop :=
  ∀ v, degree G v ≤ Δ

def overlapGraph {Q V : Type} [Fintype Q] (H : PauliHamiltonian Q V) : SimpleGraph V where
  Adj i j := i ≠ j ∧ ¬ Disjoint (pauliSupport (H.term i)) (pauliSupport (H.term j))
  symm := ⟨by intro i j h; exact ⟨h.1.symm, fun h' => h.2 h'.symm⟩⟩
  loopless := ⟨by intro i h; exact h.1 rfl⟩

def antiGraph {Q V : Type} [Fintype Q] (H : PauliHamiltonian Q V) : SimpleGraph V where
  Adj i j := i ≠ j ∧ pauliOp (H.term i) * pauliOp (H.term j) =
    -(pauliOp (H.term j) * pauliOp (H.term i))
  symm := ⟨by
    intro i j h
    refine ⟨h.1.symm, ?_⟩
    have := congrArg Neg.neg h.2
    simpa only [neg_neg] using this.symm⟩
  loopless := ⟨by intro i h; exact h.1 rfl⟩

/-- Product of ηα^(|C|-1) over nonsingleton red components, Eqs. (3.9), (3.21). -/
def redWeight {V : Type} [DecidableEq V] (A : SimpleGraph V) (Δ : ℕ) (U : Finset V) : ℝ :=
  ∏ C ∈ components A U, if C.card ≥ 2 then eta Δ * alpha Δ ^ (C.card - 1) else 1

/-- Eq. (3.20), also on residual vertex sets with the original Δ parameters. -/
def weightedPolynomial {V : Type} [DecidableEq V] (G A : SimpleGraph V)
    (Δ : ℕ) (S : Finset V) (s : ℝ) : ℝ :=
  ∑ U ∈ S.powerset, (-1 : ℝ) ^ (components G U).card * s ^ U.card * redWeight A Δ U

/-- Eq. (3.7); this is not the physical partition function. -/
def componentPolynomial {V : Type} [DecidableEq V]
    (G : SimpleGraph V) (S : Finset V) (s : ℝ) : ℝ :=
  ∑ U ∈ S.powerset, (-1 : ℝ) ^ (components G U).card * s ^ U.card

def connectedSum {V : Type} [DecidableEq V] (G A : SimpleGraph V) (Δ : ℕ)
    (S : Finset V) (v : V) (u : ℝ) : ℝ := by
  classical
  exact ∑ U ∈ S.powerset.filter (fun U => v ∈ U ∧ ConnectedSet G U),
    u ^ U.card * redWeight A Δ U

end SharpPauliEntanglement.Exact



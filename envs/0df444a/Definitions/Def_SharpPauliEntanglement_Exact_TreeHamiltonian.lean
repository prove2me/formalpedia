-- Prove2me | Definitions.Def_SharpPauliEntanglement_Exact_TreeHamiltonian
-- name    : SharpPauliEntanglement_Exact_TreeHamiltonian
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T08:57:21.767982+00:00
-- url     : https://prove2.me/theorems/b34168c2-5160-4b30-99d7-f9949d18bd15
-- title:
--   Two qubits per edge and finite complete rooted trees
-- statement:
--   Let $T$ be a finite tree with at least two vertices, orient each edge arbitrarily, and put two physical qubits $A_e,B_e$ on every edge. Define actual Pauli words and matrices by
--
--   $$Q_v=\prod_{e\text{ outgoing from }v}X_{A_e}X_{B_e}\prod_{e\text{ incoming to }v}Z_{A_e}Z_{B_e},\qquad H_T=-\sum_vQ_v.$$
--
--   There are $N=2|E(T)|$ qubits. Partial transpose on the $A$ register swaps the computational-basis row and column indices only on $A_e$, leaving $B_e$ indices in place. A complete rooted $b$-ary tree of height $h$ has vertices all words over $b$ letters of lengths at most $h$, rooted at the empty word; edges join words to their one-letter extensions.
--
--   These computed constructions supply the finite sharpness witnesses. No commuting, independence, eigenvector, or entanglement assertion is part of the definitions.
--
--   **Formalization Note** Each undirected edge has one representative with smaller endpoint first, while a Boolean independently chooses its orientation. The qubit type is edge-times-Boolean; false labels $A$ and true labels $B$. The two-qubit placement is essential: ordinary graph-state generators on vertices would have a different overlap graph.
-- source:
--   Bobak T. Kiani, Sharp universal death of entanglement threshold for Pauli Hamiltonians, STOC 2027 submission #159 (October 2026), pp. 18–20, Eq. (4.1), partial transpose before Eq. (4.3), complete trees in Lemma 4.2

import Definitions.Def_SharpPauliEntanglement_Exact_Polymers

set_option autoImplicit false
noncomputable section

attribute [local instance] Classical.decEq Classical.propDecidable
open scoped BigOperators
namespace SharpPauliEntanglement.Exact

/-- One representative per undirected edge; the Boolean orientation remains arbitrary. -/
abbrev TreeEdge {m : ℕ} (T : SimpleGraph (Fin m)) :=
  {e : Fin m × Fin m // T.Adj e.1 e.2 ∧ e.1 < e.2}
abbrev TreeQubit {m : ℕ} (T : SimpleGraph (Fin m)) := TreeEdge T × Bool

/-- Eq. (4.1). Both qubits on an outgoing edge carry X; both on an incoming edge Z. -/
def treeWord {m : ℕ} (T : SimpleGraph (Fin m)) (orientation : TreeEdge T → Bool)
    (v : Fin m) : PauliWord (TreeQubit T) := fun q =>
  let e := q.1
  let tail := if orientation e then e.val.1 else e.val.2
  let head := if orientation e then e.val.2 else e.val.1
  if v = tail then 1 else if v = head then 3 else 0

def treeGenerator {m : ℕ} (T : SimpleGraph (Fin m)) (orientation : TreeEdge T → Bool)
    (v : Fin m) : Op (TreeQubit T) := pauliOp (treeWord T orientation v)

def treeHamiltonian {m : ℕ} (T : SimpleGraph (Fin m))
    (orientation : TreeEdge T → Bool) : Op (TreeQubit T) :=
  -∑ v, treeGenerator T orientation v

/-- Computational-basis partial transpose on the A qubits (Boolean tag false).
The B indices retain their original row and column, p. 19. -/
def partialTransposeA {m : ℕ} (T : SimpleGraph (Fin m)) (M : Op (TreeQubit T)) :
    Op (TreeQubit T) := fun a b =>
  M (fun q => if q.2 = false then b q else a q)
    (fun q => if q.2 = false then a q else b q)

/-- Vertices of the finite complete rooted b-ary tree of height h are words of length ≤ h. -/
def completeTreeVertices (b h : ℕ) : Finset (List (Fin b)) :=
  (Finset.range (h + 1)).biUnion (fun k =>
    (Finset.univ : Finset (Fin k → Fin b)).image List.ofFn)

/-- Edges join a word to any one-letter extension; the empty word is the root. -/
def completeTreeGraph (b : ℕ) : SimpleGraph (List (Fin b)) where
  Adj p q := p ≠ q ∧ ((∃ a, q = p ++ [a]) ∨ (∃ a, p = q ++ [a]))
  symm := ⟨by intro p q h; exact ⟨h.1.symm, h.2.symm⟩⟩
  loopless := ⟨by intro p h; exact h.1 rfl⟩

end SharpPauliEntanglement.Exact



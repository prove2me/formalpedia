-- Prove2me | Definitions.Def_MITMSynthesis_depthOneSet
-- name    : MITMSynthesis_depthOneSet
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-29T18:02:23.640288+00:00
-- url     : https://prove2.me/theorems/c9a052fb-1caa-4a66-9b28-8c32572634c1
-- title:
--   Placed gates, depth-one layers and the set $V_{n,\mathcal G}$
-- statement:
--   Fix $n$ qubits and an instruction set $\mathcal G$.
--
--   1. A **placed gate** is a gate $g$ of arity $k$ together with an ordered choice of $k$ distinct qubits $\iota(1), \dots, \iota(k)$ among the $n$. Its $2^n \times 2^n$ matrix is $g$ acting on the chosen qubits tensored with the identity on the others: for bit strings $x, y \in \{0,1\}^n$,
--   $$
--   (g \otimes I)[x,y] = \begin{cases} g[x\circ\iota,\, y\circ\iota] & \text{if } x_j = y_j \text{ for every qubit } j \notin \iota, \\ 0 & \text{otherwise.}\end{cases}
--   $$
--   2. A **layer** (depth-one circuit) over $\mathcal G$ is a non-empty list of placed gates, all from $\mathcal G$, acting on pairwise disjoint sets of qubits. Its unitary is the product of the matrices of its placed gates.
--   3. $V_{n,\mathcal G}$ is the set of unitaries of all layers over $\mathcal G$:
--   $$
--   V_{n,\mathcal G} = \{\, \text{unitary of } L \;:\; L \text{ a layer over } \mathcal G \,\}.
--   $$
--   4. A **layer enumeration** of $V_{n,\mathcal G}$ is a list of pairs (layer $L$, matrix $M$) such that each $L$ is a layer over $\mathcal G$ with unitary $M$, the matrices are pairwise distinct, and every element of $V_{n,\mathcal G}$ occurs. It is the input format of MITM-factor: one layer per element of $V_{n,\mathcal G}$.
--
--   $V_{n,\mathcal G}$ is the set from which the meet-in-the-middle algorithm builds all circuits; depth-$m$ circuits are products of $m$ of its elements.
--
--   **Formalization Note** `Placement n` stores the gate and an embedding `Fin k ↪ Fin n`; `Placement.unitary` is the explicit formula above, so no Kronecker reindexing is used. `IsLayer`, `layerUnitary`, `depthOneSet` and `IsLayerEnumeration` are the four notions above. Since the placed gates of a layer act on disjoint qubits they commute, so the order of the list does not change the unitary.
-- source:
--   Amy, Maslov, Mosca, Roetteler, A meet-in-the-middle algorithm for fast synthesis of depth-optimal quantum circuits, arXiv:1206.0758v3, §2, p. 4 ("We may combine gates from an instruction set, each acting on different qubits, to construct circuits of depth one over n qubits ... we define V_{n,G}, the set of all unitaries corresponding to depth one n-qubit circuits over the instruction set G")

import Mathlib
import Definitions.Def_MITMSynthesis_Gate

namespace MITMSynthesis

/-- A gate placed on an ordered, injective choice of `g.arity` of the `n` qubits. -/
structure Placement (n : ℕ) where
  /-- the gate -/
  gate : Gate
  /-- the qubits it acts on, in order: qubit `j` of the gate is wire `qubits j` -/
  qubits : Fin gate.arity ↪ Fin n

open Classical in
/-- The `2^n × 2^n` matrix of a placed gate: the gate on the chosen qubits tensored with the
identity on the remaining qubits,
`(g ⊗ I)[x, y] = g[x|_ι, y|_ι]` if `x` and `y` agree off the range of `ι`, and `0` otherwise. -/
noncomputable def Placement.unitary {n : ℕ} (p : Placement n) : Matrix (Q n) (Q n) ℂ :=
  fun x y =>
    if (∀ j, j ∉ Set.range p.qubits → x j = y j) then
      (p.gate.mat : Matrix (Q p.gate.arity) (Q p.gate.arity) ℂ) (x ∘ p.qubits) (y ∘ p.qubits)
    else 0

/-- **A depth-one circuit (layer) over `G`.** A non-empty list of placed gates, all from `G`,
acting on pairwise disjoint sets of qubits. -/
def IsLayer {n : ℕ} (G : Set Gate) (L : List (Placement n)) : Prop :=
  L ≠ [] ∧ (∀ p ∈ L, p.gate ∈ G) ∧
    L.Pairwise (fun p q => Disjoint (Set.range p.qubits) (Set.range q.qubits))

/-- The unitary of a layer: the product of its placed gates (they commute, acting on disjoint
qubits). -/
noncomputable def layerUnitary {n : ℕ} (L : List (Placement n)) : Matrix (Q n) (Q n) ℂ :=
  (L.map Placement.unitary).prod

/-- **`V_{n,G}`**, arXiv:1206.0758v3, §2, p. 4: "the set of all unitaries corresponding to depth
one n-qubit circuits over the instruction set G". -/
def depthOneSet (n : ℕ) (G : Set Gate) : Set (Matrix (Q n) (Q n) ℂ) :=
  {M | ∃ L : List (Placement n), IsLayer G L ∧ layerUnitary L = M}

/-- The input format of MITM-factor: a list of pairs (layer, its unitary) enumerating `V_{n,G}`
with exactly one layer per unitary. Every label is a layer over `G` whose unitary is the paired
matrix, the matrices are pairwise distinct, and every element of `V_{n,G}` occurs. -/
def IsLayerEnumeration {n : ℕ} (G : Set Gate)
    (vs : List (List (Placement n) × Matrix (Q n) (Q n) ℂ)) : Prop :=
  (∀ p ∈ vs, IsLayer G p.1 ∧ layerUnitary p.1 = p.2) ∧ (vs.map Prod.snd).Nodup ∧
    ∀ M ∈ depthOneSet n G, ∃ p ∈ vs, p.2 = M

end MITMSynthesis



-- Prove2me | Definitions.Def_QuantumPRC_graphUnitary
-- name    : QuantumPRC_graphUnitary
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T11:34:22.566341+00:00
-- url     : https://prove2.me/theorems/23752ba3-d712-4906-8c3c-fae66dd4ee68
-- title:
--   CWS encoding unitary $U_G$ (Definition 3.14), $q_G(u)$ and $Au$ over $\mathbb F_2$
-- statement:
--   Let $G=([n],E)$ be a simple graph with adjacency matrix $A$ over $\mathbb F_2$ ($A_{i,j}=1$ iff $\{i,j\}\in E$). The **CWS encoding unitary** is
--
--   $$
--   U_G:=\Big(\prod_{\{i,j\}\in E}\mathrm{CZ}_{ij}\Big)H^{\otimes n},
--   $$
--
--   where $\mathrm{CZ}_{ij}|x\rangle=(-1)^{x_ix_j}|x\rangle$ and $H^{\otimes n}$ has entries $2^{-n/2}(-1)^{x\cdot y}$. Further, $q_G(u):=\sum_{\{i,j\}\in E}u_iu_j$ (Lemma 3.15) and $(Au)_i=\bigoplus_{j:\{i,j\}\in E}u_j$.
--
--   $U_G$ is the graph-state layer of the PRIC encoder (Construction 7.2); Lemma 3.15 describes how it conjugates Pauli errors.
--
--   **Formalization Note** A simple graph on $[n]$ is a `SimpleGraph (Fin n)`. The $\mathrm{CZ}$ gates are diagonal and commute; the product runs over the edges in lexicographic order.
-- source:
--   Hsieh, Yamada, Quantum Pseudorandom Error-Correcting Codes, arXiv:2609.38986 (version of October 29, 2026, sha256 6901b59d1cbcf0183f98f2951ab17c9baae4e341e5b2a3c767d1ae93e77976db), Definitions 3.11–3.12, p.18; Definition 3.14, p.19; Lemma 3.15, Eq. (28), p.19

import Mathlib
import Definitions.Def_QuantumPRC_pauliXZ

open Matrix

namespace QuantumPRC

/-- The edges `{i, j}` of a simple graph on `[n]`, each listed once as `(i, j)` with `i < j`, in
lexicographic order. -/
def edgeList {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] : List (Fin n × Fin n) :=
  (List.finRange n).flatMap fun i =>
    ((List.finRange n).filter fun j => decide (i < j ∧ G.Adj i j)).map fun j => (i, j)

/-- The controlled-`Z` gate `CZ_{ij}` on qubits `i, j` of `n` qubits: `|x⟩ ↦ (−1)^{x_i x_j} |x⟩`. -/
def czGate {n : ℕ} (i j : Fin n) : Matrix (Bits n) (Bits n) ℂ :=
  Matrix.diagonal fun x => if x i = true ∧ x j = true then -1 else 1

/-- `H^{⊗n}`: the entry at `(y, x)` is `2^{-n/2} (−1)^{x·y}`. -/
noncomputable def hadamardAll (n : ℕ) : Matrix (Bits n) (Bits n) ℂ :=
  fun y x => (if dotB x y then -1 else 1) / (Real.sqrt 2 : ℂ) ^ n

/-- **CWS encoding unitary**, Definition 3.14. Hsieh, Yamada, arXiv:2609.38986 (sha256 6901b59d…),
p.19: "Let `G = ([n], E)` be a simple graph. We define the unitary `U_G := (∏_{{i,j}∈E} CZ_{ij}) H^{⊗n}`,
where `H` is the Hadamard gate and `CZ_{ij}` is the controlled-`Z` gate on qubits `i` and `j`."

**Formalization Note.** A simple graph on `[n]` (Definition 3.11) is a `SimpleGraph (Fin n)`.
The `CZ` gates are diagonal and commute; the product is taken over `edgeList G`. -/
noncomputable def graphUnitary {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] :
    Matrix (Bits n) (Bits n) ℂ :=
  ((edgeList G).map fun e => czGate e.1 e.2).prod * hadamardAll n

/-- `q_G(u) := Σ_{{i,j}∈E} u_i u_j` (Lemma 3.15, Eq. (28), p.19). -/
def qG {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (u : Bits n) : ℕ :=
  ((edgeList G).filter fun e => u e.1 && u e.2).length

/-- `Au` over `𝔽₂` for the adjacency matrix `A` of `G` (Definition 3.12, p.18: `A_{i,j} = 1` iff
`{i, j} ∈ E`): `(Au)_i = ⊕_{j : {i,j}∈E} u_j`. -/
def adjMul {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (u : Bits n) : Bits n :=
  fun i => decide (Odd (Finset.univ.filter fun j => G.Adj i j ∧ u j = true).card)

end QuantumPRC



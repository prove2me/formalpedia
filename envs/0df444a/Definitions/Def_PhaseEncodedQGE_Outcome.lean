-- Prove2me | Definitions.Def_PhaseEncodedQGE_Outcome
-- name    : PhaseEncodedQGE_Outcome
-- status  : Definition
-- author  : @iris
-- created : 2026-11-12T06:45:33.411725+00:00
-- url     : https://prove2.me/theorems/013f766f-3c7e-4076-bb6f-1dd56e793145
-- title:
--   Outcomes $x\in\{0,1\}^n$, spins $z_v=(-1)^{x_v}$, defect sets and bit flips
-- statement:
--   Number the vertices of a graph on $n$ vertices $0,\dots,n-1$ and identify vertex $v$ with qubit $v$. A **computational-basis outcome** is a bit string $x\in\{0,1\}^n$.
--
--   1. The **spin** of vertex $v$ in $x$ is $z_v=(-1)^{x_v}$: $z_v=+1$ when $x_v=0$ and $z_v=-1$ when $x_v=1$.
--   2. The **defect set** of $x$ is the set of its zero bits,
--   $$D(x)=\{\,j : x_j=0\,\},$$
--   and $\ell=|D(x)|$ is its **defect count**.
--   3. For a vertex $i$, $x\oplus e_i$ is the outcome $x$ with bit $i$ flipped.
--
--   These are the combinatorial coordinates in which every first-order statement of the mission is written: the defects of $x$ are the vertices whose spin is $+1$.
--
--   **Formalization Note** An outcome is an element of the platform's published index set `QAlgorithms.Qubits n` $=(\mathrm{Fin}\,n\to\mathrm{Bool})$ with `true` the bit $1$; spins are integers. Because vertex $v$ is qubit $v$, the paper's little-endian bit order only fixes how outcomes are printed.
-- source:
--   Miller, Lee, Structural Accessibility in Phase-Encoded Quantum Graph Embeddings, STOC 2027 submission (build 2026-11-03, sha256 f1132658…7c51), §2, p.4 (PDF p.5), eq. (1) and 'The cut phase'; §2, p.5 (PDF p.6), 'Defect layers and blocks'; §3.1, p.6 (PDF p.7)

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Basic
set_option autoImplicit false

namespace PhaseEncodedQGE

/-- Computational-basis outcomes of `n` qubits, `x ∈ {0,1}ⁿ` (Miller, Lee, *Structural Accessibility
in Phase-Encoded Quantum Graph Embeddings*, STOC 2027 submission (build 2026-11-03), §2, p.4, eq. (1)).

**Formalization Note** An outcome is an element of the platform's computational-basis index set
`QAlgorithms.Qubits n = Fin n → Bool`; `true` is the bit `1` and `false` the bit `0`. Vertex `v` of
the graph is qubit `v`, so the paper's little-endian bit order only fixes how outcomes are printed
and plays no role here (no outcome is ever converted to an integer). -/
abbrev Outcome (n : ℕ) := QAlgorithms.Qubits n

/-- The spin `z_v = (−1)^{x_v}` of vertex `v` in the outcome `x` (§2, p.4, "The cut phase"):
`+1` for the bit `0` and `−1` for the bit `1`. -/
def spin {n : ℕ} (x : Outcome n) (v : Fin n) : ℤ := if x v then (-1 : ℤ) else 1

/-- The defect set `D(x) = {j : x_j = 0}` of an outcome: its zero bits (§2, p.5, "Defect layers and
blocks"). Its cardinality `ℓ = |D(x)|` is the defect count. -/
def defects {n : ℕ} (x : Outcome n) : Finset (Fin n) := Finset.univ.filter (fun j => x j = false)

/-- The outcome `x ⊕ e_i`: `x` with bit `i` flipped (§3.1, p.6). -/
def flip {n : ℕ} (x : Outcome n) (i : Fin n) : Outcome n := Function.update x i (!x i)

end PhaseEncodedQGE



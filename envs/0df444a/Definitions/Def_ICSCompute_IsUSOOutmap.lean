-- Prove2me | Definitions.Def_ICSCompute_IsUSOOutmap
-- name    : ICSCompute_IsUSOOutmap
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T21:45:20.62484+00:00
-- url     : https://prove2.me/theorems/330e78a3-a997-4369-a948-0e97d3b27c7a
-- title:
--   Unique-sink orientation outmaps of the $n$-cube and conditions (6.1), (6.2)
-- statement:
--   An orientation of the $n$-dimensional cube $\{0,1\}^n$ is represented by its **outmap** $s:\{0,1\}^n\to\{0,1\}^n$: $s_i(x) = 1$ if the edge between $x$ and $x\oplus e_i$ points away from $x$, and $s_i(x) = 0$ otherwise; in particular $s_i(x)\neq s_i(x\oplus e_i)$ for all $x, i$. A **face** fixes a subset $F\subseteq[n]$ of coordinates to specified values; a **sink** of a face is a vertex of the face with $s_i(x) = 0$ for every free coordinate $i\notin F$. The orientation is a **unique-sink orientation (USO)** if every face has exactly one sink.
--
--   The module also names the two pairwise conditions of Lemma 6.1:
--   $$(6.1)\quad x\neq x' \implies \exists i:\ x_i\neq x'_i \text{ and } s_i(x)\neq s_i(x'),\qquad (6.2)\quad x\neq x' \implies \exists i:\ x_i\neq x'_i \text{ and } h_i(x) = h_i(x'),$$
--   and bitwise XOR $x\oplus y$.
--
--   USO is the computational problem solved by the goal: given a circuit for $s$, find the global sink $z$, $s(z) = 0^n$.
--
--   **Formalization Note** Bits are `Bool`, coordinates `Fin n`. A face is given by a `Finset` $F$ and a string $c$ whose values on $F$ are the fixed values; all faces are quantified, including the whole cube and single vertices.
-- source:
--   Shmueli, What Can Be Computed with Indefinite Causal Structure?, arXiv:2610.40573 (version of 2026-11-03, sha256 d3e36399…b606), Definition 6.1, p.31; Lemma 6.1, p.31 (PDF p.33)

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Basic

namespace ICSCompute

open QAlgorithms

/-- `x ⊕ eᵢ`: the vertex adjacent to `x` along coordinate `i` (Definition 6.1, p.31). -/
def flipBit {n : ℕ} (x : Qubits n) (i : Fin n) : Qubits n :=
  Function.update x i (!x i)

/-- Bitwise XOR `x ⊕ y` of two bit strings (§3, p.14). -/
def xorQ {n : ℕ} (x y : Qubits n) : Qubits n :=
  fun i => xor (x i) (y i)

/-- **USO outmap** (Shmueli, *What Can Be Computed with Indefinite Causal Structure?*,
arXiv:2610.40573, version of 2026-11-03, sha256 d3e36399…b606, Definition 6.1, p.31
(PDF p.33)).

`s : {0,1}ⁿ → {0,1}ⁿ` is the outmap of an orientation of the `n`-cube (`sᵢ(x) = 1` iff the edge
between `x` and `x ⊕ eᵢ` points away from `x`), so `sᵢ(x) ≠ sᵢ(x ⊕ eᵢ)` for every `x` and `i`;
and the orientation is a unique-sink orientation: every face (a subset `F ⊆ [n]` of coordinates
fixed to specified values) has exactly one sink, a vertex of the face with no outgoing edge along
any free coordinate (`sᵢ(x) = 0` for every `i ∉ F`).

**Formalization Note** Bits are `Bool` (`false` = 0) and coordinates `Fin n` (the paper's
`[n]` shifted by one). A face is given by `F : Finset (Fin n)` and a string `c` whose values on
`F` are the fixed values (its other values are ignored). All faces are quantified, including the
whole cube (`F = ∅`) and single vertices (`F = univ`). -/
def IsUSOOutmap {n : ℕ} (s : Qubits n → Qubits n) : Prop :=
  (∀ (x : Qubits n) (i : Fin n), s x i ≠ s (flipBit x i) i) ∧
    ∀ (F : Finset (Fin n)) (c : Qubits n),
      ∃! x : Qubits n, (∀ i ∈ F, x i = c i) ∧ ∀ i ∉ F, s x i = false

/-- **Condition (6.1)** (Shmueli, arXiv:2610.40573, Lemma 6.1, p.31 (PDF p.33)):
`x ≠ x′ ⟹ ∃ i ∈ [n] : xᵢ ≠ x′ᵢ and sᵢ(x) ≠ sᵢ(x′)`. -/
def Eq61 {n : ℕ} (s : Qubits n → Qubits n) : Prop :=
  ∀ x x' : Qubits n, x ≠ x' → ∃ i : Fin n, x i ≠ x' i ∧ s x i ≠ s x' i

/-- **Condition (6.2)** (Shmueli, arXiv:2610.40573, Lemma 6.1, p.31 (PDF p.33)):
`x ≠ x′ ⟹ ∃ i ∈ [n] : xᵢ ≠ x′ᵢ and hᵢ(x) = hᵢ(x′)`. -/
def Eq62 {n : ℕ} (h : Qubits n → Qubits n) : Prop :=
  ∀ x x' : Qubits n, x ≠ x' → ∃ i : Fin n, x i ≠ x' i ∧ h x i = h x' i

end ICSCompute



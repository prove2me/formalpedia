-- Prove2me | Definitions.Def_QLocalCert_piKron
-- name    : QLocalCert_piKron
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T22:39:18.166558+00:00
-- url     : https://prove2.me/theorems/10c6eb1d-d6f3-4790-b9dc-121cc9daa3f7
-- title:
--   Qubit registers $\mathbb C^{2^c}$ and the tensor product $\bigotimes_i A_i$ of a family of matrices
-- statement:
--   A register of $c$ qubits is $\mathbb C^{2^c}$, with computational basis indexed by bit strings $\{0,1\}^c$. For a finite index set $I$ (the nodes of a network, or the repetitions of a protocol) and matrices $A_i\in\mathbb C^{\kappa_i\times\tau_i}$, the **tensor product** $\bigotimes_{i\in I}A_i$ is the matrix indexed by tuples $x=(x_i)_{i\in I}$, $y=(y_i)_{i\in I}$ with entries
--   $$
--   \Big(\bigotimes_{i\in I}A_i\Big)(x,y)=\prod_{i\in I}A_i(x_i,y_i).
--   $$
--
--   It is used for the joint certificate space $\mathcal H=\bigotimes_{v}\mathcal H_v$ of a quantum protocol, for the joint local operations of all nodes, and for the joint effect of independent repetitions.
--
--   **Formalization Note** `Qb c = Fin c → Bool`; `piKron A` is the tensor product of the family `A`, indexed by the dependent function type.
-- source:
--   Jauregui, Miyamoto, Quantum Advantage in Local Certification of Graph Properties, STOC 2027 submission (manuscript sha256 b707143b1ab5511bef4c2b77e1b803f28b32cced25a008516898fd11d28c0451), §2, p.14; Definition 7, pp.15–16; proof of Lemma 10, p.21

import Mathlib

set_option autoImplicit false

namespace QLocalCert

open Matrix

/-- A register of `c` qubits: its computational basis is indexed by `{0,1}^c`, so the register is
`ℂ^{2^c}`.

B. Jauregui, M. Miyamoto, *Quantum Advantage in Local Certification of Graph Properties*,
STOC 2027 submission (manuscript sha256 b707143b…0c51), §2, p.14 (all Hilbert spaces are
finite-dimensional) and §2.1, p.16 (certificate and message sizes are counted in qubits).

**Formalization Note.** `Qb c = Fin c → Bool`; a register with `c` qubits has dimension `2^c`. -/
abbrev Qb (c : ℕ) := Fin c → Bool

/-- The tensor product `⊗_i A_i` of a finite family of (possibly rectangular) matrices, one per
index `i` (one per network node, or one per repetition):
`(⊗_i A_i)(x, y) = ∏_i A_i(x_i, y_i)`.

Source: as `piKron` above (§2, p.14; Definition 7, pp.15–16: the joint certificate space is
`H = ⊗_{v∈V} H_v`; proof of Lemma 10, p.21: the joint effect `⊗_k M_k`).

**Formalization Note.** The tensor product of the spaces `ℂ^{κ_i}` is the space indexed by the
dependent function type `∀ i, κ i`; the matrix of a tensor product of operators is the product of
their entries. -/
def piKron {ι : Type} [Fintype ι] {κ τ : ι → Type} (A : ∀ i, Matrix (κ i) (τ i) ℂ) :
    Matrix (∀ i, κ i) (∀ i, τ i) ℂ :=
  fun x y => ∏ i, A i (x i) (y i)

end QLocalCert



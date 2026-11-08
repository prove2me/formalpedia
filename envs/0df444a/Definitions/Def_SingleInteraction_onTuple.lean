-- Prove2me | Definitions.Def_SingleInteraction_onTuple
-- name    : SingleInteraction_onTuple
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T07:53:29.56775+00:00
-- url     : https://prove2.me/theorems/bcf4842b-97f9-4fab-816d-54c0670a430e
-- title:
--   Application $h_e$ of a $k$-qubit operator to an ordered tuple of qubits
-- statement:
--   Let $h$ be an operator on $k$ qubits and $e=(e_1,\dots,e_k)$ an ordered tuple of pairwise distinct qubits of a register. The operator $h_e$ applies $h$ to the qubits of $e$, the $j$-th tensor factor of $h$ acting on $e_j$, and acts as the identity on all other qubits:
--
--   $$\langle s|\,h_e\,|t\rangle=\begin{cases}\langle s_{e_1}\cdots s_{e_k}|\,h\,|t_{e_1}\cdots t_{e_k}\rangle&\text{if }s_i=t_i\text{ for every qubit }i\notin e,\\0&\text{otherwise.}\end{cases}$$
--
--   For a two-qubit $h$ this is the paper's $h_{u,v}$, which in general differs from $h_{v,u}$.
--
--   **Formalization Note** The register's basis states are maps from qubit labels to $\{0,1\}$. The formula is used only for tuples of pairwise distinct qubits.
-- source:
--   Hecker, The Complexity of Single-Interaction Hamiltonians, arXiv:2609.39592 (held version, sha256 19ddc444…), §2.1, p.15; Definition 31, p.30 ("let $h_e$ denote the application of $h$ to the ordered tuple $e$")

import Mathlib

namespace SingleInteraction

/-- The application `h_e` of a `k`-qubit operator `h` to an ordered tuple `e = (e 0, …, e (k−1))` of
qubits of a register labelled by `ι`, acting as the identity on all remaining qubits
(Hecker, *The Complexity of Single-Interaction Hamiltonians*, arXiv:2609.39592 (held version, sha256 19ddc444…), §2.1, p.15: "the notation `h_{u,v}` specifies that its first tensor factor acts on `u` and its
second on `v`"; Definition 31, p.30: "let `h_e` denote the application of `h` to the ordered tuple `e`,
acting as the identity on all remaining qubits").

**Formalization Note** Basis states of the register are `ι → Fin 2` (bit `0` is `|0⟩`). The `j`-th
tensor factor of `h` acts on qubit `e j`: the entry at `(s, t)` is `h (s ∘ e) (t ∘ e)` when `s` and `t`
agree off the range of `e`, and `0` otherwise. The construction is meant for injective `e` (pairwise
distinct qubits), which is the only case used; then it is `h ⊗ I` in the qubit order of `e`. In
particular `onTuple h ![u, v]` is the paper's `h_{u,v}`, and in general it differs from
`onTuple h ![v, u]`. -/
def onTuple {ι : Type*} [Fintype ι] [DecidableEq ι] {k : ℕ}
    (h : Matrix (Fin k → Fin 2) (Fin k → Fin 2) ℂ) (e : Fin k → ι) :
    Matrix (ι → Fin 2) (ι → Fin 2) ℂ :=
  fun s t => h (s ∘ e) (t ∘ e) * if ∀ i : ι, (∀ j : Fin k, e j ≠ i) → s i = t i then 1 else 0

end SingleInteraction



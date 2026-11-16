-- Prove2me | Definitions.Def_PelagicFF_Supplement_GHS
-- name    : PelagicFF_Supplement_GHS
-- status  : Definition
-- author  : @iris
-- created : 2026-11-15T21:28:49.736203+00:00
-- url     : https://prove2.me/theorems/274f1b2a-d5c8-4e05-b823-ca0ac6dc9a1e
-- title:
--   The Graph Hadamard Support Problem $\mathrm{GHS}_n$ (Problem A.1)
-- statement:
--   For a symmetric zero-diagonal matrix $A\in\mathbb F_2^{n\times n}$ the $n$-qubit **graph state** is
--
--   $$
--   |\psi_A\rangle=2^{-n/2}\sum_{x\in\mathbb F_2^n}(-1)^{q(x)}|x\rangle,\qquad q(x)=\sum_{1\le u<v\le n}A_{uv}x_ux_v .
--   $$
--
--   For $S\subseteq[n]$, $H_S$ applies a Hadamard gate to every qubit in $S$ and the identity elsewhere; its entries are $\langle z|H_S|x\rangle=\prod_{i\in S}2^{-1/2}(-1)^{x_iz_i}\prod_{i\notin S}[x_i=z_i]$. The support of a state $|\varphi\rangle$ is the set of $z$ with $|\langle z|\varphi\rangle|^2>0$.
--
--   In $\mathrm{GHS}_n$ Alice receives $A$, Bob receives $S\subseteq[n]$, and after one message from Alice Bob must output
--
--   $$
--   z\in\operatorname{supp}(H_S|\psi_A\rangle),\qquad\text{i.e. } |\langle z|H_S|\psi_A\rangle|^2>0 .
--   $$
--
--   This is the problem of Theorems A.2, A.8 and A.10, an $n$ versus $\Theta(n^2)$ separation with a product Hadamard measurement.
--
--   **Formalization Note** $[n]$ is `Fin n`, $S$ ranges over all subsets (including $\emptyset$ and $[n]$), and strings are `Fin n → Bool`.
-- source:
--   Anselm, Ding, Gilboa, Grewal, Optimal and Verifiable Quantum Advantages in Communication Complexity, arXiv:2610.05585 (held version, sha256 4564aef3…), Appendix A, p.57 (graph state, H_S, support); Problem A.1, p.57

import Mathlib

namespace PelagicFF.Supplement

/-- Alice's inputs in `GHSₙ`: symmetric zero-diagonal matrices `A ∈ F₂^{n×n}` (adjacency matrices
of graphs on `n` vertices). -/
abbrev SymZeroDiag (n : ℕ) : Type :=
  {A : Matrix (Fin n) (Fin n) (ZMod 2) // A.IsSymm ∧ ∀ i, A i i = 0}

/-- A bit as an element of `F₂`. -/
def bitZ (b : Bool) : ZMod 2 := if b then 1 else 0

/-- The quadratic form `q(x) = ∑_{1 ≤ u < v ≤ n} A_{uv} x_u x_v` over `F₂`. -/
def graphPoly {n : ℕ} (A : Matrix (Fin n) (Fin n) (ZMod 2)) (x : Fin n → Bool) : ZMod 2 :=
  ∑ u, ∑ v ∈ Finset.univ.filter (fun v => u < v), A u v * bitZ (x u) * bitZ (x v)

/-- The `n`-qubit **graph state** `|ψ_A⟩ = 2^{−n/2} ∑_x (−1)^{q(x)} |x⟩`, as its amplitude vector in
the computational basis `Fin n → Bool`. arXiv:2610.05585 (held version, sha256 4564aef3…),
Appendix A, p.57. -/
noncomputable def graphState {n : ℕ} (A : Matrix (Fin n) (Fin n) (ZMod 2)) : (Fin n → Bool) → ℂ :=
  fun x => ((Real.sqrt (2 ^ n))⁻¹ : ℂ) * (-1) ^ (graphPoly A x).val

/-- The partial Hadamard operator `H_S`: a Hadamard gate on every qubit of `S` and the identity
elsewhere. Its entry in row `z` and column `x` is
`∏_{i∈S} 2^{−1/2}(−1)^{xᵢzᵢ} · ∏_{i∉S} [xᵢ = zᵢ]`.
arXiv:2610.05585 (held version, sha256 4564aef3…), Appendix A, p.57. -/
noncomputable def hadamardOn {n : ℕ} (S : Finset (Fin n)) : Matrix (Fin n → Bool) (Fin n → Bool) ℂ :=
  fun z x => ∏ i, if i ∈ S then ((Real.sqrt 2)⁻¹ : ℂ) * (if x i && z i then -1 else 1)
    else (if x i = z i then 1 else 0)

/-- **The Graph Hadamard Support Problem `GHSₙ` (Problem A.1)** as a two-party search relation:
Alice holds a symmetric zero-diagonal `A ∈ F₂^{n×n}`, Bob holds `S ⊆ [n]`, and `z ∈ F₂ⁿ` is correct
exactly when `z ∈ supp(H_S|ψ_A⟩)`, i.e. `|⟨z|H_S|ψ_A⟩|² > 0`.

arXiv:2610.05585 (held version, sha256 4564aef3…), Appendix A, p.57: "For an n-qubit state |φ⟩
and n-qubit quantum circuit Q, let supp(Q|φ⟩) denote the set of all bitstrings x ∈ F₂ⁿ such that
|⟨x|Q|φ⟩|² > 0." Problem A.1: "Alice receives a symmetric zero-diagonal matrix A ∈ F₂^{n×n}
specifying the graph state |ψ_A⟩, and Bob receives a subset S ⊆ [n] specifying the partial Hadamard
operator H_S. After receiving a message from Alice, Bob must output a string z ∈ F₂ⁿ such that
z ∈ supp(H_S|ψ_A⟩)."

**Formalization Note.** `[n]` is `Fin n`, subsets are `Finset (Fin n)` (all of them, including
`∅` and `[n]`), and strings are `Fin n → Bool`. -/
noncomputable def GHS (n : ℕ) (A : SymZeroDiag n) (S : Finset (Fin n)) (z : Fin n → Bool) : Prop :=
  0 < Complex.normSq (Matrix.mulVec (hadamardOn S) (graphState A.1) z)

end PelagicFF.Supplement



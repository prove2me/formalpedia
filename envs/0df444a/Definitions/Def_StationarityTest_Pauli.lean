-- Prove2me | Definitions.Def_StationarityTest_Pauli
-- name    : StationarityTest_Pauli
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T12:22:02.100632+00:00
-- url     : https://prove2.me/theorems/80491a2c-a566-48ab-928f-7a05bdfb4ae6
-- title:
--   Sites, Pauli strings $S^k_{[n]}$, Hamiltonians $H=\sum_{\gamma\in\Gamma}h_\gamma P_\gamma$ and Gibbs states $\rho_H$
-- statement:
--   The system has $n$ **sites** $i\in[n]$, each a qudit of dimension $2^q$ built from $q$ qubits, so the Hilbert space is $\mathcal H=\bigotimes_{i=1}^n\mathbb C^{2^q}$. A **Pauli string** assigns one of $I,X,Y,Z$ to every qubit; its operator is the tensor product of the single-qubit matrices. Its **site support** $\operatorname{supp}(P)\subseteq[n]$ is the set of sites on which it is not the identity, and
--
--   $$S^k_{[n]}=\{P\ne I:\ |\operatorname{supp}(P)|\le k\},\qquad S_i=\{P:\ \operatorname{supp}(P)\subseteq\{i\}\}.$$
--
--   The set $S_i$ of single-site strings on site $i$ contains the identity. A **Hamiltonian** on a clause set $\Gamma\subseteq S^k_{[n]}$ with real coefficients $h$ is
--
--   $$H=\sum_{\gamma\in\Gamma}h_\gamma P_\gamma,\qquad \Gamma_H=\{P:\ h_P\ne0\},$$
--
--   and its **Gibbs state** at inverse temperature $\beta$ is
--
--   $$\rho_H=\frac{e^{-\beta H}}{\operatorname{tr}[e^{-\beta H}]}.$$
--
--   A **full-rank state** is a positive definite matrix of trace $1$.
--
--   These are the objects every statement of the mission is about.
--
--   **Formalization Note** Sites are `Fin n`; qubit $j$ of site $i$ is wire `finProdFinEquiv (i, j)` of `QAlgorithms.Qubits (n*q)`, and the single-qubit Paulis are the published `QAlgorithms.pauliX`, `pauliY`, `pauliZ`. The paper does not care how Paulis are embedded within a site (p.13). The bound $|h_\gamma|\le1$ of (21) is a hypothesis of each statement. The exponential is the matrix exponential, and the partition function is the real part of its trace, which is a positive real for every Hermitian $H$ (proved in the mission's sanity file, with $\operatorname{tr}\rho_H=1$).
-- source:
--   Bergamaschi, The stationarity test: a framework for learning quantum many-body systems from their thermal states, arXiv:2610.01074 (held file sha256 0b7e46fb…), §2 Notation, (19)–(21), pp.13–14; (1), p.4; (100), p.28

import Mathlib
import Definitions.Def_QAlgorithms_Defs_GradientMethods
import Definitions.Def_QAlgorithms_Defs_Information

open Matrix
open scoped ComplexOrder

namespace StationarityTest

/-!
# Sites, Pauli strings, Hamiltonians and Gibbs states

T. Bergamaschi, *The stationarity test: a framework for learning quantum many-body systems from
their thermal states*, arXiv:2610.01074 (held file sha256 0b7e46fb…), §2 Notation, (19)–(20),
pp.13–14; §2.1, (21), p.14; (1), p.4; §5, (100), p.28.

**Formalization Note.** There are `n` sites `Fin n` (the paper's `[n] = {1, …, n}`, shifted to
start at `0`), each a qudit of dimension `2^q` made of `q` qubits. The Hilbert space
`⊗ᵢ ℂ^{2^q}` is functions on the computational basis `QAlgorithms.Qubits (n * q)`; qubit `j` of
site `i` is wire `finProdFinEquiv (i, j)`. A Pauli string assigns to each qubit one of
`I, X, Y, Z` (`Fin 4`, `0 = I`); the single-qubit matrices are the published `QAlgorithms.pauliX`,
`pauliY`, `pauliZ`. The paper "will never care how the Pauli strings are actually embedded
within a site" (p.13), so this embedding is a harmless choice. A Hamiltonian is a family of real
coefficients on a set `Γ` of `k`-local non-identity Pauli strings (21); its operator
`Σ_{γ∈Γ} h_γ P_γ` ignores coefficients outside `Γ`. The bound `h_γ ∈ [−1, 1]` of (21) is a
hypothesis of each statement, not part of the definition.
-/

/-- A Pauli string on `n` sites of `q` qubits: one of `I, X, Y, Z` (`0, 1, 2, 3`) on every qubit. -/
abbrev PauliString (n q : ℕ) := Fin n → Fin q → Fin 4

/-- Operators `B(H)` on `n` sites of local dimension `2^q`. -/
abbrev Op (n q : ℕ) := Matrix (QAlgorithms.Qubits (n * q)) (QAlgorithms.Qubits (n * q)) ℂ

/-- The single-qubit Pauli matrices `I₂, X, Y, Z` (19). -/
def pauli1 : Fin 4 → Matrix Bool Bool ℂ
  | 0 => 1
  | 1 => QAlgorithms.pauliX
  | 2 => QAlgorithms.pauliY
  | 3 => QAlgorithms.pauliZ

/-- The matrix of a Pauli string: the tensor product over all qubits of its single-qubit Paulis. -/
noncomputable def PauliString.mat {n q : ℕ} (P : PauliString n q) : Op n q :=
  Matrix.of fun y z => ∏ i : Fin n, ∏ j : Fin q,
    pauli1 (P i j) (y (finProdFinEquiv (i, j))) (z (finProdFinEquiv (i, j)))

/-- The site support `supp(P) ⊆ [n]`: the sites on which `P` is not the identity. -/
def siteSupport {n q : ℕ} (P : PauliString n q) : Finset (Fin n) :=
  Finset.univ.filter fun i => ∃ j, P i j ≠ 0

/-- `S^k_[n]` (§5, p.28; (21), p.14): the non-identity Pauli strings supported on at most `k`
sites. -/
def IsKLocal (n q k : ℕ) (P : PauliString n q) : Prop :=
  P ≠ 0 ∧ (siteSupport P).card ≤ k

instance (n q k : ℕ) : DecidablePred (IsKLocal n q k) := fun P => by
  unfold IsKLocal; infer_instance

/-- The type of `k`-local non-identity Pauli strings `S^k_[n]`, the clauses of a Hamiltonian. -/
abbrev KLocal (n q k : ℕ) := {P : PauliString n q // IsKLocal n q k P}

/-- `S_i` (19): the single-site Pauli strings on site `i`, i.e. the strings acting as the identity
on every other site. It contains the identity string. -/
def singleSite {n q : ℕ} (i : Fin n) : Finset (PauliString n q) :=
  Finset.univ.filter fun P => siteSupport P ⊆ {i}

/-- The Hamiltonian `H = Σ_{γ∈Γ} h_γ P_γ` (21), on a clause set `Γ ⊆ S^k_[n]` with real
coefficients `h`. -/
noncomputable def ham {n q k : ℕ} (Γ : Finset (KLocal n q k)) (h : KLocal n q k → ℝ) : Op n q :=
  ∑ γ ∈ Γ, ((h γ : ℝ) : ℂ) • γ.1.mat

/-- `Γ_H = {P : h_P ≠ 0}` (100): the clauses with nonzero coefficient. -/
noncomputable def coeffSupport {n q k : ℕ} (h : KLocal n q k → ℝ) : Finset (KLocal n q k) :=
  open Classical in Finset.univ.filter fun P => h P ≠ 0

/-- A full-rank state: a positive definite matrix of trace `1` (§2.2, p.15: "We assume ρ is full
rank throughout this section"). -/
def IsFullRankState {n q : ℕ} (σ : Op n q) : Prop :=
  σ.PosDef ∧ σ.trace = 1

/-- The partition function `tr[e^{−βH}]` (1), as a real number. -/
noncomputable def partitionFn {n q : ℕ} (β : ℝ) (H : Op n q) : ℝ :=
  (trace (NormedSpace.exp ((-(β : ℂ)) • H))).re

/-- The Gibbs state `ρ_H = e^{−βH}/tr[e^{−βH}]` (1), p.4.

**Formalization Note.** `e^{−βH}` is the matrix exponential. For Hermitian `H` (every Hamiltonian
`ham Γ h`) the trace is a positive real number. -/
noncomputable def gibbs {n q : ℕ} (β : ℝ) (H : Op n q) : Op n q :=
  (((partitionFn β H)⁻¹ : ℝ) : ℂ) • NormedSpace.exp ((-(β : ℂ)) • H)

end StationarityTest



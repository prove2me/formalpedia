-- Prove2me | Definitions.Def_QMaxCutBeyond_TwoQubit_Setting
-- name    : QMaxCutBeyond_TwoQubit_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-21T13:38:31.763987+00:00
-- url     : https://prove2.me/theorems/1a9525f2-8ea2-40b3-8fdf-6cfcc50c9348
-- title:
--   Qubits, Paulis, the quantum Max Cut Hamiltonian H_G (eq. (5)), energy, weights W and max_{e∼v} w_e, the Laplacian, stars, matchings, and tensor products of 1- and 2-qubit states (pp. 3–11)
-- statement:
--   This file fixes the model of Anshu, Gosset and Morenz for the quantum Max Cut problem.
--
--   1. **Register.** An $n$-qubit state is a vector $\psi\in\mathbb C^{\{0,1\}^n}$, indexed by computational basis configurations $x=(x_0,\dots,x_{n-1})\in\{0,1\}^n$; operators are $2^n\times 2^n$ complex matrices. It is a **unit state** if $\sum_x|\psi(x)|^2=1$. The basis state $|z\rangle$ has amplitude $1$ at $z$ and $0$ elsewhere. The **energy** of $\psi$ under $H$ is $\langle\psi|H|\psi\rangle$ (its real part).
--   2. **Paulis.** $X=\begin{pmatrix}0&1\\1&0\end{pmatrix}$, $Y=\begin{pmatrix}0&-i\\i&0\end{pmatrix}$, $Z=\begin{pmatrix}1&0\\0&-1\end{pmatrix}$; $X_i,Y_i,Z_i$ act on qubit $i$ and as the identity elsewhere.
--   3. **Hamiltonian (eq. (5)).** For a simple graph $G=(V,E)$ on $V=\{0,\dots,n-1\}$ with edge weights $w$,
--   $$H_G=\sum_{\{i,j\}\in E}w_{ij}\,h_{ij},\qquad h_{ij}=\tfrac12\bigl(I-X_iX_j-Y_iY_j-Z_iZ_j\bigr),$$
--   each edge counted once. Also $H_Z(G)=-\tfrac12\sum_{\{i,j\}\in E}w_{ij}Z_iZ_j$ (weighted form of eq. (17)).
--   4. **Weights.** $W=\sum_{e\in E}w_e$; $\max_{e\in E}w_e$; $\max_{e\sim v}w_e$, the largest weight of an edge incident to $v$; both maxima are $0$ over an empty edge set (an edgeless graph, an isolated vertex).
--   5. **Laplacian (p. 7).** $L(G)_{ii}=\sum_{e\sim i}w_e$, $L(G)_{ij}=-w_e$ if $e=\{i,j\}\in E$, and $0$ otherwise.
--   6. **Stars and matchings.** $G$ is a star with centre $c$ if every edge contains $c$. An edge set $M$ is a matching if two distinct edges of $M$ share no vertex; the vertices covered by no edge of $M$ form the set $U$.
--   7. **Tensor products of 1- and 2-qubit states (Theorem 3).** A state $\varphi=\varphi_1\otimes\cdots\otimes\varphi_L$: the qubits are partitioned into blocks of one or two qubits (described by an involution $p$ of $V$, the block of $i$ being $\{i,p(i)\}$), each block carries a unit vector of $\mathbb C^2$ or $\mathbb C^4$, and the amplitude of $\varphi$ at $x$ is the product over blocks of the block amplitudes at $x$ restricted to the block.
--   8. **The state $\varphi_z$ of p. 10.** For a matching $M$ and $z\in\{0,1\}^U$,
--   $$|\varphi_z\rangle=\Bigl(\bigotimes_{\{i,j\}\in M}\tfrac{1}{\sqrt2}(|01\rangle-|10\rangle)_{ij}\Bigr)\otimes|z\rangle_U .$$
--
--   These objects are shared by every statement of the mission: the energy of a state, the maximum energy $\mathrm{OPT}(G)=\|H_G\|$, and the class of states the main theorem optimises over.
--
--   **Formalization Note** Configurations are `Fin n → Fin 2`. `onSite i σ` is $\sigma$ on qubit $i$ tensored with identities. Edges are counted once through the ordered representative $i<j$ of $\{i,j\}$; weights are a function `Sym2 (Fin n) → ℝ` and every theorem assumes them nonnegative. The maxima are `Finset.sup` in `ℝ≥0` (of `toNNReal` of the weights), hence $0$ on empty sets. $\mathrm{OPT}(G)$ is not defined: since $H_G\succeq0$, statements about it are phrased "for every unit state $\psi$". In a two-qubit block $\{i,p(i)\}$ with $i<p(i)$ the first amplitude index is qubit $i$; the singlet on $\{i,j\}$, $i<j$, is $(|01\rangle-|10\rangle)/\sqrt2$ with qubit $i$ first (the order changes only a global sign). The partner of a covered vertex is chosen by `Classical.choose`, unique when $M$ is a matching.
-- source:
--   Anshu, Gosset & Morenz, Beyond product state approximations for a quantum analogue of Max Cut, arXiv:2003.14394v1, p. 3, eq. (5) and standing assumption; p. 5, Theorem 3; p. 7, Laplacian L(G); p. 8, eq. (17); pp. 9–10, W and max_{e∼v} w_e; p. 10, Lemma 2 and the state |φ_z⟩

import Mathlib

/-!
Anshu, Gosset & Morenz, *Beyond product state approximations for a quantum analogue of Max Cut*,
arXiv:2003.14394v1, pp. 3–11: n-qubit register, Pauli matrices, the quantum Max Cut Hamiltonian
H_G of eq. (5), the energy ⟨ψ|H|ψ⟩, weighted-graph quantities (W, max_{e∈E} w_e, max_{e∼v} w_e,
the Laplacian of p. 7), star graphs, matchings, and the class of tensor products of 1- and 2-qubit
states (Theorem 3, p. 5).
-/

namespace QMaxCutBeyond.TwoQubit

open Matrix

/-- Computational basis configurations of `n` qubits: `x i ∈ {0,1}` is the bit of qubit `i`. -/
abbrev Config (n : ℕ) := Fin n → Fin 2

/-- n-qubit operators, as matrices indexed by computational basis configurations. -/
abbrev Op (n : ℕ) := Matrix (Config n) (Config n) ℂ

/-- Pauli X = [[0,1],[1,0]]. -/
def pauliX : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; 1, 0]
/-- Pauli Y = [[0,-i],[i,0]]. -/
def pauliY : Matrix (Fin 2) (Fin 2) ℂ := !![0, -Complex.I; Complex.I, 0]
/-- Pauli Z = [[1,0],[0,-1]]. -/
def pauliZ : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, -1]

/-- The single-qubit operator `σ` acting on qubit `i` (identity on every other qubit). -/
def onSite {n : ℕ} (i : Fin n) (σ : Matrix (Fin 2) (Fin 2) ℂ) : Op n :=
  fun x y => σ (x i) (y i) * (if ∀ j, j ≠ i → x j = y j then 1 else 0)

/-- The edge term `h_ij = ½ (I − X_i X_j − Y_i Y_j − Z_i Z_j)` of eq. (5). -/
noncomputable def edgeTerm {n : ℕ} (i j : Fin n) : Op n :=
  (1 / 2 : ℂ) • (1 - onSite i pauliX * onSite j pauliX - onSite i pauliY * onSite j pauliY
    - onSite i pauliZ * onSite j pauliZ)

/-- The quantum Max Cut Hamiltonian `H_G = Σ_{{i,j}∈E} w_ij h_ij` of eq. (5). Each edge
`{i,j}` of the simple graph `G` is counted once, through its ordered representative `i < j`. -/
noncomputable def hamiltonian {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (w : Sym2 (Fin n) → ℝ) : Op n :=
  ∑ i, ∑ j, if i < j ∧ G.Adj i j then ((w s(i, j) : ℝ) : ℂ) • edgeTerm i j else 0

/-- `H_Z(G) = −½ Σ_{{i,j}∈E} w_ij Z_i Z_j` (weighted form of eq. (17)). -/
noncomputable def hamZ {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (w : Sym2 (Fin n) → ℝ) : Op n :=
  ∑ i, ∑ j, if i < j ∧ G.Adj i j then
    ((-(1 / 2) * w s(i, j) : ℝ) : ℂ) • (onSite i pauliZ * onSite j pauliZ) else 0

/-- The energy `⟨ψ|H|ψ⟩` (real part; it is real for Hermitian `H`). -/
noncomputable def energy {n : ℕ} (H : Op n) (ψ : Config n → ℂ) : ℝ :=
  (star ψ ⬝ᵥ (H *ᵥ ψ)).re

/-- `ψ` is a unit vector: `Σ_x |ψ(x)|² = 1`. -/
def IsUnitState {n : ℕ} (ψ : Config n → ℂ) : Prop :=
  ∑ x, ‖ψ x‖ ^ 2 = 1

/-- The computational basis state `|z⟩`. -/
def basisState {n : ℕ} (z : Config n) : Config n → ℂ :=
  fun x => if x = z then 1 else 0

/-- Total weight `W = Σ_{e∈E} w_e`. -/
def totalWeight {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (w : Sym2 (Fin n) → ℝ) : ℝ :=
  ∑ e ∈ G.edgeFinset, w e

/-- `max_{e∈E} w_e`, with value `0` when `E = ∅` (and negative weights truncated to `0`;
every theorem assumes `w ≥ 0`). -/
noncomputable def maxEdgeWeight {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (w : Sym2 (Fin n) → ℝ) : ℝ :=
  ((G.edgeFinset.sup fun e => (w e).toNNReal : NNReal) : ℝ)

/-- `max_{e∼v} w_e`, the largest weight of an edge incident to `v`; `0` for an isolated `v`. -/
noncomputable def maxIncident {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (w : Sym2 (Fin n) → ℝ) (v : Fin n) : ℝ :=
  (((G.incidenceFinset v).sup fun e => (w e).toNNReal : NNReal) : ℝ)

/-- The weighted graph Laplacian of p. 7: `L_ii = Σ_{e∼i} w_e`, `L_ij = −w_e` for
`e = {i,j} ∈ E`, `0` otherwise. -/
def laplacian {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (w : Sym2 (Fin n) → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => if i = j then ∑ e ∈ G.incidenceFinset i, w e
    else if G.Adj i j then -w s(i, j) else 0

/-- `G` is a star graph with centre `c`: every edge contains `c`. -/
def IsStar {n : ℕ} (G : SimpleGraph (Fin n)) (c : Fin n) : Prop :=
  ∀ i j, G.Adj i j → i = c ∨ j = c

/-- A set of edges is a matching: two distinct edges of `M` share no vertex. -/
def IsEdgeMatching {n : ℕ} (M : Finset (Sym2 (Fin n))) : Prop :=
  ∀ e ∈ M, ∀ e' ∈ M, e ≠ e' → ∀ v, v ∈ e → v ∉ e'

/-- The tensor product over blocks: `p` pairs qubits (`p i = i`: a single-qubit block `{i}` with
amplitudes `a i`; `i < p i`: a two-qubit block `{i, p i}` with amplitudes `b i`, first index
qubit `i`). The amplitude at `x` is the product of the block amplitudes. -/
def blockState {n : ℕ} (p : Fin n → Fin n) (a : Fin n → Fin 2 → ℂ)
    (b : Fin n → Fin 2 → Fin 2 → ℂ) : Config n → ℂ :=
  fun x => ∏ i, (if p i = i then a i (x i) else if i < p i then b i (x i) (x (p i)) else 1)

/-- `φ` is a tensor product `φ₁ ⊗ ⋯ ⊗ φ_L` of 1- and 2-qubit unit states (Theorem 3, p. 5):
the qubits are partitioned into blocks `{i, p i}` by an involution `p`, and each block carries a
unit vector of `ℂ²` or `ℂ⁴`. -/
def IsOneTwoProduct {n : ℕ} (φ : Config n → ℂ) : Prop :=
  ∃ (p : Fin n → Fin n) (a : Fin n → Fin 2 → ℂ) (b : Fin n → Fin 2 → Fin 2 → ℂ),
    (∀ i, p (p i) = i) ∧
    (∀ i, p i = i → ∑ s, ‖a i s‖ ^ 2 = 1) ∧
    (∀ i, i < p i → ∑ s, ∑ t, ‖b i s t‖ ^ 2 = 1) ∧
    φ = blockState p a b

/-- Singlet amplitudes `(|01⟩ − |10⟩)/√2`. -/
noncomputable def singletAmp : Fin 2 → Fin 2 → ℂ :=
  fun s t => if s = 0 ∧ t = 1 then ((Real.sqrt 2)⁻¹ : ℝ)
    else if s = 1 ∧ t = 0 then ((-(Real.sqrt 2)⁻¹ : ℝ) : ℂ) else 0

/-- The partner of `i` in the edge set `M` (some `j ≠ i` with `{i,j} ∈ M`), or `i` itself if `i`
is not covered by `M`. -/
noncomputable def matchPartner {n : ℕ} (M : Finset (Sym2 (Fin n))) (i : Fin n) : Fin n :=
  by classical exact if h : ∃ j, j ≠ i ∧ s(i, j) ∈ M then Classical.choose h else i

/-- `U`: the vertices not incident to an edge of `M`. -/
def uncovered {n : ℕ} (M : Finset (Sym2 (Fin n))) : Finset (Fin n) :=
  Finset.univ.filter fun i => ∀ e ∈ M, i ∉ e

/-- `|φ_z⟩ = (⊗_{{i,j}∈M} (|01⟩ − |10⟩)_ij/√2) ⊗ |z⟩_U` (p. 10), for `z ∈ {0,1}^U`. -/
noncomputable def matchingState {n : ℕ} (M : Finset (Sym2 (Fin n)))
    (z : ↥(uncovered M) → Fin 2) : Config n → ℂ :=
  blockState (matchPartner M)
    (fun i s => if h : i ∈ uncovered M then (if s = z ⟨i, h⟩ then 1 else 0) else 0)
    (fun _ => singletAmp)

end QMaxCutBeyond.TwoQubit



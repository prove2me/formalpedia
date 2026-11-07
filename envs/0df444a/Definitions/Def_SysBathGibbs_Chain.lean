-- Prove2me | Definitions.Def_SysBathGibbs_Chain
-- name    : SysBathGibbs_Chain
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:33:31.50307+00:00
-- url     : https://prove2.me/theorems/bb424486-6f69-464d-9bb4-6465c05e436f
-- title:
--   Sites, Pauli couplings, the nearest-neighbor chain $H_n$ and the local trace $\mathcal E_{x,r}$
-- statement:
--   A chain of $n$ sites $[n]=\{1,\dots,n\}$ carries at each site a qudit of local dimension $2^q$, viewed as $q$ qubits, so the system Hilbert space is $(\mathbb C^{2^q})^{\otimes n}$. A system operator $O$ is **supported on** $S\subseteq[n]$ when it acts as the identity on the sites outside $S$, i.e. $O=O_S\otimes \mathbf 1_{S^c}$; $\|\cdot\|_{\mathrm{op}}$ is the operator norm.
--
--   The **nearest-neighbor chain** of (1.2) is a family $(h_x)_{x=1}^{n-1}$ with
--   $$
--   h_x=h_x^\dagger,\qquad \operatorname{supp}h_x\subseteq\{x,x+1\},\qquad \|h_x\|_{\mathrm{op}}\le 1,
--   $$
--   and $H_n=\sum_{x=1}^{n-1}h_x$. No translation invariance or commutation is assumed.
--
--   The **couplings** $A_{x,a}=P_{x,a}$, $a\in[4^q-1]$, of (1.7) are the nonidentity Pauli strings $\{\mathbf 1,X,Y,Z\}^{\otimes q}\setminus\{\mathbf 1\}$ on the $q$ qubits of site $x$, tensored with the identity elsewhere. The neighborhood is $N_r(S)=\{y: \operatorname{dist}(y,S)\le r\}$ for real $r\ge0$, and the **normalized partial trace** onto $S=N_r(x)$ is
--   $$
--   \mathcal E_{x,r}(B)=2^{-q|S^c|}\operatorname{Tr}_{S^c}(B)\otimes\mathbf 1_{S^c}.
--   $$
--
--   These objects are the system side of every statement of the mission.
--
--   **Formalization Note** The site $x\in[n]$ is the index $x-1$ of `Fin n`; only distances $|x-y|$ enter. The basis of the chain is `Fin n → Fin q → Bool` with `false` $=|0\rangle$ and $Z|0\rangle=|0\rangle$. The operator norm is the norm of the matrix as a continuous linear map on Euclidean space (not Mathlib's default entrywise norm). Support is stated entrywise. At $n=1$ the family is empty and $H_1=0$.
-- source:
--   Ding, Li, Zhang, Efficient thermalization of one-dimensional noncommuting Hamiltonians via system-bath interactions with Θ(n) ancilla qubits, arXiv:2611.03422 (held file sha256 a60a3c09826df3b5399a5589f83ef3a1d2ea768d74c5e39e8a3b29d1323f024f), §1.1.1 eq. (1.2) and (1.7), pp.4–6; §2.1, p.10; normalized partial trace E_{x,r}, p.31

import Mathlib

open Matrix

namespace SysBathGibbs

/-!
# The chain: sites, Pauli couplings, the nearest-neighbor Hamiltonian

Ding, Li, Zhang, *Efficient thermalization of one-dimensional noncommuting Hamiltonians via
system-bath interactions with Θ(n) ancilla qubits*, arXiv:2611.03422 (held file sha256 a60a3c09…),
§1.1.1, (1.2), (1.7), pp.4–6; §2.1, p.10; (4.4), p.31; (8.1), p.61.

**Formalization Note.** Sites `[n] = {1,…,n}` are `Fin n`, so the paper's site `x` is `x - 1`; only
the index distance `|x - y|` enters. A site carries `q` qubits, and the system's computational basis
is `Fin n → Fin q → Bool`, with `false = |0⟩`, `true = |1⟩`. A system operator is a complex matrix on
this basis. `‖·‖_op` is the L2 operator norm (`opNorm`), not Mathlib's default entrywise norm.
-/

/-- Basis labels of the chain of `n` sites with `q` qubits per site (local dimension `2^q`). -/
abbrev Site (n q : ℕ) := Fin n → Fin q → Bool

/-- System operators: complex matrices on `(ℂ^{2^q})^{⊗n}`. -/
abbrev SysMat (n q : ℕ) := Matrix (Site n q) (Site n q) ℂ

/-- The labels `a ∈ [4^q - 1]` of the nonidentity Pauli strings on one site, (1.7): a word in
`{1, X, Y, Z}` of length `q` (encoded by `0, 1, 2, 3`) other than the all-identity word. -/
abbrev Coupling (q : ℕ) := {p : Fin q → Fin 4 // p ≠ 0}

/-- The bath labels `(x, a) ∈ [n] × [4^q - 1]`, p.5. -/
abbrev Label (n q : ℕ) := Fin n × Coupling q

/-- The operator norm `‖·‖_op`, p.5: the norm of the matrix as an operator on Euclidean space. -/
noncomputable def opNorm {ι : Type} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℂ) : ℝ :=
  ‖Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ) A‖

/-- `SupportedOn S O`, p.5 and p.10: `O` acts as the identity on the sites outside `S`, that is,
`O = O_S ⊗ 1_{Sᶜ}`. Entrywise: `O i j` vanishes unless `i, j` agree outside `S`, and otherwise it
depends only on the restrictions of `i, j` to `S`. -/
def SupportedOn {n q : ℕ} (S : Set (Fin n)) (O : SysMat n q) : Prop :=
  (∀ i j : Site n q, (∃ y, y ∉ S ∧ i y ≠ j y) → O i j = 0) ∧
    ∀ i j i' j' : Site n q, (∀ y, y ∉ S → i y = j y) → (∀ y, y ∉ S → i' y = j' y) →
      (∀ y, y ∈ S → i y = i' y) → (∀ y, y ∈ S → j y = j' y) → O i j = O i' j'

/-- The nearest-neighbor chain (1.2), p.4: a family `h_x`, `x = 1, …, n-1`, of Hermitian matrices
with `supp h_x ⊆ {x, x+1}` and `‖h_x‖_op ≤ 1`. Nothing else is assumed. At `n = 1` the family is
empty and the Hamiltonian is `0`. -/
def IsChain {n q : ℕ} (h : Fin (n - 1) → SysMat n q) : Prop :=
  ∀ x, (h x).IsHermitian ∧
    SupportedOn {y : Fin n | y.val = x.val ∨ y.val = x.val + 1} (h x) ∧ opNorm (h x) ≤ 1

/-- `H_n = ∑_x h_x`, (1.2). -/
def chainHam {n q : ℕ} (h : Fin (n - 1) → SysMat n q) : SysMat n q := ∑ x, h x

/-- The single-qubit Pauli matrices `1, X, Y, Z` (codes `0, 1, 2, 3`) in the basis
`false = |0⟩`, `true = |1⟩`, so `Z|0⟩ = |0⟩`. -/
noncomputable def pauli1 (c : Fin 4) (i j : Bool) : ℂ :=
  match c.val with
  | 0 => if i = j then 1 else 0
  | 1 => if i = j then 0 else 1
  | 2 => if i = j then 0 else if i then Complex.I else -Complex.I
  | _ => if i = j then (if i then -1 else 1) else 0

/-- The Pauli string `P_{x,a} = A_{x,a}`, (1.7), p.6: the tensor product of the single-qubit Paulis
of the word `p` on the `q` qubits of site `x`, and the identity on all other sites. -/
noncomputable def pauliString {n q : ℕ} (x : Fin n) (p : Fin q → Fin 4) : SysMat n q :=
  Matrix.of fun i j =>
    open Classical in
    if ∀ y, y ≠ x → i y = j y then ∏ k, pauli1 (p k) (i x k) (j x k) else 0

/-- The neighborhood `N_r(S) = {y ∈ [n] : dist(y, S) ≤ r}`, p.4 and (8.1), for real `r`. For empty
`S`, `dist(y, ∅) = +∞`, so `N_r(∅) = ∅`. -/
def nbhd {n : ℕ} (r : ℝ) (S : Set (Fin n)) : Set (Fin n) :=
  {y | ∃ z ∈ S, |((y.val : ℝ) - (z.val : ℝ))| ≤ r}

/-- The normalized partial trace onto `S`, p.31: `E(B) = 2^{-q|Sᶜ|} Tr_{Sᶜ}(B) ⊗ 1_{Sᶜ}`. Entrywise
it vanishes unless `i, j` agree outside `S`, and otherwise it averages `B` over the configurations
outside `S`. Here the average runs over all `k : Site n q` (whose part on `S` is ignored), which
is the same average since each configuration outside `S` occurs equally often. -/
noncomputable def traceOnto {n q : ℕ} (S : Set (Fin n)) (B : SysMat n q) : SysMat n q :=
  open Classical in
  Matrix.of fun i j =>
    if ∀ y, y ∉ S → i y = j y then
      ((Fintype.card (Site n q) : ℂ))⁻¹ *
        ∑ k : Site n q, B (fun y => if y ∈ S then i y else k y) (fun y => if y ∈ S then j y else k y)
    else 0

/-- `E_{x,r} = traceOnto (N_r(x))`, p.31. -/
noncomputable def traceAt {n q : ℕ} (x : Fin n) (r : ℝ) (B : SysMat n q) : SysMat n q :=
  traceOnto (nbhd r {x}) B

end SysBathGibbs



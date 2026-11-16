-- Prove2me | Definitions.Def_CodeSW_Supplement_pauli
-- name    : CodeSW_Supplement_pauli
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T05:48:22.581201+00:00
-- url     : https://prove2.me/theorems/b12cc488-f71b-4e43-86ad-525e2fe6a6ce
-- title:
--   Pauli operators $P(x,z)=i^{x\cdot z}X(x)Z(z)$, the symplectic form $\omega$, $h=g\omega$, stabilizer matrices, syndrome projectors $\Pi(g,s)$, $H=-\sum_iP(g_i)$ and the Gibbs state $\rho_\beta$
-- statement:
--   Operators on $n$ qubits are complex matrices indexed by the computational basis strings $b\in\{0,1\}^n$ of $(\mathbb C^2)^{\otimes n}$.
--
--   1. For $x,z\in\{0,1\}^n$, $X(x)=\prod_iX_i^{x_i}$ maps $|b\rangle$ to $|b+x\rangle$, and $Z(z)=\prod_iZ_i^{z_i}$ maps $|b\rangle$ to $(-1)^{z\cdot b}|b\rangle$. The **Pauli operator** of $p=(x,z)\in\{0,1\}^{2n}$ is
--   $$P(p)=i^{x\cdot z}\,X(x)Z(z),$$
--   the Hermitian representative of $P(p)\propto X(x)Z(z)$; on one qubit $P(0,0)=1$, $P(1,0)=X$, $P(0,1)=Z$, $P(1,1)=Y$.
--   2. The **symplectic form** is $\omega=\begin{pmatrix}0&1_n\\1_n&0\end{pmatrix}$ over $\mathbb F_2$, and for a matrix $g\in\{0,1\}^{c\times 2n}$ the classical parity check matrix is $h=g\omega$, so $(hy)_i=1$ exactly when $P(y)$ anticommutes with $P(g_i)$.
--   3. $g$ is a **stabilizer matrix** if $P(g_1),\dots,P(g_c)$ pairwise commute and the group $\mathcal S$ they generate does not contain $-I$, equivalently the code space $\{\psi: P(g_i)\psi=\psi\ \forall i\}$ is nonzero.
--   4. For $s\in\{0,1\}^c$ the **syndrome projector** is $\Pi(g,s)=\prod_i\tfrac12\big(1+(-1)^{s_i}P(g_i)\big)$, the projector onto $\{\psi: P(g_i)\psi=(-1)^{s_i}\psi\ \forall i\}$; the **syndrome set** is $S_g=\mathrm{col}(h)$.
--   5. The **stabilizer Hamiltonian** is $H=-\sum_{i\in[c]}P(g_i)$ and its **Gibbs state** is
--   $$\rho_\beta=\frac{e^{-\beta H}}{\operatorname{tr}e^{-\beta H}}.$$
--
--   These objects state Theorem 4, the convergence of the quantum code Gibbs sampler (Algorithm 1) to $\rho_\beta$.
--
--   **Formalization Note** $X(x)$ and $Z(z)$ are the published `GoodQLTC.pauliX` and `GoodQLTC.pauliZ`, with the same conventions. Basis strings are `Fin n → ZMod 2`; strings in $\{0,1\}^{2n}$ are `Fin (n + n) → ZMod 2`, with the $X$-part in the first $n$ coordinates. $x\cdot z$ is computed in $\mathbb N$. The condition $-I\notin\mathcal S$ is stated as a nonzero common $+1$ eigenvector, which is equivalent for commuting Hermitian Paulis. For a stabilizer matrix the product formula for $\Pi(g,s)$ equals the page's $\Pi(g,0)=2^{-(n-k)}\sum_{S\in\mathcal S}S$ and $\Pi(g,s)=E(s)\Pi(g,0)E(s)$. The matrix exponential is Mathlib's `NormedSpace.exp`.
-- source:
--   Hangleiter, Ju, Vazirani, Code Swendsen-Wang Dynamics, arXiv:2510.08446 (manuscript sha256 4e4abb5e…), §2.1.1, p.10; §2.1.2, eqs. (6)–(7), p.11; §2.2, pp.11–12

import Mathlib
import Definitions.Def_CodeSW_gibbs
import Definitions.Def_GoodQLTC_pauliX

set_option autoImplicit false

open Matrix

noncomputable section

namespace CodeSW.Supplement

/-- Operators on `n` qubits: complex matrices indexed by computational-basis strings
`b ∈ {0,1}^n`, the basis of `(ℂ²)^{⊗n}` (Hangleiter, Ju, Vazirani, *Code Swendsen-Wang Dynamics*,
arXiv:2510.08446, manuscript sha256 4e4abb5e…, §2.1.1, p.10).

**Formalization Note** A basis string is `Fin n → ZMod 2`; a state vector is a function on basis
strings. -/
abbrev QOp (n : ℕ) : Type := Matrix (Fin n → ZMod 2) (Fin n → ZMod 2) ℂ

/-- The `X`-part `x ∈ {0,1}^n` of a symplectic string `p = (x, z) ∈ {0,1}^{2n}`: its first `n`
coordinates (arXiv:2510.08446, manuscript sha256 4e4abb5e…, §2.1.1, p.10).

**Formalization Note** `{0,1}^{2n}` is `Fin (n + n) → ZMod 2`; coordinate `i` of the `X`-part is
coordinate `Fin.castAdd n i`, and of the `Z`-part coordinate `Fin.natAdd n i`. -/
def xPart {n : ℕ} (p : Fin (n + n) → ZMod 2) : Fin n → ZMod 2 := fun i => p (Fin.castAdd n i)

/-- The `Z`-part `z ∈ {0,1}^n` of a symplectic string `p = (x, z) ∈ {0,1}^{2n}`: its last `n`
coordinates (arXiv:2510.08446, manuscript sha256 4e4abb5e…, §2.1.1, p.10). -/
def zPart {n : ℕ} (p : Fin (n + n) → ZMod 2) : Fin n → ZMod 2 := fun i => p (Fin.natAdd n i)

/-- The **Pauli operator** `P(p)` of a string `p = (x, z) ∈ {0,1}^{2n}`:
`P(p) = i^{x·z} X(x) Z(z)`, the Hermitian representative of `P(p) ∝ X(x)Z(z)`, so that
`P(0,0) = 1`, `P(1,0) = X`, `P(0,1) = Z`, `P(1,1) = Y` on one qubit
(arXiv:2510.08446, manuscript sha256 4e4abb5e…, §2.1.1, p.10).

**Formalization Note** `X(x)` (`|b⟩ ↦ |b + x⟩`) and `Z(z)` (`|b⟩ ↦ (−1)^{z·b}|b⟩`) are the
published `GoodQLTC.pauliX` and `GoodQLTC.pauliZ`. `x·z = ∑_i x_i z_i` is computed in `ℕ`. The phase
`i^{x·z}` is the one that makes `P(p)` Hermitian; the page fixes `P(p)` only up to a phase but lists `P(1,1) = Y`. -/
def pauli {n : ℕ} (p : Fin (n + n) → ZMod 2) : QOp n :=
  (Complex.I ^ (∑ i, (xPart p i).val * (zPart p i).val)) •
    (GoodQLTC.pauliX (xPart p) * GoodQLTC.pauliZ (zPart p))

/-- The **symplectic form** `ω = [[0, 1_n], [1_n, 0]] ∈ {0,1}^{2n×2n}`, with
`[P(x), P(y)] = 0 ⇔ ω(x, y) := xᵀωy = 0` (arXiv:2510.08446, manuscript sha256 4e4abb5e…, §2.1.1,
p.10). -/
def symplecticForm (n : ℕ) : Matrix (Fin (n + n)) (Fin (n + n)) (ZMod 2) :=
  Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks 0 1 1 0)

/-- The classical parity check matrix `h := gω ∈ {0,1}^{c×2n}` of a stabilizer matrix
`g ∈ {0,1}^{c×2n}`: `(hy)_i = ω(g_i, y)` is `1` exactly when `P(y)` anticommutes with `P(g_i)`
(arXiv:2510.08446, manuscript sha256 4e4abb5e…, §2.1.1, p.10; §2.2, p.12). -/
def checkMatrix {n c : ℕ} (g : Matrix (Fin c) (Fin (n + n)) (ZMod 2)) :
    Matrix (Fin c) (Fin (n + n)) (ZMod 2) :=
  g * symplecticForm n

/-- `g ∈ {0,1}^{c×2n}` is a **stabilizer matrix**: the Paulis `P(g_1), …, P(g_c)` pairwise
commute, and the group `S = ⟨P(g_1), …, P(g_c)⟩` they generate does not contain `−I`
(arXiv:2510.08446, manuscript sha256 4e4abb5e…, §2.1.1, p.10; §2.2, p.11, "the stabilizer code (of
dimension k)").

**Formalization Note** For pairwise commuting Hermitian Paulis, `−I ∉ S` is equivalent to the code
space `C_S = {ψ : P(g_i)ψ = ψ ∀ i}` being nonzero, which is how it is stated here. Rows of `g` may
be linearly dependent. -/
def IsStabilizerMatrix {n c : ℕ} (g : Matrix (Fin c) (Fin (n + n)) (ZMod 2)) : Prop :=
  (∀ i j, pauli (g i) * pauli (g j) = pauli (g j) * pauli (g i)) ∧
    ∃ ψ : (Fin n → ZMod 2) → ℂ, ψ ≠ 0 ∧ ∀ i, pauli (g i) *ᵥ ψ = ψ

/-- The **syndrome projector** `Π(g, s)` for `s ∈ {0,1}^c`: the projector onto the joint
eigenspace `{ψ : P(g_i)ψ = (−1)^{s_i} ψ ∀ i}`, here written as the product
`∏_i (1 + (−1)^{s_i} P(g_i))/2`. `Π(g, 0)` is the projector onto the code space
(arXiv:2510.08446, manuscript sha256 4e4abb5e…, §2.1.1, p.11).

**Formalization Note** For a stabilizer matrix the factors commute and are projectors, so the
product is the orthogonal projector onto the joint eigenspace; it equals the page's
`Π(g,0) = 2^{−(n−k)} ∑_{S∈S} S` and `Π(g,s) = E(s)Π(g,0)E(s)`. The product is taken in the order
`i = 0, 1, …, c − 1`. -/
def synProj {n c : ℕ} (g : Matrix (Fin c) (Fin (n + n)) (ZMod 2)) (s : Fin c → ZMod 2) : QOp n :=
  (List.ofFn fun i : Fin c => (1 / 2 : ℂ) • (1 + ((-1 : ℂ) ^ (s i).val) • pauli (g i))).prod

open Classical in
/-- The **syndrome set** `S_g = col(h)`, `h = gω`: the possible outcomes of measuring the Paulis
`P(g_1), …, P(g_c)` (arXiv:2510.08446, manuscript sha256 4e4abb5e…, §2.1.1, p.11).

**Formalization Note** `col(h)` is the range of `y ↦ hy` over `F₂ = ZMod 2`; it equals `col(g)`
since `ω` is invertible. -/
def syndromes {n c : ℕ} (g : Matrix (Fin c) (Fin (n + n)) (ZMod 2)) : Finset (Fin c → ZMod 2) :=
  Finset.univ.filter fun s => s ∈ LinearMap.range (checkMatrix g).mulVecLin

/-- The **stabilizer Hamiltonian** `H = −∑_{i∈[c]} P(g_i)` of eq. (6)
(arXiv:2510.08446, manuscript sha256 4e4abb5e…, §2.1.2, eq. (6), p.11). -/
def stabHamiltonian {n c : ℕ} (g : Matrix (Fin c) (Fin (n + n)) (ZMod 2)) : QOp n :=
  -∑ i, pauli (g i)

/-- The **quantum Gibbs state** `ρ_β = e^{−βH} / tr e^{−βH}` of eq. (7)
(arXiv:2510.08446, manuscript sha256 4e4abb5e…, §2.1.2, eq. (7), p.11).

**Formalization Note** `e^{−βH}` is Mathlib's matrix exponential `NormedSpace.exp`; the page's
`ρ_β ∝ e^{−βH}` is made an equality by the trace normalization. -/
def quantumGibbs {n c : ℕ} (g : Matrix (Fin c) (Fin (n + n)) (ZMod 2)) (β : ℝ) : QOp n :=
  ((NormedSpace.exp ((-(β : ℂ)) • stabHamiltonian g)).trace)⁻¹ •
    NormedSpace.exp ((-(β : ℂ)) • stabHamiltonian g)

end CodeSW.Supplement



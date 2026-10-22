-- Prove2me | Definitions.Def_QMCProduct_HalfApprox_Basic
-- name    : QMCProduct_HalfApprox_Basic
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-21T13:48:20.621747+00:00
-- url     : https://prove2.me/theorems/c290dce7-5082-4d9e-b47d-bd933c5695ea
-- title:
--   Definitions 1, 3, 4, 6, 12, eq. (1), pp. 6–8, 17, 20 — Pauli polynomials, pseudo-densities, strictly quadratic terms, the QMC Hamiltonian, edge values µ, v, s and the SWAP Gram matrix
-- statement:
--   A register of $n$ qubits has Pauli operators $X_i,Y_i,Z_i$ acting on qubit $i$. A Pauli string is a tensor product of $I,X,Y,Z$; its degree is the number of nonidentity factors. A degree-$k$ Pauli polynomial is a real linear combination of strings of degree at most $k$.
--
--   A **$k$-positive pseudo-density** $\widetilde\rho$ is Hermitian, has trace one, and satisfies
--   $$\operatorname{Tr}(\widetilde\rho P^2)\ge0$$
--   for every Pauli polynomial $P$ of degree at most $k$. Level $k$ of the quantum Lasserre hierarchy has value
--   $$\nu_k(H)=\max_{\widetilde\rho\in\widetilde D_n(k)}\operatorname{Tr}(H\widetilde\rho),$$
--   where $\widetilde D_n(k)$ is the set of $k$-positive pseudo-densities (equation (1)); an **optimal level-$k$ solution** is a $k$-positive pseudo-density attaining this maximum. Algorithm 4 uses $k=2$.
--
--   For an undirected weighted graph $G=(V,E)$ with $w_{ij}\ge0$ on its edges, the Quantum Max Cut Hamiltonian is
--   $$H=\sum_{\{i,j\}\in E}w_{ij}H_{ij},\qquad H_{ij}=\frac{I-X_iX_j-Y_iY_j-Z_iZ_j}{4}.$$
--   Each edge occurs once. With $\langle A\rangle=\operatorname{Tr}(\widetilde\rho A)$, the edge quantities are
--   $$\mu_{ij}=\frac{1-\langle X_iX_j\rangle-\langle Y_iY_j\rangle-\langle Z_iZ_j\rangle}{4},\quad v_{ij}=-\frac{\langle X_iX_j\rangle+\langle Y_iY_j\rangle+\langle Z_iZ_j\rangle}{3},\quad s_{ij}=\frac{1+\langle X_iX_j\rangle+\langle Y_iY_j\rangle+\langle Z_iZ_j\rangle}{2}.$$
--   A **strictly quadratic local term** (Definition 3) on an edge $ij$ is $c(I)\,I+\sum_{\tau,\sigma\in\{X,Y,Z\}}c(\tau\sigma)\,\tau_i\sigma_j$ with real coefficients; $H_{ij}$ above is the case $c(I)=1/4$, $c(\tau\tau)=-1/4$, $c(\tau\sigma)=0$ for $\tau\ne\sigma$. The file also defines the symmetric $4\times4$ SWAP Gram matrix from Section 4.3, with diagonal one and off-diagonal entries $p,q,r,(p+q+r-1)/2$.
--
--   These objects are the common model for the approximation statement and its edge and monogamy lemmas.
--
--   **Formalization Note** Vertices are `Fin n`, corresponding to the paper's $1,\ldots,n$; the register basis is `Fin n → Bool`. The real part of a trace is used for Hermitian expressions. The two directions of each undirected edge share one Hamiltonian term.
-- source:
--   Parekh & Thompson, An Optimal Product-State Approximation for 2-Local Quantum Hamiltonians with Positive Terms, arXiv:2206.08342v2, pp. 6–8, 13, 17, 20, Definitions 1, 3, 4, 6, 12, equation (1) and Section 4.3

import Definitions.Def_QAlgorithms_Defs_Basic
import Definitions.Def_QAlgorithms_Defs_Gates
import Definitions.Def_QAlgorithms_Defs_BinaryStabilizer
import Definitions.Def_QAlgorithms_Defs_Information
import Mathlib

set_option autoImplicit false

namespace QMCProduct.HalfApprox

abbrev Op (n : ℕ) := Matrix (QAlgorithms.Qubits n) (QAlgorithms.Qubits n) ℂ
abbrev PauliString (n : ℕ) := Fin n → Fin 4

/-- A single-qubit Pauli, with 0 coding the identity. Definition 1, p. 6. -/
def pauli1 (a : Fin 4) : Matrix Bool Bool ℂ :=
  if a = 0 then 1 else if a = 1 then QAlgorithms.pauliX
  else if a = 2 then QAlgorithms.pauliY else QAlgorithms.pauliZ

/-- A Pauli monomial, Definition 1, p. 6. -/
def pauliOp {n : ℕ} (s : PauliString n) : Op n :=
  QAlgorithms.kronAll (fun i => pauli1 (s i))

def pauliDegree {n : ℕ} (s : PauliString n) : ℕ :=
  (Finset.univ.filter (fun i => s i ≠ 0)).card

/-- All real linear combinations of Pauli monomials of degree at most k. -/
def IsPauliPoly {n : ℕ} (k : ℕ) (P : Op n) : Prop :=
  ∃ c : PauliString n → ℝ,
    (∀ s, c s ≠ 0 → pauliDegree s ≤ k) ∧
    P = ∑ s, (c s : ℂ) • pauliOp s

/-- Definition 6, p. 8. The positivity test ranges over every degree-k Pauli polynomial. -/
def IsPseudoDensity {n : ℕ} (k : ℕ) (ρt : Op n) : Prop :=
  ρt.IsHermitian ∧ ρt.trace = 1 ∧
    ∀ P : Op n, IsPauliPoly k P → 0 ≤ (ρt * P * P).trace.re

/-- Equation (1), p. 8: `ρt` attains the level-k value `νk(H)`, the maximum of `Tr[H σt]`
over k-positive pseudo-densities. -/
def IsOptimalLk {n : ℕ} (k : ℕ) (H ρt : Op n) : Prop :=
  IsPseudoDensity k ρt ∧
    ∀ σt : Op n, IsPseudoDensity k σt → (H * σt).trace.re ≤ (H * ρt).trace.re

/-- Equation (1), p. 8, at the second level (Algorithm 4, step 1). -/
def IsOptimalL2 {n : ℕ} (H ρt : Op n) : Prop := IsOptimalLk 2 H ρt

/-- The Pauli `A` acting on site `i`, p. 6. -/
def onSite {n : ℕ} (i : Fin n) (A : Matrix Bool Bool ℂ) : Op n :=
  QAlgorithms.kronAll (fun q => if q = i then A else 1)

def X {n : ℕ} (i : Fin n) : Op n := onSite i QAlgorithms.pauliX
def Y {n : ℕ} (i : Fin n) : Op n := onSite i QAlgorithms.pauliY
def Z {n : ℕ} (i : Fin n) : Op n := onSite i QAlgorithms.pauliZ

/-- Definition 4, p. 7: one QMC edge Hamiltonian. -/
noncomputable def hQMC {n : ℕ} (i j : Fin n) : Op n :=
  (1 / 4 : ℂ) • (1 - X i * X j - Y i * Y j - Z i * Z j)

/-- Definition 3, p. 7: a strictly quadratic local term
`c(I) • I + ∑_{τ,σ ∈ {X,Y,Z}} c(τσ) • τ_i σ_j`; `a, b : Fin 3` code `X, Y, Z` as `0, 1, 2`. -/
noncomputable def sqTerm {n : ℕ} (c0 : ℝ) (c : Fin 3 → Fin 3 → ℝ) (i j : Fin n) : Op n :=
  (c0 : ℂ) • 1 + ∑ a : Fin 3, ∑ b : Fin 3,
    (c a b : ℂ) • (onSite i (pauli1 a.succ) * onSite j (pauli1 b.succ))

/-- Each undirected edge is included exactly once, with the smaller endpoint first. -/
noncomputable def edges {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] :
    Finset (Fin n × Fin n) :=
  Finset.univ.filter (fun e => e.1 < e.2 ∧ G.Adj e.1 e.2)

/-- The weighted QMC Hamiltonian of §3.2.2, p. 13. -/
noncomputable def qmcHamiltonian {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (w : Fin n → Fin n → ℝ) : Op n :=
  ∑ e ∈ edges G, (w e.1 e.2 : ℂ) • hQMC e.1 e.2

noncomputable def val {n : ℕ} (ρt φ : Op n) : ℝ := (ρt * φ).trace.re

/-- Definition 12, p. 17. -/
noncomputable def mu {n : ℕ} (ρt : Op n) (i j : Fin n) : ℝ :=
  (1 - val ρt (X i * X j) - val ρt (Y i * Y j) - val ρt (Z i * Z j)) / 4

/-- Definition 12, p. 17; the minus sign applies to all three Pauli correlations. -/
noncomputable def v {n : ℕ} (ρt : Op n) (i j : Fin n) : ℝ :=
  -(val ρt (X i * X j) + val ρt (Y i * Y j) + val ρt (Z i * Z j)) / 3

/-- Definition 12, p. 17; the relaxed SWAP value. -/
noncomputable def s {n : ℕ} (ρt : Op n) (i j : Fin n) : ℝ :=
  (1 + val ρt (X i * X j) + val ρt (Y i * Y j) + val ρt (Z i * Z j)) / 2

/-- The 4 by 4 SWAP Gram matrix displayed on p. 20. -/
noncomputable def swapGram (p q r : ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  let t := (p + q + r - 1) / 2
  Matrix.of fun i j =>
    if i = j then 1
    else if i = 0 then if j = 1 then p else if j = 2 then q else r
    else if j = 0 then if i = 1 then p else if i = 2 then q else r
    else t

end QMCProduct.HalfApprox



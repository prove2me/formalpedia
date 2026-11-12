-- Prove2me | Definitions.Def_ImpuritySim_Fermion
-- name    : ImpuritySim_Fermion
-- status  : Definition
-- author  : @iris
-- created : 2026-11-11T08:28:14.626713+00:00
-- url     : https://prove2.me/theorems/923cd62f-8481-445b-b917-559a38fc786e
-- title:
--   Fermionic modes: Majoranas $\gamma_j$, ladder operators $a_j$, $a(\mu)$, $\Phi(P)$, $n_i$, $\Gamma_A$, density matrices, ground energy and ground states
-- statement:
--   On $n$ fermionic modes the Hilbert space is $(\mathbb C^2)^{\otimes n}$ with computational (Fock) basis $\{|x\rangle : x\in\{0,1\}^n\}$. The **Majorana operators** are the Jordan–Wigner generators (2.4)
--   $$\gamma_{2k-1}=Z_1\cdots Z_{k-1}X_k,\qquad \gamma_{2k}=Z_1\cdots Z_{k-1}Y_k,$$
--   which satisfy $\{\gamma_j,\gamma_k\}=2\delta_{jk}I$. The **annihilation operators** are $a_j=(\gamma_{2j-1}+i\gamma_{2j})/2$, i.e. $a_j=Z_1\otimes\cdots\otimes Z_{j-1}\otimes\begin{pmatrix}0&1\\0&0\end{pmatrix}$ (2.2), and $a_j^\dagger$ are the creation operators; they satisfy the canonical anticommutation relations (2.1). For $\mu\in\mathbb C^n$ and an $n\times n$ matrix $P$,
--   $$a(\mu)=\sum_{j=1}^n\mu_ja_j\quad(2.7),\qquad \Phi(P)=\sum_{j,k}\langle e_j,Pe_k\rangle\,a_k^\dagger a_j\quad(2.9),\qquad n_i=a_i^\dagger a_i\quad(4.1).$$
--   For a set $A$ of Majorana indices, $\Gamma_A=i^{|A|(|A|-1)/2}\prod^{\nearrow}_{p\in A}\gamma_p$ (increasing order) is the Hermitian Majorana monomial.
--
--   The file also fixes: the **spectral norm** $\|M\|$ (largest singular value); **density matrices** (positive semidefinite, trace one); the **ground energy** of a square matrix as the Rayleigh infimum
--   $$\lambda_{\min}(M)=\inf_{v\neq0}\frac{\operatorname{Re}\langle v,Mv\rangle}{\langle v,v\rangle},$$
--   which is the least eigenvalue for Hermitian $M$; **ground states** (density matrices $\rho$ with $M\rho=\lambda_{\min}(M)\rho$, pure or mixed); the projector $P_S$ onto $\mathcal H_S=\operatorname{span}\{|x\rangle:x\in S\}$; and the restriction $H_S$ with entries $(H_S)_{x,y}=\langle x|H|y\rangle$, $x,y\in S$.
--
--   These are the operators every statement of the mission is written in.
--
--   **Formalization Note** The Majoranas are the published `FermiCap.Gaussian.majorana n p`, $p\in\{0,\dots,2n-1\}$: the page's $\gamma_j$ is index $j-1$, and modes are $0,\dots,n-1$. The annihilation operators are the published `GaussTesting.annihilator` and the occupation numbers the published `FermiHubbardMix.numOp` (same conventions); this file adds $a(\mu)$, $\Phi(P)$, $\Gamma_A$ and the matrix notions below. The spectral norm is Mathlib's $L^2$ operator norm on Euclidean space. On an empty index type the Rayleigh infimum would be $0$; every index type used (Fock configurations, threshold sets containing $0$) is nonempty.
-- source:
--   Jiang–Ju–Parekh–Rayudu–Zhao, Polynomial-time classical and quantum simulation of quantum impurity models, arXiv:2610.02167 (held version, sha256 88d2a4e6…f0fff9b2), (1.1) and Jordan–Wigner remark, p.4; (2.1)–(2.4), p.10; Fock basis and (2.7), p.11; (2.9), p.12; (4.1), p.20; H_S, p.27

import Mathlib
import Definitions.Def_FermiCap_Gaussian_Majorana
import Definitions.Def_GaussTesting_annihilator
import Definitions.Def_FermiHubbardMix_parityOp

open scoped Matrix.Norms.L2Operator ComplexOrder
open Matrix

namespace ImpuritySim

/-!
# Fermionic operators on `n` modes, density matrices and ground energy

J. Jiang, N. Ju, O. Parekh, C. Rayudu, A. Zhao, *Polynomial-time classical and quantum simulation
of quantum impurity models*, arXiv:2610.02167 (held version, sha256 88d2a4e6…f0fff9b2):
(1.1) and the Jordan–Wigner remark, p.4; (2.1)–(2.4), p.10; Fock basis and (2.7), p.11; (2.9),
p.12; (4.1), p.20; the ground state of §2.2, p.12; `H_S` in the proof of Theorem 5.3, p.27.

**Formalization Note.**
* The Majoranas are the published Jordan–Wigner generators `FermiCap.Gaussian.majorana n p`,
  `p : Fin (2n)`, 0-based: the page's `γ_j` is `gamma n ⟨j − 1, _⟩`, so `γ_{2k−1} = Z⋯Z X_k` is
  `gamma n ⟨2(k−1), _⟩` and `γ_{2k} = Z⋯Z Y_k` is `gamma n ⟨2(k−1)+1, _⟩` (2.4).
* The annihilation operator `a_j = (γ_{2j−1} + iγ_{2j})/2` (p.4), which under Jordan–Wigner is
  (2.2), `Z ⊗ ⋯ ⊗ Z ⊗ [[0,1],[0,0]]`, is the published `GaussTesting.annihilator n j` (modes `Fin n`,
  0-based); the creation operator is its conjugate transpose. The occupation number operator
  `n_i = a_i† a_i` (4.1) is the published `FermiHubbardMix.numOp n i`.
* `annVec n μ = a(μ) = Σ_j μ_j a_j` (2.7) is linear in `μ`; `Phi n P = Σ_{j,k} ⟨e_j, P e_k⟩ a_k† a_j`
  (2.9), with `⟨e_j, P e_k⟩ = P j k`.
* Fock configurations are `Qubits n = Fin n → Fin 2`; `|x⟩` is the standard basis vector of `x`
  (p.11: Fock states are computational basis states under Jordan–Wigner).
* `majMono n A = Γ_A = i^{|A|(|A|−1)/2} ∏↗_{p ∈ A} γ_p`, the product in increasing order; it is
  Hermitian.
* `specNorm` is the spectral norm (Mathlib's `L2` operator norm, `Matrix.Norms.L2Operator`), not
  the entrywise sup norm.
* `groundEnergy M = inf_{v ≠ 0} Re⟨v, Mv⟩ / ⟨v, v⟩`, the Rayleigh infimum; for Hermitian `M` on a
  nonempty index type it is the least eigenvalue `λ_min(M)`. (On an empty index type it would be
  `sInf ∅ = 0`; the index types used, `Qubits n` and threshold sets containing `0`, are nonempty.)
* `IsGroundState M ρ`: `ρ` is a density matrix with `Mρ = λ_min(M) ρ`, i.e. supported on the
  ground space; this covers pure and mixed ground states.
-/

open FermiCap.Gaussian

/-- The spectral norm of a square matrix: the operator norm on Euclidean space (largest singular
value). -/
noncomputable def specNorm {𝕜 : Type*} [RCLike 𝕜] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι 𝕜) : ℝ :=
  ‖M‖

/-- The Majorana operator `γ_{p+1}`, `p : Fin (2n)` (0-based), the Jordan–Wigner generator (2.4). -/
noncomputable def gamma (n : ℕ) (p : Fin (2 * n)) : Op n := majorana n p

/-- `a(μ) = Σ_j μ_j a_j` (2.7). -/
noncomputable def annVec (n : ℕ) (μ : Fin n → ℂ) : Op n :=
  ∑ j, μ j • GaussTesting.annihilator n j

/-- The quadratic Hamiltonian `Φ(P) = Σ_{j,k} ⟨e_j, P e_k⟩ a_k† a_j` (2.9). -/
noncomputable def Phi (n : ℕ) (P : Matrix (Fin n) (Fin n) ℂ) : Op n :=
  ∑ j, ∑ k, P j k • ((GaussTesting.annihilator n k)ᴴ * GaussTesting.annihilator n j)

/-- The Hermitian Majorana monomial `Γ_A = i^{|A|(|A|−1)/2} ∏↗_{p ∈ A} γ_p` (increasing order). -/
noncomputable def majMono (n : ℕ) (A : Finset (Fin (2 * n))) : Op n :=
  (Complex.I ^ (A.card * (A.card - 1) / 2)) • ((A.sort (· ≤ ·)).map (gamma n)).prod

/-- A density matrix: positive semidefinite with unit trace. -/
def IsDensity {ι : Type*} [Fintype ι] (ρ : Matrix ι ι ℂ) : Prop :=
  ρ.PosSemidef ∧ ρ.trace = 1

/-- The ground energy as the Rayleigh infimum `inf_{v ≠ 0} Re⟨v, Mv⟩ / ⟨v, v⟩`; for Hermitian `M`
this is `λ_min(M)`. -/
noncomputable def groundEnergy {ι : Type*} [Fintype ι] (M : Matrix ι ι ℂ) : ℝ :=
  ⨅ v : {v : ι → ℂ // v ≠ 0}, (star v.1 ⬝ᵥ (M *ᵥ v.1)).re / (star v.1 ⬝ᵥ v.1).re

/-- `ρ` is a (pure or mixed) ground state of `M`: a density matrix with `M ρ = λ_min(M) ρ`. -/
def IsGroundState {ι : Type*} [Fintype ι] (M : Matrix ι ι ℂ) (ρ : Matrix ι ι ℂ) : Prop :=
  IsDensity ρ ∧ M * ρ = ((groundEnergy M : ℝ) : ℂ) • ρ

/-- The projector `P_S` onto `H_S = span{|x⟩ : x ∈ S}`: the diagonal `0/1` matrix of `S`. -/
noncomputable def projS {n : ℕ} (S : Finset (Qubits n)) : Op n :=
  Matrix.diagonal fun x => if x ∈ S then 1 else 0

/-- The restriction `H_S` of `M` to `H_S`, `(H_S)_{x,y} = ⟨x|M|y⟩` for `x, y ∈ S` (p.27). -/
def restrictTo {n : ℕ} (M : Op n) (S : Finset (Qubits n)) : Matrix S S ℂ :=
  M.submatrix (fun x => (x : Qubits n)) (fun x => (x : Qubits n))

end ImpuritySim



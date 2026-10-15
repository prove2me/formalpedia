-- Prove2me | Definitions.Def_QReversal_NearOpt_Setting
-- name    : QReversal_NearOpt_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-15T06:41:30.641981+00:00
-- url     : https://prove2.me/theorems/78439232-66f0-4f29-a3a1-55ec8988a0bc
-- title:
--   §II–§IV — trace-preserving Kraus families, composite maps, the generalized inverse square root, the reversal operation (12), and the fidelities (8)–(10)
-- statement:
--   Fix a finite-dimensional system with orthonormal basis indexed by a finite set $n$; operators are complex $n\times n$ matrices and $X^\dagger$ is the conjugate transpose. A completely positive map is given by a finite **decomposition** $\mathcal A\sim\{A_i\}_i$ and acts by $\mathcal A(X)=\sum_i A_iXA_i^\dagger$ (the published map `krausUpdate`). This module defines:
--
--   1. **Trace preservation** $\sum_i A_i^\dagger A_i=I$ and **trace non-increase** $\sum_i A_i^\dagger A_i\le I$ (Loewner order).
--   2. The **composite** $\mathcal R\mathcal A$ of $\mathcal R\sim\{R_k\}_k$ after $\mathcal A\sim\{A_i\}_i$, with decomposition $\{R_kA_i\}_{(k,i)}$.
--   3. The **generalized inverse square root** $X^{-1/2}$ of a Hermitian matrix, which replaces each eigenvalue $x>0$ by $x^{-1/2}$ and keeps every zero eigenvalue at $0$, and the **support projector** $P_C$ of $\rho$ (eigenvalue $0\mapsto0$, non-zero $\mapsto1$).
--   4. The **reversal operation** of $\mathcal A$ with respect to a state $\rho$,
--   $$
--   \mathcal R_{\mathcal A,\rho}\sim\{\rho^{1/2}A_i^\dagger\,\mathcal A(\rho)^{-1/2}\}_i .
--   $$
--   5. The **entanglement fidelity** $F_e(\rho,\mathcal K)=\sum_k|\operatorname{tr}K_k\rho|^2$ of a map $\mathcal K\sim\{K_k\}_k$, and the **average entanglement fidelity** $\bar F_e(E,\mathcal K)=\sum_l p_lF_e(\rho_l,\mathcal K)$ of an ensemble $E=\{p_l,\rho_l\}_l$.
--   6. A **commuting ensemble**: weights $p_l\ge0$ with $\sum_lp_l=1$, density matrices $\rho_l$ (positive semidefinite, unit trace), pairwise commuting; its average state $\rho=\sum_lp_l\rho_l$.
--   7. For an orthonormal basis $|i\rangle$ and weights $p_i$, the **classical fidelity** $F_{\mathrm{cl}}(\rho,\mathcal K)=\sum_ip_i\langle i|\mathcal K(|i\rangle\langle i|)|i\rangle$.
--
--   These are the objects in which the near-optimality of the reversal operation (Theorem 3, Corollary 4) is stated; the generalized inverse square root $X^{-1/2}$ is also the one used in the pretty-good-measurement bound (36)–(42) and Theorem 5 of the companion mission.
--
--   **Formalization Note** Maps are unbundled Kraus families over finite index types; no completeness proof is stored in them, and the hypotheses of each theorem say which families are trace-preserving. The entanglement fidelity is defined by the formula (8), which the paper derives from its purification definition $\|P_0|\Psi_f\rangle\|^2$; the platform's `WildeQIT.entanglementFidelity` is the same quantity for bundled channels but is not used, because the reversal and composite families carry no bundled completeness proof. $X^{-1/2}$ is the continuous functional calculus applied to $x\mapsto(\sqrt x)^{-1}$, whose value at $0$ is $0$, never the matrix inverse. The reversal family uses the matrix square root $\rho^{1/2}$ and is meant for a positive semidefinite $\rho$ and the positive semidefinite $\mathcal A(\rho)$; the theorems that use it state the paper's assumption that $\mathcal A(\rho)$ has full support (p. 7). In $F_{\mathrm{cl}}$ the weights $p$ and the basis $e$ are free arguments; each theorem ties them to $\rho=\sum_ip_i|i\rangle\langle i|$. The classical fidelity takes the real part of $\langle i|\mathcal K(|i\rangle\langle i|)|i\rangle$, which is real.
-- source:
--   Barnum, Knill, Reversing quantum dynamics with near-optimal quantum and classical fidelity, arXiv:quant-ph/0004088v2, pp. 2–3 (§II), p. 5 (8)–(10), pp. 6–7 (12) and the generalized inverse (p. 7)

import Mathlib
import Definitions.Def_PeresTerno_kraus_basics

open Matrix PeresTerno
open scoped MatrixOrder ComplexOrder

namespace QReversal.NearOpt

/-- §II, p. 3: a Kraus family `A ∼ {A_i}_i` is trace-preserving when `∑_i A_i† A_i = I`. -/
def IsTracePreserving {n ι : Type*} [Fintype n] [DecidableEq n] [Fintype ι]
    (A : ι → Matrix n n ℂ) : Prop :=
  ∑ i, (A i)ᴴ * A i = 1

/-- §II, p. 3: a Kraus family is trace-nonincreasing when `∑_i A_i† A_i ≤ I` (Loewner order). -/
def IsTraceNonincreasing {n ι : Type*} [Fintype n] [DecidableEq n] [Fintype ι]
    (A : ι → Matrix n n ℂ) : Prop :=
  ∑ i, (A i)ᴴ * A i ≤ 1

/-- The composite `RA` of `R ∼ {R_k}_k` after `A ∼ {A_i}_i`, with decomposition
`{R_k A_i}_{(k,i)}`. -/
def comp {n κ ι : Type*} [Fintype n] (R : κ → Matrix n n ℂ) (A : ι → Matrix n n ℂ) :
    κ × ι → Matrix n n ℂ :=
  fun ki => R ki.1 * A ki.2

/-- p. 7: the generalized inverse square root `X^{-1/2}`, obtained by inverting the non-zero
eigenvalues of `X^{1/2}` in an eigenbasis and keeping the zero eigenvalues (`(√0)⁻¹ = 0`). -/
noncomputable def invSqrt {n : Type*} [Fintype n] [DecidableEq n] (X : Matrix n n ℂ) :
    Matrix n n ℂ :=
  cfc (fun x : ℝ => (Real.sqrt x)⁻¹) X

/-- The projector `P_C` onto the support of `ρ` (p. 7): eigenvalue `0 ↦ 0`, nonzero `↦ 1`. -/
noncomputable def supportProj {n : Type*} [Fintype n] [DecidableEq n] (ρ : Matrix n n ℂ) :
    Matrix n n ℂ :=
  cfc (fun x : ℝ => if x = 0 then (0 : ℝ) else 1) ρ

/-- (12), p. 6: the reversal operation `R_{A,ρ} ∼ {ρ^{1/2} A_i† A(ρ)^{-1/2}}_i`. -/
noncomputable def reversal {n ι : Type*} [Fintype n] [DecidableEq n] [Fintype ι]
    (A : ι → Matrix n n ℂ) (ρ : Matrix n n ℂ) : ι → Matrix n n ℂ :=
  fun i => CFC.sqrt ρ * (A i)ᴴ * invSqrt (krausUpdate A ρ)

/-- (8), p. 5: the entanglement fidelity `F_e(ρ, K) = ∑_k |tr K_k ρ|²`. -/
noncomputable def Fe {n κ : Type*} [Fintype n] [Fintype κ]
    (ρ : Matrix n n ℂ) (K : κ → Matrix n n ℂ) : ℝ :=
  ∑ k, Complex.normSq (Matrix.trace (K k * ρ))

/-- (9), p. 5: the average entanglement fidelity `F̄_e(E, K) = ∑_l p_l F_e(ρ_l, K)` of the
ensemble `E = {p_l, ρ_l}_l`. -/
noncomputable def Fbar {n L κ : Type*} [Fintype n] [Fintype L] [Fintype κ]
    (p : L → ℝ) (ρs : L → Matrix n n ℂ) (K : κ → Matrix n n ℂ) : ℝ :=
  ∑ l, p l * Fe (ρs l) K

/-- Theorem 3, p. 7: `E = {p_l, ρ_l}_l` is an ensemble of commuting density matrices. -/
def IsCommutingEnsemble {n L : Type*} [Fintype n] [Fintype L]
    (p : L → ℝ) (ρs : L → Matrix n n ℂ) : Prop :=
  (∀ l, 0 ≤ p l) ∧ ∑ l, p l = 1 ∧ (∀ l, IsDensityMatrix (ρs l)) ∧
    ∀ l l', Commute (ρs l) (ρs l')

/-- The average state `ρ = ∑_l p_l ρ_l` of an ensemble. -/
noncomputable def avgState {n L : Type*} [Fintype L]
    (p : L → ℝ) (ρs : L → Matrix n n ℂ) : Matrix n n ℂ :=
  ∑ l, (p l : ℂ) • ρs l

/-- `e : n → (n → ℂ)` is an orthonormal basis of `ℂ^n`: `⟨e_i|e_j⟩` is `1` if `i = j` and `0` otherwise. -/
def IsOrthonormalBasis {n : Type*} [Fintype n] [DecidableEq n] (e : n → n → ℂ) : Prop :=
  ∀ i j, star (e i) ⬝ᵥ e j = if i = j then 1 else 0

/-- (10), p. 5: the classical fidelity `F_cl(ρ, K) = ∑_i p_i ⟨i| K(|i⟩⟨i|) |i⟩`, for the
eigenbasis `|i⟩ = e i` and eigenvalues `p_i` of `ρ = ∑_i p_i |i⟩⟨i|`. -/
noncomputable def Fcl {n κ : Type*} [Fintype n] [Fintype κ]
    (p : n → ℝ) (e : n → n → ℂ) (K : κ → Matrix n n ℂ) : ℝ :=
  ∑ i, p i * (star (e i) ⬝ᵥ (krausUpdate K (vecMulVec (e i) (star (e i))) *ᵥ e i)).re

end QReversal.NearOpt



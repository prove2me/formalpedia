-- Prove2me | Definitions.Def_QuarticGauss390_EigenBound_CAR
-- name    : QuarticGauss390_EigenBound_CAR
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T10:36:02.072766+00:00
-- url     : https://prove2.me/theorems/e48ae915-c0cf-49f8-bbec-e558000f19a5
-- title:
--   eq. (1.1)–(1.4) — CAR system, Majorana monomials, homogeneous quartic $H$, $\tau$, $\sigma$, density matrices, $\lambda_{\max}$, $[X]_k$
-- statement:
--   A system of $n$ fermionic modes has $d=2n$ **Majorana operators** $c_1,\dots,c_d$ acting on a Hilbert space $\mathcal H$ of dimension $2^n$, satisfying the canonical anticommutation relations
--   $$c_i^\dagger=c_i,\qquad c_ic_j+c_jc_i=2\delta_{ij}I_{\mathcal H}.$$
--   Any such family is admissible; no particular (e.g. Jordan–Wigner) representation is fixed.
--
--   For $S=\{s_1<\dots<s_k\}\subseteq[d]$ the ordered monomial is $c_S=c_{s_1}\cdots c_{s_k}$, with $c_\emptyset=I$. A **homogeneous quartic Hamiltonian** with real coefficients $w_S$ is
--   $$H=\sum_{S\subseteq[d],\ |S|=4}w_S\,c_S.$$
--
--   The **normalized trace** is $\tau[A]=2^{-n}\operatorname{Tr}[A]$ and the **normalized Frobenius norm** of $H$ is $\sigma=\sqrt{\tau[H^2]}$. A **density matrix** is a positive semidefinite operator of unit trace, a **state** $|\psi\rangle$ is a unit vector, $\langle A\rangle_\rho=\operatorname{Tr}[\rho A]$, and the top eigenvalue is
--   $$\lambda_{\max}(H)=\max_{\rho}\langle H\rangle_\rho,$$
--   the maximum over density matrices. Finally $[X]_k=\sum_{|S|=k}\tau[c_S^\dagger X]\,c_S$ is the degree-$k$ part of the Majorana expansion of $X$.
--
--   These objects are the model of the whole mission: every statement quantifies over every CAR system on a $2^n$-dimensional space and every real coefficient vector.
--
--   **Formalization Note.** $\mathcal H$ is indexed by bit strings `Fin n → Fin 2`; Majoranas are indexed by `Fin (2n)` (paper index $i$ is Lean index $i-1$). Coefficients are a function on all subsets, of which only the 4-element ones enter $H$. $\lambda_{\max}$ is the supremum of $\operatorname{Re}\operatorname{Tr}[\rho H]$ over density matrices (the set is nonempty and bounded, and for Hermitian $H$ the value is the largest eigenvalue); $\sigma$ uses the real part of $\tau[H^2]$, which is real and nonnegative for Hermitian $H$.
-- source:
--   Ojas Parekh, Improved classical optimization of fermionic Hamiltonians beyond Gaussian states, STOC 2027 submission #390 (October 2026), source.pdf SHA-256 9018757e184cce1091160d8b5847294a0e6c16cc09386b1f2b6bb000f7542101, p.2, eq. (1.1), (1.2), (1.4); p.5–6, §2 preamble and §2.1 ([X]_k)

import Mathlib

open Matrix
open scoped ComplexOrder

namespace QuarticGauss390.EigenBound

/-- Basis labels of the `2^n`-dimensional Hilbert space `𝓗`: bit strings of length `n`. -/
abbrev Basis (n : ℕ) := Fin n → Fin 2

/-- Operators on `𝓗` (complex `2^n × 2^n` matrices). -/
abbrev Op (n : ℕ) := Matrix (Basis n) (Basis n) ℂ

/-- Vectors of `𝓗` (not necessarily normalized). -/
abbrev Vec (n : ℕ) := Basis n → ℂ

/-- eq. (1.1), p.2: `d = 2n` Majorana operators `c_0, …, c_{2n-1}` on the `2^n`-dimensional
space `𝓗`, Hermitian and satisfying `c_i c_j + c_j c_i = 2 δ_ij I`. Every such family is allowed
(no fixed Jordan–Wigner choice). Paper index `i` is Lean index `i - 1`. -/
structure CAR (n : ℕ) where
  c : Fin (2 * n) → Op n
  herm : ∀ i, (c i).IsHermitian
  anticomm : ∀ i j, c i * c j + c j * c i = if i = j then (2 : ℂ) • (1 : Op n) else 0

/-- Ordered Majorana monomial `c_S = c_{s_1} ⋯ c_{s_k}` with `s_1 < ⋯ < s_k` (p.2);
`c_∅ = I`. -/
noncomputable def monomial {n : ℕ} (C : CAR n) (S : Finset (Fin (2 * n))) : Op n :=
  ((S.sort (· ≤ ·)).map C.c).prod

/-- eq. (1.2), p.2: the homogeneous quartic Hamiltonian `H = ∑_{|S| = 4} w_S c_S` with real
coefficients. Values of `w` on sets of size other than 4 are ignored. -/
noncomputable def quartic {n : ℕ} (C : CAR n) (w : Finset (Fin (2 * n)) → ℝ) : Op n :=
  ∑ S ∈ Finset.powersetCard 4 (Finset.univ : Finset (Fin (2 * n))), (w S : ℂ) • monomial C S

/-- eq. (1.4), p.2: normalized trace `τ[A] = 2^{-n} Tr[A]`. -/
noncomputable def normTrace (n : ℕ) (A : Op n) : ℂ := ((2 : ℂ) ^ n)⁻¹ * A.trace

/-- eq. (1.4), p.2: normalized Frobenius norm `σ = √(τ[H²])` (real part taken; `τ[H²]` is
real and nonnegative for Hermitian `H`). -/
noncomputable def sigma (n : ℕ) (H : Op n) : ℝ := Real.sqrt (normTrace n (H * H)).re

/-- A density matrix: positive semidefinite with unit trace. -/
def IsDensity {n : ℕ} (ρ : Op n) : Prop := ρ.PosSemidef ∧ ρ.trace = 1

/-- A state `|ψ⟩`: a unit vector (§2 preamble, p.5). -/
def IsState {n : ℕ} (ψ : Vec n) : Prop := star ψ ⬝ᵥ ψ = 1

/-- `⟨A⟩_ρ = Tr[ρ A]` (p.2). -/
noncomputable def expect {n : ℕ} (ρ A : Op n) : ℂ := (ρ * A).trace

/-- `|ψ⟩⟨ψ|`. -/
def pureProj {n : ℕ} (ψ : Vec n) : Op n := vecMulVec ψ (star ψ)

/-- p.2: `λ_max(H) = max_ρ ⟨H⟩_ρ` over density matrices, as a supremum (real part taken). -/
noncomputable def lambdaMax {n : ℕ} (H : Op n) : ℝ :=
  sSup {e : ℝ | ∃ ρ : Op n, IsDensity ρ ∧ e = (expect ρ H).re}

/-- p.6: `[X]_k`, the degree-`k` part of the Majorana expansion of `X`,
`[X]_k = ∑_{|S| = k} τ[c_S† X] c_S` (the coefficients are those of the orthonormal
expansion (2.1)). -/
noncomputable def degPart {n : ℕ} (C : CAR n) (k : ℕ) (X : Op n) : Op n :=
  ∑ S ∈ Finset.powersetCard k (Finset.univ : Finset (Fin (2 * n))),
    normTrace n ((monomial C S)ᴴ * X) • monomial C S

end QuarticGauss390.EigenBound



-- Prove2me | Definitions.Def_RelDecoding_Supplement_majoranaGen
-- name    : RelDecoding_Supplement_majoranaGen
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T14:12:30.987114+00:00
-- url     : https://prove2.me/theorems/9f03c05b-0c6f-4426-a863-93a92c857f07
-- title:
--   Hermitian Majorana monomials $\Gamma(u)$ and signed Majorana generators
-- statement:
--   Let $\gamma_1,\dots,\gamma_{2n}$ be the Majorana operators of the full Fock space of $n$ fermionic modes, $\gamma_{2j-1}=f_j+f_j^*$, $\gamma_{2j}=i(f_j^*-f_j)$ (eq. (140)), which satisfy $\gamma_j^*=\gamma_j$ and $\{\gamma_j,\gamma_k\}=2\delta_{jk}I$.
--
--   1. For $u\in\mathbb F_2^{2n}$ the **Hermitian Majorana monomial** is
--   $$\Gamma(u)=i^{|u|(|u|-1)/2}\prod_{j=1}^{2n}\gamma_j^{u_j},$$
--   the product taken in increasing order (eq. (141)); it satisfies $\Gamma(u)^*=\Gamma(u)$, $\Gamma(u)^2=I$.
--   2. The **signed Majorana generators** are $a_i=\eta_i\Gamma(w_i)$ with $\eta_i\in\{\pm1\}$ (eq. (151)).
--
--   These are the marked terms of a parity-preserving fermionic Hamiltonian in the Majorana instance of relative decoding (§6.1).
--
--   **Formalization Note** The Majoranas are realized by the Jordan–Wigner matrices of eq. (167), $\gamma_{2j-1}=Z_1\cdots Z_{j-1}X_j$, $\gamma_{2j}=Z_1\cdots Z_{j-1}Y_j$: the published `FermiCap.Gaussian.majorana n p` with 0-based index $p=0,\dots,2n-1$ (so $\gamma_{p+1}$), on `Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ`. Every family satisfying the canonical anticommutation relations (136) on $\mathbb C^{2^n}$ is unitarily equivalent to this one.
-- source:
--   Shang, Stilck França, From Simple Sources to Quantum Advantage: Homomorphic Polynomial Transduction via Relative Decoding, arXiv:2609.35101 (held version, sha256 d2be7859…), eqs. (136), (140)–(141), p.33; eq. (151), p.35; eq. (167), p.36 (pdf_pages 33–36)

import Mathlib
import Definitions.Def_FermiCap_Gaussian_Majorana

set_option autoImplicit false

namespace RelDecoding.Supplement

open FermiCap.Gaussian

/-- The **Hermitian Majorana monomial** `Γ(u) := i^{|u|(|u|−1)/2} ∏_{j=1}^{2n} γ_j^{u_j}`, product in
increasing index order, for a label `u ∈ F₂^{2n}`. Shang, Stilck França, *From Simple Sources to
Quantum Advantage: Homomorphic Polynomial Transduction via Relative Decoding*, arXiv:2609.35101
(held version, sha256 d2be7859…), eq. (141), p.33 (also eq. (485), p.88).

**Formalization Note.** The Majoranas `γ₁, …, γ_{2n}` of the full Fock space of `n` modes are the
Jordan–Wigner matrices `γ_{2j−1} = Z₁⋯Z_{j−1}X_j`, `γ_{2j} = Z₁⋯Z_{j−1}Y_j` of eq. (167), p.36: the
published `FermiCap.Gaussian.majorana n p` for `p = 0, …, 2n − 1` (0-based, so `γ_{p+1}`), acting
on `Op n = Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ`. Every family satisfying the canonical
anticommutation relations (136) on `ℂ^{2^n}` is unitarily equivalent to this one. `|u|` is the
Hamming weight; `|u|(|u|−1)/2` is an exact natural-number quotient. -/
noncomputable def majoranaMonomial (n : ℕ) (u : Fin (2 * n) → ZMod 2) : Op n :=
  (Complex.I ^ (hammingNorm u * (hammingNorm u - 1) / 2)) •
    ((List.finRange (2 * n)).map fun j => majorana n j ^ (u j).val).prod

/-- The **signed Majorana generators** `aᵢ = ηᵢ Γ(wᵢ)`, `ηᵢ ∈ {±1}`. Eq. (151), p.35 (and eq. (486),
p.88). -/
noncomputable def majoranaGen {n s : ℕ} (η : Fin s → ℤˣ) (w : Fin s → Fin (2 * n) → ZMod 2) :
    Fin s → Op n :=
  fun i => (((η i : ℤ) : ℂ)) • majoranaMonomial n (w i)

end RelDecoding.Supplement



-- Prove2me | Definitions.Def_GapAgnosticGS_Supplement_LH
-- name    : GapAgnosticGS_Supplement_LH
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T07:29:42.594248+00:00
-- url     : https://prove2.me/theorems/110da3ad-92cc-43d3-b127-7394f913c5bb
-- title:
--   Warm-start complexity $L_H(\varepsilon,|\psi_0\rangle)$
-- statement:
--   Let $H=\sum_j E_j|\phi_j\rangle\langle\phi_j|$ be a Hermitian matrix on $\mathbb C^n$ with an orthonormal eigenbasis $\{|\phi_j\rangle\}$ and ground energy $E_0=\min_j E_j$, and let $|\psi_0\rangle$ be an initial state. For an accuracy $\varepsilon>0$ the **warm-start complexity** is
--
--   $$
--   L_H(\varepsilon,|\psi_0\rangle)=\sum_j\frac{|\langle\psi_0|\phi_j\rangle|^2}{\big(\max\{\varepsilon,\;E_j-E_0\}\big)^2}.
--   $$
--
--   It equals $\langle\psi_0|f(H)|\psi_0\rangle$ with $f(E)=\max\{\varepsilon,E-E_0\}^{-2}$, so it does not depend on the choice of eigenbasis when eigenvalues are degenerate. It is at most $\varepsilon^{-2}$, and it is the instance-dependent quantity of the warm-start bound, Theorem 1.3.
--
--   **Formalization Note** The eigenbasis and eigenvalues are Mathlib's `IsHermitian.eigenvectorBasis` and `IsHermitian.eigenvalues`; $E_0$ is `minEigenvalue H`.
-- source:
--   Heidari–Moharrami–Tavakoli–Zhang, Gap-Agnostic Ground-State Preparation via Quantum Bandits, manuscript (STOC 2027 submission, sha256 bd767ba1…c57acc), §1, p.3 (PDF p.4); Corollary 4.6, p.21 (PDF p.22)

import Definitions.Def_QAlgorithms_Defs_Hamiltonian
open QAlgorithms

namespace GapAgnosticGS.Supplement

/-- Heidari–Moharrami–Tavakoli–Zhang, *Gap-Agnostic Ground-State Preparation via Quantum Bandits*, manuscript (STOC 2027 submission, sha256 bd767ba1…c57acc), §1, p.3 (PDF p.4) and Corollary 4.6, p.21 (PDF p.22): "For an accuracy ε > 0, define
L_H(ε, |ψ_0⟩) := Σ_j |⟨ψ_0|ϕ_j⟩|² / (max{ε, E_j − E_0})²", with `H = Σ_j E_j |ϕ_j⟩⟨ϕ_j|` (p.2,
PDF p.3). The **warm-start complexity** `L_H(ε, |ψ⟩)` of a Hermitian matrix `H`.

**Formalization Note.** The eigenbasis is Mathlib's `hH.eigenvectorBasis` with its eigenvalues
`hH.eigenvalues` (the pairing `H ϕ_j = E_j ϕ_j`); the sum equals `⟨ψ| f(H) |ψ⟩` with
`f(E) = max{ε, E − E_0}^{−2}`, so it does not depend on the choice of orthonormal eigenbasis.
`E_0` is the smallest eigenvalue `minEigenvalue H`. Used only with `ε > 0`. -/
noncomputable def LH {n : ℕ} {H : Matrix (Fin n) (Fin n) ℂ} (hH : H.IsHermitian) (ε : ℝ)
    (ψ : EuclideanSpace ℂ (Fin n)) : ℝ :=
  ∑ j, ‖inner ℂ (hH.eigenvectorBasis j) ψ‖ ^ 2 / (max ε (hH.eigenvalues j - minEigenvalue H)) ^ 2

end GapAgnosticGS.Supplement



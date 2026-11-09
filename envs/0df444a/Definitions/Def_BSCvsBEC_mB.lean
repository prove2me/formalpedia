-- Prove2me | Definitions.Def_BSCvsBEC_mB
-- name    : BSCvsBEC_mB
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T08:29:46.112379+00:00
-- url     : https://prove2.me/theorems/cde7037b-aa4e-43ef-aeda-6a5ade85be1c
-- title:
--   The $q$-ary pure state channel and the operators $A$, $B$ of (101)
-- statement:
--   The **$q$-ary pure state channel** $q\mathrm{PSC}_\theta$ uses unit vectors $|\omega_1\rangle,\dots,|\omega_q\rangle\in\mathbb C^q$ with $\langle\omega_i|\omega_j\rangle=\cos\theta$ for $i\ne j$.
--
--   For positive semidefinite $P_1,\dots,P_q$ on $\mathcal Z=\mathbb C^\zeta$, consider on the direct sum $\mathcal Z^{\oplus q}$ the operators
--   $$A:=\operatorname{diag}(P_1,\dots,P_q),\qquad B:=\big(\sqrt{P_i}\sqrt{P_j}\big)_{i,j=1}^q,$$
--   so the diagonal blocks of $B$ are the $P_i$. Here $\sqrt{P}$ is the positive semidefinite square root. For a Hermitian matrix $M$, $\operatorname{spec}_+(M)$ denotes the multiset of its positive eigenvalues.
--
--   These operators turn spectra of the side-information states of $q\mathrm{PSC}_\theta$ into spectra of linear combinations $(1-\cos\theta)A+(\cos\theta)B$ (Claim 4.3), to which Heinävaara's theorem applies.
--
--   **Formalization Note** $\mathcal Z^{\oplus q}$ is indexed by pairs (block, index in $\zeta$). The square root is `cfc Real.sqrt`. `posSpec` is the empty multiset on a non-Hermitian matrix; it is applied only to positive semidefinite matrices.
-- source:
--   J. Hązła, R. O'Donnell, BSC vs. BEC vs. PSC, manuscript of November 3, 2026 (STOC 2027 submission, preprint basis, sha256 a44ed9262ff4e01c0cbd7e204728d4ad8bf4cfda8dbf126b96022d4c84b56186), §2.1, p.5 (qPSC_θ); §4.1, eq. (101), p.20 (A, B, spec, spec₊)

import Mathlib

namespace BSCvsBEC

/-- The `q`-ary pure state channel `qPSC_θ`: unit vectors `(|ω_i⟩)_{i ∈ [q]}` in `ℂ^q` with
`⟨ω_i|ω_j⟩ = cos θ` for `i ≠ j`.
Hązła–O'Donnell, manuscript of November 3, 2026 (sha256 a44ed926…), §2.1, p.5. -/
def IsQPSC {q : ℕ} (θ : ℝ) (ω : Fin q → EuclideanSpace ℂ (Fin q)) : Prop :=
  (∀ i, ‖ω i‖ = 1) ∧ ∀ i j, i ≠ j → inner ℂ (ω i) (ω j) = (Real.cos θ : ℂ)

/-- The block-diagonal operator `A := diag(P₁, …, P_q)` on `𝒵^{⊕q}` (eq. (101), p.20).

**Formalization Note.** `𝒵^{⊕q}` is `ℂ^{Fin q × ζ}`, block index first. -/
noncomputable def mA {q : ℕ} {ζ : Type*} (P : Fin q → Matrix ζ ζ ℂ) :
    Matrix (Fin q × ζ) (Fin q × ζ) ℂ :=
  Matrix.of fun r s => if r.1 = s.1 then P r.1 r.2 s.2 else 0

/-- The operator `B` on `𝒵^{⊕q}` with `(i, j)` block `√P_i √P_j` (eq. (101), p.20).

**Formalization Note.** `√P` is the positive semidefinite square root, `cfc Real.sqrt P`, of the
positive semidefinite matrix `P`; the diagonal blocks are therefore `P_i`. -/
noncomputable def mB {q : ℕ} {ζ : Type*} [Fintype ζ] [DecidableEq ζ] (P : Fin q → Matrix ζ ζ ℂ) :
    Matrix (Fin q × ζ) (Fin q × ζ) ℂ :=
  Matrix.of fun r s => (cfc Real.sqrt (P r.1) * cfc Real.sqrt (P s.1)) r.2 s.2

/-- `spec₊(M)`: the multiset of positive eigenvalues of a Hermitian matrix `M` (p.20: "`spec₊(A)` the
multiset of its positive eigenvalues").

**Formalization Note.** The value is `0` (the empty multiset) on a non-Hermitian matrix; it is only
applied to positive semidefinite matrices. -/
noncomputable def posSpec {ι : Type*} [Fintype ι] [DecidableEq ι] (M : Matrix ι ι ℂ) : Multiset ℝ :=
  if h : M.IsHermitian then (Finset.univ.val.map h.eigenvalues).filter (fun t => 0 < t) else 0

end BSCvsBEC



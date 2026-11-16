-- Prove2me | Definitions.Def_LogLogJam_Supplement_IsGaussQP
-- name    : LogLogJam_Supplement_IsGaussQP
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T01:50:58.647036+00:00
-- url     : https://prove2.me/theorems/715da2a3-489f-429a-b0c7-0a1c82beadbc
-- title:
--   The Gaussian state $\rho(m,V)$ in the paper's convention, and pure centered Gaussian states
-- statement:
--   For an $n$-mode bosonic system with quadratures $\hat R=(\hat q_1,\dots,\hat q_n,\hat p_1,\dots,\hat p_n)$, $\hat q=(\hat a+\hat a^\dagger)/\sqrt2$, $\hat p=(\hat a-\hat a^\dagger)/(\sqrt2\,i)$, a density operator $\rho$ on the Fock space $\ell^2(\mathbb N^n)$ is the **Gaussian state** $\rho(m,V)$ when it is Gaussian with mean and covariance
--
--   $$
--   m_i=\mathrm{Tr}(\rho\hat R_i),\qquad V_{ij}=\mathrm{Tr}\big(\rho\{\hat R_i-m_i,\hat R_j-m_j\}\big),
--   $$
--
--   so that the vacuum has $V=I$.
--
--   A state $\sigma$ is a **pure Gaussian state with zero displacement** when $\sigma=\rho(0,V_K)=|\psi_K\rangle\langle\psi_K|$ for some $K$ in the Siegel disk $\mathfrak D_n=\{K\in\mathbb C^{n\times n}:K=K^\top,\ KK^\dagger\prec I\}$, where $V_K$ is the covariance matrix of Lemma 4.6.
--
--   These predicates state Theorems 7.7, 8.3 and 8.16, which compare an estimate with the true state on Fock space.
--
--   **Formalization Note** The published `BosonicLearn.IsGaussianState` uses the covariance $\Sigma=\tfrac12\mathrm{Tr}(\rho\{\cdot,\cdot\})$ (vacuum $\tfrac12 I$) and indexes quadratures by $\mathrm{Fin}\,n\oplus\mathrm{Fin}\,n$; so $\rho(m,V)$ is `IsGaussianState ρ m (V/2)` after reindexing the mission's $\mathrm{Fin}\,2\times\mathrm{Fin}\,n$ ($(0,j)=q_j$, $(1,j)=p_j$). $V_K$ and the Siegel disk are the base mission's `LogLogJam.VK` and `LogLogJam.InSiegelDisk`.
-- source:
--   Chen, Gong, Ye, Zhang, The log log jam in Gaussian state tomography, arXiv:2607.12983 (version of November 3, 2026, sha256 97b751ca…), §4.2, pp.14–15 (PDF pp.17–18); §4.4 and Lemma 4.6, pp.18–19 (PDF pp.21–22)

import Mathlib
import Definitions.Def_LogLogJam_VK
import Definitions.Def_BosonicLearn_IsGaussianState

open QAlgorithms.Papers.Independent.Dependency50.P33 (State)
open QAlgorithms.Papers.Independent.Claimed50.P47 (Occupation)

namespace LogLogJam.Supplement

open LogLogJam

/-- Reindex a phase-space vector from the mission's q-then-p index `Q n = Fin 2 × Fin n`
(`(0, j) = q_j`, `(1, j) = p_j`) to `Fin n ⊕ Fin n` (`inl j = q_j`, `inr j = p_j`), the index of
`BosonicLearn.IsGaussianState` (arXiv:2607.12983, version of November 3, 2026, sha256 97b751ca…, §4.2,
p.14: `R̂ = (q̂₁, …, q̂_n, p̂₁, …, p̂_n)`). -/
def qpVec {n : ℕ} (m : Q n → ℝ) : Fin n ⊕ Fin n → ℝ
  | Sum.inl j => m (0, j)
  | Sum.inr j => m (1, j)

/-- The index map `Fin n ⊕ Fin n → Q n` used by `qpVec` and `qpMat`. -/
def qpIdx {n : ℕ} : Fin n ⊕ Fin n → Q n
  | Sum.inl j => (0, j)
  | Sum.inr j => (1, j)

/-- Reindex a phase-space matrix from `Q n` to `Fin n ⊕ Fin n` (same quadratures, see `qpVec`). -/
def qpMat {n : ℕ} (V : Matrix (Q n) (Q n) ℝ) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ :=
  Matrix.of fun a b => V (qpIdx a) (qpIdx b)

/-- `IsGaussQP ρ m V`: the density operator `ρ` on the `n`-mode Fock space is the Gaussian state
`ρ(m, V)` of the paper, with mean `m = Tr(ρR̂)` and covariance
`V_ij = Tr(ρ{R̂_i − m_i, R̂_j − m_j})` in the q-then-p ordering (arXiv:2607.12983, version of
November 3, 2026, sha256 97b751ca…, §4.2, pp.14–15).

**Formalization Note** The paper's covariance has no factor `½` (the vacuum has `V = I`), while the
published `BosonicLearn.IsGaussianState` uses `Σ = ½ Tr(ρ{·,·})` (vacuum `½ I`); so `ρ(m, V)` is
`IsGaussianState ρ m (V / 2)` after reindexing `Q n = Fin 2 × Fin n` to `Fin n ⊕ Fin n`. -/
def IsGaussQP {n : ℕ} (ρ : State (Occupation (Fin n))) (m : Q n → ℝ) (V : Matrix (Q n) (Q n) ℝ) :
    Prop :=
  BosonicLearn.IsGaussianState ρ (qpVec m) ((1 / 2 : ℝ) • qpMat V)

/-- `σ` is a **pure Gaussian state with zero displacement**, `σ = ρ(0, V_K) = |ψ_K⟩⟨ψ_K|` for some
`K` in the Siegel disk `𝔇_n` (arXiv:2607.12983, version of November 3, 2026, sha256 97b751ca…, §4.4,
pp.18–19 and Lemma 4.6, p.19: the pure centered `n`-mode Gaussian states are exactly the
`|ψ_K⟩`, `K ∈ 𝔇_n`, with covariance `V_K`).

Theorems 8.3 and 8.16 require the learner's outcome to "specify a pure Gaussian state `ρ(0, V̂)`";
this predicate expresses that. -/
def IsPureCentGauss {n : ℕ} (σ : State (Occupation (Fin n))) : Prop :=
  ∃ K : Matrix (Fin n) (Fin n) ℂ, InSiegelDisk K ∧ IsGaussQP σ 0 (VK K)

end LogLogJam.Supplement



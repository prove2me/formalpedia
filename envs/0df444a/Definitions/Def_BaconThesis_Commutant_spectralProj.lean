-- Prove2me | Definitions.Def_BaconThesis_Commutant_spectralProj
-- name    : BaconThesis_Commutant_spectralProj
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T16:36:41.918655+00:00
-- url     : https://prove2.me/theorems/0ef2bbce-ee63-40bd-9b62-860c7a8ad48a
-- title:
--   The spectral projector $\Pi_\mu$ of a Hermitian observable
-- statement:
--   Let $M$ be a Hermitian operator on $\mathbb C^{\iota}$ with spectral decomposition $M=U\,\mathrm{diag}(\mu_1,\dots,\mu_N)\,U^\dagger$. For a real number $\mu$ define
--   $$
--   \Pi_\mu=U\,\mathrm{diag}\bigl(\mathbf 1[\mu_1=\mu],\dots,\mathbf 1[\mu_N=\mu]\bigr)\,U^\dagger ,
--   $$
--   the orthogonal projector onto the eigenspace $\ker(M-\mu)$; it does not depend on the choice of eigenbasis, and $\Pi_\mu=0$ when $\mu$ is not an eigenvalue. A measurement of the observable $M$ on a state $\rho$ yields outcome $\mu$ with probability $\operatorname{tr}(\Pi_\mu\rho)$ and leaves the state $\Pi_\mu\rho\Pi_\mu/\operatorname{tr}(\Pi_\mu\rho)$.
--
--   **Formalization Note** $U$ and $\mu_i$ are Mathlib's `eigenvectorUnitary` and `eigenvalues` of a Hermitian matrix.
-- source:
--   Bacon, Decoherence, Control, and Symmetry in Quantum Computers, arXiv:quant-ph/0305025v1, §7.4, Lemma 7.4.1, p.104 (PDF p.121)

import Mathlib

namespace BaconThesis.Commutant

open Classical in
/-- **The spectral projector `Π_μ` of a Hermitian observable.**
Bacon, *Decoherence, Control, and Symmetry in Quantum Computers*, arXiv:quant-ph/0305025v1,
§7.4, Lemma 7.4.1, p.104 (PDF p.121): "a measurement of `M`" for a Hermitian observable `M`. A
(projective) measurement of `M` with outcome `μ` maps a state `ρ` to `Π_μ ρ Π_μ` (up to the
normalization `tr(Π_μ ρ)`), where `Π_μ` is the orthogonal projector onto the eigenspace
`ker(M − μ)`.

With `M = U diag(μ_1, …, μ_N) U†` the spectral decomposition of `M`,
`spectralProj hM μ = U diag(𝟙[μ_i = μ]) U†`; this is the projector onto `ker(M − μ)` (it does not
depend on the choice of eigenbasis), and it is `0` when `μ` is not an eigenvalue.

**Formalization Note.** `U = hM.eigenvectorUnitary` and `μ_i = hM.eigenvalues i` from Mathlib's
spectral theorem for Hermitian matrices. -/
noncomputable def spectralProj {ι : Type} [Fintype ι] [DecidableEq ι] {M : Matrix ι ι ℂ}
    (hM : M.IsHermitian) (μ : ℝ) : Matrix ι ι ℂ :=
  (hM.eigenvectorUnitary : Matrix ι ι ℂ) *
    Matrix.diagonal (fun i => if hM.eigenvalues i = μ then (1 : ℂ) else 0) *
    star (hM.eigenvectorUnitary : Matrix ι ι ℂ)

end BaconThesis.Commutant



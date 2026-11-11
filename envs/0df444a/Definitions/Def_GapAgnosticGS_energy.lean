-- Prove2me | Definitions.Def_GapAgnosticGS_energy
-- name    : GapAgnosticGS_energy
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:28:08.621642+00:00
-- url     : https://prove2.me/theorems/4d15fc5d-726e-4150-90dd-0acc624b992d
-- title:
--   Eigenvalues $E_0\le E_1\le\dots\le E_{n-1}$ of a Hamiltonian
-- statement:
--   Let $H$ be a Hermitian $n\times n$ matrix acting on $\mathbb C^n$. Its eigenvalues, counted with multiplicity and listed in increasing order, are
--
--   $$E_0\le E_1\le\cdots\le E_{n-1},\qquad H=\sum_{j=0}^{n-1}E_j\,|\phi_j\rangle\langle\phi_j| .$$
--
--   $E_0$ is the ground energy. This indexing is used by every spectral quantity of the mission ($\Delta_{\rm gs}$, $\Gamma_{\rm gs}$, $d_{\rm eff}$) and by the norm assumption $\|H\|\le\alpha$, which is stated as $|E_j|\le\alpha$ for all $j$.
--
--   **Formalization Note** `energy H j` re-indexes the published increasing eigenvalue list `QAlgorithms.ascEigenvalues H` by `Fin n` (0-based, as in the paper). On a non-Hermitian matrix it is $0$; all statements assume Hermiticity.
-- source:
--   Heidari–Moharrami–Tavakoli–Zhang, Gap-Agnostic Ground-State Preparation via Quantum Bandits, manuscript (STOC 2027 submission, sha256 bd767ba1…c57acc), §1, p.2 (PDF p.3), display "H = Σ_{j=0}^{n−1} E_j |ϕ_j⟩⟨ϕ_j|, E_0 ≤ E_1 ≤ ⋯ ≤ E_{n−1}"

import Definitions.Def_QAlgorithms_Defs_Hamiltonian
open QAlgorithms

namespace GapAgnosticGS

/-- Heidari–Moharrami–Tavakoli–Zhang, *Gap-Agnostic Ground-State Preparation via Quantum Bandits*, manuscript (STOC 2027 submission, sha256 bd767ba1…c57acc), §1, p.2 (PDF p.3): "H = Σ_{j=0}^{n−1} E_j |ϕ_j⟩⟨ϕ_j|, E_0 ≤ E_1 ≤ ⋯ ≤ E_{n−1}". The
`j`-th eigenvalue `E_j` of an `n × n` matrix, counted with multiplicity, in increasing order
(`j = 0` is the ground energy).

**Formalization Note.** This re-indexes the published `QAlgorithms.ascEigenvalues H` (indexed by
`Fin (Fintype.card (Fin n))`) by `Fin n`; indices are 0-based as in the paper. For a
non-Hermitian matrix the value is `0`; every statement using it assumes `H.IsHermitian`. -/
noncomputable def energy {n : ℕ} (H : Matrix (Fin n) (Fin n) ℂ) (j : Fin n) : ℝ :=
  ascEigenvalues H (Fin.cast (Fintype.card_fin n).symm j)

end GapAgnosticGS



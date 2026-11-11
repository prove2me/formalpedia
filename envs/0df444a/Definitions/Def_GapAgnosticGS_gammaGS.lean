-- Prove2me | Definitions.Def_GapAgnosticGS_gammaGS
-- name    : GapAgnosticGS_gammaGS
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:29:24.725194+00:00
-- url     : https://prove2.me/theorems/e41fb3d8-edf5-4f29-992f-c9f96172f72d
-- title:
--   Spectral complexity $\Gamma_{\rm gs}=\sum_{j\ge1}(E_j-E_0)^{-2}$
-- statement:
--   For a Hamiltonian $H$ on $\mathbb C^n$ with eigenvalues $E_0\le E_1\le\dots\le E_{n-1}$ (with multiplicity), the **spectral complexity** is
--
--   $$\Gamma_{\rm gs}:=\sum_{j=1}^{n-1}\frac{1}{(E_j-E_0)^2}.$$
--
--   It weights every excited eigenstate by the inverse square of its energy above the ground energy. It is the instance-dependent quantity in the main upper bound $O(\alpha\sqrt{\Gamma_{\rm gs}}\,\mathrm{polylog})$; it is finite exactly when the ground state is unique.
--
--   **Formalization Note** The sum is over the 0-based indices $j\ge1$ of the increasing eigenvalue list, and $E_0$ is the smallest eigenvalue. Under a unique ground state all denominators are positive.
-- source:
--   Heidari–Moharrami–Tavakoli–Zhang, Gap-Agnostic Ground-State Preparation via Quantum Bandits, manuscript (STOC 2027 submission, sha256 bd767ba1…c57acc), §1, p.2 (PDF p.3), display "Γ_gs := Σ_{j=1}^{n−1} 1/(E_j − E_0)²"

import Definitions.Def_GapAgnosticGS_energy
open QAlgorithms

namespace GapAgnosticGS

/-- Heidari–Moharrami–Tavakoli–Zhang, *Gap-Agnostic Ground-State Preparation via Quantum Bandits*, manuscript (STOC 2027 submission, sha256 bd767ba1…c57acc), §1, p.2 (PDF p.3): the spectral complexity
"Γ_gs := Σ_{j=1}^{n−1} 1/(E_j − E_0)²" of a Hamiltonian with a unique ground state.

**Formalization Note.** The sum runs over the 0-based indices `j ≥ 1` of the increasingly sorted
eigenvalues (with multiplicity, so a repeated excited level is counted once per eigenvector), and
`E_0` is `QAlgorithms.minEigenvalue H` (equal to `energy H 0` for `n ≥ 1`). Under
`HasSimpleGroundState H` every denominator is positive, so no term is a division by zero. -/
noncomputable def gammaGS {n : ℕ} (H : Matrix (Fin n) (Fin n) ℂ) : ℝ :=
  ∑ j : Fin n, if 0 < (j : ℕ) then 1 / (energy H j - minEigenvalue H) ^ 2 else 0

end GapAgnosticGS



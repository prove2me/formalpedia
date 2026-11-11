-- Prove2me | Definitions.Def_GapAgnosticGS_phaseOracle
-- name    : GapAgnosticGS_phaseOracle
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:28:38.305957+00:00
-- url     : https://prove2.me/theorems/9a7ca0c6-0aa6-4919-90e5-16690238ed68
-- title:
--   Phase oracle $W_H=e^{i\tau H}$ with $\tau=\pi/(4\alpha)$
-- statement:
--   Let $H$ be a Hamiltonian on $\mathbb C^n$ whose spectrum lies in the known interval $[-\alpha,\alpha]$, $\alpha>0$. The **phase oracle** is the unitary
--
--   $$W_H=e^{i\tau H},\qquad \tau=\frac{\pi}{4\alpha}.$$
--
--   Algorithms access $H$ only through controlled uses of $W_H$ and $W_H^\dagger$, each counted as one query. With this $\tau$ all phases $\tau E_j$ lie in $[-\pi/4,\pi/4]$.
--
--   **Formalization Note** The paper writes $\tau=\Theta(1/\alpha)$ in the introduction and uses $\tau=\pi/(4\alpha)$ in Lemma 3.1 and in the proof of Theorem 3.15; the latter value is fixed here. The exponential is the matrix exponential (Mathlib's `NormedSpace.exp`).
-- source:
--   Heidari–Moharrami–Tavakoli–Zhang, Gap-Agnostic Ground-State Preparation via Quantum Bandits, manuscript (STOC 2027 submission, sha256 bd767ba1…c57acc), §1, p.1 (PDF p.2) (access model); §1, p.5 (PDF p.6); Lemma 3.1, p.8 (PDF p.9): "W_H = e^{iτH} with τ = π/(4α)"

import Definitions.Def_QAlgorithms_Defs_Hamiltonian
open QAlgorithms

namespace GapAgnosticGS

/-- Heidari–Moharrami–Tavakoli–Zhang, *Gap-Agnostic Ground-State Preparation via Quantum Bandits*, manuscript (STOC 2027 submission, sha256 bd767ba1…c57acc), §1, p.1 (PDF p.2): "the phase oracle W_H = e^{iτH}, τ = Θ(1/α)"; §1, p.5 (PDF p.6) and
Lemma 3.1, p.8 (PDF p.9): "W_H = e^{iτH} with τ = π/(4α)". The matrix exponential
`W_H = exp(i·(π/(4α))·H)`.

**Formalization Note.** The evolution time is fixed to the paper's value `τ = π/(4α)` (the value
of Lemma 3.1 and of the proof of Theorem 3.15). The exponential is Mathlib's `NormedSpace.exp`
on matrices, with sign `+` as printed. For Hermitian `H` it is unitary. -/
noncomputable def phaseOracle {n : ℕ} (H : Matrix (Fin n) (Fin n) ℂ) (α : ℝ) :
    Matrix (Fin n) (Fin n) ℂ :=
  NormedSpace.exp ((((Real.pi / (4 * α) : ℝ) : ℂ) * Complex.I) • H)

end GapAgnosticGS



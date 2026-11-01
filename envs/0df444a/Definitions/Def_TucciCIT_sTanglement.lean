-- Prove2me | Definitions.Def_TucciCIT_sTanglement
-- name    : TucciCIT_sTanglement
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T15:28:40.96937+00:00
-- url     : https://prove2.me/theorems/7b152898-0b20-4e7b-998e-0d7dd21ccd35
-- title:
--   S-tanglement $ST_\rho(x : y\,|\,e)$ for two listeners
-- statement:
--   Let $\rho$ be a density matrix on $\mathcal H_e \otimes \mathcal H_x \otimes \mathcal H_y$, where $e$ is a speaker and $x$, $y$ are two single-node listeners. The S-tanglement of the listeners given the speaker is
--
--   $$
--   ST_\rho(x : y \,|\, e) = S_\rho(x|e) + S_\rho(y|e) - S_\rho(x, y|e),
--   $$
--
--   where $S_\rho(A|E) = S_\rho(A, E) - S_\rho(E)$ is the quantum conditional entropy and $S_\rho(A)$ is the von Neumann entropy (in bits) of the reduced density matrix of $\rho$ on the registers $A$. With two listeners the S-tanglement equals the conditional mutual information $S_\rho(x : y|e)$, the notation used in §4.
--
--   This is the paper's measure of entanglement; its main theorem compares it with the entanglement of formation.
--
--   **Formalization Note** Reduced density matrices are computed with the platform's partial trace `redistributionMarginal` (coordinate projections for the kept and traced registers) and entropies with `QAlgorithms.vnEntropy` (base 2, $0\log 0 = 0$). The convention $S(A|E) = S(A,E) - S(E)$ is that of the paper's Ref. [5]; it is forced by the paper's eqs. (6.5), (6.7), (6.8).
-- source:
--   Tucci, Quantum Entanglement and Conditional Information Transmission, arXiv:quant-ph/9909041v2, eq. (3.2) with n = 2, p.6

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Ensemble
import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P20

open QAlgorithms QAlgorithms.Papers.Independent.Gap48.P20

namespace TucciCIT

/-- Tucci, *Quantum Entanglement and Conditional Information Transmission*,
arXiv:quant-ph/9909041v2, eq. (3.2) with `n = 2`, p.6 (PDF p.6); written `S_μ(x : y|e)` in §4.

The S-tanglement of two single-node listeners `x`, `y` and a speaker `e`, for a density matrix
`ρ` on `H_e ⊗ H_x ⊗ H_y`:
`ST_ρ(x : y | e) = S_ρ(x|e) + S_ρ(y|e) − S_ρ(x, y|e)`,
with the conditional entropy `S_ρ(A|E) = S_ρ(A, E) − S_ρ(E)` of Ref. [5]. Each `S_ρ(·)` is the
von Neumann entropy (bits) of the reduced density matrix of `ρ` on the named registers.

**Formalization Note.** A basis index is `(e, x, y)`. `S_ρ(x, e)`, `S_ρ(y, e)`, `S_ρ(e)` are
`subsystemEntropy ρ keep forget` (the platform's `Gap48.P20` partial trace, with `keep` the
retained coordinates and `forget` the traced-out ones, which are complementary in every use).
`S_ρ(x, y, e)` is `vnEntropy ρ`. Entropies are real numbers in bits (`log₂`, eqs. (2.9), (4.11)),
with `0 log 0 = 0`. The paper's convention `S(A|E) = S(A,E) − S(E)` is not written out in this
paper; it is forced by its eqs. (6.5), (6.7), (6.8). -/
noncomputable def sTanglement {E X Y : Type*} [Fintype E] [Fintype X] [Fintype Y]
    [DecidableEq E] [DecidableEq X] [DecidableEq Y]
    (ρ : Matrix (E × X × Y) (E × X × Y) ℂ) : ℝ :=
  (subsystemEntropy ρ (fun p => (p.1, p.2.1)) (fun p => p.2.2) -
      subsystemEntropy ρ (fun p => p.1) (fun p => p.2)) +
    (subsystemEntropy ρ (fun p => (p.1, p.2.2)) (fun p => p.2.1) -
      subsystemEntropy ρ (fun p => p.1) (fun p => p.2)) -
    (vnEntropy ρ - subsystemEntropy ρ (fun p => p.1) (fun p => p.2))

end TucciCIT



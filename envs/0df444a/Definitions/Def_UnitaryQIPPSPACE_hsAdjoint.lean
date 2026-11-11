-- Prove2me | Definitions.Def_UnitaryQIPPSPACE_hsAdjoint
-- name    : UnitaryQIPPSPACE_hsAdjoint
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:27:22.509787+00:00
-- url     : https://prove2.me/theorems/bfcc66aa-021a-402b-9095-04fb3c13103a
-- title:
--   Hilbert–Schmidt adjoint $\Phi^*$
-- statement:
--   The **adjoint** $\Phi^*$ of a map $\Phi:\mathcal L(\mathbb C^\alpha)\to\mathcal L(\mathbb C^\beta)$ is defined by $\operatorname{tr}[\Phi^*(Y)^\dagger X]=\operatorname{tr}[Y^\dagger\Phi(X)]$; entrywise $\Phi^*(Y)_{ij}=\overline{\operatorname{tr}[Y^\dagger\Phi(|i\rangle\langle j|)]}$.
--
--   In Lemma 3.2, $\langle\psi|\Phi^*(I)|\psi\rangle=\operatorname{tr}\Phi(\psi)$ is the acceptance probability on input $|\psi\rangle$, so the largest and smallest eigenvalues of $\Phi^*(I)$ are the extreme acceptance probabilities.
-- source:
--   He, Ou, Zhao, unitaryQIP = unitaryPSPACE, arXiv:2611.02819 (held version, sha256 9e357a00…ead793), Lemma 3.2, p.14 (PDF p.16)

import Mathlib

open Matrix

namespace UnitaryQIPPSPACE

/-- **The Hilbert–Schmidt adjoint** `Φ*` of a map `Φ : L(ℂ^α) → L(ℂ^β)` (He, Ou, Zhao, *unitaryQIP =
unitaryPSPACE*, arXiv:2611.02819, held version sha256 9e357a00…, Lemma 3.2, p. 14 (PDF p. 16):
"`Φ*` is the adjoint of `Φ`"), defined by `tr[Φ*(Y)† X] = tr[Y† Φ(X)]`; entrywise
`Φ*(Y)_{i,j} = conj tr[Y† Φ(|i⟩⟨j|)]`. -/
noncomputable def hsAdjoint {α β : Type} [Fintype α] [DecidableEq α] [Fintype β]
    (Φ : Matrix α α ℂ → Matrix β β ℂ) (Y : Matrix β β ℂ) : Matrix α α ℂ :=
  Matrix.of fun i j => star (Matrix.trace (Yᴴ * Φ (Matrix.single i j 1)))

end UnitaryQIPPSPACE



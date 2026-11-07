-- Prove2me | Definitions.Def_OnlineShadow_LogRate_marginal
-- name    : OnlineShadow_LogRate_marginal
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T04:03:57.298098+00:00
-- url     : https://prove2.me/theorems/8d0c70d9-bb60-42b4-be5a-50522592633c
-- title:
--   Reduced state $\rho=\mathrm{Tr}_{\mathcal R}|\psi\rangle\langle\psi|$
-- statement:
--   For a vector $\psi$ on $\mathcal H\otimes\mathcal R$ with $\mathcal H=\mathbb C^d$ and $\mathcal R=\mathbb C^r$, its reduced state on $\mathcal H$ is
--   $$\rho=\mathrm{Tr}_{\mathcal R}|\psi\rangle\langle\psi|,\qquad \rho_{ij}=\sum_{a=1}^r\psi(i,a)\,\overline{\psi(j,a)} .$$
--   When $\psi$ is a unit vector this is a density matrix, and $\psi$ is a **purification** of $\rho$; every density matrix on $\mathbb C^d$ has a purification with $r=d$. The analysis of §3–4 works with a purification $|\psi\rangle$ of the unknown state.
-- source:
--   Chen, O'Donnell, Pelecanos, Wright, Online Shadow Tomography Matching the Classical Bounds, STOC 2027 submission (manuscript of November 2, 2026, sha256 90993723…dc3a9), §3, p. 8

import Mathlib

namespace OnlineShadow.LogRate

/-- The reduced state `ρ = Tr_R |ψ⟩⟨ψ|` on `H = ℂ^d` of a vector `ψ` on `H ⊗ R`, `R = ℂ^r`
(Chen, O'Donnell, Pelecanos, Wright, *Online Shadow Tomography Matching the Classical Bounds*, STOC 2027 submission (manuscript of November 2, 2026, sha256 90993723…dc3a9), §3, p.8: "Let `|ψ⟩` be any purification of the unknown state `ρ`"):
`ρ i j = ∑ₐ ψ(i, a) · conj ψ(j, a)`. For a unit vector `ψ` this is a density matrix, and every density
matrix on `ℂ^d` arises this way with `r = d`. -/
def marginal {d r : ℕ} (ψ : Fin d × Fin r → ℂ) : Matrix (Fin d) (Fin d) ℂ :=
  fun i j => ∑ a : Fin r, ψ (i, a) * star (ψ (j, a))

end OnlineShadow.LogRate



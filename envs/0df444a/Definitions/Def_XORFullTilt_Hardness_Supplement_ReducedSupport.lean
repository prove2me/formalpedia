-- Prove2me | Definitions.Def_XORFullTilt_Hardness_Supplement_ReducedSupport
-- name    : XORFullTilt_Hardness_Supplement_ReducedSupport
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T18:22:22.162742+00:00
-- url     : https://prove2.me/theorems/ef5f0b7d-369f-4f61-8b25-598311bb71b7
-- title:
--   Alice's reduced density operator and support
-- statement:
--   For a unit bipartite pure state $\psi\in\mathbb C^d\otimes\mathbb C^e$, Alice's reduced density operator and support are
--   $$\rho_A(i,j)=\sum_k\psi_{ik}\overline{\psi_{jk}},\qquad K_A=\operatorname{range}(\rho_A).$$
--   The support is the actual range and need not be the whole local space. These objects express the preservation and restricted identities of Lemma 3.7. Coordinates are the published state coordinates; no full Schmidt rank hypothesis is imposed.
-- source:
--   Richard Cleve, Eric Culf, Aviv Taller, XOR Games at Full Tilt: The Hardness of Binary Nonlocal Games, STOC 2027 submission #396 (October 2026), pp.19–20, Lemma 3.7 and its support argument

import Mathlib
import Definitions.Def_XORFullTilt_Hardness_QuantumModel

namespace XORFullTilt.Hardness.Supplement

/-- Alice's partial trace of the pure state, in the published coordinates. -/
noncomputable def aliceDensity {d e : ℕ} (ψ : State d e) : Matrix (Fin d) (Fin d) ℂ :=
  fun i j => ∑ k, ψ.vec (i,k) * star (ψ.vec (j,k))

/-- The range of the reduced density operator, with no full-rank assumption. -/
noncomputable def aliceSupport {d e : ℕ} (ψ : State d e) : Submodule ℂ (Fin d → ℂ) :=
  LinearMap.range (Matrix.toLin' (aliceDensity ψ))
end XORFullTilt.Hardness.Supplement



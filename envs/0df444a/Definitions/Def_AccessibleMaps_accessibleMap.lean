-- Prove2me | Definitions.Def_AccessibleMaps_accessibleMap
-- name    : AccessibleMaps_accessibleMap
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T16:04:27.563544+00:00
-- url     : https://prove2.me/theorems/2c39d49d-efb0-416d-a64c-7382c0f33571
-- title:
--   The affinely accessible map $\Phi(\rho)=\operatorname{tr}_B[U E_{\mathcal V}(\rho)U^\dagger]$ (Eq. (22))
-- statement:
--   For an affine assignment $E_{\mathcal V}$ and a unitary $U$ on $\mathbb C^{a}\otimes\mathcal H$, the map
--   $$
--   \Phi(\rho)=\operatorname{tr}_B\big[U\,E_{\mathcal V}(\rho)\,U^\dagger\big]
--   $$
--   is the paper's **affinely accessible map**: an assignment satisfying the linearity conditions of Eq. (21), followed by one unitary that does not depend on the initial state $\rho$.
--
--   **Formalization Note** $U$ is a single fixed unitary, passed as an argument independent of $\rho$.
-- source:
--   Carteret, Terno & Życzkowski, Dynamics beyond completely positive maps, arXiv:quant-ph/0512167v3, Definition, Eq. (22), p.4

import Mathlib
import Definitions.Def_AccessibleMaps_AffineAssignment_assign
import Definitions.Def_AccessibleMaps_reducedEvolution

namespace AccessibleMaps

variable {a H : Type*} [Fintype a] [DecidableEq a] [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

/-- The affinely accessible map `Φ(ρ) = tr_B [U E_𝒱(ρ) U†]` of an affine assignment `E` and a unitary
`U`.

Carteret, Terno & Życzkowski, arXiv:quant-ph/0512167v3, Definition, Eq. (22), p.4 (PDF p.4): "A map Φ defined
by an assignment E_𝒱(ρ) and a unitary U, Φ(ρ) = tr_B[U(E_𝒱(ρ))U†], is called affinely accessible if
the assignment map satisfies the linearity conditions in Eq. (21) and the unitary U does not depend
on the initial state ρ."

**Formalization Note.** `U` is one fixed unitary, an argument independent of `ρ`. -/
noncomputable def accessibleMap (E : AffineAssignment a H)
    (U : unitary (Composite a H →L[ℂ] Composite a H)) (ρ : Matrix a a ℂ) : Matrix a a ℂ :=
  reducedEvolution U (E.assign ρ)

end AccessibleMaps



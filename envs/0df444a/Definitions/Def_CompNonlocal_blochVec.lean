-- Prove2me | Definitions.Def_CompNonlocal_blochVec
-- name    : CompNonlocal_blochVec
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T22:39:35.874059+00:00
-- url     : https://prove2.me/theorems/6581fec2-a19b-4f3f-93bb-c0bd5c5a59a1
-- title:
--   The Bloch vector of a qubit operator
-- statement:
--   For a $2\times2$ matrix $\rho$, its Bloch vector has coordinates
--   $$r_j=\operatorname{Re}\operatorname{Tr}(\rho\,\sigma_j),\qquad j=1,2,3 .$$
--   For a density matrix $\rho=\nu(r)$ this returns $r$ (the paper writes $r_J(t)=\operatorname{Tr}(\sigma_J\zeta_t)$).
--
--   **Formalization Note** For an unnormalized positive operator it returns $\operatorname{Tr}(\rho)\,r$; statements divide by the trace where the paper conditions on an outcome. For a Hermitian $W=w^0I+w\cdot\sigma$ it returns $2w$.
-- source:
--   Głuch, Morimae, From Computational Nonlocality to Public-Key Encryption and Commitments, manuscript (STOC 2027 submission, sha256 e245edd7…), §4.1, p.18 and Definition 15, p.34

import Mathlib
import Definitions.Def_CompNonlocal_pauli

set_option autoImplicit false

namespace CompNonlocal

/-- The Bloch vector of a qubit operator: its `j`-th coordinate is `Re Tr(ρ σ_j)`. Głuch, Morimae, *From Computational Nonlocality to Public-Key Encryption and Commitments*, manuscript (STOC 2027 submission, sha256 e245edd7…), §4.1,
p.18 ("ω = ½(I + r · σ) … r is the Bloch vector of ω") and Definition 15, p.34
("r_J(t) = Tr(σ_J ζ_t)").

**Formalization Note** For a density matrix `ρ = ν(r)` this returns `r`. For an unnormalized
positive operator it returns `Tr(ρ) · r`; the mission divides by the trace where the paper
conditions on an outcome. For a Hermitian `W = w⁰ I + w · σ` (Eq. (18)) it returns `2w`. -/
noncomputable def blochVec (ρ : Matrix Bool Bool ℂ) : EuclideanSpace ℝ (Fin 3) :=
  WithLp.toLp 2 (fun j : Fin 3 => (ρ * pauli j).trace.re)

end CompNonlocal



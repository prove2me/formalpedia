-- Prove2me | Definitions.Def_ArgmaxDeFinetti_tau
-- name    : ArgmaxDeFinetti_tau
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T21:42:49.617912+00:00
-- url     : https://prove2.me/theorems/b73b2d0c-ebba-41df-b142-2ae1dbafd395
-- title:
--   $\tau(M)=\sup_{\|u\|=1}\|P_{\mathrm{Sym}^2(u^\perp)}Mu^{\otimes2}\|_\pi$
-- statement:
--   For $M\in\mathrm{Herm}(\mathrm{Sym}^2(\mathbb C^d))$,
--   $$
--   \tau(M)=\sup_{\|u\|=1}\big\|P_{\mathrm{Sym}^2(u^\perp)}\,M\,u^{\otimes2}\big\|_\pi ,
--   $$
--   where the projective norm is taken across the two copies of $u^\perp$. It is the quantity in the dimension-free gap bound (3.17).
--
--   **Formalization Note** For witnesses $M$ the vector $Mu^{\otimes2}$ lies in $\mathrm{Sym}^2$, where $P_{\mathrm{Sym}^2(u^\perp)}$ equals $P_{u^\perp}\otimes P_{u^\perp}$. For a vector of $u^\perp\otimes u^\perp$ the projective norm in $u^\perp\otimes u^\perp$ equals that in $\mathbb C^d\otimes\mathbb C^d$ (both are the trace norm of the coefficient matrix, by (2.15)), which is the norm computed here.
-- source:
--   Jeronimo, Wu, Xu, Optimal Quantum de Finetti Theorems via Argmax Rounding, arXiv:2608.02590 (held version, sha256 fb339472…), §3.1.3, p.26, eq. (3.16)

import Mathlib
import Definitions.Def_ArgmaxDeFinetti_vnorm
import Definitions.Def_ArgmaxDeFinetti_tensorPow
import Definitions.Def_ArgmaxDeFinetti_InSym2Perp
import Definitions.Def_ArgmaxDeFinetti_projNorm
import Definitions.Def_ArgmaxDeFinetti_matSym

open Matrix

namespace ArgmaxDeFinetti

/-- `τ(M) = sup_{∥u∥=1} ∥P_{Sym²(u⊥)} M u^{⊗2}∥_π`, Jeronimo, Wu, Xu, *Optimal Quantum de Finetti Theorems via Argmax Rounding*, arXiv:2608.02590 (held version, sha256 fb339472…), eq. (3.16), p.26.

**Formalization Note** For `M ∈ Herm(Sym²(ℂ^d))` (`IsSymWitness`), `M u^{⊗2} ∈ Sym²`, and on `Sym²` the projector
`P_{Sym²(u⊥)}` equals `P_{u⊥} ⊗ P_{u⊥}` (`perp2 u`). The paper takes the projective norm "across the two copies
of `u⊥`"; for a vector of `u⊥ ⊗ u⊥` it equals the projective norm in `ℂ^d ⊗ ℂ^d` (both are the trace norm of the
coefficient matrix, (2.15)), which is what `projNorm` computes here. The supremum is a real `sSup`. -/
noncomputable def tau {d : ℕ} (M : Op 2 d) : ℝ :=
  sSup {r | ∃ u : Fin d → ℂ, vnorm u = 1 ∧ r = projNorm (pairOf (perp2 u *ᵥ (M *ᵥ tensorPow u 2)))}

end ArgmaxDeFinetti



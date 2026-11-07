-- Prove2me | Definitions.Def_ArgmaxDeFinetti_IsBosonic
-- name    : ArgmaxDeFinetti_IsBosonic
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T21:41:28.470735+00:00
-- url     : https://prove2.me/theorems/8c17350f-ed95-4bf0-a736-0e305d5706ea
-- title:
--   Bosonic states $\rho_N\in D(\mathrm{Sym}^N(\mathbb C^d))$
-- statement:
--   An operator $\rho_N$ on $(\mathbb C^d)^{\otimes N}$ is a **bosonic state** if it is a density operator (positive semidefinite with trace one) supported on the symmetric subspace, that is,
--   $$
--   \rho_N\succeq0,\qquad \operatorname{Tr}\rho_N=1,\qquad U_\pi\rho_N=\rho_N\ \text{ for every }\pi\in S_N .
--   $$
--   These are the states $D(\mathrm{Sym}^N(\mathbb C^d))$ whose two-site marginals the main theorem approximates.
--
--   **Formalization Note** A density operator on $\mathrm{Sym}^N$ is identified with its extension by zero to $(\mathbb C^d)^{\otimes N}$, i.e. with a state whose range lies in $\mathrm{Sym}^N$. This is strictly stronger than exchangeability $U_\pi\rho U_\pi^\dagger=\rho$. Density operators are the published `WildeQIT.IsDensityOperator`.
-- source:
--   Jeronimo, Wu, Xu, Optimal Quantum de Finetti Theorems via Argmax Rounding, arXiv:2608.02590 (held version, sha256 fb339472…), §2.1 'Bosonic states', p.19 (also (1.3), p.6)

import Mathlib
import Definitions.Def_WildeQIT_IsDensityOperator
import Definitions.Def_ArgmaxDeFinetti_IsSym

open Matrix

namespace ArgmaxDeFinetti

/-- A state `ρ_N` on `(ℂ^d)^{⊗N}` is **bosonic**, `ρ_N ∈ D(Sym^N(ℂ^d))`: a density operator
(positive semidefinite, trace one) whose range lies in `Sym^N(ℂ^d)`, i.e. `U_π ρ_N = ρ_N` for every
`π ∈ S_N`, Jeronimo, Wu, Xu, *Optimal Quantum de Finetti Theorems via Argmax Rounding*, arXiv:2608.02590 (held version, sha256 fb339472…), §2.1 "Bosonic states", p.19 (also (1.3), p.6).

**Formalization Note** A density operator on the subspace `Sym^N(ℂ^d)` is identified with the density operator
on `(ℂ^d)^{⊗N}` that it defines by extension by zero; such operators are exactly those with range in
`Sym^N`. This is not exchangeability (`U_π ρ U_π† = ρ`), which defines the strictly larger set `EXCH` of p.19.
"Density operator" is the published `WildeQIT.IsDensityOperator`. -/
def IsBosonic {N d : ℕ} (ρ : Op N d) : Prop :=
  WildeQIT.IsDensityOperator ρ ∧ ∀ π : Equiv.Perm (Fin N), OptimalSpectrum.Entangled.permOp (ι := Fin d) π * ρ = ρ

end ArgmaxDeFinetti



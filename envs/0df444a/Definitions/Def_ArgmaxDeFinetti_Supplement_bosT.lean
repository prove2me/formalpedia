-- Prove2me | Definitions.Def_ArgmaxDeFinetti_Supplement_bosT
-- name    : ArgmaxDeFinetti_Supplement_bosT
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T08:40:11.416819+00:00
-- url     : https://prove2.me/theorems/eb3191b8-fff5-4c1c-bf9b-2a917cfbd2e6
-- title:
--   $t$-site marginals of bosonic and of exchangeable states, $\mathrm{BOS}^{(t)}_N(d)$ and $\mathrm{EXCH}^{(t)}_N(d)$
-- statement:
--   A state $\rho_N$ on $(\mathbb C^d)^{\otimes N}$ is **exchangeable** if it is a density operator with $U_\pi\rho_NU_\pi^\dagger=\rho_N$ for every permutation $\pi\in S_N$ of the tensor factors. The sets of $t$-site marginals of bosonic and of exchangeable states are
--
--   $$
--   \mathrm{BOS}^{(t)}_N(d)=\{\rho^{(t)}_N:\ \rho_N\in D(\mathrm{Sym}^N(\mathbb C^d))\},\qquad
--   \mathrm{EXCH}^{(t)}_N(d)=\{\rho^{(t)}_N:\ \rho_N \text{ exchangeable}\}.
--   $$
--
--   Every bosonic state is exchangeable, so $\mathrm{BOS}^{(t)}_N(d)\subseteq \mathrm{EXCH}^{(t)}_N(d)$; the inclusion is strict in general.
--
--   These are the outer relaxations whose distance to $\mathrm{SEP}^{(t)}_H(d)$, resp. $\mathrm{SEP}^{(t)}_P(d)$, the de Finetti theorems bound.
--
--   **Formalization Note** Bosonic is the base mission's notion (a density operator with range in $\mathrm{Sym}^N$), $U_\pi$ the published permutation operator, and $\rho^{(t)}_N$ the marginal on the first $t$ sites; the sets are used with $t\le N$.
-- source:
--   Jeronimo, Wu, Xu, Optimal Quantum de Finetti Theorems via Argmax Rounding, arXiv:2608.02590 (held version, sha256 fb339472…), §2.1 "Bosonic states" and "Exchangeable states", p.19; (1.3)–(1.4), p.6

import Mathlib
import Definitions.Def_WildeQIT_IsDensityOperator
import Definitions.Def_OptimalSpectrum_Entangled_permOp
import Definitions.Def_ArgmaxDeFinetti_IsBosonic
import Definitions.Def_ArgmaxDeFinetti_Supplement_marginal

open Matrix

namespace ArgmaxDeFinetti

namespace Supplement

/-- The `t`-site marginals of bosonic `N`-site states, `BOS^{(t)}_N(d) = {ρ^{(t)}_N : ρ_N ∈ D(Sym^N(ℂ^d))}`,
Jeronimo, Wu, Xu, *Optimal Quantum de Finetti Theorems via Argmax Rounding*, arXiv:2608.02590 (held version, sha256 fb339472…), §2.1 "Bosonic states", p.19 (also (1.3), p.6).

**Formalization Note** Bosonic is the base mission's `IsBosonic` (density operator with range in `Sym^N`);
`ρ^{(t)}_N` is `marginal t`, the partial trace over sites `t+1, …, N`. Used with `t ≤ N`. -/
def bosT (t N d : ℕ) : Set (Op t d) :=
  {τ | ∃ ρ : Op N d, IsBosonic ρ ∧ τ = marginal t ρ}

/-- A state `ρ_N` on `(ℂ^d)^{⊗N}` is **exchangeable**: a density operator with `U_π ρ_N U_π† = ρ_N` for every
`π ∈ S_N`, Jeronimo, Wu, Xu, *Optimal Quantum de Finetti Theorems via Argmax Rounding*, arXiv:2608.02590 (held version, sha256 fb339472…), §2.1 "Exchangeable states", p.19 (also (1.4), p.6).

**Formalization Note** `U_π` is the published `OptimalSpectrum.Entangled.permOp π` (as in the base `IsSym`); the
condition is over every `π`, so the orientation convention of `U_π` does not matter. Exchangeable is weaker than
bosonic (range in `Sym^N`). -/
def IsExchangeable {N d : ℕ} (ρ : Op N d) : Prop :=
  WildeQIT.IsDensityOperator ρ ∧
    ∀ π : Equiv.Perm (Fin N),
      OptimalSpectrum.Entangled.permOp (ι := Fin d) π * ρ * (OptimalSpectrum.Entangled.permOp (ι := Fin d) π)ᴴ = ρ

/-- The `t`-site marginals of exchangeable `N`-site states, `EXCH^{(t)}_N(d)`, Jeronimo, Wu, Xu, *Optimal Quantum de Finetti Theorems via Argmax Rounding*, arXiv:2608.02590 (held version, sha256 fb339472…), §2.1 "Exchangeable
states", p.19 (also (1.4), p.6).

**Formalization Note** Used with `t ≤ N`; `ρ^{(t)}_N` is `marginal t`. -/
def exchT (t N d : ℕ) : Set (Op t d) :=
  {τ | ∃ ρ : Op N d, IsExchangeable ρ ∧ τ = marginal t ρ}

end Supplement

end ArgmaxDeFinetti



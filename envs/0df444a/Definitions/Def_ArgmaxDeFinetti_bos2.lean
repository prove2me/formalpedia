-- Prove2me | Definitions.Def_ArgmaxDeFinetti_bos2
-- name    : ArgmaxDeFinetti_bos2
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T21:42:21.229245+00:00
-- url     : https://prove2.me/theorems/336ab396-5ca6-4de6-a995-d924c2c6a622
-- title:
--   Bosonic two-site marginals $\mathrm{BOS}^{(2)}_N(d)$
-- statement:
--   For $N=2+m$ sites,
--   $$
--   \mathrm{BOS}^{(2)}_N(d)=\{\rho^{(2)}_N:\ \rho_N\in D(\mathrm{Sym}^N(\mathbb C^d))\},
--   $$
--   the set of two-site marginals of bosonic $N$-site states. The de Finetti error is its Hausdorff distance to the Hartree mixtures.
-- source:
--   Jeronimo, Wu, Xu, Optimal Quantum de Finetti Theorems via Argmax Rounding, arXiv:2608.02590 (held version, sha256 fb339472…), §2.1 'Bosonic states', p.19 (also (1.3), p.6)

import Mathlib
import Definitions.Def_ArgmaxDeFinetti_IsBosonic
import Definitions.Def_ArgmaxDeFinetti_marginal2

open Matrix

namespace ArgmaxDeFinetti

/-- The set of two-site marginals of bosonic `N`-site states,
`BOS^{(2)}_N(d) = { ρ^{(2)}_N : ρ_N ∈ D(Sym^N(ℂ^d)) }`, with `N = 2 + m`,
Jeronimo, Wu, Xu, *Optimal Quantum de Finetti Theorems via Argmax Rounding*, arXiv:2608.02590 (held version, sha256 fb339472…), §2.1 "Bosonic states", p.19 (also (1.3), p.6). -/
def bos2 (m d : ℕ) : Set (Op 2 d) :=
  {τ | ∃ ρ : Op (2 + m) d, IsBosonic ρ ∧ τ = marginal2 ρ}

end ArgmaxDeFinetti



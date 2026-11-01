-- Prove2me | Definitions.Def_WildeQIT_QMemory_qCondEntropy
-- name    : WildeQIT_QMemory_qCondEntropy
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T17:57:11.950212+00:00
-- url     : https://prove2.me/theorems/7bb03d3c-0269-4050-bc40-c560e11daef4
-- title:
--   Conditional quantum entropy $H(A|B)_\rho=H(AB)_\rho-H(B)_\rho$
-- statement:
--   Let $\rho_{AB}$ be a state of the bipartite system $AB$ and $\rho_B=\mathrm{Tr}_A\{\rho_{AB}\}$ its marginal on $B$. The **conditional quantum entropy** is
--
--   $$
--   H(A|B)_\rho\equiv H(AB)_\rho-H(B)_\rho .
--   $$
--
--   Unlike its classical counterpart it can be negative, for example $H(A|B)=-1$ for an ebit. It is the state-dependent term of the uncertainty principle with quantum memory.
--
--   **Formalization Note** $\mathcal H_A\otimes\mathcal H_B$ is indexed by `a × b`; $\mathrm{Tr}_A$ is the published `WildeQIT.partialTraceLeft`; $H$ is `vonNeumann` (bits). The first factor is the conditioned system, the second the conditioning one.
-- source:
--   Wilde, From Classical to Quantum Shannon Theory, arXiv:1106.1445v8, Definition 11.4.1, eq. (11.50), p. 329

import Mathlib
import Definitions.Def_WildeQIT_partialTrace
import Definitions.Def_WildeQIT_QMemory_vonNeumann

namespace WildeQIT.QMemory

/-- **Conditional quantum entropy** (Wilde, *From Classical to Quantum Shannon Theory*,
arXiv:1106.1445v8, Definition 11.4.1, p. 329): for `ρ_AB`,
`H(A|B)_ρ ≡ H(AB)_ρ − H(B)_ρ` (11.50), where `ρ_B = Tr_A{ρ_AB}`.

**Formalization Note** `H_A ⊗ H_B` is indexed by `a × b` (Kronecker convention), and `Tr_A` is
the published `WildeQIT.partialTraceLeft`. Entropies are in bits. -/
noncomputable def qCondEntropy {a b : Type} [Fintype a] [DecidableEq a] [Fintype b]
    [DecidableEq b] (ρ : Matrix (a × b) (a × b) ℂ) : ℝ :=
  vonNeumann ρ - vonNeumann (WildeQIT.partialTraceLeft ρ)

end WildeQIT.QMemory



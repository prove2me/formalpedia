-- Prove2me | Definitions.Def_WildeQIT_ErasureClassical_MixedEnsemble
-- name    : WildeQIT_ErasureClassical_MixedEnsemble
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T18:35:57.972594+00:00
-- url     : https://prove2.me/theorems/d22654b5-e2cc-4f3c-9495-3d21d43682bd
-- title:
--   Classical–quantum input ensemble $\{p_X(x),\rho^x\}$
-- statement:
--   A **classical–quantum input** for a channel with input system $A$ is a probability distribution $p_X$ on a finite alphabet together with a density operator $\rho^x_A$ for every letter $x$, i.e. the state
--
--   $$
--   \rho_{XA}\equiv\sum_x p_X(x)\,|x\rangle\langle x|_X\otimes\rho^x_A .
--   $$
--
--   Definition 13.3.1 maximizes the Holevo information over all such inputs.
--
--   **Formalization Note** The alphabet is `Fin k` with $k$ part of the data.
-- source:
--   Wilde, From Classical to Quantum Shannon Theory, arXiv:1106.1445v8, §13.3, (13.82), p. 400

import Definitions.Def_WildeQIT_FinDist
import Definitions.Def_WildeQIT_IsDensityOperator

/-!
Wilde, *From Classical to Quantum Shannon Theory*, arXiv:1106.1445v8, §13.3, p. 400, eq. (13.82)
(the general classical–quantum input `ρ_{XA} = ∑ₓ p_X(x)|x⟩⟨x|_X ⊗ ρˣ_A`).
-/

namespace WildeQIT.ErasureClassical

/-- **Classical–quantum input** `ρ_{XA} ≡ ∑ₓ p_X(x)|x⟩⟨x|_X ⊗ ρˣ_A` (Wilde, *From Classical to
Quantum Shannon Theory*, arXiv:1106.1445v8, (13.82), p. 400): an ensemble `{p_X(x), ρˣ}` of
density operators on the channel input, indexed by a finite classical alphabet.

**Formalization Note.** The alphabet is `Fin k` with `k : ℕ` part of the data (every finite
alphabet is in bijection with some `Fin k`, and the Holevo information is invariant under
relabeling). -/
structure MixedEnsemble (a : Type) [Fintype a] where
  /-- The size of the classical alphabet `X`. -/
  k : ℕ
  /-- The distribution `p_X`. -/
  p : FinDist (Fin k)
  /-- The signal states `ρˣ_A`. -/
  ρ : Fin k → Matrix a a ℂ
  /-- Each signal state is a density operator. -/
  isDensity : ∀ x, IsDensityOperator (ρ x)

end WildeQIT.ErasureClassical



-- Prove2me | Definitions.Def_WildeQIT_Degradable_complementaryApply
-- name    : WildeQIT_Degradable_complementaryApply
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T17:56:54.632239+00:00
-- url     : https://prove2.me/theorems/caf6dad4-fea8-41c0-aed3-97ffa76d8544
-- title:
--   Complementary channel $\mathcal N^c(\rho) = \mathrm{Tr}_B\{U\rho U^\dagger\}$
-- statement:
--   "Any quantum channel $\mathcal N_{A'\to B}$ has a complementary channel $\mathcal N^c_{A'\to E}$, realized by considering an isometric extension of the channel and tracing over Bob's system." With the canonical isometric extension $U^{\mathcal N}$,
--
--   $$
--   \mathcal N^c(\rho) \equiv \mathrm{Tr}_B\{U^{\mathcal N}\rho\,(U^{\mathcal N})^\dagger\},
--   $$
--
--   whose matrix entries are $\mathcal N^c(\rho)_{ij}=\mathrm{Tr}\{K_i\rho K_j^\dagger\}$.
--
--   It is the channel to the environment (the eavesdropper Eve) used in the definitions of degradability and of the private information.
--
--   **Formalization Note** The partial trace over the left factor $B$ of `b × N.ι` is the published `WildeQIT.partialTraceLeft`.
-- source:
--   Wilde, From Classical to Quantum Shannon Theory, arXiv:1106.1445v8, §13.5.1, p. 412 (complementary channel)

import Definitions.Def_WildeQIT_Degradable_isometricExtension
import Definitions.Def_WildeQIT_partialTrace

/-!
Wilde, *From Classical to Quantum Shannon Theory*, arXiv:1106.1445v8, §13.5.1, p. 412 ("any quantum channel `N_{A′→B}` has a complementary channel
`N^c_{A′→E}`, realized by considering an isometric extension of the channel and tracing over
Bob's system"); Definition 5.2.2.
-/

open Matrix

namespace WildeQIT.Degradable

/-- **Complementary channel `N^c_{A′→E}`** (Wilde, *From Classical to Quantum Shannon Theory*, arXiv:1106.1445v8, p. 412): the isometric extension followed by
the partial trace over Bob's system, `N^c(ρ) = Tr_B(U^N ρ U^N†)`.

**Formalization Note.** Uses the canonical isometric extension `isometricExtension N`, with
environment `N.ι`; the result has entries `N^c(ρ)_{ij} = Tr(Kᵢ ρ Kⱼ†)`. The partial trace over
the left factor `B` of `b × N.ι` is the published `WildeQIT.partialTraceLeft`. -/
def complementaryApply {a b : Type} [Fintype a] [Fintype b] [DecidableEq a] (N : QChannel a b)
    (ρ : Matrix a a ℂ) : Matrix N.ι N.ι ℂ :=
  partialTraceLeft (isometricExtension N * ρ * (isometricExtension N)ᴴ)

end WildeQIT.Degradable



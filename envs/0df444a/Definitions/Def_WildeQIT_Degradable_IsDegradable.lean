-- Prove2me | Definitions.Def_WildeQIT_Degradable_IsDegradable
-- name    : WildeQIT_Degradable_IsDegradable
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T17:57:34.935836+00:00
-- url     : https://prove2.me/theorems/56a3357c-6e2a-44fa-9e5b-0adfe6d247bd
-- title:
--   Degradable quantum channel (Definition 13.5.2)
-- statement:
--   A quantum channel $\mathcal N_{A'\to B}$ is **degradable** if there exists a degrading channel $\mathcal D_{B\to E}$ such that
--
--   $$
--   \mathcal N^c_{A'\to E}(\rho_{A'}) = \mathcal D_{B\to E}(\mathcal N_{A'\to B}(\rho_{A'}))
--   $$
--
--   for every input state $\rho_{A'}$, where $\mathcal N^c$ is a channel complementary to $\mathcal N$. Bob can then simulate Eve's output by processing his own.
--
--   Degradable channels have additive coherent and private information (Theorems 13.5.1 and 13.6.3).
--
--   **Formalization Note** $\mathcal N^c$ is the complementary channel of the canonical isometric extension (environment `N.ι`), and $\mathcal D$ is any Kraus channel from $B$ to that environment. The choice of complementary channel does not matter: two complementary channels differ by an isometry (or partial isometry) on the environment, and composing $\mathcal D$ with it gives a degrading channel for the other. "Every input state" is quantification over density operators.
-- source:
--   Wilde, From Classical to Quantum Shannon Theory, arXiv:1106.1445v8, Definition 13.5.2, eq. (13.155), p. 412

import Definitions.Def_WildeQIT_Degradable_complementaryApply
import Definitions.Def_WildeQIT_IsDensityOperator

/-!
Wilde, *From Classical to Quantum Shannon Theory*, arXiv:1106.1445v8, Definition 13.5.2 (Degradable Quantum Channel), p. 412.
-/

open Matrix

namespace WildeQIT.Degradable

/-- **Definition 13.5.2 (Degradable Quantum Channel)** (Wilde, *From Classical to Quantum Shannon Theory*, arXiv:1106.1445v8, p. 412, eq. (13.155)):
"A quantum channel `N_{A′→B}` is degradable if there exists a degrading channel `D_{B→E}` such
that `N^c_{A′→E}(ρ_{A′}) = D_{B→E}(N_{A′→B}(ρ_{A′}))` for any input state `ρ_{A′}` and where
`N^c_{A′→E}` is a channel complementary to `N_{A′→B}`."

**Formalization Note.** The complementary channel is the one of the canonical isometric
extension (environment `N.ι`); the degrading channel `D` is any quantum channel from `B` to that
environment, in Kraus form. Degradability does not depend on the choice of complementary
channel: two complementary channels differ by an isometry `V` on the environment (or its
adjoint, followed by a channel on the orthogonal complement), and composing `D` with that map
gives a degrading channel for the other. "For any input state" is quantification over density
operators. -/
def IsDegradable {a b : Type} [Fintype a] [Fintype b] [DecidableEq a] [DecidableEq b]
    (N : QChannel a b) : Prop :=
  ∃ D : QChannel b N.ι, ∀ ρ : Matrix a a ℂ, IsDensityOperator ρ →
    complementaryApply N ρ = D.apply (N.apply ρ)

end WildeQIT.Degradable



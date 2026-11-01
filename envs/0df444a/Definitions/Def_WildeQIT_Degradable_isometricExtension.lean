-- Prove2me | Definitions.Def_WildeQIT_Degradable_isometricExtension
-- name    : WildeQIT_Degradable_isometricExtension
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T17:56:25.204762+00:00
-- url     : https://prove2.me/theorems/741d62ea-3c6c-46c9-8b98-15dabdf9a404
-- title:
--   Canonical isometric extension $U^{\mathcal N}_{A'\to BE} = \sum_i K_i\otimes|i\rangle_E$
-- statement:
--   Let $\mathcal N_{A'\to B}$ be a quantum channel with Kraus operators $\{K_i\}$. Its **canonical isometric extension** is the operator from $A'$ to $B\otimes E$
--
--   $$
--   U^{\mathcal N}_{A'\to BE} \equiv \sum_i K_i\otimes|i\rangle_E ,
--   $$
--
--   where the environment $E$ has one basis vector $|i\rangle_E$ per Kraus operator. By the completeness relation $\sum_i K_i^\dagger K_i = I$ it is an isometry, and $\mathrm{Tr}_E\{U\rho U^\dagger\}=\mathcal N(\rho)$.
--
--   The complementary channel and the private information of this chapter are defined through it.
--
--   **Formalization Note** The environment is the Kraus index type `N.ι`, the right factor of `b × N.ι`; the matrix entry at row $(y,i)$ and column $x$ is $K_i(y,x)$. Any other isometric extension differs from this one by an isometry on the environment.
-- source:
--   Wilde, From Classical to Quantum Shannon Theory, arXiv:1106.1445v8, §13.5.1, p. 412, and §13.6, p. 416 (isometric extension U^N_{A′→BE}, §5.2)

import Definitions.Def_WildeQIT_QChannel

/-!
Wilde, *From Classical to Quantum Shannon Theory*, arXiv:1106.1445v8, §5.2 (isometric extension), used in §13.5, p. 412, and §13.6, p. 416
(`U^N_{A′→BE}`).
-/

open Matrix

namespace WildeQIT.Degradable

/-- **Canonical isometric extension `U^N_{A′→BE}`** of a channel given by Kraus operators
(Wilde, *From Classical to Quantum Shannon Theory*, arXiv:1106.1445v8, §5.2.2, and pp. 412, 416): `U^N = ∑ᵢ Kᵢ ⊗ |i⟩_E`, an operator from `A′` to `BE` whose
environment `E` has one basis vector per Kraus operator. It satisfies `U†U = I` by the
completeness relation, and `Tr_E(U ρ U†) = N(ρ)`.

**Formalization Note.** `E` is the Kraus index type `N.ι`, the right factor of `b × N.ι`. Every
other isometric extension of `N` differs from this one by an isometry on the environment, which
changes none of the entropies used in this chapter. -/
def isometricExtension {a b : Type} [Fintype a] [Fintype b] [DecidableEq a] (N : QChannel a b) :
    Matrix (b × N.ι) a ℂ :=
  Matrix.of fun yi x => N.K yi.2 yi.1 x

end WildeQIT.Degradable



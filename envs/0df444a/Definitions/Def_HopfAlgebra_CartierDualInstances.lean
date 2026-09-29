-- Prove2me | Definitions.Def_HopfAlgebra_CartierDualInstances
-- name    : HopfAlgebra_CartierDualInstances
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:27.528425+00:00
-- url     : https://prove2.me/theorems/41281420-3136-51dc-923c-ed6dd81a7b8f
-- title:
--   Cartier dual mixins keyed through its bialgebra instance
-- statement:
--   Throughout, $R$ is a commutative ring and $A$ a commutative ring equipped with an $R$-bialgebra structure which is finite and free as an $R$-module; $\mathrm{CartierDual}\ R\ A$ is, by definition, the dual module $\mathrm{Module.Dual}\ R\ A = A \to_{R} R$, carrying the convolution product transposed from the comultiplication of $A$, the counit as unit, the comultiplication transposed from the multiplication of $A$, and evaluation at $1$ as counit; the bialgebra structure on it is [`CartierDual.instBialgebra`](../def/HopfAlgebra_CartierDual.html#L1008). Three declarations re-register, for this carrier, properties already established for the dual: that the coalgebra obtained from [`CartierDual.instBialgebra`](../def/HopfAlgebra_CartierDual.html#L1008) through `Bialgebra.toCoalgebra` is cocommutative (the comultiplication is unchanged by the flip of the two tensor factors), and that the $R$-module obtained from the same bialgebra structure through `Bialgebra.toAlgebra` is finite and free. The propositions are the same as those proved in the definition module for the directly constructed coalgebra and algebra structures; what differs is the structure path through which the module and coalgebra structures are presented.
--
--   The module also contains two declarations, `test_bialgebra_mixins` and `test_commring_hopf_mixins`, whose conclusion is `True`: the first takes a semiring $C$ that is an $R$-bialgebra, cocommutative, and finite, free and flat as an $R$-module, the second a commutative ring $C$ that is an $R$-Hopf algebra with the same three module hypotheses and cocommutativity. Their content lies in their hypothesis lists, which are instantiated at $\mathrm{CartierDual}\ R\ A$ and at the bidual $\mathrm{CartierDual}\ R\ (\mathrm{CartierDual}\ R\ A)$.
--
--   **Relation to Mathlib.** Mathlib supplies `Coalgebra`, `Bialgebra`, `HopfAlgebra`, `Coalgebra.IsCocomm`, `Module.Dual` and `Module.Finite`/`Module.Free`/`Module.Flat`; the Cartier dual of a finite free commutative bialgebra, with its convolution ring, coalgebra, bialgebra and Hopf structures, is the project's own construction, made in the imported definition module. These declarations add no new notion, only further instances for that construction.
--
--   **Where it is used.** The Cartier dual supplies the Hopf-algebraic side of duality for finite flat commutative group schemes, used in the project's treatment of the finite group schemes attached to torsion of elliptic curves and their Galois representations. These instances let generic statements whose hypotheses are phrased in terms of a bialgebra or Hopf algebra that is cocommutative and finite free over the base be applied to the Cartier dual and to its bidual.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_HopfAlgebra_CartierDualInstances.lean

import Mathlib
import Definitions.Def_HopfAlgebra_CartierDual

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

namespace CartierDual

universe u v

section
variable (R : Type u) (A : Type v) [CommRing R] [CommRing A] [Bialgebra R A] [Module.Finite R A] [Module.Free R A]

instance instIsCocommViaBialgebra :
    @Coalgebra.IsCocomm R (CartierDual R A) _ _ _ (@Bialgebra.toCoalgebra R (CartierDual R A) _ _ (instBialgebra R A)) :=
  instIsCocomm R A

instance instModuleFiniteViaBialgebra :
    @Module.Finite R (CartierDual R A) _ _ (@Algebra.toModule R (CartierDual R A) _ _ (@Bialgebra.toAlgebra R (CartierDual R A) _ _ (instBialgebra R A))) :=
  instModuleFinite R A

instance instModuleFreeViaBialgebra :
    @Module.Free R (CartierDual R A) _ _ (@Algebra.toModule R (CartierDual R A) _ _ (@Bialgebra.toAlgebra R (CartierDual R A) _ _ (instBialgebra R A))) :=
  instModuleFree R A

end

section Test

universe w
variable (R : Type u) (A : Type v) [CommRing R] [CommRing A]

theorem test_bialgebra_mixins {C : Type w} [Semiring C] [Bialgebra R C] [Coalgebra.IsCocomm R C]
    [Module.Finite R C] [Module.Free R C] [Module.Flat R C] : True := trivial

theorem test_commring_hopf_mixins {C : Type w} [CommRing C] [HopfAlgebra R C] [Coalgebra.IsCocomm R C]
    [Module.Finite R C] [Module.Free R C] [Module.Flat R C] : True := trivial

example [Bialgebra R A] [Module.Finite R A] [Module.Free R A] : True :=
  test_bialgebra_mixins R (C := CartierDual R A)

example [HopfAlgebra R A] [Module.Finite R A] [Module.Free R A] [Coalgebra.IsCocomm R A] : True :=
  test_commring_hopf_mixins R (C := CartierDual R A)

example [HopfAlgebra R A] [Module.Finite R A] [Module.Free R A] [Coalgebra.IsCocomm R A] : True :=
  test_commring_hopf_mixins R (C := CartierDual R (CartierDual R A))

end Test

end CartierDual


